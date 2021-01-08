#!/usr/bin/python
# Simple, proof-generating QBF solver based on BDDs

import sys
import getopt
import datetime

import bdd
import resolver
import stream
import qreader
import permutation
import proof

# Increase maximum recursion depth
sys.setrecursionlimit(50 * sys.getrecursionlimit())

def usage(name):
    sys.stderr.write("Usage: %s [-h][-b][-v LEVEL] [-m (n|s|r)] [-i CNF] [-o file.{qrat,qproof}] [-B BPERM] [-p VPERM] [-c CLUSTER] [-L logfile]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -b          Use bucket elimination\n")
    sys.stderr.write("  -m MODE     Set proof mode (n = no proof, s = satisfaction, r = refutation)\n")
    sys.stderr.write("  -v LEVEL    Set verbosity level\n")
    sys.stderr.write("  -i CNF      Name of CNF input file\n")
    sys.stderr.write("  -o pfile    Name of proof output file (QRAT or QPROOF format)\n")
    sys.stderr.write("  -B BPERM    Process terms via bucket elimination ordered by permutation file BPERM\n")
    sys.stderr.write("  -p VPERM    Name of file specifying mapping from CNF variable to BDD level\n")
    sys.stderr.write("  -c CLUSTER  Name of file specifying how to group clauses into clusters\n")
    sys.stderr.write("  -L logfile  Append standard error output to logfile\n")

# Verbosity levels
# 0: Totally silent
# 1: Key statistics only
# 2: Summary information
# 3: Proof information
# 4: ?
# 5: Tree generation information

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

# Abstract representation of Boolean function
class Term:

    manager = None
    root = None
    support = None    # Variables in support represented by list
    size = 0
    validation = None # Clause id providing validation
    mode = None # What is type of proof is being generated

    def __init__(self, manager, root, validation, mode = None):
        self.manager = manager
        self.root = root
        self.size = self.manager.getSize(root)
        self.support = None
        self.validation = validation
        if mode is None:
            self.mode = proof.ProverMode.noProof
        else:
            self.mode = mode

    def getSupport(self):
        if self.support is None:
            self.support = self.manager.getSupportIds(self.root)
        return self.support

    # Generate conjunction of two terms
    def combine(self, other):
        validation = None
        if self.mode == proof.ProverMode.refProof:
            antecedents = [self.validation, other.validation]
            newRoot, implication = self.manager.applyAndJustify(self.root, other.root)
            if newRoot == self.manager.leaf0:
                comment = "Conjunction: Validation of Empty clause"
            else:
                comment = "Conjunction: Validation of %s" % newRoot.label()
            if implication == resolver.tautologyId:
                if newRoot == self.root:
                    validation = self.validation
                elif newRoot == other.root:
                    validation = other.validation
            else:
                antecedents += [implication]
            if validation is None:
                validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, comment)
        else:
            newRoot = self.manager.applyAnd(self.root, other.root)
        return Term(self.manager, newRoot, validation, mode = self.mode)

    def equantify(self, literals, prover):
        newRoot = self.manager.equant(self.root, literals)
        validation = None
        if self.mode == proof.ProverMode.refProof:
            antecedents = [self.validation]
            check, implication = self.manager.justifyImply(self.root, newRoot)
            if not check:
                raise bdd.BddException("Implication failed %s -/-> %s" % (self.root.label(), newRoot.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, "EQuant: Validation of %s" % newRoot.label())
        return Term(self.manager, newRoot, validation, mode = self.mode)

    def uquantify(self, literals, prover):
        newRoot = self.manager.uquant(self.root, literals)
        validation = None
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # Refutation proof: Split universal quantification into two operations per variable
    def restrictRefutation(self, literal, prover):
        antecedents = [self.validation]
        newRoot, implication = self.manager.applyRestrictDown(self.root, literal)
        if implication != resolver.tautologyId:
            antecedents += [implication]
        if newRoot == self.manager.leaf1:
            return None
        elif newRoot == self.manager.leaf0:
            comment = "Restrict: Validation of Empty clause"
        else:
            comment = "Restrict: Validation of %s" % newRoot.label()
        ulit = literal.variable.id
        if literal.high == self.manager.leaf1:
            ulit = -ulit
        rclause = [ulit, newRoot.id]
        # Now apply universal reduction.
        comment = "Apply universal reduction to eliminate variable %d" % literal.variable.id
        if self.manager.prover.doQrat:
            rule1 = self.manager.prover.createClause(rclause, antecedents, comment)
            validation = self.manager.prover.createClause(rclause, [rule1], comment=None, isUniversal=True)
        else:
            rule1 = self.manager.prover.proveAddResolution(rclause, antecedents, comment)
            validation = self.manager.prover.proveUniversal(ulit, rule1, None)
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # Satisfaction proof.  Existential quantification
    def equantifySatisfaction(self, lit, nlit, prover):
        lname = str(lit.variable)
        litid = lit.variable.id

        root1, implication1 = self.manager.applyRestrictUp(self.root, lit)
        if root1 == self.manager.leaf1:
            # Implication will be [-lit, self.root.id]
            up1 = implication1
            shannon1 = None
        elif root1 == self.manager.leaf0:
            rclause = [-litid]
            comment = "Shannon Expansion: Assert !%s" % (lname)
            shannon1 = self.manager.prover.proveAdd(rclause, comment)
            up1 = shannon1
        else:
            rclause = [-litid, root1.id]
            comment = "Shannon Expansion: Assert %s --> %s" % (lname, root1.label())
            shannon1 = self.manager.prover.proveAdd(rclause, comment)
            antecedents = [shannon1, implication1]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up1 = prover.proveAddResolution([-litid, self.root.id], antecedents, comment)

        root0, implication0 = self.manager.applyRestrictUp(self.root, nlit)
        if root0 == self.manager.leaf1:
            up0 = implication0
            shannon0 = None
        elif root0 == self.manager.leaf0:
            rclause = [litid]
            comment = "Shannon Expansion: Assert %s" % (lname)
            shannon0 = self.manager.prover.proveAdd(rclause, comment)
            up0 = shannon0
        else:
            rclause = [litid, root0.id]
            comment = "Shannon Expansion: Assert -%s --> %s" % (lname, root0.label())
            shannon0 = self.manager.prover.proveAdd(rclause, comment)
            antecedents = [shannon0, implication0]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up0 = prover.proveAddResolution([litid, self.root.id], antecedents, comment)

        antecedents = [up1, up0]
        comment = "Deletion of clause [%d] during existential quantfication" % self.root.id
        prover.proveDeleteResolution(self.validation, antecedents, comment)
        prover.qcollect(lit.variable.qlevel)

        comment = "Davis Putnam reduction of variable %s" % lname
        if root1 == self.manager.leaf1:
            newRoot = root1
            prover.proveDeleteDavisPutnam(litid, [shannon0], [], comment)
            validation = self.manager.prover.proveAdd([newRoot.id])
        elif root0 == self.manager.leaf1:
            newRoot = root0
            prover.proveDeleteDavisPutnam(litid, [shannon1], [], comment)
            validation = self.manager.prover.proveAdd([newRoot.id])
        else:            
            comment = "Introduce intermediate disjunction of %s and %s" % (root1.label(), root0.label())
            distid = prover.proveAdd([root1.id, root0.id], comment = comment)
            comment = "Delete Shannon expansion clauses"
            prover.proveDeleteDavisPutnam(litid, [shannon1, shannon0], [distid], comment)
            newRoot, justifyOr = self.manager.applyOrJustify(root1, root0)
            antecedents = []
            if justifyOr == resolver.tautologyId:
                pass
            else:
                antecedents.append(justifyOr)
            if newRoot != self.manager.leaf1:
                comment = "Assert unit clause for disjunction %s (= %s | %s)" % (newRoot.label(), root1.label(), root0.label())
                validation = self.manager.prover.proveAdd([newRoot.id], comment)
                antecedents.append(validation)
            comment = "Remove intermediate disjunction"
            prover.proveDeleteResolution(distid, antecedents, comment)

        if newRoot == self.manager.leaf1:
            return None

        # Manager needs to be informed that quantification has completed
        self.manager.markQuantified(lit.variable)
        return Term(self.manager, newRoot, validation, mode = self.mode)


class SolverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Solver Exception: " + str(self.value)


class Solver:
    
    verbLevel = 1
    manager = None
    # How many terms have been generated
    termCount = 0
    # Mapping from input Ids to BDD representation of literal
    litMap = {}

    # Dictionary of Ids of terms remaining to be combined
    activeIds = {}
    # Have found formula to be True, False, or Unknown (None)
    outcome = None
    permuter = None
    prover = None
    writer = None
    # Mapping from quantifier levels to tuple (vars,isExistential)
    quantMap = {}

    def __init__(self, reader = None, prover = None, permuter = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if prover is None:
            prover = proof.Prover(verbLevel = verbLevel)
        self.prover = prover
        self.writer = prover.writer
        #  mapping from each variable to (qlevel,isExistential)
        qmap = { v : (qlevel, isExistential) for (v, qlevel, isExistential) in reader.varList }
        # Construct quantifer level mapping
        self.quantMap = {}
        for (v,qlevel,isExistential) in reader.varList:
            if qlevel in self.quantMap:
                self.quantMap[qlevel][0].append(v)
            else:
                self.quantMap[qlevel] = ([v], isExistential)
        clauseCount = 0
        # Print input clauses
        for clause in reader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount, isInput = True)

        if clauseCount == 0:
            self.writer.write("No clauses in CNF File\n")
            raise SolverException("Empty CNF file")

        self.prover.inputDone()

        self.manager = bdd.Manager(prover = self.prover, rootGenerator = self.rootGenerator,
                                   nextNodeId = reader.nvar+1, verbLevel = verbLevel)
        # Generate BDD representations of literals
        if permuter is None:
            # Default is identity permutation
            permuter = permutation.Permuter(list(range(1, reader.nvar+1)))
        self.permuter = permuter
        # Construct literal map
        self.litMap = {}
        for vlevel in range(1, reader.nvar+1):
            inputId = self.permuter.forward(vlevel)
            qlevel,isExistential = qmap[inputId]
            var = self.manager.newVariable(qlevel, name = "input-%d" % inputId, id = inputId, existential = isExistential)
            t = self.manager.literal(var, 1)
            self.litMap[ inputId] = t
            e = self.manager.literal(var, 0)
            self.litMap[-inputId] = e
        # Generate BDD representations of clauses
        self.termCount = 0
        self.activeIds = {}
        for clause in reader.clauses:
            self.termCount += 1
            litList = [self.litMap[v] for v in clause]
            if self.prover.mode == proof.ProverMode.noProof:
                root, validation = self.manager.constructClauseNoProof(self.termCount, litList)
            elif self.prover.mode == proof.ProverMode.refProof:
                root, validation = self.manager.constructClause(self.termCount, litList)
            else:
                root, validation = self.manager.constructClauseReverse(self.termCount, litList)
            term = Term(self.manager, root, validation, mode = prover.mode)
            self.activeIds[self.termCount] = term
        self.outcome = None

    # Determine whether term is constant.  Optionally matching specified value
    def termIsConstant(self, id):
        root = self.activeIds[id].root
        return root == self.manager.leaf1 or root == self.manager.leaf0

    # Simplistic version of scheduling
    def choosePair(self):
        ids = sorted(self.activeIds.keys())
        return ids[0], ids[1]

    def combineTerms(self, id1, id2):
        termA = self.activeIds[id1]
        termB = self.activeIds[id2]
        self.termCount += 1
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) & T%d (Node %s) --> T%d" % (id1, termA.root.label(), id2, termB.root.label(), self.termCount))
        newTerm = termA.combine(termB)
        comment = "T%d (Node %s) & T%d (Node %s) --> T%s (Node %s)" % (id1, termA.root.label(), id2, termB.root.label(),
                                                                      self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        if self.verbLevel >= 3:
            print("  T%d (Node N%d, QL=%d) support = %s" % (self.termCount, newTerm.root.id, newTerm.root.qlevel, self.manager.getSupportIds(newTerm.root)))

        if self.prover.mode == proof.ProverMode.satProof:
            comment = "Assertion of T%d (N%d)" % (self.termCount, newTerm.root.id)
            newTerm.validation = self.prover.proveAdd([newTerm.root.id], comment)
            justificationA = [newTerm.validation]
            implA = self.manager.justifyImply(newTerm.root, termA.root)[1]
            if implA is not resolver.tautologyId:
                justificationA.append(implA)
            implB = self.manager.justifyImply(newTerm.root, termB.root)[1]
            justificationB = [newTerm.validation]
            if implB is not resolver.tautologyId:
                justificationB.append(implB)
            comment = "Delete unit clauses for T%d and T%d" % (id1, id2)
            self.prover.proveDeleteResolution(termA.validation, justificationA, comment)
            self.prover.proveDeleteResolution(termB.validation, justificationB)

        del self.activeIds[id1]
        del self.activeIds[id2]
        if self.prover.opened and self.verbLevel >= 3:
            self.writer.write(comment + '\n')
        self.activeIds[self.termCount] = newTerm
        if newTerm.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Conjunction: Formula FALSE\n")
            self.outcome = False
            self.manager.summarize()
            return -1
        return self.termCount

    # Used in refutation proofs, and when no proof
    def equantifyTerm(self, id, varList):
        term = self.activeIds[id]
        del self.activeIds[id]
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        self.termCount += 1
        vstring = " ".join(sorted([str(v) for v in varList]))
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) EQuant(%s) --> T%d" % (id, term.root.label(), vstring, self.termCount))
        newTerm = term.equantify(clause, self.prover)
        if self.prover.mode == proof.ProverMode.refProof:
            comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
            self.prover.comment(comment)
            if self.verbLevel >= 3:
                print(comment)
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC(generateClauses = self.prover.mode != proof.ProverMode.noProof)
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return self.termCount

    # Used in refutation proofs
    def uquantifyTermSingle(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) Restrict1(%s)" % (id, term.root.label(), str(var)))
        term1 = term.restrictRefutation(lit, self.prover)
        if term1 is not None:
            if term1.root == self.manager.leaf0:
                if self.verbLevel >= 1:
                    self.writer.write("Positive cofactor FALSE\n")
                self.outcome = False
                self.manager.summarize()
                return -1
            self.termCount += 1
            id1 = self.termCount
            self.activeIds[id1] = term1

        nlit = self.litMap[-var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) Restrict0(%s)" % (id, term.root.label(), str(var)))
        term0 = term.restrictRefutation(nlit, self.prover)
        if term0 is not None:
            if term0.root == self.manager.leaf0:
                if self.verbLevel >= 1:
                    self.writer.write("Negative cofactor FALSE\n")
                self.outcome = False
                self.manager.summarize()
                return -1
            self.termCount += 1
            id0 = self.termCount
            self.activeIds[id0] = term0

        if term1 is None and term0 is None:
            msg = "Got C1 for both cofactors of %s" % (term.root.label())
            raise SolverException(msg)

        if term1 is None:
            newId = id0
        elif term0 is None:
            newId = id1
        else:
            newId = self.combineTerms(id1, id0)
        # Manager needs to be informed that quantification has completed
        self.manager.markQuantified(lit.variable)
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return newId

    # Used in satisfaction proofs
    def equantifyTermSingle(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        nlit = self.litMap[-var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) EQuant(%s)" % (id, term.root.label(), str(var)))
            print("  lit = %s,  nlit = %s" % (lit.label(), nlit.label()))
        newTerm = term.equantifySatisfaction(lit, nlit, self.prover)
        newId = -1
        if newTerm is None:
            if self.verbLevel >= 3:
                print("T%d (Node %s) EQuant(%s) --> ONE" % (id, term.root.label(), str(var)))
        else:
            self.termCount += 1

            comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, newTerm.root.label())
            self.prover.comment(comment)
            if self.verbLevel >= 3:
                print(comment)
            self.activeIds[self.termCount] = newTerm
            newId = self.termCount
        # This could be a good time for garbage collection
        self.manager.checkGC(generateClauses = False)
        return newId



    # Used in satisfaction proofs, and when no proof
    def uquantifyTerm(self, id, varList):
        term = self.activeIds[id]
        del self.activeIds[id]
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        vstring = " ".join(sorted([str(v) for v in varList]))
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) UQuant(%s)" % (id, term.root.label(), vstring))
        newTerm = term.uquantify(clause, self.prover)
        if newTerm.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Universal Quantification: Formula FALSE\n")
            self.outcome = False
            self.manager.summarize()
            return -1
        self.termCount += 1
        if self.prover.mode == proof.ProverMode.satProof:
            comment = "T%d (Node %s) UQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
            newTerm.validation = self.manager.prover.proveAdd([newTerm.root.id], comment)
            antecedents = [newTerm.validation]
            check, implication = self.manager.justifyImply(newTerm.root, term.root)
            if not check:
                raise bdd.BddException("Implication failed %s -/-> %s" % (newTerm.root.label(), term.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            self.manager.prover.proveDeleteResolution(term.validation, antecedents, "Delete unit clause for T%d" % (id))
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        self.manager.checkGC(generateClauses = False)
        return self.termCount

    def processClusters(self, cfile):
        try:
            infile = open(cfile, 'r')
        except:
            self.writer.write("ERROR: Could not open cluster file '%s'\n" % cfile)
            return False
        clusterCount = 0
        clauseCount = 0
        for line in infile:
            line = trim(line)
            cnum = clusterCount + 1
            slist = line.split()
            try:
                clist = [int(s) for s in line.split()]
            except:
                self.writer.write("ERROR: Invalid clause number in cluster #%d\n" % cnum)
                return False
            if len(clist) == 0:
                continue
            id = clist[0]
            for nextId in clist[1:]:
                id = self.combineTerms(id, nextId)
                if id < 0:
                    self.writer.write("ERROR: Conjunction of input clauses for cluster #%d is unsatisfiable\n" % cnum)
                    return False
            clauseCount += len(clist)
            clusterCount += 1
            if self.verbLevel >= 3:
                self.writer.write("Combined %d clauses to form cluster #%d (T%d)\n" % (len(clist), cnum, id))
        if self.verbLevel >= 2:
            self.writer.write("Combined %d clauses to form %d clusters\n" % (clauseCount, clusterCount))
        infile.close()
        return True
                

    def runNoSchedule(self):
        # Start by conjuncting all clauses to get single BDD
        id = self.activeIds.keys()[0]
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            id = self.combineTerms(i, j)
            if id < 0:
                return
        if self.verbLevel >= 2:
            self.writer.write("Conjunction of clauses.  Size: %d\n" % (self.activeIds[id].size))
        # Now handle all of the quantifications:
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        for level in levels:
     
            if self.termIsConstant(id):
                if self.verbLevel >= 3:
                    self.writer.write("Encountered constant value before performing quantification level %d\n" % level)
                break
            vars, isExistential = self.quantMap[level]
            if len(vars) == 0:
                continue
            if self.verbLevel >= 3:
                self.writer.write("Quantifying %s level %d.  Vars = %s\n" % 
                                  ("existential" if isExistential else "universal", level, str(vars)))
            if self.prover.mode == proof.ProverMode.refProof:
                if isExistential:
                    id = self.equantifyTerm(id, vars)
                else:
                    # Must have single variable at this level
                    v = vars[0]
                    id = self.uquantifyTermSingle(id, v)
                    if id < 0:
                        return
            else:
                if isExistential:
                    # Must have single variable as this level
                    v = vars[0]
                    id = self.equantifyTermSingle(id, v)
                    if id < 0:
                        break
                else:
                    id = self.uquantifyTerm(id, vars)

                    if id < 0:
                        return

        # Get here only haven't hit 0
        if self.prover.mode == proof.ProverMode.satProof:
            # Make sure all clauses cleared away
            self.prover.qcollect(1)
        if self.verbLevel > 0:
            if self.prover.mode == proof.ProverMode.refProof:
                self.writer.write("ERROR: Formula is TRUE\n")
            else:
                self.writer.write("Formula TRUE\n")
            self.manager.summarize()

        
    def placeInQuantBucket(self, buckets, id):
        term = self.activeIds[id]
        level = term.root.qlevel-1
        if level > 0:
            buckets[level].append(id)

    # Bucket elimination based on quantification levels
    def runQuantBucket(self):
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        buckets = { level : [] for level in levels }
        # Insert ids into lists according quantification level
        ids = sorted(self.activeIds.keys())
        for id in ids:
            if self.verbLevel >= 3:
                self.writer.write("Initial cluster #%d.  Size: %d\n" % (id, self.activeIds[id].size))
            self.placeInQuantBucket(buckets, id)
        for blevel in levels:
            vars, isExistential = self.quantMap[blevel]
            if self.verbLevel >= 3:
                self.writer.write("Quantifying %s level %d.  Vars = %s.  Bucket size = %d\n" %
                                  ("existential" if isExistential else "universal", blevel, str(vars), len(buckets[blevel])))
            if isExistential:
                # Conjunct all terms in bucket
                while len(buckets[blevel]) > 1:
                    id1 = buckets[blevel][0]
                    id2 = buckets[blevel][1]
                    buckets[blevel] = buckets[blevel][2:]
                    newId = self.combineTerms(id1, id2)
                    if newId < 0:
                        # Hit False case
                        return
                    self.placeInQuantBucket(buckets, newId)
                if blevel > 0 and len(buckets[blevel]) > 0:
                    id = buckets[blevel][0]
                    buckets[blevel] = []
                    if self.prover.mode == proof.ProverMode.satProof:
                        # Satisfaction
                        if len(vars) > 1:
                            raise SolverException("Must serialize existential quantifiers")
                        var = vars[0]
                        newId = self.equantifyTermSingle(id, var)
                        if newId >= 0:
                            self.placeInQuantBucket(buckets, newId)
                    else:
                        # Refutation, or no proof
                        newId = self.equantifyTerm(id, vars)
                        self.placeInQuantBucket(buckets, newId)
            else:
                # Universal quantification
                if self.prover.mode == proof.ProverMode.refProof:
                    # Require vars to be single variable
                    if len(vars) > 1:
                        raise SolverException("Must serialize universal quantifiers")
                    v = vars[0]
                    for id in buckets[blevel]:
                        newId = self.uquantifyTermSingle(id, v)
                        if newId < 0:
                            # Formula is False
                            return
                        self.placeInQuantBucket(buckets, newId)
                else:
                    # Satisfaction, or no proof
                    for id in buckets[blevel]:
                        newId = self.uquantifyTerm(id, vars)
                        if newId < 0:
                            # Formula is False
                            if self.verbLevel >= 0:
                                if self.proverMode == proof.ProverMode.satProof:
                                    self.writer.write("ERROR: Formula is FALSE\n")
                                else:
                                    self.writer.write("Formula is FALSE\n")
                                return
                        self.placeInQuantBucket(buckets, newId)

        # Get here only haven't hit 0
        if self.prover.mode == proof.ProverMode.satProof:
            # Make sure all clauses cleared away
            self.prover.qcollect(1)

        if self.verbLevel >= 0:
            if self.prover.mode == proof.ProverMode.refProof:
                self.writer.write("ERROR: Formula is TRUE\n")
            else:
                self.writer.write("Formula TRUE\n")
            self.manager.summarize()

    # Provide roots of active nodes to garbage collector
    def rootGenerator(self):
        rootList = [t.root for t in self.activeIds.values()]
        rootList += self.litMap.values()
        return rootList


      
def run(name, args):
    cnfName = None
    proofName = None
    permuter = None
    bpermuter = None
    doBucket = False
    verbLevel = 1
    logName = None
    mode = proof.ProverMode.noProof
    clusterFile = None

    optlist, args = getopt.getopt(args, "hbB:c:m:v:i:o:m:p:L:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        if opt == '-b':
            doBucket = True
        elif opt == '-B':
            bpermuter = permutation.readPermutation(val)
            if bpermuter is None:
                return
        elif opt == '-c':
            clusterFile = val
        elif opt == '-m':
            if val == 's':
                mode = proof.ProverMode.satProof
            elif val == 'r':
                mode = proof.ProverMode.refProof
            elif val == 'n':
                mode = proof.ProverMode.noProof
            else:
                sys.stderr.write("Unknown proof mode '%s'\n" % val)
                usage(name)
                return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-o':
            proofName = val
        elif opt == '-p':
            permuter = permutation.readPermutation(val)
            if permuter is None:
                return
        elif opt == '-L':
            logName = val
        else:
            sys.stderr.write("Unknown option '%s'\n" % opt)
            usage(name)
            return

    writer = stream.Logger(logName)

    try:
        prover = proof.Prover(proofName, writer = writer, verbLevel = verbLevel, mode = mode)
    except Exception as ex:
        writer.write("Couldn't create prover (%s)\n" % str(ex))
        return

    start = datetime.datetime.now()

    stretchExistential = mode == proof.ProverMode.satProof
    stretchUniversal = mode == proof.ProverMode.refProof

    try:
        reader = qreader.QcnfReader(cnfName, bpermuter, stretchExistential, stretchUniversal)
    except Exception as ex:
        writer.write("Aborted: %s\n" % str(ex))
        return
    
    if reader.stretched:
        prover.generateLevels(reader.varList)

    solver = Solver(reader, prover = prover, permuter = permuter, verbLevel = verbLevel)

    if clusterFile is None or solver.processClusters(clusterFile):
        if doBucket:
            solver.runQuantBucket()
        else:
            solver.runNoSchedule()

    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    if verbLevel > 0:
        writer.write("Elapsed time for SAT: %.2f seconds\n" % seconds)
    if writer != sys.stderr:
        writer.close()
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

    

    
