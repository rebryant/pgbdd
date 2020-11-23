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
    sys.stderr.write("Usage: %s [-h][-v LEVEL] [-i CNF] [-o file.{qrat,qproof}] [-m (s|r)] [-B BPERM] [-p PERMUTE] [-L logfile]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -m MODE     Set proof mode (s = satisfaction, r = refutation)\n")
    sys.stderr.write("  -v LEVEL    Set verbosity level\n")
    sys.stderr.write("  -i CNF      Name of CNF input file\n")
    sys.stderr.write("  -o pfile    Name of proof output file (QRAT or QPROOF format)\n")
    sys.stderr.write("  -B BPERM    Process terms via bucket elimination ordered by permutation file BPERM\n")
    sys.stderr.write("  -p PERMUTE  Name of file specifying mapping from CNF variable to BDD level\n")
    sys.stderr.write("  -L logfile  Append standard error output to logfile\n")

# Verbosity levels
# 0: Totally silent
# 1: Key statistics only
# 2: Summary information
# 3: Proof information
# 4: ?
# 5: Tree generation information


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
        if self.mode == proof.ProverMode.refProof:
            antecedents = [self.validation, other.validation]
            newRoot, implication = self.manager.applyAndJustify(self.root, other.root)
            if implication != resolver.tautologyId:
                antecedents += [implication]
            if newRoot == self.manager.leaf0:
                comment = "Validation of Empty clause"
            else:
                comment = "Validation of %s" % newRoot.label()
            validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, comment)
        elif self.mode == proof.ProverMode.satProof:
            newRoot = self.manager.applyAnd(self.root, other.root)
            implA = self.manager.justifyImply(newRoot, self.root)
            implB = self.manager.justifyImply(newRoot, other.root)
            comment = "Assertion of %s, and deletion of arguments %s and %s" % (newRoot.label(), self.label(), other.label())
            validation = self.prover.proveAdd([newRoot.id], comment)
            self.prover.proveDeleteResolution(self.id, [validation, implA])
            self.prover.proveDeleteResolution(other.id, [validation, implB])
        else:
            newRoot = self.manager.applyAnd(self.root, other.root)
            validation = None
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
            validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, "Validation of %s" % newRoot.label())
        return Term(self.manager, newRoot, validation, mode = self.mode)

    def uquantify(self, literals, prover):
        newRoot = self.manager.uquant(self.root, literals)
        validation = None
        if self.mode == proof.ProverMode.satProof:
            antecedents = [newRoot.id]
            check, implication = self.manager.justifyImply(newRoot, self.root)
            if not check:
                raise bdd.BddException("Implication failed %s -/-> %s" % (newRoot.label(), self.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            validation = self.manager.prover.proveDeleteResolution(self.id, antecedents, "Deletion of %s " % self.label())
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # Refutation proof: Split universal quantification into two operations per variable
    def restrictRefutation(self, literal, prover):
        antecedents = [self.validation]
        newRoot, implication = self.manager.applyRestrictDown(self.root, literal)
        if implication != resolver.tautologyId:
            antecedents += [implication]
        if newRoot == self.manager.leaf0:
            comment = "Validation of Empty clause"
        else:
            comment = "Validation of %s" % newRoot.label()
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
        rclause = [-litid, root1.id]
        comment = "Assert %s --> %s" % (lname, root1.label())
        shannon1 = self.manager.prover.proveAdd(rclause, comment)
        antecedents1 = [shannon1, implication1]
        up1 = self.prover.proveAddResolution([-litid, self.id], antecedents, None)

        root0, implication0 = self.manager.applyRestrictUp(self,root, nlit)
        rclause = [litid, root0.id]
        comment = "Assert -%s --> %s" % (lname, root0.label())
        shannon0 = self.manager.prover.proveAdd(rclause, comment)
        antecedents0 = [shannon0, implication0]
        up0 = self.prover.proveAddResolution([litid, self.id], antecedents, None)
        
        antecedents = [up1, up0]
        comment = "Deletion of %s during existential quantfication" % self.label()
        self.prover.deleteResolution(self.validation, antecedents, comment)
        comment = "Introduce intermediate disjunction of %s and %s" % (root1.label(), root0.label())
        distid = self.prover.proveAdd([root1.id, root0.id], comment = comment)
        self.prover.collect(lit.variable.qlevel)
        comment = "Davis Putnam reduction of variable %s" % lname
        self.prover.proveDeleteDavisPutnam(litid, [shannon1, shannon0], [distid], comment)
        newRoot, justifyOr = self.manager.applyOrJustify(root1, root0)
        antecedents = []
        if justifyOr != resolver.tautologyId:
            antecents.append(justifyOr)
        if newRoot == self.manager.leaf1:
            validation = resolver.tautologyId
        else:
            validation = self.manager.prover.proveAdd([newRoot])
            antecedents.append(validation)
        comment = "Remove intermediate disjunction"
        self.prover.proveDeleteResolution(distid, antecedents, comment)
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
    unsat = False
    permuter = None
    prover = None
    writer = None
    # Turn on to have information about node include number of solutions
    countSolutions = True
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
            root, validation = self.manager.constructClause(self.termCount, litList)
            term = Term(self.manager, root, validation, mode = prover.mode)
            self.activeIds[self.termCount] = term
        self.unsat = False

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

        del self.activeIds[id1]
        del self.activeIds[id2]
        if self.prover.opened and self.verbLevel >= 3:
            self.writer.write(comment + '\n')
        self.activeIds[self.termCount] = newTerm
        if newTerm.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Conjunction UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1
        return self.termCount

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
        comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return self.termCount

    def uquantifyTermSingle(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        self.termCount += 1
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) Restrict1(%s) --> T%d" % (id, term.root.label(), str(var), self.termCount))
        term1 = term.restrictRefutation(lit, self.prover)
        comment = "T%d (Node %s) Restrict1(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, term1.root.label())
        if term1.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Positive cofactor UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1, -1
        self.activeIds[self.termCount] = term1
        id1 = self.termCount
        nlit = self.litMap[-var]
        self.termCount += 1
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) Restrict0(%s) --> T%d" % (id, term.root.label(), str(var), self.termCount))
        term0 = term.restrictRefutation(nlit, self.prover)
        comment = "T%d (Node %s) Restrict0(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, term0.root.label())
        if term0.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Negative cofactor UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1, -1
        self.activeIds[self.termCount] = term0
        id0 = self.termCount
        newId = self.combineTerms(id0, id1)
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return newId


    def runNoSchedule(self):
        # Start by conjuncting all clauses to get single BDD
        id = 0
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            id = self.combineTerms(i, j)
            if id < 0:
                return
        # Now handle all of the quantifications:
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        for level in levels:
            vars, isExistential = self.quantMap[level]
            if len(vars) == 0:
                continue
            if self.verbLevel >= 3:
                self.writer.write("Quantifying %s level %d.  Vars = %s\n" % 
                                  ("existential" if isExistential else "universal", level, str(vars)))
            if isExistential:
                id = self.equantifyTerm(id, vars)
            else:
                for v in vars:
                    id = self.uquantifyTermSingle(id, v)
                    if id < 0:
                        return
        
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
                        # Hit unsat case
                        return
                    self.placeInQuantBucket(buckets, newId)
                # Quantify all variables for this bucket
                if blevel > 0 and len(buckets[blevel]) > 0:
                    id = buckets[blevel][0]
                    buckets[blevel] = []
                    newId = self.equantifyTerm(id, vars)
                    self.placeInQuantBucket(buckets, newId)
            else:
                # Require vars to be single variable
                if len(vars) > 1:
                    raise SolverException("Must serialize universal quantifiers")
                v = vars[0]
                for id in buckets[blevel]:
                    newId = self.uquantifyTermSingle(id, v)
                    if newId < 0:
                        # Unsat
                        return
                    self.placeInQuantBucket(buckets, newId)
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")

    # Provide roots of active nodes to garbage collector
    def rootGenerator(self):
        rootList = [t.root for t in self.activeIds.values()]
        return rootList


def readPermutation(fname, writer = None):
    valueList = []
    permutedList = []
    vcount = 0
    lineCount = 0
    if writer is None:
        writer = sys.stderr
    try:
        infile = open(fname, 'r')
    except:
        writer.write("Could not open permutation file '%s'\n" % fname)
        return None
    for line in infile:
        lineCount += 1
        fields = line.split()
        if len(fields) == 0:
            continue
        if fields[0][0] == '#':
            continue
        try:
            values = [int(v) for v in fields]
        except Exception:
                writer.write("Line #%d.  Invalid list of variables '%s'\n" % (lineCount, line))
                return None
        for v in values:
            vcount += 1
            valueList.append(vcount)
            permutedList.append(v)
    infile.close()
    try:
        permuter = permutation.Permuter(valueList, permutedList)
    except Exception as ex:
        writer.write("Invalid permutation: %s\n" % str(ex))
        return None
    return permuter
        
def run(name, args):
    cnfName = None
    proofName = None
    permuter = None
    bpermuter = None
    doBucket = False
    verbLevel = 1
    logName = None
    mode = proof.ProverMode.noProof

    optlist, args = getopt.getopt(args, "hbB:m:v:i:o:m:p:L:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        if opt == '-b':
            doBucket = True
        elif opt == '-B':
            bpermuter = readPermutation(val)
            if bpermuter is None:
                return
        elif opt == '-m':
            if val == 's':
                mode = proof.ProverMode.satProof
            elif val == 'r':
                mode = proof.ProverMode.refProof
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
            permuter = readPermutation(val)
            if permuter is None:
                return
        elif opt == '-L':
            logName = val
        else:
            sys.stderr.write("Unknown option '%s'\n" % opt)
            usage(name)
            return

    writer = stream.Logger(logName)

    if mode == proof.ProverMode.satProof:
        writer.write("Satisfaction not implemented\n")
        return

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
        proof.generateLevels(reader.varList)

    solver = Solver(reader, prover = prover, permuter = permuter, verbLevel = verbLevel)
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

    

    
