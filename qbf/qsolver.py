#!/usr/bin/python
# Simple, proof-generating SAT solver based on BDDs

import sys
import getopt
import datetime

import bdd
import resolver
import stream
import qreader

# Increase maximum recursion depth
sys.setrecursionlimit(50 * sys.getrecursionlimit())

def usage(name):
    sys.stderr.write("Usage: %s [-h][-S][-v LEVEL] [-i CNF] [-o file.{qrat,qproof}] [-B BPERM] [-p PERMUTE] [-L logfile]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -S          Generate satisfaction proof\n")
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

    def __init__(self, manager, root, validation):
        self.manager = manager
        self.root = root
        self.size = self.manager.getSize(root)
        self.support = None
        self.validation = validation

    def getSupport(self):
        if self.support is None:
            self.support = self.manager.getSupportIds(self.root)
        return self.support

    # Generate conjunction of two terms
    def combine(self, other):
        antecedents = [self.validation, other.validation]
        newRoot, implication = self.manager.applyAndJustify(self.root, other.root)
        if implication != resolver.tautologyId:
            antecedents += [implication]
        if newRoot == self.manager.leaf0:
            comment = "Validation of Empty clause"
        else:
            comment = "Validation of %s" % newRoot.label()
        validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, comment)
        return Term(self.manager, newRoot, validation)

    def equantify(self, literals, prover):
        antecedents = [self.validation]
        newRoot = self.manager.equant(self.root, literals)
        check, implication = self.manager.justifyImply(self.root, newRoot)
        if not check:
            raise bdd.BddException("Implication failed %s -/-> %s" % (self.root.label(), newRoot.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, "Validation of %s" % newRoot.label())
        return Term(self.manager, newRoot, validation)

    # Must split universal quantification into two operations per variable
    def restrict(self, literal, prover):
        antecedents = [self.validation]
        newRoot, implication = self.manager.applyRestrictDown(self.root, literal)
#        if newRoot == self.root:
#            print("  Restriction returned argument node N%d" % newRoot.id)
#            return Term(self.manager, newRoot, self.validation)
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
        return Term(self.manager, newRoot, validation)


class PermutationException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Permutation Exception: " + str(self.value)


class Permuter:
    forwardMap = {}
    reverseMap = {}
    
    def __init__(self, valueList = [], permutedList = []):
        self.forwardMap = {}
        self.reverseMap = {}
        identity = False
        if len(permutedList) == 0:
            permutedList = valueList
            identity = True
        if len(valueList) != len(permutedList):
            raise PermutationException("Unequal list lengths: %d, %d" % (len(valueList), len(permutedList)))
        for v, p in zip(valueList, permutedList):
            self.forwardMap[v] = p
            self.reverseMap[p] = v
        if identity:
            return
        # Check permutation
        for v in valueList:
            if v not in self.reverseMap:
                raise PermutationException("Not permutation: Nothing maps to %s" % str(v))
        for v in permutedList:
            if v not in self.forwardMap:
                raise PermutationException("Not permutation: %s does not map anything" % str(v))
            
            
    def forward(self, v):
        if v not in self.forwardMap:
            raise PermutationException("Value %s not in permutation" % (str(v)))
        return self.forwardMap[v]

    def permLess(self, v1, v2):
        pv1 = self.reverse(v1)
        pv2 = self.reverse(v2)
        return pv1 < pv2

    def sortList(self, ls):
        return sorted(ls, key = lambda x: self.reverse(x))


    def reverse(self, v):
        if v not in self.reverseMap:
            raise PermutationException("Value %s not in permutation range" % (str(v)))
        return self.reverseMap[v]
    
    def __len__(self):
        return len(self.forwardMap)
        
class ProverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Prover Exception: " + str(self.value)


class Prover:

    inputClauseCount = 0
    clauseCount = 0
    proofCount = 0
    file = None
    writer = None
    opened = False
    verbLevel = 1
    clauseDict = {}  # Mapping from clause ID to list of literals in clause
    antecedentDict = {}  # Mapping from clause ID to list of antecedents
    refutation = True
    doQrat = True

    def __init__(self, fname = None, writer = None, refutation = True, verbLevel = 1):
        self.verbLevel = verbLevel
        self.refutation = refutation
        self.doQrat = False
        if fname is None:
            self.opened = False
            self.file = sys.stdout
        else:
            self.opened = True
            try:
                self.file = open(fname, 'w')
            except Exception:
                raise ProverException("Could not open file '%s'" % fname)
            fields = fname.split('.')
            self.doQrat = fields[-1] == 'qrat'
        self.writer = sys.stderr if writer is None else writer
        self.clauseCount = 0
        self.proofCount = 0
        self.clauseDict = {}
        self.antecedentDict = {}

    def inputDone(self):
        self.inputClauseCount = self.clauseCount

    def comment(self, comment):
        if self.verbLevel > 1 and comment is not None:
            self.file.write("c " + comment + '\n')

    def createClause(self, result, antecedent, comment = None, isInput = False, isUniversal = False):
        self.comment(comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            return result
        if result == -resolver.tautologyId:
            result = []
        self.clauseCount += 1
        antecedent = list(antecedent)
        middle = ['u'] if isUniversal else []
        rest = result + [0]
        if self.refutation and not self.doQrat:
            rest += antecedent + [0]
        ilist = [self.clauseCount] if not self.doQrat else []
        ilist += middle + rest
        slist = [str(i) for i in ilist]
        istring = " ".join(slist)
        if isInput:
            self.comment(istring)
        else:
            self.file.write(istring + '\n')
        self.clauseDict[self.clauseCount] = result
        self.antecedentDict[self.clauseCount] = antecedent
        return self.clauseCount

    def deleteClauses(self, clauseList):
        if self.refutation:
            for id in clauseList:
                del self.clauseDict[id]
            middle = ['d']
            rest = clauseList + [0]
            ilist = [self.clauseCount] + middle + rest
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            self.file.write(istring + '\n')
        else:
            for id in clauseList:
                middle = ['d']
                rest = clauseList + [0] + self.antecedentDict[id] + [0]
            ilist = [self.clauseCount] + middle + rest
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            self.file.write(istring + '\n')
            del self.clauseDict[id]
            del self.antecedentDict[id]

    def generateStepQP(self, fields, addNumber = True, comment = None):
        self.comment(comment)
        if addNumber:
            self.clauseCount += 1
            fields = [str(self.clauseCount)] + fields
        else:
            fields = ['-'] + fields
        self.file.write(' '.join(fields) + '\n')
        return self.clauseCount
    
    def proveAddResolution(self, result, antecedent, comment = None):
        if self.doQrat:
            return self.createClause(result, antecedent, comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        if result == -resolver.tautologyId:
            result = []
        rfields = [str(r) for r in result]
        afields = [str(a) for a in antecedent]
        fields = ['ar'] + rfields + ['0'] + afields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        self.clauseDict[stepNumber] = result
        self.antecedentDict[stepNumber] = antecedent
        return stepNumber

    def proveExtend(self, var, level, comment = None):
        if self.doQrat:
            # Don't need to declare extension variables
            return
        fields = ['x', str(level), str(var), '0']
        self.generateStepQP(fields, False, comment)

    def proveAddBlocked(self, clause, blockers, comment = None):
        if self.doQrat:
            return self.createClause(clause, blockers, comment)
        result = resolver.cleanClause(clause)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        bfields = [str(-abs(b)) for b in blockers]
        fields = ['ab'] + rfields + ['0'] + bfields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        self.clauseDict[stepNumber] = result
        return stepNumber

    def proveUniversal(self, lit, oldId, comment = None):
        fields = ['u', str(lit), str(oldId)]
        stepNumber = self.generateStepQP(fields, True, comment)
        oclause = self.clauseDict[oldId]
        nclause = [l for l in oclause if l != lit]
        self.clauseDict[stepNumber] = nclause
        return stepNumber

    def proveDelete(self, idList, comment = None):
        ilist = [str(id) for id in idList]
        fields = ['d'] + ilist + ['0']
        self.generateStepQP(fields, False, comment)

    # Declare variable levels when not default
    def generateLevels(self, varList):
        levelDict = {}
        for (v, l, e) in varList:
            if l in levelDict:
                levelDict[l].append(v)
            else:
                levelDict[l] = [v]
        levels = sorted(levelDict.keys())
        for l in levels:
            fields = ['-', 'l', str(l)] + [str(v) for v in levelDict[l]] + ['0']
            self.file.write(' '.join(fields) + '\n')

    def summarize(self):
        if self.verbLevel >= 1:
            self.writer.write("Total Clauses: %d\n" % self.clauseCount)
            self.writer.write("Input clauses: %d\n" % self.inputClauseCount)
            acount = self.clauseCount - self.inputClauseCount - self.proofCount
            self.writer.write("Added clauses without antecedents: %d\n" % acount)
            self.writer.write("Added clauses requiring proofs: %d\n" % (self.proofCount))

    def __del__(self):
        if self.opened:
            self.file.close()



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
            prover = Prover(verbLevel = verbLevel)
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
            permuter = Permuter(list(range(1, reader.nvar+1)))
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
            term = Term(self.manager, root, validation)
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
        term1 = term.restrict(lit, self.prover)
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
        term0 = term.restrict(nlit, self.prover)
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
        permuter = Permuter(valueList, permutedList)
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
    refutation = True

    optlist, args = getopt.getopt(args, "hbB:Sv:i:o:m:p:L:")
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
        elif opt == '-S':
            refutation = False
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

    if not refutation:
        writer.write("Satisfaction not implemented\n")
        return

    try:
        prover = Prover(proofName, writer = writer, verbLevel = verbLevel, refutation = refutation)
    except Exception as ex:
        writer.write("Couldn't create prover (%s)\n" % str(ex))
        return

    start = datetime.datetime.now()

    stretchExistential = not refutation
    stretchUniversal = refutation

    try:
        reader = qreader.QcnfReader(cnfName, bpermuter, stretchExistential, stretchUniversal)
    except Exception as ex:
        writer.write("Aborted: %s\n" % str(ex))
        return
    
    if reader.stretched:
        prover.generateLevels(reader.varList)

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

    

    
