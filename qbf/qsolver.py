#!/usr/bin/python
# Simple, proof-generating SAT solver based on BDDs

import sys
import getopt
import datetime

import bdd
import resolver
import stream

# Increase maximum recursion depth
sys.setrecursionlimit(10 * sys.getrecursionlimit())

def usage(name):
    sys.stderr.write("Usage: %s [-h][-S][-v LEVEL] [-i CNF] [-o file.qrat] [-p PERMUTE] [-L logfile]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -S          Generate satisfaction proof\n")
    sys.stderr.write("  -v LEVEL    Set verbosity level\n")
    sys.stderr.write("  -i CNF      Name of CNF input file\n")
    sys.stderr.write("  -o pfile    Name of proof output file (QRAT format)\n")
    sys.stderr.write("  -p PERMUTE  Name of file specifying mapping from CNF variable to BDD level\n")
    sys.stderr.write("  -L logfile  Append standard error output to logfile\n")

# Verbosity levels
# 0: Totally silent
# 1: Key statistics only
# 2: Summary information
# 3: Proof information
# 4: ?
# 5: Tree generation information

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# Read QCNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class QcnfReader():
    file = None
    commentLines = []
    clauses = []
    # List of input variables.
    # Each is triple of form (varNumber, qlevel, isExistential)
    varList = []
    nvar = 0
    verbLevel = 1
    
    def __init__(self, fname = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            opened = True
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise CnfException("Could not open file '%s'" % fname)
        self.clauses = []
        self.commentLines = []
        try:
            self.readCnf()
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    def readCnf(self):
        self.nvar = 0
        # Dictionary of variables that have been declared.
        # Maps from var to line number
        foundDict = {}
        lineNumber = 0
        nclause = 0
        self.varList = []
        qlevel = 1
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
                if self.verbLevel > 1:
                    self.commentLines.append(line)
            elif line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
            elif line[0] == 'a' or line[0] == 'e':
                # Variable declaration
                isExistential = line[0] == 'a'
                try:
                    vars = [int(s) for s in line.split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if vars[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                vars = vars[:-1]
                for v in vars:
                    if v <= 0 or v > self.nvar:
                        raise CnfException("Line %d.  Invalid variable %d" % (lineNumber, v))
                    if v in foundDict:
                        raise CnfException("Line %d.  Variable %d already declared on line %d" % (lineNumber, v, foundDict[v]))
                    foundDict[v] = lineNumber
                    self.varList.append((v, qlevel, isExistential))
                # Prepare for next set of input variables
                qlevel += 2
            else:
                if nclause == 0:
                    raise CnfException("Line %d.  No header line.  Not cnf" % (lineNumber))
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if lits[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                lits = lits[:-1]
                vars = sorted([abs(l) for l in lits])
                if len(vars) == 0:
                    raise CnfException("Line %d.  Empty clause" % lineNumber)                    
                if vars[-1] > self.nvar or vars[0] == 0:
                    raise CnfException("Line %d.  Out-of-range literal" % lineNumber)
                for i in range(len(vars) - 1):
                    if vars[i] == vars[i+1]:
                        raise CnfException("Line %d.  Opposite or repeated literal" % lineNumber)
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            raise CnfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
        # See if there are any undeclared variables
        outerVars = [v for v in range(1, self.nvar+1) if v not in foundDict]
        if len(outerVars) > 0:
            # These must be added as existential variables in first quantifier block
            ovarList = [(v, 1, True) for v in outerVars]
            nvarList = [(v, qlevel+2, isExistential) for (v, qlevel, isExistential) in self.varList]
            self.varList = ovarList + nvarList
                        


# Abstract representation of Boolean function
class Term:

    manager = None
    root = None
#    support = None    # Variables in support represented by clause (omitted)
    size = 0
    validation = None # Clause id providing validation

    def __init__(self, manager, root, validation):
        self.manager = manager
        self.root = root
#        self.support = self.manager.getSupport(root)
        self.size = self.manager.getSize(root)
        self.validation = validation

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
        validation = self.manager.prover.createClause([newRoot.id], antecedents, comment)
        return Term(self.manager, newRoot, validation)

    def equantify(self, literals, prover):
        antecedents = [self.validation]
        newRoot = self.manager.equant(self.root, literals)
        check, implication = self.manager.justifyImply(self.root, newRoot)
        if not check:
            raise bdd.BddException("Implication failed %s -/-> %s" % (self.root.label(), newRoot.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        validation = self.manager.prover.createClause([newRoot.id], antecedents, "Validation of %s" % newRoot.label())
        return Term(self.manager, newRoot, validation)

    # Must split universal quantification into two operations per variable
    def restrict(self, literal, prover):
        antecedents = [self.validation]
        newRoot, implication = self.manager.applyRestrictDown(self.root, literal)
        if implication != resolver.tautologyId:
            antecedents += [implication]
        if newRoot == self.manager.leaf0:
            comment = "Validation of Empty clause"
        else:
            comment = "Validation of %s" % newRoot.label()
        var = literal.variable.id
        if literal.high = self.manager.leaf1:
            var = -var
        rule1 = self.manager.prover.createClause([var, newRoot.id], antecedents, comment)
        # Now apply universal reduction
        validation = self.manager.prover.createClause([newRoot.id], [rule1], isUniversal=True)
        return Term(self.manager, newRoot, validation)

    def equalityTest(self, other):
        root1 = self.root
        root2 = other.root
        return root1 == root2
                                

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


# Hack to allow writing binary data to standard output
class StdOutWriter:

    def write(self, data):
        if sys.version_info < (3,0):
            sys.stdout.write(data)
        elif type(data) is str:
            sys.stdout.buffer.write(bytearray(data, 'ascii'))
        else:
            sys.stdout.buffer.write(data)

    def close(self):
        pass

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
        self.doQrat = True
        if fname is None:
            self.opened = False
            self.file = StdOutWriter()
        else:
            self.opened = True
            try:
                self.file = open(fname, 'w')
            except Exception:
                raise ProverException("Could not open file '%s'" % fname)
        self.writer = sys.stderr if writer is None else writer
        self.clauseCount = 0
        self.proofCount = 0
        self.clauseDict = {}
        self.antecedentDict = {}

    def inputDone(self):
        self.inputClauseCount = self.clauseCount

    def fileOutput(self):
        return self.opened

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
        middle = ['u'] is isUniversal else []
        if self.refutation and not self.doQrat:
            rest = result + [0] + antecedent + [0]
        else:
            rest = result + [0]
        ilist = [self.clauseCount] + middle + rest
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

    def __init__(self, fname = None, prover = None, permuter = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if prover is None:
            prover = Prover(verbLevel = verbLevel)
        self.prover = prover
        self.writer = prover.writer
        try:
            reader = CnfReader(fname, verbLevel = verbLevel)
        except Exception as ex:
            self.writer.write("Aborted: %s\n" % str(ex))
            raise ex
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
#        for line in reader.commentLines:
#            self.prover.comment(line)
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
        for level in range(1, reader.nvar+1):
            inputId = self.permuter.forward(level)
            qlevel,isExistential = qmap[level]
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
        newTerm = termA.combine(termB)
        self.termCount += 1
        comment = "T%d (Node %s) & T%d (Node %s)--> T%s (Node %s)" % (id1, termA.root.label(), id2, termB.root.label(),
                                                                      self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        del self.activeIds[id1]
        del self.activeIds[id2]
        if self.prover.fileOutput() and self.verbLevel >= 3:
            self.writer.write(comment)
        self.activeIds[self.termCount] = newTerm
        if newTerm.root == self.manager.leaf0:
            if self.prover.fileOutput() and self.verbLevel >= 1:
                self.writer.write("UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1
        return self.termCount

    def equantifyTerm(self, id, varList):
        term = self.activeIds[id]
        del self.activeIds[id]
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        newTerm = term.equantify(clause, self.prover)
        self.termCount += 1
        vstring = " ".join(sorted([str(v) for v in varList]))
        comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return self.termCount

    def uquantifyTermInner(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        term1 = term.restrict(lit, self.prover))
        self.termCount += 1
        comment = "T%d (Node %s) Restrict1(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, term1.root.label())
        if term1.root == self.manager.leaf0:
            if self.prover.fileOutput() and self.verbLevel >= 1:
                self.writer.write("UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1
        nlit = self.litMap[-var]
        term0 = term.restrict(nlit, self.prover)
        self.termCount += 1
        comment = "T%d (Node %s) Restrict0(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, term0.root.label())
        if term0.root == self.manager.leaf0:
            if self.prover.fileOutput() and self.verbLevel >= 1:
                self.writer.write("UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return self.termCount

    def uquantifyTerm(self, id, varList):
        nid = id
        for v in varList:
            nid = self.uquantifyTermInner(nid, v)
            if nid < 0:
                return nid
        return nid


    def runNoSchedule(self):
        # Start by conjuncting all clauses to get single BDD
        id = 0
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            id = self.combineTerms(i, j)
            if id < 0:
                return
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")
        # Now handle all of the quantifications:
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        for level in levels:
            vars, isExistential = self.quantMap[level]
            if len(vars) == 0:
                continue
            if self.verbLevel >= 2:
                self.writer.write("Quantifying %s level %d.  Vars = %s" % ("existential" if isExistential else "universal", level, str(vars)))
            if isExistential:
                id = self.equantifyTerm(id, vars)
            else:
                id = self.uquantifyTerm(id, v)
                if id < 0:
                    return
        
    def runSchedule(self, scheduler):
        idStack = []
        lineCount = 0
        # Make sure program runs from innermost quantifier to outermost
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        curVars = []
        while len(curVars) == 0:
            curLevel = levels[0]
            levels = levels[1:]
            curVars, curExistential = self.quantMap[level]
        for line in scheduler:
            line = trim(line)
            lineCount += 1
            fields = line.split()
            if len(fields) == 0:
                continue
            cmd = fields[0]
            if cmd == '#':
                continue
            if cmd == 'i':  # Information request
                if len(idStack) == 0:
                    raise SolverException("Line #%d.  Nothing on stack" % lineCount)
                # Use rest of string as documentation
                line = trim(line)
                cstring = line[1:] if  len(line) >= 1 else ""
                root =  self.activeIds[idStack[-1]].root
                size = self.manager.getSize(root)
                if self.verbLevel >= 1:
                    if self.countSolutions:
                        count = self.manager.satisfyCount(root)
                        self.writer.write("Node %d.  Size = %d, Solutions = %d.%s\n" % (root.id, size, count, cstring))
                    else:
                        self.writer.write("Node %d.  Size = %d.%s\n" % (root.id, size, cstring))
                continue
            try:
                values = [int(v) for v in fields[1:]]
            except:
                raise SolverException("Line #%d.  Invalid field '%s'" % (lineCount, line))
            if cmd == 'c':  # Put listed clauses onto stack
                idStack += values
            elif cmd == 'a':  # Pop n+1 clauses from stack.  Form their conjunction.  Push result back on stack
                count = values[0]
                if count+1 > len(idStack):
                    raise SolverException("Line #%d.  Invalid conjunction count %d.  Only have %d on stack" %
                                          (lineCount, count, len(idStack)))
                for i in range(count):
                    id1 = idStack[-1]
                    id2 = idStack[-2]
                    idStack = idStack[:-2]
                    nid = self.combineTerms(id1, id2)
                    if nid < 0:
                        # Hit unsat case
                        return
                    else:
                        idStack.append(nid)
            elif cmd == 'q':
                if len(idStack) < 1:
                    raise SolverException("Line #%d.  Stack is empty" % (lineCount))
                id = idStack[-1]
                idStack = idStack[:-1]
                # Figure out which variables are being quantified
                while len(curVars) == 0:
                    curLevel = levels[0]
                    levels = levels[1:]
                    curVars, curExistential = self.quantMap[level]
                nVars = []
                vcount = 0
                for v in curVars:
                    if v in values:
                        vcount += 1
                    else:
                        nVars.append(v)
                if len(values) != vcount:
                    msg = "Line %d.  Attempting to quantify level %d variables %s, but current quantifier block has %s" % (lineCount, curLevel, str(values), str(curVars))
                    raise SolverException(msg)
                curVars = nVars
                if self.verbLevel >= 2:
                    self.writer.write("Quantifying %s level %d.  Vars = %s" % ("existential" if curExistential else "universal", curLevel, str(values)))
                if curExistential:
                    nid = self.equantifyTerm(id, values)
                else:
                    nid = self.uquantifyTerm(id, values)
                    if nid < 0:
                        # Hit unsat case
                        return
                idStack.append(nid)
            else:
                raise SolverException("Line %d.  Unknown scheduler action '%s'" % (lineCount, cmd))
        
    def placeInBucket(self, buckets, id):
        term = self.activeIds[id]
        level = term.root.variable.qlevel
        if level == bdd.Variable.leafLevel:
            buckets[0].append(id)
        else:
            buckets[level].append(id)

    # Bucket elimination
    def runBucketSchedule(self):
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        buckets = { level : [] for level in levels }
        # Insert ids into lists according to top variable in BDD
        ids = sorted(self.activeIds.keys())
        for id in ids:
            self.placeInBucket(buckets, id)
        for blevel in levels:
            # Conjunct all terms in bucket
            while len(buckets[blevel]) > 1:
                id1 = buckets[blevel][0]
                id2 = buckets[blevel][1]
                buckets[blevel] = buckets[blevel][2:]
                newId = self.combineTerms(id1, id2)
                if newId < 0:
                    # Hit unsat case
                    return
                self.placeInBucket(buckets, newId)
            # Quantify top variable for this bucket
            if blevel > 0 and len(buckets[blevel]) > 0:
                id = buckets[blevel][0]
                buckets[blevel] = []
                vars, isExistential = self.quantMap[level]
                if isExistential:
                    newId = self.equantifyTerm(id, vars)
                else:
                    newId = self.uquantifyTerm(id, vars)
                    if newId < 0:
                        # Hit unsat case
                        return
                self.placeInBucket(buckets, newId)
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
        
def readScheduler(fname, writer = None):
    lineCount = 0
    actionList = []
    if writer is None:
        writer = sys.stderr
    try:
        infile = open(fname, 'r')
    except:
        writer.write("Could not open schedule file '%s'\n" % fname)
        return None
    for line in infile:
        lineCount += 1
        fields = line.split()
        if len(fields) == 0:
            continue
        if fields[0][0] == '#':
            continue
        actionList.append(line)
    return actionList

def run(name, args):
    cnfName = None
    proofName = None
    doLrat = False
    doBinary = False
    permuter = None
    doBucket = False
    scheduler = None
    verbLevel = 1
    logName = None

    optlist, args = getopt.getopt(args, "hbv:i:o:m:p:s:L:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        if opt == '-b':
            doBucket = True
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-o':
            proofName = val
            extension = proofName.split('.')[-1]
            if extension == 'lrat' or extension == 'lratb':
                doLrat = True
                doBinary = extension[-1] == 'b'
        elif opt == '-m':
            proofName = None
            if val == 'b':
                doLrat = True
                doBinary = True
            elif val == 't':
                doLrat = True
        elif opt == '-p':
            permuter = readPermutation(val)
            if permuter is None:
                return
        elif opt == '-s':
            scheduler = readScheduler(val)
            if scheduler is None:
                return
        elif opt == '-L':
            logName = val
        else:
            sys.stderr.write("Unknown option '%s'\n" % opt)
            usage(name)
            return

    writer = stream.Logger(logName)

    if doBucket and scheduler is not None:
        writer.write("Cannot have both bucket scheduling and defined scheduler\n")
        return

    try:
        prover = Prover(proofName, writer = writer, verbLevel = verbLevel, doLrat = doLrat, doBinary = doBinary)
    except Exception as ex:
        writer.write("Couldn't create prover (%s)\n" % str(ex))
        return

    start = datetime.datetime.now()
    solver = Solver(cnfName, prover = prover, permuter = permuter, verbLevel = verbLevel)
    if doBucket:
        solver.runBucketSchedule()
    elif scheduler is not None:
        solver.runSchedule(scheduler)
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

    

    
