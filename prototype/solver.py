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
    sys.stderr.write("Usage: %s [-h] [-b] [-v LEVEL] [-i CNF] [-o file.{proof,lrat,lratb}] [-m t|b|p] [-p PERMUTE] [-s SCHEDULE] [-L logfile]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -b          Process terms via bucket elimination\n")
    sys.stderr.write("  -v LEVEL    Set verbosity level\n")
    sys.stderr.write("  -i CNF      Name of CNF input file\n")
    sys.stderr.write("  -o pfile    Name of proof output file (.proof = tracecheck, .lrat = LRAT text, .lratb = LRAT binary)\n")
    sys.stderr.write("  -m (t|b|p)  Pipe proof to stdout (p = tracecheck, t = LRAT text, b = LRAT binary)\n")
    sys.stderr.write("  -p PERMUTE  Name of file specifying mapping from CNF variable to BDD level\n")
    sys.stderr.write("  -s SCHEDULE Name of action schedule file\n")
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

# Read CNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class CnfReader():
    file = None
    commentLines = []
    clauses = []
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
        lineNumber = 0
        nclause = 0
        self.nvar = 0
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

    def quantify(self, literals, prover):
        antecedents = [self.validation]
        newRoot = self.manager.equant(self.root, literals)
        check, implication = self.manager.justifyImply(self.root, newRoot)
        if not check:
            raise bdd.BddException("Implication failed %s -/-> %s" % (self.root.label(), newRoot.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        validation = self.manager.prover.createClause([newRoot.id], antecedents, "Validation of %s" % newRoot.label())
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
    doLrat = False
    doBinary = False
    clauseDict = {}  # Mapping from clause ID to list of literals in clause

    def __init__(self, fname = None, writer = None, verbLevel = 1, doLrat = False, doBinary = False):
        self.verbLevel = verbLevel
        if fname is None:
            self.opened = False
            self.file = StdOutWriter()
        else:
            self.opened = True
            try:
                self.file = open(fname, 'wb' if doBinary else 'w')
            except Exception:
                raise ProverException("Could not open file '%s'" % fname)
        self.writer = sys.stderr if writer is None else writer
        self.doLrat = doLrat
        self.doBinary = doBinary
        self.clauseCount = 0
        self.proofCount = 0
        self.clauseDict = {}

    def inputDone(self):
        self.inputClauseCount = self.clauseCount

    def fileOutput(self):
        return self.opened

    def comment(self, comment):
        if self.verbLevel > 1 and comment is not None and not self.doBinary:
            self.file.write("c " + comment + '\n')

    def createClause(self, result, antecedent, comment = None, isInput = False):
        self.comment(comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            return result
        if result == -resolver.tautologyId:
            result = []
        self.clauseCount += 1
        antecedent = list(antecedent)
        if not self.doLrat:
            antecedent.sort()
        middle = [ord('a')] if self.doBinary else []
        rest = result + [0] + antecedent + [0]
        ilist = [self.clauseCount] + middle + rest
        if self.doBinary:
            if isInput and self.doLrat:
                pass
            else:
                bytes = stream.CompressArray(ilist).bytes
                self.file.write(bytes)
        else:
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            if isInput and self.doLrat:
                self.comment(istring)
            else:
                self.file.write(istring + '\n')
        self.clauseDict[self.clauseCount] = result
        return self.clauseCount

    def deleteClauses(self, clauseList):
        for id in clauseList:
            del self.clauseDict[id]
        if not self.doLrat:
            return
        middle = [ord('d')] if self.doBinary else ['d']
        rest = clauseList + [0]
        ilist = [self.clauseCount] + middle + rest
        if self.doBinary:
            bytes = stream.CompressArray(ilist).bytes
            self.file.write(bytes)
        else:
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            self.file.write(istring + '\n')

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
    # Dictionary of terms stored for later reuse.  Track so that don't get GCed
    storeTerms = {}
    # Dictionary of Ids of terms that are stored for reuse
    unsat = False
    permuter = None
    prover = None
    writer = None
    # Turn on to have information about node include number of solutions
    countSolutions = True

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
        clauseCount = 0
        for line in reader.commentLines:
            self.prover.comment(line)
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
            var = self.manager.newVariable(name = "input-%d" % inputId, id = inputId)
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

    def quantifyTerm(self, id, varList):
        term = self.activeIds[id]
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        newTerm = term.quantify(clause, self.prover)
        self.termCount += 1
        vstring = " ".join(sorted([str(v) for v in varList]))
        comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        del self.activeIds[id]
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return self.termCount

    # Allow temporary storage of Ids for reuse
    def storeTerm(self, id):
        self.storeTerms[id] = self.activeIds[id]

    def unstoreTerm(self, id):
        del self.storeTerms[id]

    def runNoSchedule(self):
        nid = 0
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            nid = self.combineTerms(i, j)
            if nid < 0:
                return
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")
        if self.verbLevel >= 1:
            for s in self.manager.satisfyStrings(self.activeIds[nid].root, limit = 20):
                self.writer.write("  " + s)
        
    def runSchedule(self, scheduler):
        idStack = []
        registerDict = {}
        lineCount = 0
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
            if cmd == 's':  # Pop top element into register
                if len(fields) != 2:
                    raise SolverException("Line #%d.  Invalid store command.  Must have 2 fields" % (lineCount))
                name = fields[1]
                id = idStack[-1]
                term = self.activeIds[id]
                registerDict[name] = (id, term)
                self.storeTerm(id)
                continue
            if cmd == 'r':  # Retrieve element from register and push on top of stack; don't delete register
                if len(fields) != 2:
                    raise SolverException("Line #%d.  Invalid retrieve command.  Must have 2 fields" % (lineCount))
                name = fields[1]
                if name not in registerDict:
                    msg = "Line #%d.  Invalid retrieve command.  Name %s unknown" % (lineCount, name)
                    raise SolverException(msg)
                id, term = registerDict[name]
                idStack.append(id)
                # Reactivate
                self.activeIds[id] = term
                continue
            if cmd == 'd':  # Delete named register
                if len(fields) != 2:
                    raise SolverException("Line #%d.  Invalid delete command.  Must have 2 fields" % (lineCount))
                name = fields[1]
                if name not in registerDict:
                    msg = "Line #%d.  Invalid delete command.  Name %s unknown" % (lineCount, name)
                    raise SolverException(msg)
                id, term = registerDict[name]
                del registerDict[name]
                self.unstoreTerm(id)
                continue
            if cmd == 'e':
                # Equality test
                if len(idStack) < 2:
                    raise SolverException("Line #%d.  Need to items for implication test" % (lineCount))
                term1 = self.activeIds[idStack[-1]]
                term2 = self.activeIds[idStack[-2]]
                idStack = idStack[:-2]
                if term1.equalityTest(term2):
                    self.writer.write("Equality test PASSED.  %d == %d\n" % (term1.root.id, term2.root.id))
                else:
                    self.writer.write("Equality test FAILED.  %d != %d\n" % (term1.root.id, term2.root.id))
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
                nid = self.quantifyTerm(id, values)
                idStack.append(nid)
            else:
                raise SolverException("Line %d.  Unknown scheduler action '%s'" % (lineCount, cmd))
        
    def placeInBucket(self, buckets, id):
        term = self.activeIds[id]
        level = term.root.variable.level
        if level == bdd.Variable.leafLevel:
            buckets[0].append(id)
        else:
            buckets[level].append(id)

    # Bucket elimination
    def runBucketSchedule(self):
        maxLevel = len(self.manager.variables)
        buckets = { level : [] for level in range(0, maxLevel + 1) }
        # Insert ids into lists according to top variable in BDD
        ids = sorted(self.activeIds.keys())
        for id in ids:
            self.placeInBucket(buckets, id)
        for blevel in range(0, maxLevel + 1):
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
                var = self.manager.variables[blevel-1]
                vid = var.id
                newId = self.quantifyTerm(id, [vid])
                self.placeInBucket(buckets, newId)
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")

    # Provide roots of active nodes to garbage collector
    def rootGenerator(self):
        rootList = [t.root for t in self.activeIds.values()] + [t.root for t in self.storeTerms.values()]
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

    

    
