#!/usr/bin/python
# Simple, proof-generating SAT solver based on BDDs

import sys
import getopt
import bdd
import resolver
import datetime

def usage(name):
    print("Usage: %s [-h] [-v LEVEL] [-i CNF] [-o PROOF] [-p PERMUTE] [-s SCHEDULE]" % name)
    print("  -h          Print this message")
    print("  -v LEVEL    Set verbosity level")
    print("  -i CNF      Name of CNF input file")
    print("  -o PROOF    Name of proof output file")
    print("  -p PERMUTE  Name of file specifying mapping from CNF variable to BDD level")
    print("  -s SCHEDULE Name of action schedule file")

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
    support = []
    size = 0
    validation = None # Clause id providing validation

    def __init__(self, manager, root, validation):
        self.manager = manager
        self.root = root
        self.support = self.manager.getSupport(root)
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


class Prover:

    inputClauseCount = 0
    clauseCount = 0
    proofCount = 0
    file = None
    opened = False
    verbLevel = 1

    def __init__(self, fname = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if fname is None:
            self.opened = False
            self.file = sys.stdout
        else:
            self.opened = True
            try:
                self.file = open(fname, 'w')
            except Exception:
                raise ProverException("Could not open file '%s'" % fname)
        self.clauseCount = 0
        self.proofCount = 0

    def inputDone(self):
        self.inputClauseCount = self.clauseCount

    def fileOutput(self):
        return self.opened

    def comment(self, comment):
        if self.verbLevel > 1 and comment is not None:
            self.file.write("c " + comment + '\n')

    def createClause(self, result, antecedent, comment = None):
        self.comment(comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            return result
        if result == -resolver.tautologyId:
            result = []
        self.clauseCount += 1
        ilist = [self.clauseCount] + result + [0] + sorted(antecedent) + [0]
        slist = [str(i) for i in ilist]
        istring = " ".join(slist)
        self.file.write(istring + '\n')
        return self.clauseCount

    def emitProof(self, proof, ruleIndex, comment):
        if proof.isLeaf:
            self.comment(comment)
            return ruleIndex[proof.name]
        else:
            antecedent = []
            for c in proof.children:
                antecedent.append(self.emitProof(c, ruleIndex, comment))
                comment = None
            self.proofCount += 1
            return self.createClause(proof.literalList, antecedent)

    def summarize(self):
        if self.verbLevel >= 1:
            print("Input clauses: %d" % self.inputClauseCount)
            acount = self.clauseCount - self.inputClauseCount - self.proofCount
            print("Added clauses without antecedents: %d" % acount)
            print("Added clauses requiring proofs: %d" % (self.proofCount))

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
    scheduler = None

    def __init__(self, fname = None, prover = None, permuter = None, scheduler = None, verbLevel = 1):
        self.verbLevel = verbLevel
        self.scheduler = scheduler
        if prover is None:
            prover = Prover(verbLevel = verbLevel)
        self.prover = prover
        try:
            reader = CnfReader(fname, verbLevel = verbLevel)
        except Exception as ex:
            print("Aborted: %s" % str(ex))
            raise ex
        clauseCount = 0
        for line in reader.commentLines:
            self.prover.comment(line)
        # Print input clauses
        for clause in reader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount)

        self.prover.inputDone()

        self.manager = bdd.Manager(prover = self.prover, rootGenerator = self.rootGenerator, nextNodeId = clauseCount+1, verbLevel = verbLevel)
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
            print(comment)
        self.activeIds[self.termCount] = newTerm
        if newTerm.root == self.manager.leaf0:
            if self.prover.fileOutput() and self.verbLevel >= 1:
                print("UNSAT")
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
        self.manager.checkGC()
        return self.termCount

    def runNoSchedule(self):
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            nid = self.combineTerms(i, j)
            if nid < 0:
                return
        if self.verbLevel >= 0:
            print("SAT")
        if self.verbLevel >= 4:
            for s in self.manager.satisfyStrings(self.activeIds[nid].root):
                print("  " + s)
        
    def runSchedule(self):
        idStack = []
        lineCount = 0
        for line in self.scheduler:
            lineCount += 1
            fields = line.split()
            if len(fields) == 0:
                continue
            cmd = fields[0]
            if cmd == 'i':  # Information request
                if len(idStack) == 0:
                    raise SolverException("Line #%d.  Nothing on stack" % lineCount)
                # Use rest of string as documentation
                line = trim(line)
                cstring = line[1:] if  len(line) >= 1 else ""
                root =  self.activeIds[idStack[-1]].root
                size = self.manager.getSize(root)
                print("Node %d.  Size = %d.%s" % (root.id, size, cstring))
                continue
            try:
                values = [int(v) for v in fields[1:]]
            except:
                raise SolverException("Line #%d.  Invalid field '%s'" % (lineCount, line))
            if cmd == '#':
                continue
            elif cmd == 'c':  # Put listed clauses onto stack
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
        
    # Provide roots of active nodes to garbage collector
    def rootGenerator(self):
        rootList = [t.root for t in self.activeIds.values()] 
        return rootList

    def run(self):
        if self.scheduler is None:
            self.runNoSchedule()
        else:
            self.runSchedule()

def readPermutation(fname):
    valueList = []
    permutedList = []
    vcount = 0
    lineCount = 0
    try:
        infile = open(fname, 'r')
    except:
        print("Could not open permutation file '%s'" % fname)
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
                print("Line #%d.  Invalid list of variables '%s'" % (lineCount, line))
                return None
        for v in values:
            vcount += 1
            valueList.append(vcount)
            permutedList.append(v)
    infile.close()
    try:
        permuter = Permuter(valueList, permutedList)
    except Exception as ex:
        print("Invalid permutation: %s" % str(ex))
        return None
    return permuter
        
def readScheduler(fname):
    lineCount = 0
    actionList = []
    try:
        infile = open(fname, 'r')
    except:
        print("Could not open schedule file '%s'" % fname)
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
    permuter = None
    scheduler = None
    verbLevel = 1

    optlist, args = getopt.getopt(args, "hv:i:o:p:s:")
    for (opt, val) in optlist:
        if opt == '-h':
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
        elif opt == '-s':
            scheduler = readScheduler(val)
            if scheduler is None:
                return
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return

    try:
        prover = Prover(proofName, verbLevel = verbLevel)
    except Exception as ex:
        print("Couldn't create prover (%s)" % str(ex))
        return

    start = datetime.datetime.now()
    solver = Solver(cnfName, prover = prover, permuter = permuter, scheduler = scheduler, verbLevel = verbLevel)
    solver.run()
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    if verbLevel > 0:
        print("Elapsed time for SAT: %.2f seconds" % seconds)

    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
            
                    
            

    

    
