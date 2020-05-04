# Simple, proof-generating SAT solver based on BDDs

import bdd

class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# Read CNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class CnfReader():
    cnfName = None
    file = None
    commentLines = []
    clauses = []
    nvar = 0
    
    def __init__(self, fname = None):
        self.cnfName = fname
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
        
    def trim(self, s):
        while len(s) > 0 and s[-1] in '\r\n':
            s = s[:-1]
        return s

    def readCnf(self):
        lineNumber = 0
        nclause = 0
        nvar = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = self.trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
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
class Function:

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

    def combine(self, other):
        antecedents = [self.validation, other.validation]
        newRoot, implication = self.manager.applyAndJustify(self.root, other.root)
        if implication is not None:
            antecedents += [implication]
        validation = self.manager.prover.createClause([newRoot.id], antecedents, "Validation of %d" % newRoot.id)
        return Function(self.manager, newRoot, validation)

    def quantify(self, literals, prover):
        antecedents = [self.validation]
        newRoot = self.manager.equant(self.root, literals)
        check, implication = self.manager.justifyImply(self.root, newRoot):
        if not check
            raise bdd.BddException("Implication failed %s -/-> %s" % (str(self.root), str(newRoot)))
        validation = self.manager.prover.createClause([newRoot.id], [self.validation, implication], "Validation of %d" % newRoot.id)
        return Function(self.manager, newRoot, validation)

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
        if len(permutedList) == 0:
            permutedList = valueList
        if len(valueList) != len(permutedList):
            raise PermutationException("Unequal list lengths: %d, %d" % (len(valueList), len(permutedList)))
        for v, p in zip(valueList, permutedList):
            self.forwardMap[v] = p
            self.reverseMap[p] = v
            
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
        

class Solver:
    
    manager = None
    # How many terms have been generated
    termCount = 0
    # Dictionary of Ids of terms remaining to be combined
    activeIds = {}
    unsat = False
    prover = None

    def __init__(self, fname = None, prover = None, permuter = None):
        self.prover = prover
        try:
            reader = cnf.CnfReader(fname)
        except Exception as ex:
            print(str(ex))
        clauseCount = 0
        for line in reader.commentLines:
            self.prover.comment(line)
        # Print input clauses
        for clause in reader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount)
        self.manager = bdd.Manager(self.prover, self.clauseCount+1)
        # Generate BDD representations of literals
        if permuter is None:
            self.permuter = Permuter(list(range(1, reader.nvar+1)))
        else:
            self.permuter = permuter
        litMap = {}
        for level in range(1, range(1, reader.nvar+1)):
            inputId = self.permuter.reverse(level)
            v = self.manager.newVariable("input-%d" % inputId)
            t = self.manager.literal(var, 1)
            litMap[ inputId] = t
            e = self.manager.literal(var, 0)
            litMap[-inputId] = e
        # Generate BDD representations of clauses
        self.termCount = 0
        self.activeIds = {}
        for clause in reader.clauses:
            self.termCount += 1
            litList = [litMap[v] for v in clause]
            root, validation = self.manager.constructClause(clauseCount, litList)
            term = Function(self.manager, root, validation)
            self.activeIds[self.termCount] = term
        self.unsat = False

    # Simplistic version 
    def choosePair(self):
        ids = sorted(self.activeIds.keys())
        return ids[0], ids[1]

    def run(self):
        while (len(self.activeIds) > 1):
            
            i, j = self.choosePair()
            termA = self.activeIds[i]
            termB = self.activeIds[j]
            newTerm = termA.combine(termB)
            del self.activeIds[i]
            del self.activeIds[j]
            self.termCount += 1
            print("%d & %d --> %d" % (i, j, self.termCount))
            self.activeIds[self.termCount] = newTerm
            if newTerm.root == self.manager.leaf0:
                antecedents = [self.termCount, self.manager.leaf0.inferValue]
                self.prover.createClause([], antecedents, "Empty clause")
                print("UNSAT")
                self.unsat = True
                return

        print("SAT")
        for s in self.manager.satisfyStrings(result):
            print("  " + s)
        
        
    
            
                    
            

    

    
