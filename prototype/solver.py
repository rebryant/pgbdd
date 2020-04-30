# Simple, proof-generating SAT solver based on BDDs

import bdd
import sys

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

# Abstract representation of Boolean function
class Function:

    manager = None
    root = None
    support = []
    size = 0
    id = 0 # Assigned to track derivations

    def __init__(self, manager, root, id):
        self.manager = manager
        self.root = root
        self.support = self.manager.getSupport(root)
        self.size = self.manager.getSize(root)
        self.id = id

    def combine(self, other, newId):
        newRoot = self.manager.applyAnd(self.root, other.root)
        return Function(self.manager, newRoot, newId)

    def quantify(self, literals, newId):
        newRoot = self.manager.equant(self.root, literals)
        if not self.manager.checkImply(self.root, newRoot):
            raise bdd.BddException("Implication failed %s -/-> %s" % (str(self.root, newRoot)))
        return Function(self.manager, newRoot, newId)

class Solver:
    
    manager = None
    # Terms are lists of functions
    allTerms = []
    # Dictionary of Ids of terms remaining to be combined
    activeIds = {}
    # Track how the functions were combined and quantified
    derivations = []

    def __init__(self, file = None):
        self.manager = bdd.Manager()
        # Terms numbered from 1 upward
        self.allTerms = []
        self.activeIds = {}
        self.derivations = []
        if file is not None:
            if self.readCnf(file):
                print("%d clauses read" % len(self.allTerms))
            else:
                print("Read failed")

    def newTerm(self, root, derivation):
        id = len(self.allTerms) + 1
        term = Function(self.manager, root, id)
        self.allTerms.append(term)
        self.activeIds[id] = term
        self.derivations.append(derivation)

    # Read non-comment line from DIMACS file
    def readClause(self, line):
        try:
            fields = [int(s) for s in line.split()]
        except Exception:
            raise bdd.BddException("Could not parse clause line '%s'" % line)
        if len(fields) == 0:
            return
        if fields[-1] != 0:
            raise bdd.BddException("Clause line '%s' does not end with 0" % line)
        fields = fields[:-1]
        litList = []
        for v in fields:
            phase = 1 if v > 0 else 0
            if phase == 0:
                v = -v
            if v < 1 or v > len(self.manager.variables):
                raise bdd.BddException("Clause line '%s' contains invalid variable %d" % (line, v))
            lit = self.manager.literal(self.manager.variables[v-1], phase)
            litList.append(lit)
        return self.manager.constructClause(litList)

    def readCnf(self, file = sys.stdin):
        opened = type(file) == type("abc")
        if opened:
            try:
                f = open(file, 'r')
            except Exception:
                print("Could not open file '%s'" % file)
                return False
            file = f
        lineNumber = 0
        nclause = 0
        nvar = 0
        ok = True
        for line in file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            if line[0] == 'c':
                continue
            if line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    print("Line %d.  Bad header line '%s'" % (lineNumber, line))
                    ok = False
                    break
                try:
                    nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    print("Line %d.  Bad header line '%s'" % (lineNumber, line))
                    ok = False
                    break
                for level in range(1, nvar+1):
                    self.manager.newVariable("var-%d" % level)
            else:
                try:
                    clause = self.readClause(line)
                except Exception as ex:
                    print("Line %d.  %s" % (lineNumber, str(ex)))
                    ok = False
                if ok:
                    term = self.newTerm(clause, ("clause"))

        if ok and len(self.allTerms) != nclause:
            print("Line %d: Got %d clauses.  Expected %d" % (lineNumber, len(self.allTerms), nclause))
            ok = False
        if opened:
            file.close()
        return ok
            
    # Simplistic version 
    def choosePair(self):
        ids = sorted(self.activeIds.keys())
        return ids[0], ids[1]

    def run(self):
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            newRoot = self.manager.applyAnd(self.activeIds[i].root, self.activeIds[j].root)
            self.newTerm(newRoot, ("and", i, j))
            del self.activeIds[i]
            del self.activeIds[j]
            print("%d & %d --> %d" % (i, j, len(self.allTerms)))
        result = self.allTerms[-1].root
        if result == self.manager.leaf0:
            print("UNSAT")
        else:
            print("SAT")
            for s in self.manager.satisfyStrings(result):
                print("  " + s)
        
            
            
                    
            

    

    
