# Simple, proof-generating SAT solver based on BDDs

import bdd
import cnf
import prover

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
    # How many terms have been generated
    termCount = 0
    # Dictionary of Ids of terms remaining to be combined
    activeIds = {}
    unsat = False
    # Save clauses in event that file read from standard input
    clauseLines = []

    def __init__(self, fname = None):
        self.manager = bdd.Manager()
        # Terms numbered from 1 upward
        self.activeIds = {}
        if file is not None:
            if self.readCnf(fname):
                print("%d clauses read" % self.termCount)
            else:
                print("Read failed")
        self.unsat = False

    def newTerm(self, root):
        self.termCount += 1
        term = Function(self.manager, root, self.termCount)
        self.activeIds[self.termCount] = term

    # Helper functions for reading CNF file
    def countAction(self, nvar, nclause):
        for level in range(1, nvar+1):
            self.manager.newVariable("var-%d" % level)
    
    # Read non-comment line from DIMACS file
    def readClause(self, line):
        # Have already checked formatting
        fields = [int(s) for s in line.split()]
        fields = fields[:-1]
        litList = []
        for v in fields:
            phase = 1 if v > 0 else 0
            if phase == 0:
                v = -v
            lit = self.manager.literal(self.manager.variables[v-1], phase)
            litList.append(lit)
        self.newTerm(self.manager.constructClause(litList))

    def readCnf(self, fname = None):
        try:
            c = cnf.CnfReader(self.countAction, self.readClause, None, fname)
            self.clauseLines = c.clauseLines
            return True
        except Exception as ex:
            print(str(ex))
            return False
            
    # Simplistic version 
    def choosePair(self):
        ids = sorted(self.activeIds.keys())
        return ids[0], ids[1]

    def run(self):
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            newRoot = self.manager.applyAnd(self.activeIds[i].root, self.activeIds[j].root)
            self.newTerm(newRoot)
            del self.activeIds[i]
            del self.activeIds[j]
            print("%d & %d --> %d" % (i, j, self.termCount))
        if newRoot == self.manager.leaf0:
            print("UNSAT")
            self.unsat = True
        else:
            print("SAT")
            for s in self.manager.satisfyStrings(result):
                print("  " + s)
        
    def prove(self, cnfName = None, proofName = None):
        if not self.unsat:
            print("Have not determined that formula is unsatisfiable")
            return False
        p = prover.Prover(self.manager.operationLog, self.clauseLines, cnfName, proofName)
        p.run()
        
    
            
                    
            

    

    
