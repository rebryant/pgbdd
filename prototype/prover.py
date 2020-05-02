# Handle proof generation

import sys
import cnf

class ProverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Prover Exception: " + str(self.value)

class Prover:

    outFile = None
    operationLog = None
    clauseCount = 0
    clauseDict = {}
    
    def __init__(self, operationLog, clauseLines, cnfName = None, proofName = None):
        self.operationLog = operationLog
        opened = False
        self.outFile = sys.stdout
        if proofName is not None:
            try:
                self.outFile = open(proofName, 'w')
            except Exception:
                self.ProverException("Could not open proof output file '%s'" % proofName)
        if cnfName is None:
            for line in clauseLines:
                self.inputClause(line)
        else:
            try:
                c = cnf.CnfReader(self.countAction, self.inputClause, self.commentAction, cnfName)
            except Exception as ex:
                if opened:
                    self.outFile.close()
                raise ex
            
    def comment(self, line):
        self.outFile.write("c" + line + '\n')        

    def addClause(self, literalList, antecedentList):
        self.comment("Input clauses")
        self.ClauseCount += 1
        self.clauseDict[self.clauseCount] = (literalList, antecedentList)
        nums = [self.ClauseCount] + literalList + [0] + antecedentList + [0]
        self.outFile.write(" ".join([str(n) for n in nums]) + '\n')

    def inputClause(self, line):
        lits = [int(s) for s in lines.split()[:-1]]
        self.addClause(lits, [])

    def countAction(self, nvar, nclause):
        pass

    def commentAction(self, line):
        self.comment(line)


    def run(self):
        pass


