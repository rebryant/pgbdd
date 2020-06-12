#!/usr/bin/python

import sys
import  getopt
import writer


# Generate files for pigeonhole problem using Sinz's represent of AtMost1 constraints
def usage(name):
    print("Usage: %s [-h] [-c] [-v] [-r ROOT] -n N" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule")
    print("  -n N     Specify number of holes (pigeons = n+1)")


# Numbering scheme:
# Columns numbered from 0 to N, representing pigeons
# Rows numbered from 0 to N-1, representing holes
# Input variable M(h,p) indicates that pigeon p occupies hole h
#   Range: h: 0..n-1, p: 0..n
# Tseitin variable S(h,p):
#     indicates that hole h contains at most one pigeon p' such that p' <= p
#   Range: h: 0..n-1, p: 0..n-2

# Square  at position h,p denotes how the presence of pigeon p
# will affect the status of hole h

class Position:
    h = 0
    p = 0
    M = None
    Sprev = None
    S = None
    # idDict: Dictionary of variable identifiers, indexed by (h, p, ('S'|'M'))
    def __init__(self, h, p, idDict):
        self.h = h
        self.p = p
        self.M, self.Sprev, self.S = [None] * 3
        
        if (h,p,'M') in idDict:
            self.M = idDict[(h,p,'M')]
        if (h,p,'S') in idDict:
            self.S = idDict[(h,p,'S')]
        if (h,p-1,'S') in idDict:
            self.Sprev = idDict[(h,p-1,'S')]

    def doClauses(self, writer):
        clist = []
        writer.doComment("AtMost1 constraint for hole %d, pigeon %d" % (self.h, self.p))
        if self.S is not None:
            clist.append(writer.doClause([-self.M, self.S]))
        if self.Sprev is not None:
            clist.append(writer.doClause([-self.Sprev, -self.M]))
            if self.S is not None:
                clist.append(writer.doClause([-self.Sprev, self.S]))
        return clist

class Configuration:
    # Variable ids, indexed by (row, col, ('M'|'S'))
    idDict = {}
    # Positions indexed by (row, col)
    positions = {}
    variableCount = 0
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    verbose = False
    n = None

    def __init__(self, n, rootName, verbose = False):
        self.n = n
        variableCount = (n+1)*n + n*n
        self.verbose = verbose
        self.cnfWriter = writer.CnfWriter(variableCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(variableCount, rootName, self.verbose)
        self.orderWriter = writer.OrderWriter(variableCount, rootName, self.verbose)
        self.idDict = {}
        self.positions = {}
        self.variableCount = 0

    def nextVariable(self):
        self.variableCount += 1
        return self.variableCount

    def generateVariables(self):
        # Declared in hole-major order
        for h in range(self.n):
            hlist = []
            for p in range(self.n+1):
                mv = self.nextVariable()
                self.idDict[(h, p, 'M')] = mv
                hlist.append(mv)
                if p < self.n:
                    sv = self.nextVariable()        
                    self.idDict[(h, p, 'S')] = sv
                    hlist.append(sv)
                    self.cnfWriter.doComment("Hole %d, pigeon %d: M=%d S=%d" % (h, p, mv, sv))
                else:
                    self.cnfWriter.doComment("Hole %d, pigeon %d: M=%d" % (h, p, mv))
            self.orderWriter.doOrder(hlist)

    def buildPositions(self):
        for h in range(self.n):
            for p in range(self.n+1):
                self.positions[(h,p)] = Position(h,p, self.idDict)

    # Capture the effect pigeon p has on the holes
    # Return list of variables from previous pigeon
    def processPigeon(self, p):
        # The pigeon must be in some hole:
        self.cnfWriter.doComment("Pigeon %d must be in some hole" % p)
        pvars = [self.idDict[(h, p, 'M')] for h in range(self.n)]
        cfirst = self.cnfWriter.doClause(pvars)
        self.scheduleWriter.getClauses([cfirst])
        # Compute new value of S for each hole
        plist = []
        quants = []
        for h in range(self.n):
            position = self.positions[(h,p)]
            clist = position.doClauses(self.cnfWriter)
            self.scheduleWriter.getClauses(clist)
            self.scheduleWriter.doAnd(len(clist))
            if position.Sprev is not None:
                pvars.append(position.Sprev)
            quants.append(position.M)
        if len(quants) > 0:
            self.scheduleWriter.doQuantify(quants)
        self.scheduleWriter.doComment("Completed pigeon %d.  Quantified %d variables" % (p, len(quants)))
        return pvars

    def constructProblem(self):
        # Process all pigeons
        for p in range(self.n + 1):
            pvars = self.processPigeon(p)
            if p > 0:
                self.scheduleWriter.doComment("Combine pigeon %d with predecessors" % p)
                self.scheduleWriter.doAnd(1)
                self.scheduleWriter.doInformation("Before quantification for pigeon %d" % p)
                self.scheduleWriter.doQuantify(pvars)
                self.scheduleWriter.doInformation("After quantification for pigeon %d" % p)

    def build(self):
        self.generateVariables()
        self.buildPositions()
        self.constructProblem()

    def finish(self):
        self.cnfWriter.finish()
        self.orderWriter.finish()
        self.scheduleWriter.finish()
                           
def run(name, args):
    verbose = False
    n = 0
    rootName = None
    
    optlist, args = getopt.getopt(args, "hvcr:n:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-r':
            rootName = val
        elif opt == '-n':
            n = int(val)
        
    if n == 0:
        print("Must have value for n")
        usage(name)
        return
    if rootName is None:
        print("Must have root name")
        usage(name)
        return
    c = Configuration(n, rootName, verbose)
    c.build()
    c.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

