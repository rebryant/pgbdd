#!/usr/bin/python

import sys
import  getopt
import writer


# Generate files for pigeonhole problem using variant of Sinz's representation of AtMost1 constraints
# This version reduces the number of Tseitin variables by factor of 2.
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
#   Range: h: 0..n-1, p: 2, 4, 6, .. n-1

# Square  at position h,p denotes how the presence of pigeon p
# will affect the status of hole h

# Encode leftmost 1, 2, or 3 pigeons for hole h
class LeftPosition:
    h = 0
    width = 3
    M0 = None
    M1 = None
    M2 = None
    Sprev = None
    S = None


    def __init__(self, h, width, idDict):
        self.h = h
        self.width = width
        self.M0, self.M1, self.M2, self.Sprev, self.S = [None] * 5

        self.M0 = idDict[(h,0,'M')]
        if width > 1:
            self.M1 = idDict[(h,1,'M')]
        if width > 2:
            self.M2 = idDict[(h,2,'M')]
        if (h,width-1,'S') in idDict:
            self.S = idDict[(h,width-1,'S')]

    def mlist(self):
        ls = [self.M0]
        if self.width > 1:
            ls.append(self.M1)
        if self.width > 2:
            ls.append(self.M2)
        return ls

    def doClauses(self, writer):
        clist = []
        writer.doComment("AtMost1 constraint for hole %d, pigeons 0..%d" % (self.h, self.width-1))
        if self.S is not None:
            clist.append(writer.doClause([-self.M0, self.S]))
            if self.width > 1:
                clist.append(writer.doClause([-self.M1, self.S]))
            if self.width > 2:
                clist.append(writer.doClause([-self.M2, self.S]))
        if self.width > 1:
            clist.append(writer.doClause([-self.M0, -self.M1]))
        if self.width > 2:
            clist.append(writer.doClause([-self.M0, -self.M2]))
            clist.append(writer.doClause([-self.M1, -self.M2]))
        return clist

# Encode 1 or 2 pigeons for hole h
# p denotes position just to the left of this one
class Position:
    h = 0
    p = 0
    width = 2
    M0 = None
    M1 = None
    Sprev = None
    S = None
    # idDict: Dictionary of variable identifiers, indexed by (h, p, ('S'|'M'))
    def __init__(self, h, p, width, idDict):
        self.h = h
        self.p = p
        self.width = width
        self.M0, self.M1, self.Sprev, self.S = [None] * 4

        self.M0 = idDict[(h,p+1,'M')]
        if width > 1:
            self.M1 = idDict[(h,p+2,'M')]
        self.Sprev = idDict[(h,p,'S')]
        if (h,p+width,'S') in idDict:
            self.S = idDict[(h,p+width,'S')]

    def mlist(self):
        ls = [self.M0]
        if self.width > 1:
            ls.append(self.M1)
        return ls

    def doClauses(self, writer):
        clist = []
        writer.doComment("AtMost1 constraint for hole %d, pigeons %d-%d" % (self.h, self.p, self.p+self.width-1))
        if self.S is not None:
            clist.append(writer.doClause([-self.Sprev, self.S]))
            clist.append(writer.doClause([-self.M0, self.S]))
            if self.width > 1:
                clist.append(writer.doClause([-self.M1, self.S]))
        clist.append(writer.doClause([-self.Sprev, -self.M0]))
        if self.width > 1:
            clist.append(writer.doClause([-self.Sprev, -self.M1]))            
            clist.append(writer.doClause([-self.M0, -self.M1]))            
        return clist

class Configuration:
    # Variable ids, indexed by (row, col, ('M'|'S'))
    idDict = {}
    # Positions indexed by (row, col)
    positions = {}
    pindexList = []
    variableCount = 0
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    verbose = False
    n = None

    def __init__(self, n, rootName, verbose = False):
        self.n = n
        if self.n > 2:
            tvarPerHole = int((n-2)/2 if n%2== 0 else (n-1)/2)
        else:
            tvarPerHole = 0
        variableCount = n*(n+1) + tvarPerHole * n
        self.verbose = verbose
        self.cnfWriter = writer.CnfWriter(variableCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(variableCount, rootName, self.verbose)
        self.orderWriter = writer.OrderWriter(variableCount, rootName, self.verbose)
        self.idDict = {}
        self.positions = {}
        self.pindexList = [p for p in range(self.n) if p % 2 == 0]
        self.variableCount = 0

    def nextVariable(self):
        self.variableCount += 1
        return self.variableCount

    def hasTseitin(self, p):
        return p > 0 and p < self.n and p % 2 == 0

    def generateVariables(self):
        # Declared in hole-major order
        for h in range(self.n):
            hlist = []
            for p in range(self.n+1):
                mv = self.nextVariable()
                self.idDict[(h, p, 'M')] = mv
                hlist.append(mv)
                if self.hasTseitin(p):
                    sv = self.nextVariable()        
                    self.idDict[(h, p, 'S')] = sv
                    hlist.append(sv)
                    self.cnfWriter.doComment("Hole %d, pigeon %d: M=%d S=%d" % (h, p, mv, sv))
                else:
                    self.cnfWriter.doComment("Hole %d, pigeon %d: M=%d" % (h, p, mv))
            self.orderWriter.doOrder(hlist)

    def buildPositions(self):
        for h in range(self.n):
            if self.n < 3:
                self.positions[(h,0)] = LeftPosition(h, self.n+1, self.idDict)
            else:
                self.positions[(h,0)] = LeftPosition(h, 3, self.idDict)
                for p in self.pindexList[1:]:
                    width = min(2, self.n-p)
                    self.positions[(h,p)] = Position(h, p, width, self.idDict)


    # Capture the effect pigeon p (and possibly p+1 and p+2) has on the holes
    # Return list of variables from previous pigeon
    def processPigeons(self, p, width):
        # The pigeon(s) must be in some hole:
        firstP = 0 if p == 0 else p+1
        clist = []
        for w in range(width):
            self.cnfWriter.doComment("Pigeon %d must be in some hole" % (firstP+w))
            pvars = [self.idDict[(h, firstP+w, 'M')] for h in range(self.n)]
            clist.append(self.cnfWriter.doClause(pvars))
        self.scheduleWriter.getClauses(clist)
        if width > 1:
            self.scheduleWriter.doAnd(width-1)

        # Compute new value of S for each hole
        plist = []
        quants = []
        for h in range(self.n):
            position = self.positions[(h,p)]
            clist = position.doClauses(self.cnfWriter)
            self.scheduleWriter.getClauses(clist)
            self.scheduleWriter.doAnd(len(clist))
            if position.Sprev is not None:
                plist.append(position.Sprev)
            quants += position.mlist()
        if len(quants) > 0:
            self.scheduleWriter.doQuantify(quants)
        self.scheduleWriter.doComment("Completed pigeons %d-%d.  Quantified %d variables" % (p, p+width-1, len(quants)))
        return plist

    def constructProblem(self):
        # Process all pigeons
        for p in self.pindexList:
            position = self.positions[(0,p)]
            width = position.width
            pvars = self.processPigeons(p,width)
            if p > 0:
                self.scheduleWriter.doComment("Combine pigeons %d..%d with predecessors" % (p, p+width-1))
                self.scheduleWriter.doAnd(1)
                self.scheduleWriter.doInformation("Before quantification for pigeons %d..%d" % (p, p+width-1))
                self.scheduleWriter.doQuantify(pvars)
                self.scheduleWriter.doInformation("After quantification for pigeons %d..%d" % (p, p+width-1))

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

