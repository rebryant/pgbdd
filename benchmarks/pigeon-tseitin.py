#!/usr/bin/python

import sys
import  getopt
import writer


# Generate files for pigeonhole problem using Tseitin encoding of exactly-one constraint
def usage(name):
    print("Usage: %s [-h] [-c] [-v] [-r ROOT] -n N" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule")
    print("  -n N     Specify number of holes (pigeons = n+1)")


def exactlyOne(vars):
    n = len(vars)
    if n == 0:
        return None # Can't do it
    # Generate integer values for not = 1
    bits = []
    for x in range(1<<n):
        if popcount(x) != 1:
            bits.append(bitList(x, n))
    # Build clauses, inverting bits
    clauses = []
    for blist in bits:
        clause = [vars[i] if blist[i] == 0 else -vars[i] for i in range(n)]
        clauses.append(clause)
    return clauses
    

# Numbering scheme:
# Columns numbered from 0 to N, representing pigeons
# Rows numbered from 0 to N-1, representing holes
# Input variable M(h,p) indicates that pigeon p occupies hole h
#   Range: h: 0..n-1, p: 0..n
# Tseitin variable Z(h,p):
#     indicates that hole h does not contain any pigeons p' such that p' <= p
#   Range: h: 0..n-2, p: 0..n
# Tseitin variable O(h,p):
#     indicates that hold h contains exactly one pigeon p' such that p' <= p
#   Range: h: 0..n-1, p: 0..n

# Square at position at position h,p denotes how the presence of pigeon p
# will affect the status of hole h

class Position:
    h = 0
    p = 0
    M = None
    Zprev = None
    Oprev = None
    Z = None
    O = None
    # idDict: Dictionary of variable identifiers, indexed by (h, p, ('Z'|'O'|'M'))
    def __init__(self, h, p, idDict):
        self.h = h
        self.p = p
        self.M, self.Zprev, self.Oprev, self.Z, self.O = [None] * 5
        
        if (h,p,'M') in idDict:
            self.M = idDict[(h,p,'M')]
        if (h,p,'Z') in idDict:
            self.Z = idDict[(h,p,'Z')]
        if (h,p,'O') in idDict:
            self.O = idDict[(h,p,'O')]
        if (h,p-1,'Z') in idDict:
            self.Zprev = idDict[(h,p-1,'Z')]
        if (h,p-1,'O') in idDict:
            self.Oprev = idDict[(h,p-1,'O')]

    def doClauses(self, writer):
        clist = []
        if self.Z is not None:
            writer.doComment("Zero constraint for hole %d, pigeon %d" % (self.h, self.p))
            if self.Zprev is None:
                # Degenerate case Z <--> -M
                clist.append(writer.doClause([-self.Z, -self.M]))
                clist.append(writer.doClause([self.Z, self.M]))
            else:
                # General case Z <--> And(-M, Zprev)
                clist.append(writer.doClause([self.Z, self.M, -self.Zprev]))
                clist.append(writer.doClause([-self.Z, -self.M]))
                clist.append(writer.doClause([-self.Z, self.Zprev]))
        writer.doComment("One constraint for hole %d, pigeon %d" % (self.h, self.p))
        if self.Oprev is None:
            # Degenerate case: O <--> M
            clist.append(writer.doClause([-self.O, self.M]))
            clist.append(writer.doClause([self.O, -self.M]))
        else:
            # General case O <--> ITE(M, Zprev, Oprev)
            clist.append(writer.doClause([self.O, self.M, -self.Oprev]))
            clist.append(writer.doClause([-self.O, self.M, self.Oprev]))                         
            clist.append(writer.doClause([self.O, -self.M, -self.Zprev]))
            clist.append(writer.doClause([-self.O, -self.M, self.Zprev]))                         
        return clist

class Configuration:
    # Variable ids, indexed by (row, col, ('M'|'Z'|'O'))
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
        variableCount = 2*(n+1)*n + n*n
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
                ov = self.nextVariable()
                self.idDict[(h, p, 'O')] = ov
                hlist.append(ov)
                if p < self.n:
                    zv = self.nextVariable()        
                    self.idDict[(h, p, 'Z')] = zv
                    hlist.append(zv)
                    self.cnfWriter.doComment("Hole %d, pigeon %d: M=%d O=%d Z=%d" % (h, p, mv, ov, zv))
                else:
                    self.cnfWriter.doComment("Hole %d, pigeon %d: M=%d O=%d" % (h, p, mv, ov))
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
        # Compute new values of Z and O for each hole
        plist = []
        quants = []
        for h in range(self.n):
            position = self.positions[(h,p)]
            clist = position.doClauses(self.cnfWriter)
            self.scheduleWriter.getClauses(clist)
            self.scheduleWriter.doAnd(len(clist))
            if position.Zprev is not None:
                pvars.append(position.Zprev)
            if position.Oprev is not None:
                pvars.append(position.Oprev)
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
        # Enforce exactly-one constraint for all holes
        self.cnfWriter.doComment("Enforce exactly-one constraints for all holes")
        clist = []
        for h in range(self.n):
            clist.append(self.cnfWriter.doClause([self.idDict[(h,p,'O')]]))
        # Conjunct with final state constraint
        self.scheduleWriter.doComment("Conjunct state constraint with exactly-one constraints for all holes")
        self.scheduleWriter.getClauses(clist)
        self.scheduleWriter.doAnd(self.n)

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

