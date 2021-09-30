#!/usr/bin/python

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

import sys
import  getopt
import writer


# Generate files for pigeonhole problem using Sinz's represent of AtMost1 constraints
def usage(name):
    print("Usage: %s [-h] [-p] [-e] [-C] [-c] [-v] [-r ROOT] -n N" % name) 
    print("  -h       Print this message")
    print("  -p       Use pigeon-major variable ordering")
    print("  -E       Generate version with exactly-one constraints in both directions.  (Must also give -C)")
    print("  -C       Generate clauses only.  No order or schedule")
    print("  -c       Generate schedule that produces pseudoboolean constraints")
    print("  -v       Run in verbose mode")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, and possibly ROOT.order, and ROOT.schedule")
    print("  -n N     Specify number of holes (pigeons = n+1)")


# Numbering scheme:
# Columns numbered from 0 to N, representing pigeons
# Rows numbered from 0 to N-1, representing holes
# Input variable M(h,p) indicates that pigeon p occupies hole h
#   Range: h: 0..n-1, p: 0..n
# Tseitin variable S(h,p):
#     indicates that hole h contains at most one pigeon p' such that p' <= p
#   Range: h: 0..n-1, p: 0..n-1
# Optionally: Tseitin variable T(h,p):
#     indicates that pigeon p is placed in at most one hole h' such that h' <= h
#   Range: h: 0..n-2, p: 0..n


# Square  at position h,p denotes how the presence of pigeon p
# will affect the status of hole h

class Position:
    h = 0
    p = 0
    M = None
    Sprev = None
    S = None
    Tprev = None
    T = None

    clauseList = []
    # idDict: Dictionary of variable identifiers, indexed by (h, p, ('M'|'S'|'T'))
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
        if (h,p,'T') in idDict:
            self.T = idDict[(h,p,'T')]
        if (h-1,p,'T') in idDict:
            self.Tprev = idDict[(h-1,p,'T')]

    def doClauses(self, writer):
        clist = []
        if self.S is not None or self.Sprev is not None:
            writer.doComment("AtMost1 constraint for hole %d, pigeon %d" % (self.h, self.p))
        if self.S is not None:
            clist.append(writer.doClause([-self.M, self.S]))
        if self.Sprev is not None:
            clist.append(writer.doClause([-self.Sprev, -self.M]))
            if self.S is not None:
                clist.append(writer.doClause([-self.Sprev, self.S]))
        if self.T is not None or self.Tprev is not None:
            writer.doComment("AtMost1 constraint for pigeon %d, hole %d" % (self.p, self.h))
        if self.T is not None:
            clist.append(writer.doClause([-self.M, self.T]))
        if self.Tprev is not None:
            clist.append(writer.doClause([-self.Tprev, -self.M]))
            if self.T is not None:
                clist.append(writer.doClause([-self.Tprev, self.T]))
        # Save clause list so that can later generate constraints
        self.clauseList = clist
        return clist

class Configuration:
    # Variable ids, indexed by (row, col, ('M'|'S'|'T'))
    idDict = {}
    # Positions indexed by (row, col)
    positions = {}
    variableCount = 0
    doExactly1 = False
    doConstraints = False
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    verbose = False
    n = None

    def __init__(self, n, rootName, doExactly1, doConstraints = False, verbose = False, clauseOnly = False):
        self.n = n
        self.doExactly1 = doExactly1
        self.doConstraints = doConstraints
        self.verbose = verbose
        variableCount = n*(n+1) + n*n
        if doExactly1:
            variableCount += (n-1)*(n+1)
            clauseOnly =  True
        self.cnfWriter = writer.CnfWriter(variableCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(variableCount, rootName, self.verbose, isNull = clauseOnly)
        self.orderWriter = writer.OrderWriter(variableCount, rootName, self.verbose, isNull = clauseOnly)
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
                cstring = "Hole %d, pigeon %d: M=%d" % (h, p, mv)
                if p < self.n:
                    sv = self.nextVariable()        
                    self.idDict[(h, p, 'S')] = sv
                    hlist.append(sv)
                    cstring += " S=%d" % (sv)
                if self.doExactly1 and h < self.n-1:
                    tv = self.nextVariable()
                    self.idDict[(h, p, 'T')] = tv
                    hlist.append(tv)
                    cstring += " T=%d" % (tv)
                self.cnfWriter.doComment(cstring)
            self.orderWriter.doOrder(hlist)


    def generateVariablesPM(self):
        # Declared in pigeon-major order
        for p in range(self.n+1):
            plist = []
            for h in range(self.n):
                mv = self.nextVariable()
                self.idDict[(h, p, 'M')] = mv
                plist.append(mv)
                cstring = "Hole %d, pigeon %d: M=%d" % (h, p, mv)
                if p < self.n:
                    sv = self.nextVariable()        
                    self.idDict[(h, p, 'S')] = sv
                    plist.append(sv)
                    cstring += " S=%d" % (sv)
                if self.doExactly1 and h < self.n-1:
                    tv = self.nextVariable()
                    self.idDict[(h, p, 'T')] = tv
                    plist.append(tv)
                    cstring += " T=%d" % (tv)
                self.cnfWriter.doComment(cstring)
            self.orderWriter.doOrder(plist)
          

    def buildPositions(self):
        for h in range(self.n):
            for p in range(self.n+1):
                self.positions[(h,p)] = Position(h,p, self.idDict)

    def processHole(self, h):
        # When doing Exactly1 constraints
        # The hole must contain a pigeon
        self.cnfWriter.doComment("Hole %s must contain some pigeon" % h)
        hvars = [self.idDict[(h, p, 'M')] for p in range(self.n+1)]
        self.cnfWriter.doClause(hvars)

    # Capture the effect pigeon p has on the holes
    # Return list of variables from previous pigeon
    def processPigeon(self, p):
        # The pigeon must be in some hole:
        self.cnfWriter.doComment("Pigeon %d must be in some hole" % p)
        pvars = [self.idDict[(h, p, 'M')] for h in range(self.n)]
        cfirst = self.cnfWriter.doClause(pvars)
        if self.doConstraints:
            self.scheduleWriter.newTree()
            self.scheduleWriter.doComment("ALO constraint for pigeon %d" % p)
            self.scheduleWriter.getClauses([cfirst])
            self.scheduleWriter.doPseudoBoolean(pvars, [1]*len(pvars), 1, isEquation=False)
        else:
            self.scheduleWriter.getClauses([cfirst])
        # Compute new value of S for each hole
        plist = []
        quants = []
        for h in range(self.n):
            position = self.positions[(h,p)]
            clist = position.doClauses(self.cnfWriter)
            if not self.doConstraints:
                self.scheduleWriter.getClauses(clist)
                self.scheduleWriter.doAnd(len(clist))
            if position.Sprev is not None:
                pvars.append(position.Sprev)
            quants.append(position.M)
        if not self.doConstraints:
            if len(quants) > 0:
                self.scheduleWriter.doQuantify(quants)
                self.scheduleWriter.doComment("Completed pigeon %d.  Quantified %d variables" % (p, len(quants)))
        return pvars

    def constructProblem(self):
        # Process all pigeons
        for p in range(self.n + 1):
            pvars = self.processPigeon(p)
            if not self.doConstraints and p > 0:
                self.scheduleWriter.doComment("Combine pigeon %d with predecessors" % p)
                self.scheduleWriter.doAnd(1)
                self.scheduleWriter.doInformation("Before quantification for pigeon %d" % p)
                self.scheduleWriter.doQuantify(pvars)
                self.scheduleWriter.doInformation("After quantification for pigeon %d" % p)
        if self.doExactly1:
            for h in range(self.n):
                self.processHole(h)

    def constructAmoConstraints(self):
        for h in range(self.n):
            self.scheduleWriter.doComment("AMO constraint for hole %d" % h)
            self.scheduleWriter.newTree()
            svars = [self.idDict[(h,p,'S')] for p in range(self.n)]
            pvars = [self.idDict[(h,p,'M')] for p in range(self.n+1)]
            for p in range(self.n+1):
                clist = self.positions[(h,p)].clauseList
                self.scheduleWriter.getClauses(clist)
                self.scheduleWriter.doAnd(len(clist))
                if p > 0:
                    self.scheduleWriter.doQuantify([svars[p-1]])
            self.scheduleWriter.doPseudoBoolean(pvars, [-1]*len(pvars), -1, isEquation=False)


    def build(self, pigeonMajor = False):
        if pigeonMajor:
            self.generateVariablesPM()
        else:
            self.generateVariables()
        self.buildPositions()
        self.constructProblem()
        if self.doConstraints:
            self.constructAmoConstraints()

    def finish(self):
        self.cnfWriter.finish()
        self.orderWriter.finish()
        self.scheduleWriter.finish()
                           
def run(name, args):
    doConstraints = False
    verbose = False
    n = 0
    pigeonMajor = False
    rootName = None
    exactly1 = False
    clauseOnly = False
    
    optlist, args = getopt.getopt(args, "hvpECcr:n:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-p':
            pigeonMajor = True
        elif opt == '-c':
            doConstraints = True
        elif opt == '-E':
            exactly1 = True
        elif opt == '-C':
            clauseOnly = True
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

    if exactly1 and not clauseOnly:
        print("Cannot generate schedule for exacty-one constraints")
        return

    c = Configuration(n, rootName, exactly1, doConstraints, verbose, clauseOnly)
    c.build(pigeonMajor)
    c.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

