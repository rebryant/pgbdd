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
import random

import writer


# Generate files for mutilated chessboard problem
def usage(name):
    print("Usage: %s [-h] [-C] [-c] [-v] [-r ROOT] -n N [-w n|h|v|b] [-p e|c|d] [-s SEED]" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -C       Generate clauses only.  No order or schedule")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, and possibly ROOT.order, ROOT.schedule")
    print("  -c       Include corners")
    print("  -w WRAP  Wrap board horizontally (h), vertically (v), both (b) or neither (n)")
    print("  -p e|c|d Generate schedule that produces pseudoboolean equations (e), single constraints (c), or dual constraints (d)")
    print("  -n N     Specify size of board")
    print("  -s SEED  Provide random seed for randomizing variables")


def exactlyOne(vars):
    n = len(vars)
    if n == 0:
        return None # Can't do it
    # At least one
    clauses = [vars]
    # at most one via pairwise constraints
    for i in range(n):
        for j in range(i):
            clause = [-vars[i], -vars[j]]
            clauses.append(clause)
    return clauses


# Numbering scheme:
# Columns numbered from 0 to N-1
# Rows numbered from 0 to N-1
# H(r,c) denotes horizontal divider between rows r-1 and r for column c
#   Range: 
#    When wrap vertically: r: 1..n-1.  c:0..n-1  
#    Without wrap          r: 0..n-1.  c:0..n-1  
# V(r,c) denotes vertical divider between columns c-1 and c for row r
#   Range:
#    When wrap horizontally: r: 0..n-1,  c:0..n-1
#    Without wrap:           r: 0..n-1,  c:1..n-1

# Square at position r,c has
# top divider at r,c
# bottom divider at (r+1) mod N, c  (Mod only required for vertical wrap)
# left divider at r,c
# right divider at r, (c+1) mod N   (Mod only required for horizontal wrap)

class Square:
    top = None
    right = None
    bottom = None
    left = None
    row = 0
    col = 0

    # idDict: Dictionary of variable identifiers, indexed by (row, col, isHorizontal)
    def __init__(self, row, col, n, idDict):
        self.row = row
        self.col = col
        rp1 = (row+1) % n
        cp1 = (col+1) % n
        
        if (row,col,True) in idDict:
            self.top = idDict[(row,col,True)]
        else:
            self.top = None

        if (rp1,col,True) in idDict:
            self.bottom = idDict[(rp1,col,True)]
        else:
            self.bottom = None


        if (row,col,False) in idDict:
            self.left = idDict[(row,col,False)]
        else:
            self.left = None
        if (row,cp1,False) in idDict:
            self.right = idDict[(row,cp1,False)]
        else:
            self.right = None

    def doClauses(self, writer):
        allVars = [self.top, self.right, self.bottom, self.left]
        vars = [v for v in allVars if v is not None]
        clist = []
        if len(vars) > 1:  # Not chopped corner
            writer.doComment("Exactly one constraints for square %d,%d (%d variables)" % (self.row, self.col, len(vars)))
            clauses = exactlyOne(vars)
            for clause in clauses:
                clist.append(writer.doClause(clause))
        return clist

    # Generate commands for schedule to issue equation representing
    # this square
    def doEquation(self, swriter):
        allVars = [self.top, self.right, self.bottom, self.left]
        vlist = sorted([v for v in allVars if v is not None])
        clist = [1] * len(vlist)
        swriter.doPseudoBoolean(vlist, clist, 1, True)

    # Generate at-most-one constraint for this square
    def doAMO(self, swriter):
        allVars = [self.top, self.right, self.bottom, self.left]
        vlist = sorted([v for v in allVars if v is not None])
        clist = [-1] * len(vlist)
        swriter.doPseudoBoolean(vlist, clist, -1, False)

    # Generate at-least-one constraint for this square
    def doALO(self, swriter):
        allVars = [self.top, self.right, self.bottom, self.left]
        vlist = sorted([v for v in allVars if v is not None])
        clist = [1] * len(vlist)
        swriter.doPseudoBoolean(vlist, clist, 1, False)


class Board:
    # Variable ids, indexed by (row, col, isHorizontal)
    idDict = {}
    # Squares indexed by (row, col)
    squares = {}
    variableCount = 0
    variableList = []
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    verbose = False
    includeCorners = False
    wrapHorizontal = False
    wrapVertical = False
    n = None
    # What approach should be used to construct board
    doLinear = True
    doEquation = False
    doConstraint = False
    doDualConstraint = False

    def __init__(self, n, rootName, verbose = False, includeCorners = False, seed = None, wrapHorizontal = False, wrapVertical = False, pseudoType = None, clauseOnly = False):
        self.n = n
        expectedVariableCount = 2 * n * (n-1)
        if wrapHorizontal:
            expectedVariableCount += n
        if wrapVertical:
            expectedVariableCount += n
        if not includeCorners:
            expectedVariableCount -= 4
            if wrapHorizontal:
                expectedVariableCount -= 2
            if wrapVertical:
                expectedVariableCount -= 2
        self.variableList = list(range(1, expectedVariableCount+1))
        if seed is not None:
            random.seed(seed)
            random.shuffle(self.variableList)

        self.doEquation = False
        self.doConstraint = False
        if pseudoType is not None:
            self.doLinear = False
            if pseudoType == 'e':
                self.doEquation = True
            elif pseudoType == 'c':
                self.doConstraint  = True
            elif pseudoType == 'd':
                self.doDualConstraint = True
        self.verbose = verbose
        self.includeCorners = includeCorners
        self.wrapHorizontal = wrapHorizontal
        self.wrapVertical = wrapVertical
        self.cnfWriter = writer.CnfWriter(expectedVariableCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(expectedVariableCount, rootName, self.verbose, isNull=clauseOnly)
        self.orderWriter = writer.OrderWriter(expectedVariableCount, rootName, self.verbose, isNull=clauseOnly)
        self.idDict = {}
        self.squares = {}
        self.variableCount = 0
        self.idList = []

    def nextVariable(self):
        var = self.variableList[self.variableCount]
        self.variableCount += 1
        return var

    # Construct Column i.  Return lists of variables on left and right
    def doColumn(self, c):
        left = []
        right = []
        quants = []
        self.scheduleWriter.doComment("Adding column %d" % c)
        # Has something been put onto the stack?
        gotValue = False
        for ir in range(self.n):
            r = self.n-ir-1
            sq = self.squares[(r,c)]
            clist = sq.doClauses(self.cnfWriter)
            if len(clist) > 0:
                self.scheduleWriter.getClauses(clist)
                count = len(clist) if gotValue else len(clist)-1
                if count > 0:
                    self.scheduleWriter.doAnd(count)
                    gotValue = True
            if sq.bottom is not None:
                quants.append(sq.bottom)
            if sq.left is not None:
                left.append(sq.left)
            if sq.right is not None:
                right.append(sq.right)
        if len(quants) > 0:
            self.scheduleWriter.doQuantify(quants)
        self.scheduleWriter.doComment("Completed column %d.  Quantified %d variables" % (c, len(quants)))
        return (left, right)


    def constructBoardLinear(self):
        # Combine columns from left to right
        for c in range(self.n):
            (left, right) = self.doColumn(c)
            if c > 0:
                self.scheduleWriter.doComment("Combine column %d with predecessors" % c)
                self.scheduleWriter.doAnd(1)
                if len(left) > 0:
#                    if c == self.n//2:
#                        self.scheduleWriter.doInformation("Before quantification for column %d" % c)
                    self.scheduleWriter.doQuantify(left)
#                    if c == self.n//2:
#                        self.scheduleWriter.doInformation("After quantification for column %d" % c)
            self.scheduleWriter.doInformation("After quantification for column %d" % c)


    def constructBoardEquation(self):
        # Generate equation for each square
        for r in range(self.n):
            for c in range(self.n):
                # Generate clauses, And them, and generate equation
                # Each set of conjunctions is independent
                sq = self.squares[(r,c)]
                clist = sq.doClauses(self.cnfWriter)
                if len(clist) > 0:
                    self.scheduleWriter.doComment("Validating and generating equation for square %d,%d" % (r,c))
                    self.scheduleWriter.newTree()
                    self.scheduleWriter.getClauses(clist)
                    self.scheduleWriter.doAnd(len(clist))
                    sq.doEquation(self.scheduleWriter)


    def constructBoardConstraint(self):
        # Assumption: There are least as many squares with r+c odd than with it even
        # Generate constraint for each square
        for r in range(self.n):
            for c in range(self.n):
                # Generate clauses, And them, and generate equation
                # Each set of conjunctions is independent
                sq = self.squares[(r,c)]
                clist = sq.doClauses(self.cnfWriter)
                if len(clist) > 0:
                    doAMO = (r+c) % 2 == 0
                    cstring = "at-most-one" if doAMO else "at-least-one"
                    self.scheduleWriter.doComment("Validating and generating %s constraint for square %d,%d" % (cstring, r,c))
                    # Exploit fact that at-least-one is single clause at beginning
                    # and rest encode at-most-one
                    clist = clist[1:] if doAMO else clist[0:1]
                    self.scheduleWriter.newTree()
                    self.scheduleWriter.getClauses(clist)
                    self.scheduleWriter.doAnd(len(clist))
                    if doAMO:
                        sq.doAMO(self.scheduleWriter)
                    else:
                        sq.doALO(self.scheduleWriter)

    def constructBoardDualConstraint(self):
        # Generate both AMO & ALO constraints for each square
        for r in range(self.n):
            for c in range(self.n):
                # Generate clauses, And them, and generate equation
                # Each set of conjunctions is independent
                sq = self.squares[(r,c)]
                clist = sq.doClauses(self.cnfWriter)
                if len(clist) > 0:
                    self.scheduleWriter.doComment("Validating and generating both ALO and AMO constraints for square %d,%d" % (r,c))
                    # Exploit fact that at-least-one is single clause at beginning
                    # and rest encode at-most-one
                    aloList = clist[0:1]
                    amoList = clist[1:]
                    self.scheduleWriter.newTree()
                    self.scheduleWriter.getClauses(aloList)
                    self.scheduleWriter.doAnd(len(aloList))
                    sq.doALO(self.scheduleWriter)
                    self.scheduleWriter.newTree()
                    self.scheduleWriter.getClauses(amoList)
                    self.scheduleWriter.doAnd(len(amoList))
                    sq.doAMO(self.scheduleWriter)


    # Construct constraints for specified number of columns.  
    # Return lists of variables on left and right
    def treeBuild(self, leftIndex, columnCount):
        if columnCount == 1:
            (left, right) = self.doColumn(leftIndex)
            self.scheduleWriter.doInformation("Generated column %d" % (leftIndex))
            if leftIndex == 2:
                self.scheduleWriter.doInformation("RCSIZE %d %d" % (self.n, columnCount))
            return (left, right)
        rightIndex = leftIndex + columnCount - 1
        self.scheduleWriter.doComment("Generating columns %d .. %d" % (leftIndex, rightIndex))
        lcount = columnCount // 2
        rcount = columnCount - lcount
        left, rightMid = self.treeBuild(leftIndex, lcount)
        leftMid, right = self.treeBuild(leftIndex+lcount, rcount)
        midLeftIndex = leftIndex + lcount - 1
        midRightIndex = midLeftIndex + 1
        self.scheduleWriter.doComment("Merge columns %d .. %d with %d .. %d" % (leftIndex, midLeftIndex, midRightIndex, rightIndex))
        self.scheduleWriter.doAnd(1)
        if len(rightMid) > 0:
            self.scheduleWriter.doQuantify(rightMid)
        self.scheduleWriter.doInformation("Merged columns %d .. %d with %d .. %d" % (leftIndex, midLeftIndex, midRightIndex, rightIndex))
        if leftIndex <= self.n // 2 and rightIndex >= (self.n+1)//2 and rightIndex < self.n-1:
            self.scheduleWriter.doInformation("RCSIZE %d %d" % (self.n, columnCount))
        return (left, right)

    

    def constructBoard(self):
        if self.doLinear:
            self.constructBoardLinear()
        elif self.doEquation:
            self.constructBoardEquation()
        elif self.doConstraint:
            self.constructBoardConstraint()
        elif self.doDualConstraint:
            self.constructBoardDualConstraint()
        else:
            self.treeBuild(0, self.n)

    

    def build(self):
        n = self.n
        rmin = 0 if self.wrapVertical else 1
        cmin = 0 if self.wrapHorizontal else 1
        # Generate variables
        for r in range(n):
            if r >= rmin:
                hlist = []
                for c in range(n):
                    # Horizontal divider above.  Omit ones for UL and LR corners
                    omit = False
                    if not self.includeCorners:
                        omit = (r==1 and c ==0) or (r==n-1 and c==n-1)
                        if self.wrapVertical:
                            omit = omit or (r==0 and c==0) or (r==0 and c==n-1)
                    if not omit:
                        v = self.nextVariable()
                        self.idDict[(r,c,True)] = v
                        hlist.append(v)
                self.orderWriter.doOrder(hlist)

            vlist = []
            for c in range(cmin, n):
                # Vertical divider to left.  Omit ones for UL and LR corners
                omit = False
                if not self.includeCorners:
                    omit = (r==0 and c ==1) or (r==n-1 and c==n-1)
                    if self.wrapHorizontal:
                        omit = omit or (r==0 and c==0) or (r==n-1 and c==0)
                if not omit:
                    v = self.nextVariable()
                    self.idDict[(r,c,False)] = v
                    vlist.append(v)
            self.orderWriter.doOrder(vlist)

        # Generate squares
        for r in range(n):
            for c in range(n):
                self.squares[(r,c)] = Square(r, c, n, self.idDict)

        self.constructBoard()

    def finish(self):
        self.cnfWriter.finish()
        self.orderWriter.finish()
        self.scheduleWriter.finish()
    
                           
def run(name, args):
    verbose = False
    n = 0
    rootName = None
    includeCorners = False
    wrapHorizontal = False
    wrapVertical = False    
    pseudoType = None
    clauseOnly = False
    seed = None
    optlist, args = getopt.getopt(args, "hvCcar:n:w:p:s:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-c':
            includeCorners = True
        elif opt == '-C':
            clauseOnly = True
        elif opt == '-r':
            rootName = val
        elif opt == '-n':
            n = int(val)
        elif opt == '-w':
            if len(val) != 1 or val not in "nhvb":
                print("Invalid wrap specification '%s'" % val)
                usage(name)
                return
            if val in "hb":
                wrapHorizontal = True
            if val in "vb":
                wrapVertical = True
        elif opt == '-p':
            if len(val) == 1 and val in  "ecd":
                pseudoType = val
            else:
                print("Invalid pseudoboolean type '%s'" % val)
                usage(name)
                return
        elif opt == '-s':
            seed = int(val)

    if n == 0:
        print("Must have value for n")
        usage(name)
        return
    if rootName is None:
        print("Must have root name")
        usage(name)
        return
    b = Board(n, rootName, verbose, seed, includeCorners, wrapHorizontal, wrapVertical, pseudoType, clauseOnly)
    b.build()
    b.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

