#!/usr/bin/python

import sys
import  getopt
import writer


# Generate files for mutilated chessboard problem
# Experiment with different orderings of variables for bucket elimination

def usage(name):
    print("Usage: %s [-h] [-B] [-c] [-v] [-r ROOT] -n N [-m 1-5]" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, ROOT.schedule, and ROOT.buckets")
    print("  -c       Include corners")
    print("  -n N     Specify size of board")
    print("  -m MODE  Specify elimination bucket ordering (1-5)")


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
#   Range: r: 1..n-1.  c:0..n-1
# V(r,c) denotes vertical divider between columns c-1 and c for row r
#   Range: r: 0..n-1,  c:1..n-1


# Square at position r,c has
# top divider at r,c
# bottom dividerr at r+1,c
# left divider at r,c
# right divider at r,c+1

class Square:
    top = None
    right = None
    bottom = None
    left = None
    row = 0
    col = 0

    # idDict: Dictionary of variable identifiers, indexed by (row, col, isHorizontal)
    def __init__(self, row, col, idDict):
        self.row = row
        self.col = col
        
        if (row,col,True) in idDict:
            self.top = idDict[(row,col,True)]
        else:
            self.top = None
        if (row+1,col,True) in idDict:
            self.bottom = idDict[(row+1,col,True)]
        else:
            self.bottom = None

        if (row,col,False) in idDict:
            self.left = idDict[(row,col,False)]
        else:
            self.left = None
        if (row,col+1,False) in idDict:
            self.right = idDict[(row,col+1,False)]
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

class Board:
    # Variable ids, indexed by (row, col, isHorizontal)
    idDict = {}
    # Squares indexed by (row, col)
    squares = {}
    variableCount = 0
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    bucketWriter = None
    verbose = False
    includeCorners = False
    n = None
    # What approach should be used to construct board
    doLinear = True
    # List of variable Ids for bucket ordering
    idList = []
    bucketMode = 1
    bucketDescription = ""

    def __init__(self, n, rootName, verbose = False, includeCorners = False, bucketMode = 1):
        self.n = n
        variableCount = 2 * n * (n-1)
        if not includeCorners:
            variableCount -= 4
        self.verbose = verbose
        self.includeCorners = includeCorners
        self.bucketMode = bucketMode
        self.cnfWriter = writer.CnfWriter(variableCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(variableCount, rootName, self.verbose)
        self.bucketWriter = writer.OrderWriter(variableCount, rootName, self.verbose, suffix = "buckets")
        self.orderWriter = writer.OrderWriter(variableCount, rootName, self.verbose)
        self.idDict = {}
        self.squares = {}
        self.variableCount = 0
        self.idList = []

    def nextVariable(self):
        self.variableCount += 1
        return self.variableCount

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
        else:
            self.treeBuild(0, self.n)

    def build(self):
        n = self.n
        # Generate variables
        for r in range(n):
            if r >= 1:
                hlist = []
                for c in range(n):
                    # Horizontal divider above.  Omit ones for UL and LR corners
                    omit = not self.includeCorners and (r==1 and c ==0)
                    omit = omit or not self.includeCorners and (r==n-1 and c==n-1)
                    if not omit:
                        v = self.nextVariable()
                        self.idDict[(r,c,True)] = v
                        hlist.append(v)
                self.orderWriter.doOrder(hlist)

            vlist = []
            for c in range(1, n):
                # Vertical divider to left.  Omit ones for UL and LR corners
                omit = not self.includeCorners and (r==0 and c ==1)
                omit = omit or not self.includeCorners and (r==n-1 and c==n-1)
                if not omit:
                    v = self.nextVariable()
                    self.idDict[(r,c,False)] = v
                    vlist.append(v)
            self.orderWriter.doOrder(vlist)

        # Generate squares
        for r in range(n):
            for c in range(n):
                self.squares[(r,c)] = Square(r, c, self.idDict)

        # Generate bucket ordering
        self.bucketize()
        self.constructBoard()

    def finish(self):
        self.cnfWriter.finish()
        self.orderWriter.finish()
        self.bucketWriter.finish()
        self.scheduleWriter.finish()
                           
    def bucketize(self):
        bmode = self.bucketMode
        if bmode == 1:
            self.bucketize_1()
        elif bmode == 2:
            self.bucketize_2()
        elif bmode == 3:
            self.bucketize_3()
        elif bmode == 4:
            self.bucketize_4()
        elif bmode == 5:
            self.bucketize_5()
        elif bmode == 6:
            self.bucketize_6()
        else:
            print("Don't support bucket mode #%d" % self.bucketMode)
            sys.exit(1)
        if True or self.verbose:
            print("Bucket strategy: %s" % self.bucketDescription)        

    def bucketize_1(self):
        n = self.n
        self.bucketDescription = "H1H2V2[HiVi]"
        # Generate bucket ordering
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,True) in self.idDict:
                    blist.append(self.idDict[(r,c,True)])
            for r in range(n):
                if (r,c,False) in self.idDict:
                    blist.append(self.idDict[(r,c,False)])
            self.bucketWriter.doOrder(blist)

    def bucketize_2(self):
        n = self.n
        self.bucketDescription = "H1V2H2[ViHi]"
        # Generate bucket ordering
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,False) in self.idDict:
                    blist.append(self.idDict[(r,c,False)])
            for r in range(n):
                if (r,c,True) in self.idDict:
                    blist.append(self.idDict[(r,c,True)])
            self.bucketWriter.doOrder(blist)

    def bucketize_3(self):
        n = self.n
        self.bucketDescription = "H1[Hi]V2[Vi]"
        # Generate bucket ordering
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,True) in self.idDict:
                    blist.append(self.idDict[(r,c,True)])
            self.bucketWriter.doOrder(blist)

        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,False) in self.idDict:
                    blist.append(self.idDict[(r,c,False)])
            self.bucketWriter.doOrder(blist)

    def bucketize_4(self):
        n = self.n
        self.bucketDescription = "V2[Vi]H1[Hi]"
        # Generate bucket ordering
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,False) in self.idDict:
                    blist.append(self.idDict[(r,c,False)])
            self.bucketWriter.doOrder(blist)
            
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,True) in self.idDict:
                    blist.append(self.idDict[(r,c,True)])
            self.bucketWriter.doOrder(blist)

    def bucketize_5(self):
        n = self.n
        self.bucketDescription = "H1HV2[HVi]"
        # Generate bucket ordering
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,True) in self.idDict:
                    blist.append(self.idDict[(r,c,True)])
                if (r,c,False) in self.idDict:
                    blist.append(self.idDict[(r,c,False)])
            self.bucketWriter.doOrder(blist)

    def bucketize_6(self):
        n = self.n
        self.bucketDescription = "HV+1[HV+i]"
        # Generate bucket ordering
        for c in range(n):
            blist = []
            for r in range(n):
                if (r,c,True) in self.idDict:
                    blist.append(self.idDict[(r,c,True)])
                if (r,c+1,False) in self.idDict:
                    blist.append(self.idDict[(r,c+1,False)])
            self.bucketWriter.doOrder(blist)
            

            
def run(name, args):
    verbose = False
    n = 0
    rootName = None
    includeCorners = False
    bucketMode = 1
    
    optlist, args = getopt.getopt(args, "hvcar:n:m:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-c':
            includeCorners = True
        elif opt == '-r':
            rootName = val
        elif opt == '-n':
            n = int(val)
        elif opt == '-m':
            bucketMode = int(val)
        
    if n == 0:
        print("Must have value for n")
        usage(name)
        return
    if rootName is None:
        print("Must have root name")
        usage(name)
        return
    b = Board(n, rootName, verbose, includeCorners, bucketMode = bucketMode)
    b.build()
    b.finish()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

