#!/usr/bin/python

import sys
import  getopt
import random
import writer

# Increase maximum recursion depth
sys.setrecursionlimit(100 * sys.getrecursionlimit())


# Generate CNF, order, and schedule files to compare two trees of xor's over a common set of inputs

def usage(name):
    print("Usage: %s [-h] [-v] [-f] [-r ROOT] -n N -m M1M2" % name)
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -O (f|r) Specify order of nodes (f = flipped, r = random)")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule")
    print("  -n N     Specify number of tree inputs")
    print("  -m M1M2  Specify modes for the two trees: ")
    print("             B=balanced, L=left linear, R=right linear, X=random, P=permuted")


# General/leaf tree node
class Node:
    isLeaf = True
    output =  0 # Identity of Output variable
    height = 0

    def __init__(self, output):
        self.isLeaf = True
        self.height = 0
        self.output = output

    def emitClauses(self, writer):
        pass

    def emitSchedule(self, writer):
        pass

    def getVariables(self, heightDict):
        pass

    def show(self, maxHeight = None, spacing = 4):
        if maxHeight is None:
            maxHeight = self.height
        indent = " " * spacing * (maxHeight-self.height)
        print("%sL%d" % (indent, self.output))

class TreeNode(Node):
    left = None
    right = None
    clauseIds = []

    def __init__(self, output, left, right):
        Node.__init__(self, output)
        self.left = left
        self.right = right
        self.isLeaf = False
        self.height = max(left.height, right.height) + 1
        self.clauseIds = []

    def emitClauses(self, writer):
        self.left.emitClauses(writer)
        self.right.emitClauses(writer)
        A = self.left.output
        B = self.right.output
        C = self.output
        writer.doComment("Xor(%d, %d) --> %d" % (A, B, C))
        self.clauseIds.append(writer.doClause([-A, -B, -C]))
        self.clauseIds.append(writer.doClause([-A,  B,  C]))
        self.clauseIds.append(writer.doClause([ A, -B,  C]))
        self.clauseIds.append(writer.doClause([ A,  B, -C]))

    def emitSchedule(self, writer):
        self.left.emitSchedule(writer)
        self.right.emitSchedule(writer)
        writer.getClauses(self.clauseIds)
        writer.doAnd(len(self.clauseIds))
        quants = []
        if not self.left.isLeaf:
            quants.append(self.left.output)
        if not self.right.isLeaf:
            quants.append(self.right.output)
        if len(quants) > 0:
            writer.doQuantify(quants)
                              
    # Gather all non-input variables into dictionary, indexed by height
    def getVariables(self, heightDict):
        if self.height not in heightDict:
            heightDict[self.height] = [self.output]
        else:
            heightDict[self.height].append(self.output)
        self.left.getVariables(heightDict)
        self.right.getVariables(heightDict)
    
    def show(self, maxHeight = None, spacing = 4):
        if maxHeight is None:
            maxHeight = self.height
        indent = " " * spacing * (maxHeight-self.height)
        self.left.show(maxHeight, spacing)
        print("%sT%d (%d, %d)" % (indent, self.output, self.left.output, self.right.output))
        self.right.show(maxHeight, spacing)

class TreeBuilder:
    (modeLeft, modeRight, modeBalanced, modeRandom, modePermute) = range(5)
    # Number of inputs
    inputCount = 1
    variableCount = 0
    roots = []
    rootClauses = []
    modes = []
    leafTrees = []
    cnfWriter = None
    scheduleWriter = None
    orderWriter = None
    verbose = False

    def __init__(self, count, rootName, verbose = False):
        self.verbose = verbose
        self.inputCount = count
        # Leaves + 2 binary trees
        fullCount = 3 * count - 2
        self.leafTrees = [Node(v) for v in range(1, count+1)]
        self.variableCount = count
        self.roots = []
        self.modes = []
        self.cnfWriter = writer.CnfWriter(fullCount, rootName, self.verbose)
        self.scheduleWriter = writer.ScheduleWriter(fullCount, rootName, self.verbose)
        self.orderWriter = writer.OrderWriter(fullCount, rootName, self.verbose)

    def findMode(self, shortName):
        names = {"L": self.modeLeft,
                 "R": self.modeRight,
                 "B": self.modeBalanced,
                 "X": self.modeRandom,
                 "P": self.modePermute}
        if shortName in names:
            return names[shortName]
        print("Unknown mode '%s'.  Aborting" % shortName)
        sys.exit(1)

    def getModeName(self, mode):
        return ["Left", "Right", "Balanced", "Random", "Permuted"][mode]

    def addRoot(self, mode):
        subtrees = self.leafTrees
        if mode == self.modeLeft:
            root = self.buildSplit(subtrees, self.chooseMost)
        elif mode == self.modeRight:
            root = self.buildSplit(subtrees, self.chooseLeast)
        elif mode == self.modeBalanced:
            root = self.buildSplit(subtrees, self.chooseHalf)
        elif mode == self.modeRandom:
            root = self.buildRandom(subtrees)
        else:
            # Permuted mode: Left tree with permuted leaves
            random.shuffle(subtrees)
            root = self.buildSplit(subtrees, self.chooseMost)
        self.roots.append(root)
        self.modes.append(mode)


    def buildSplit(self, subtrees, leftChooser):
        if len(subtrees) == 1:
            return subtrees[0]
        leftCount = leftChooser(len(subtrees))
        leftTrees = subtrees[:leftCount]
        rightTrees = subtrees[leftCount:]
        leftRoot = self.buildSplit(leftTrees, leftChooser)
        rightRoot = self.buildSplit(rightTrees, leftChooser)
        self.variableCount += 1
        root = TreeNode(self.variableCount, leftRoot, rightRoot)
        return root

    def chooseLeast(self, count):
        return 1

    def chooseMost(self, count):
        return count-1

    def chooseHalf(self, count):
        return count // 2
        
    def buildRandom(self, subtrees):
        while len(subtrees) > 1:
            id1 = random.choice(list(range(len(subtrees))))
            t1 = subtrees[id1]
            subtrees = subtrees[:id1] + subtrees[id1+1:]
            id2 = random.choice(list(range(len(subtrees))))
            t2 = subtrees[id2]
            subtrees = subtrees[:id2] + subtrees[id2+1:]
            self.variableCount += 1
            tn = TreeNode(self.variableCount, t1, t2)
            subtrees.append(tn)
        return subtrees[0]

    def emitCnf(self):
        if len(self.roots) != 2:
            print("Fatal: Must have two roots.")
            sys.exit(1)
        for root in self.roots:
            root.emitClauses(self.cnfWriter)
        # Emit comparator
        id1 = self.roots[0].output
        id2 = self.roots[1].output
        self.rootClauses = []
        self.cnfWriter.doComment("Comparison of two tree roots")
        self.rootClauses.append(self.cnfWriter.doClause([id1, id2]))
        self.rootClauses.append(self.cnfWriter.doClause([-id1, -id2]))
        self.cnfWriter.finish()
        
    def emitSchedule(self):
        if len(self.roots) != 2:
            print("Fatal: Must have two roots.")
            sys.exit(1)
        for root in self.roots:
            self.scheduleWriter.newTree()
            root.emitSchedule(self.scheduleWriter)
        # Final steps.  Have two roots on stack
        self.scheduleWriter.getClauses(self.rootClauses)
        self.scheduleWriter.doAnd(3)
        self.scheduleWriter.finish()

    def emitOrder(self, doFlip = False, doRandom = False):
        if doRandom:
            vars = list(range(1, self.variableCount+1))
            random.shuffle(vars)
            self.orderWriter.doOrder(vars)
            self.orderWriter.finish()
            return
        varDict1 = {}
        self.roots[0].getVariables(varDict1)
        keyFun = (lambda h : h) if doFlip else (lambda h : -h)
        h1list = sorted(varDict1.keys(), key = keyFun)
        for k in h1list:
            self.orderWriter.doOrder(varDict1[k])
        varDict2 = {}
        self.roots[1].getVariables(varDict2)
        h2list = sorted(varDict2.keys(), key = keyFun)
        for k in h2list:
            self.orderWriter.doOrder(varDict2[k])
        leaves = list(range(1, self.inputCount+1))
        if self.modeLeft in self.modes or self.modePermute in self.modes:
            leaves.reverse()
        self.orderWriter.doOrder(leaves)
        self.orderWriter.finish()

def run(name, args):
    verbose = False
    count = 0
    rootName = None
    mstring = ""
    doFlip = False
    doRandom = False
    
    optlist, args = getopt.getopt(args, "hvr:n:m:O:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-O':
            if val == 'f':
                doFlip = True
            elif val == 'r':
                doRandom = True
            else:
                print("Unknown ordering mode '%s'" % val)
                return
        elif opt == '-v':
            verbose = True
        elif opt == '-r':
            rootName = val
        elif opt == '-n':
            count = int(val)
        elif opt == '-m':
            if len(val) != 2:
                print("Must specify two tree building modes")
                usage(name)
                return
            mstring = val
    if count == 0:
        print("Count required")
        return
    if rootName is None:
        print("Root name required")
        return
    t = TreeBuilder(count, rootName, verbose)
    for m in mstring:
        mode = t.findMode(m)
        t.addRoot(mode)
    t.emitCnf()
    t.emitOrder(doFlip = doFlip, doRandom = doRandom)
    t.emitSchedule()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
