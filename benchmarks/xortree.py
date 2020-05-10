#!/usr/bin/python

import sys
import  getopt
import random

# Generate CNF, order, and schedule files to compare two trees of xor's over a common set of inputs

def usage(name):
    print("Usage: %s [-h] [-r ROOT] [-n N] [-m M1M2]" % name)
    print("  -h       Print this message")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule")
    print("  -n N     Specify number of tree inputs")
    print("  -m M1M2  Specify modes for the two trees: B=balanced, L=left linear, R=right linear, X=random")

# Creating CNF
class CnfWriter:
    variableCount = 0
    clauseCount = 0
    outputList = []

    def __init__(self):
        self.variableCount = 0
        self.clauseCount = 0
        self.ouputList = []

    def newVariable(self):
        self.variableCount += 1
        return self.variableCount

    def comment(self, line):
        outputList.append("c " + line)

    def clause(self, literals):
        ilist = literals + [0]
        outputList.append(" ".join([str(i) for i in ilist]))
        self.ClauseCount += 1

    def write(self, fname = None):
        if fname is None:
            outfile = sys.stdout
        else:
            try:
                outfile = open(fname, 'w')
            except Exception as ex:
                print("Couldn't open output file '%s'.  Aborting" % fname)
                sys.exit(1)
        outfile.write("p cnf %d %d" % (self.variableCount, self.clauseCount))
        for line in self.outputList:
            outfile.write(line + '\n')
        outfile.close()
    
class ScheduleWriter:
    outfile = None
    
    def __init__(self, fname):
        try:
            self.outfile = open(fname, 'w')
        except:
            print("Couldn't open schedule file '%s'. Aborting" % fname)
            sys.exit(1)
    
    def getClauses(self, clist):
        self.outfile.write("c %s\n" % " ".join([str(c) for c in clist]))

    def doAnd(self, count):
        self.outfile.write("a %d\n" % count)

    def doQuantify(self, vlist):
        self.outfile.write("q %s\n", " ".join([str(c) for c in vlist]))

    def finish(self):
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None

    def __del__(self):
        self.finish()

# General tree node
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
        writer.coment("Xor(%d, %d) --> %d" % (A, B, C))
        self.clauseIds.append(writer.clause([-A, -B, -C]))
        self.clauseIds.append(writer.clause([-A,  B,  C]))
        self.clauseIds.append(writer.clause([ A, -B,  C]))
        self.clauseIds.append(writer.clause([ A,  B, -C]))

    def emitSchedule(self, writer):
        self.left.emitSchedule(writer)
        self.right.emitSchedule(writer)
        self.writer.getClauses(self.clauseIds)
        self.writer.doAnd(len(self.clauseIds))
        quants = []
        if not self.left.isLeaf:
            quants.append(self.left.output)
        if not self.right.isLeaf:
            quants.append(self.right.output)
        if len(quants) > 0:
            self.writer.doQuantify(quants)
                              
    # Gather all non-input variables into dictionary, indexed by height
    def getVariables(self, heightDict):
        if self.height not in heightDict:
            self.heightDict[self.height] = [self.output]
        else:
            self.heightDict[self.height].append(self.output)
        self.getVariables(self.left)
        self.getVariables(self.right)
    
    def show(self, maxHeight = None, spacing = 4):
        if maxHeight is None:
            maxHeight = self.height
        indent = " " * spacing * (maxHeight-self.height)
        self.left.show(maxHeight, spacing)
        print("%sT%d (%d, %d)" % (indent, self.output, self.left.output, self.right.output))
        self.right.show(maxHeight, spacing)

class TreeBuilder:
    (modeLeft, modeRight, modeBalanced, modeRandom) = range(4)
    # Number of inputs
    inputCount = 1
    treeCount = 0
    root = None

    def __init__(self, count, mode):
        self.inputCount = count
        subtrees = [Node(v) for v in range(1, count+1)]
        self.treeCount = count
        if mode == self.modeLeft:
            self.root = self.buildSplit(subtrees, self.chooseLeast)
        elif mode == self.modeRight:
            self.root = self.buildSplit(subtrees, self.chooseMost)
        elif mode == self.modeBalanced:
            self.root = self.buildSplit(subtrees, self.chooseHalf)
        else:
            self.root = self.buildRandom(subtrees)

    def buildSplit(self, subtrees, leftChooser):
        if len(subtrees) == 1:
            return subtrees[0]
        leftCount = leftChooser(len(subtrees))
        leftTrees = subtrees[:leftCount]
        rightTrees = subtrees[leftCount:]
        leftRoot = self.buildSplit(leftTrees, leftChooser)
        rightRoot = self.buildSplit(rightTrees, leftChooser)
        self.treeCount += 1
        root = TreeNode(self.treeCount, leftRoot, rightRoot)
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
            subtrees = subtrees[:id2] + subtrees[id2+2:]
            self.treeCount += 1
            tn = TreeNode(self.treeCount, t1, t2)
            subtrees.append(tn)
        return subtrees[0]

        
