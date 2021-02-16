#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# Last edit: Feb. 16, 2021
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

# Implementation of simple BDD package

from functools import total_ordering

import sys
import resolver
import proof

class BddException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BDD Exception: " + str(self.value)

# Object that is part of quantification sequence.
# Position defined by combination of qindex and qlevel
# Also have quantifier type
# Quantifier levels are odd for input variables and even for extension variables
class Quantified:
    qindex = 0
    qlevel = 0
    isExistential = True

    def __init__(self, qindex, qlevel, existential):
        self.qindex = qindex
        self.qlevel = qlevel
        self.isExistential = existential

    def qless(self, other):
        return self.qlevel < other.level or self.qlevel == other.qlevel and self.qindex < other.qindex

@total_ordering
class Variable(Quantified):
    name = None
    level = 0  # For ordering
    leafLevel = -1 # Special value
    id = None # Serves as identity of resolution variable

    def __init__(self, level, qlevel, name = None, id = None, existential = True):
        self.level = level
        if id is None:
            self.id = level
        elif level == self.leafLevel:
            self.id = 0
        else:
            self.id = id
        if name is None:
            name = "var-%d" % level
        self.name = str(name)
        Quantified.__init__(self, id, qlevel, existential)

    def __eq__(self, other):
        return self.level == other.level

    def __ne__(self, other):
        return self.level != other.level

    def __lt__(self, other):
        # Check for leaves
        if self.level == self.leafLevel:
            return False
        if other.level == self.leafLevel:
            return True
        return self.level < other.level

    def __hash__(self):
        return hash(self.level)

    def __str__(self):
        return self.name


class Node(Quantified):
    id = 0 # Also serves as identity of ER variable
    variable = None

    def __init__(self, id, variable):
        self.id = id
        self.variable = variable
    
    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

    def label(self):
        return "N%d" % self.id

    def isZero(self):
        return False

    def isOne(self):
        return False


class LeafNode(Node):
    value = None # 0 or 1
    inferValue = None # Number of unit clause asserting its value

    def __init__(self, value):
        id = resolver.tautologyId if value == 1 else -resolver.tautologyId        
        Node.__init__(self, id, Variable(Variable.leafLevel, 0, "leaf-%d" % value))
        self.value = value
        self.inferValue = self.id
        Quantified.__init__(self, id, 0, False)

    def isLeaf(self):
        return True

    def label(self):
        return "C%d" % self.value

    def isZero(self):
        return self.value == 0

    def isOne(self):
        return self.value == 1
    
    def __str__(self):
        return "leaf-%d" % self.value


class VariableNode(Node):
    high = None
    low = None
    # Identity of clauses generated from node
    inferTrueUp = None
    inferFalseUp = None
    inferTrueDown = None
    inferFalseDown = None
    
    def __init__(self, id, variable, high, low, prover):
        Node.__init__(self, id, variable)
        self.high = high
        self.low = low
        # Extension variable must be at higher level than node variable
        # and at least as high as children
        qlevel = max(variable.qlevel+1, high.qlevel, low.qlevel)
        Quantified.__init__(self, id, qlevel, True)
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id

        if prover.mode == proof.ProverMode.noProof:
            self.inferTrueUp = None
            self.inferTrueDown = None
            self.inferFalseUp = None
            self.inferFalseDown = None
            return

        hname = "ONE" if hid == resolver.tautologyId else "ZERO" if hid == -resolver.tautologyId else "N%d" % hid
        lname = "ONE" if lid == resolver.tautologyId else "ZERO" if lid == -resolver.tautologyId else "N%d" % lid
        prover.proveExtend(id, qlevel, "Define extension variable for node %s = ITE(%d, %s, %s).  Qlevel=%d" % (self.label(), vid, hname, lname, self.qlevel))
        blockers = []
        self.inferTrueUp = prover.proveAddBlocked([id, -vid, -hid], blockers, "ITE assertions for node %s" % self.label())
        self.inferFalseUp = prover.proveAddBlocked([id, vid, -lid], blockers)
        if self.inferTrueUp != resolver.tautologyId:
            blockers.append(-self.inferTrueUp)
        if self.inferFalseUp != resolver.tautologyId:
            blockers.append(-self.inferFalseUp)
        self.inferTrueDown = prover.proveAddBlocked([-id, -vid, hid], blockers)
        self.inferFalseDown = prover.proveAddBlocked([-id, vid, lid], blockers)

    def isLeaf(self):
        return False

    def branchHigh(self, variable):
        if self.variable < variable:
            raise BddException("Node at level %d cannot branch on variable at level %d" % 
                               (self.variable.level, variable.level))
        if self.isLeaf():
            return self
        elif self.variable == variable:
            return self.high
        else:
            return self

    def branchLow(self, variable):
        if self.variable < variable:
            raise BddException("Node at level %d cannot branch on variable at level %d" % 
                               (self.variable.level, variable.level))
        if self.isLeaf():
            return self
        elif self.variable == variable:
            return self.low
        else:
            return self
        
    def __str__(self):
        return "%d:%s->%s,%s" % (self.id, str(self.variable), self.high.label(), self.low.label())

class Manager:
    prover = None
    writer = None
    # List of variables, ordered by level
    variables = []
    nextNodeId = 0
    # Leaf nodes
    leaf0 = None
    leaf1 = None
    # Mapping from (variable, high, low) to node
    uniqueTable = {}
    # Operation cache
    # Key = (opName, operand1 ...) to (node, justification, clauseList)
    operationCache = {}
    verbLevel = 1
    andResolver = None
    orResolver = None
    implyResolver = None
    restrictResolver = None
    # GC support
    # Callback function from driver that will collect accessible roots for GC
    rootGenerator = None
    # How many quantifications had been performed by last GC?
    lastGC = 0
    # How many variables should be quantified to trigger GC?
    gcThreshold = 4
    # Dictionary mapping variables to their IDs.
    # Used to determine when to trigger GC
    quantifiedVariableSet = None
    # Statistics
    cacheJustifyAdded = 0
    cacheNoJustifyAdded = 0
    applyCount = 0
    auxApplyCount = 0
    nodeCount = 0
    maxLiveCount = 0
    variableCount = 0
    cacheRemoved = 0
    nodesRemoved = 0
    gcCount = 0

    def __init__(self, prover = None, rootGenerator = None, nextNodeId = 0, verbLevel = 1):
        self.verbLevel = verbLevel
        self.prover = DummyProver() if prover is None else prover
        self.writer = self.prover.writer
        self.rootGenerator = rootGenerator
        self.variables = []
        self.leaf0 = LeafNode(0)
        self.leaf1 = LeafNode(1)
        self.nextNodeId = nextNodeId
        self.uniqueTable = {}
        self.operationCache = {}
        self.andResolver = resolver.AndResolver(prover)
        self.orResolver = resolver.OrResolver(prover)
        self.implyResolver = resolver.ImplyResolver(prover)
        self.restrictResolver = resolver.RestrictResolver(prover)
        self.quantifiedVariableSet = set([])
        self.lastGC = 0
        self.cacheJustifyAdded = 0
        self.cacheNoJustifyAdded = 0
        self.applyCount = 0
        self.auxApplyCount = 0
        self.nodeCount = 0
        self.maxLiveCount = 0
        self.variableCount = 0
        self.cacheRemoved = 0
        self.nodesRemoved = 0
        self.gcCount = 0

    def newVariable(self, qlevel, name, id = None, existential = False):
        level = len(self.variables) + 1
        var = Variable(level, qlevel, name, id, existential)
        self.variables.append(var)
        self.variableCount += 1
        self.prover.idToQlevel[id] = qlevel
        return var
        
    def findOrMake(self, variable, high, low):
        key = (variable.level, high.id, low.id)
        if key in self.uniqueTable:
            return self.uniqueTable[key]
        else:
            node = VariableNode(self.nextNodeId, variable, high, low, self.prover)
            self.prover.idToQlevel[node.id] = node.qlevel
            self.nextNodeId += 1
            self.uniqueTable[key] = node
            self.nodeCount += 1
            self.maxLiveCount = max(self.maxLiveCount, len(self.uniqueTable))
            return node
  
    def literal(self, variable, phase):
        if phase == 1:
            return self.findOrMake(variable, self.leaf1, self.leaf0)
        else:
            return self.findOrMake(variable, self.leaf0, self.leaf1)

    # Is a literal positive or negative
    def isPositive(self, literal):
        return literal.high == self.leaf1 and literal.low == self.leaf0

    def buildClause(self, literalList):
        lits = sorted(literalList, key=lambda n: -n.variable.level)
        return self.reduceList(lits, self.applyOr, self.leaf0)

    # Construct BDD representation of clause
    # plus proof that clause entails BDD
    def constructClause(self, clauseId, literalList):
        root = self.buildClause(literalList)
        lits = self.deconstructClause(root)
        # List antecedents in reverse order of resolution steps
        antecedents = []
        for node in lits:
            positive = node.high == self.leaf1
            if positive:
                antecedents.append(node.inferTrueUp)
                if node.low != self.leaf0:
                    antecedents.append(node.inferFalseUp)
            else:
                antecedents.append(node.inferFalseUp)
                if node.high != self.leaf0:
                    antecedents.append(node.inferTrueUp)
        antecedents.append(clauseId)
        validation = self.prover.proveAddResolution([root.id], antecedents, "Validate clause %d entails node N%d" % (clauseId, root.id))
        return root, validation

    # Construct BDD representation of clause
    # plus proof that BDD entails clause
    def constructClauseReverse(self, clauseId, literalList):
        root = self.buildClause(literalList)
        lits = self.deconstructClause(root)
        lits.reverse()
        # List antecedents in reverse order of resolution steps
        antecedents = []
        for node in lits:
            positive = node.high == self.leaf1
            if positive:
                antecedents.append(node.inferFalseDown)
            else:
                antecedents.append(node.inferTrueDown)
        validation = self.prover.proveAdd([root.id], "Assert unit clause for N%d" % root.id)
        antecedents.append(validation)
        self.prover.proveDeleteResolution(clauseId, antecedents, "Node N%d entails clause %d, and so can delete clause" % (root.id, clauseId))
        return root, validation

    # Construct BDD representation of clause
    # plus proofs that BDD equivalent to clause
    def constructClauseEquivalent(self, clauseId, literalList):
        root = self.buildClause(literalList)
        lits = self.deconstructClause(root)
        # List antecedents in reverse order of resolution steps
        upAntecedents = []
        for node in lits:
            positive = node.high == self.leaf1
            if positive:
                upAntecedents.append(node.inferTrueUp)
                if node.low != self.leaf0:
                    upAntecedents.append(node.inferFalseUp)
            else:
                upAntecedents.append(node.inferFalseUp)
                if node.high != self.leaf0:
                    upAntecedents.append(node.inferTrueUp)
        upAntecedents.append(clauseId)
        validation = self.prover.proveAddResolution([root.id], upAntecedents, "Validate clause %d entails node N%d" % (clauseId, root.id))
        lits.reverse()
        # List downAntecedents in reverse order of resolution steps
        downAntecedents = []
        for node in lits:
            positive = node.high == self.leaf1
            if positive:
                downAntecedents.append(node.inferFalseDown)
            else:
                downAntecedents.append(node.inferTrueDown)
        downAntecedents.append(validation)
        self.prover.proveDeleteResolution(clauseId, downAntecedents, "Node N%d entails clause %d, and so can delete clause" % (root.id, clauseId))
        return root, validation

    
    # Construct BDD representation of clause
    # without proof
    def constructClauseNoProof(self, clauseId, literalList):
        root = self.buildClause(literalList)
        validation = None
        return root, validation


    def deconstructClause(self, clause):
        lits = []
        while not clause.isLeaf():
            positive = clause.high == self.leaf1
            lits.append(clause)
            clause = clause.low if positive else clause.high
        return lits

    # Build dictionary mapping nodes in DAG rooted by node to values
    # nodeFunction should be a function mapping a node to a value
    def buildInformation(self, node, nodeFunction, sofarDict):
        if node in sofarDict:
            return sofarDict
        sofarDict[node] = nodeFunction(node)
        if node.isLeaf():
            return sofarDict
        else:
            sofarDict = self.buildInformation(node.high, nodeFunction, sofarDict)
            return self.buildInformation(node.low, nodeFunction, sofarDict)
        
    # Find support for function rooted by node.  Return as clause
    def getSupport(self, node):
        varDict = self.buildInformation(node, lambda n: n.variable, {})
        fullList = sorted(varDict.values())
        vlist = []
        for v in fullList:
            if (len(vlist) == 0 or vlist[-1] != v) and v.level != Variable.leafLevel:
                vlist.append(v)
        lits = [self.literal(v, 1) for v in  vlist]
        return self.buildClause(lits)

    def getSupportIds(self, node):
        varDict = self.buildInformation(node, lambda n: n.variable.id, {})
        fullList = sorted(varDict.values())
        ilist = []
        for id in fullList:
            if (len(ilist) == 0 or ilist[-1] != id) and id > 0:
                ilist.append(id)
        return ilist

    def getSize(self, node):
        oneDict = self.buildInformation(node, lambda n: 1, {})
        return len(oneDict)

    # Get combined size of set of nodes
    def getCombinedSize(self, nodeList):
        oneDict = {}
        for node in oneDict:
            self.buildInformation(node, lambda n:1, oneDict)
        return len(oneDict)

    def showLiteral(self, lit):
        positive = lit.high == self.leaf1
        prefix = ' ' if positive else '!'
        return prefix + str(lit.variable)

    def showLiterals(self, litList):
        return "(" + ''.join(self.showLiteral(l) for l in litList) + ")"

    def showLiteralList(self, litLL):
        return '[' + ', '.join(self.showLiterals(ls) for ls in litLL) + ']'

    # Count number of solutions to function
    # Over variables consisting of support set for function
    def satisfyCount(self, root):
        supportClause = self.getSupport(root)
        # Mapping from (node, support) to count
        countDict = {(self.leaf1, self.leaf0) : 1}
        count = self.countStep(root, supportClause, countDict)
        return count

    # Recursive step of solution counting
    def countStep(self, root, supportClause, countDict):
        if (root, supportClause) in countDict:
            return countDict[(root, supportClause)]
        if root == self.leaf0:
            countDict[(root, supportClause)] = 0
            return 0
        if supportClause == self.leaf0:
            msg = "Ran out of support variables with nonleaf root node %s" % (str(root))
            raise BddException(msg)
        varS = supportClause.variable
        varR = root.variable
        nsupport = supportClause.low
        if varS < varR:
            ncount = self.countStep(root, nsupport, countDict)
            count = 2 * ncount
        elif varS == varR:
            highR = root.high
            lowR =  root.low
            countH = self.countStep(highR, nsupport, countDict)
            countL = self.countStep(lowR, nsupport, countDict)
            count = countH + countL
        else:
            msg = "Node variable not in support set" % (str(root))
            raise BddException(msg)
        countDict[(root, supportClause)] = count
        return count

    # Return lists of literals representing all solutions
    def satisfy(self, node):
        if node.isLeaf():
            return [] if node.value == 0 else [[]]
        highList = self.satisfy(node.high)
        highPrefix = [self.literal(node.variable, 1)]
        highList = [highPrefix + ls for ls in highList]
        lowList = self.satisfy(node.low)
        lowPrefix = [self.literal(node.variable, 0)]
        lowList = [lowPrefix + ls for ls in lowList]        
        return  highList + lowList

    # Generate strings representing all possible solutions
    def satisfyStrings(self, node, limit = None):
        satList = self.satisfy(node)
        stringList = []
        for litList in satList:
            slist = ['-'] * len(self.variables)
            for lit in litList:
                positive = lit.high == self.leaf1
                slist[lit.variable.level-1] = '1' if positive else '0'
            stringList.append(''.join(slist))
            if limit is not None and len(stringList) >= limit:
                break
        return stringList

    # Return node + id of clause justifying that nodeA & NodeB ==> result
    def applyAndJustify(self, nodeA, nodeB):
        self.applyCount += 1
        # Constant cases.
        # No justifications required, since all return one of the arguments
        if nodeA == self.leaf0 or nodeB == self.leaf0:
            return (self.leaf0, resolver.tautologyId)
        if nodeA == self.leaf1:
            return (nodeB, resolver.tautologyId)
        if nodeB == self.leaf1:
            return (nodeA, resolver.tautologyId)
        if nodeA == nodeB:
            return (nodeA, resolver.tautologyId)

        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA
        key = ("andj", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][:2]

        # Mapping from rule names to clause numbers
        ruleIndex = {}
        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            ruleIndex["UHD"] = nodeA.inferTrueDown
            ruleIndex["ULD"] = nodeA.inferFalseDown
        if highB != lowB:
            ruleIndex["VHD"] = nodeB.inferTrueDown
            ruleIndex["VLD"] = nodeB.inferFalseDown

        (newHigh, andHigh) = self.applyAndJustify(highA, highB)
        ruleIndex["ANDH"] = andHigh
            
        (newLow, andLow) = self.applyAndJustify(lowA, lowB)
        ruleIndex["ANDL"] = andLow

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode = self.findOrMake(splitVar, newHigh, newLow)
            ruleIndex["WHU"] = newNode.inferTrueUp
            ruleIndex["WLU"] = newNode.inferFalseUp

        targetClause = resolver.cleanClause([-nodeA.id, -nodeB.id, newNode.id])
        if targetClause == resolver.tautologyId:
            justification, clauseList = resolver.tautologyId, []
        else:
            comment = "Justification that %s & %s ==> %s" % (nodeA.label(), nodeB.label(), newNode.label())
            justification, clauseList = self.andResolver.run(targetClause, ruleIndex, comment)
        self.operationCache[key] = (newNode, justification,clauseList)
        self.cacheJustifyAdded += 1
        return (newNode, justification)

    # Version that runs without generating justification
    def applyAnd(self, nodeA, nodeB):
        self.applyCount += 1
        # Constant cases.
        if nodeA == self.leaf0 or nodeB == self.leaf0:
            return self.leaf0
        if nodeA == self.leaf1:
            return nodeB
        if nodeB == self.leaf1:
            return nodeA
        if nodeA == nodeB:
            return nodeA

        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA
        key = ("andnj", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][0]

        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyAnd(highA, highB)
        newLow  = self.applyAnd(lowA, lowB)

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode = self.findOrMake(splitVar, newHigh, newLow)

        self.operationCache[key] = (newNode, resolver.tautologyId, [])
        return newNode

    def applyNot(self, node):
        # Constant case
        if node == self.leaf1:
            return self.leaf0
        if node == self.leaf0:
            return self.leaf1
        key = ("notnj", node.id)
        if key in self.operationCache:
            return self.operationCache[key][0]
        var = node.variable
        high = node.high
        low = node.low
        newHigh = self.applyNot(high)
        newLow = self.applyNot(low)
        if newHigh == newLow:
            newNode = newNode
        else:
            newNode = self.findOrMake(var, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
        return newNode

    def applyOr(self, nodeA, nodeB):
        # Constant cases
        if nodeA == self.leaf1:
            return self.leaf1
        if nodeB == self.leaf1:
            return self.leaf1
        if nodeA == self.leaf0:
            return nodeB
        if nodeB == self.leaf0:
            return nodeA
        if nodeA == nodeB:
            return nodeA
        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA

        key = ("ornj", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][0]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyOr(highA, highB)
        newLow = self.applyOr(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
        return newNode

    # Return node + id of clause justifying that result ==> nodeA | NodeB
    def applyOrJustify(self, nodeA, nodeB):
        self.applyCount += 1
        # Constant cases.
        # No justifications required, since all return one of the arguments
        if nodeA == self.leaf1 or nodeB == self.leaf1:
            return (self.leaf1, resolver.tautologyId)
        if nodeA == self.leaf0:
            return (nodeB, resolver.tautologyId)
        if nodeB == self.leaf0:
            return (nodeA, resolver.tautologyId)
        if nodeA == nodeB:
            return (nodeA, resolver.tautologyId)

        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA
        key = ("orj", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][:2]

        # Mapping from rule names to clause numbers
        ruleIndex = {}
        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            ruleIndex["UHU"] = nodeA.inferTrueUp
            ruleIndex["ULU"] = nodeA.inferFalseUp
        if highB != lowB:
            ruleIndex["VHU"] = nodeB.inferTrueUp
            ruleIndex["VLU"] = nodeB.inferFalseUp

        (newHigh, orHigh) = self.applyOrJustify(highA, highB)
        ruleIndex["ORH"] = orHigh
            
        (newLow, orLow) = self.applyOrJustify(lowA, lowB)
        ruleIndex["ORL"] = orLow

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode = self.findOrMake(splitVar, newHigh, newLow)
            ruleIndex["WHD"] = newNode.inferTrueDown
            ruleIndex["WLD"] = newNode.inferFalseDown

        targetClause = resolver.cleanClause([-newNode.id, nodeA.id, nodeB.id])
        if targetClause == resolver.tautologyId:
            justification, clauseList = resolver.tautologyId, []
        else:
            comment = "Justification that %s ==> %s | %s" % (newNode.label(), nodeA.label(), nodeB.label())
            justification, clauseList = self.orResolver.run(targetClause, ruleIndex, comment)
        self.operationCache[key] = (newNode, justification,clauseList)
        self.cacheJustifyAdded += 1
        return (newNode, justification)

    def applyXor(self, nodeA, nodeB):
        # Constant cases
        if nodeA == self.leaf1:
            return self.applyNot(nodeB)
        if nodeB == self.leaf1:
            return self.applyNot(nodeA)
        if nodeA == self.leaf0:
            return nodeB
        if nodeB == self.leaf0:
            return nodeA
        if nodeA == nodeB:
            return self.leaf0
        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA

        key = ("xornj", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][0]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyXor(highA, highB)
        newLow = self.applyXor(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
        return newNode
    
    def justifyImply(self, nodeA, nodeB):
        self.auxApplyCount += 1

        # Special cases
        if nodeA == nodeB:
            return (True, resolver.tautologyId)
        if nodeA == self.leaf0:
            return (True, resolver.tautologyId)
        if nodeB == self.leaf1:
            return (True, resolver.tautologyId)
        # It would be an error if implication fails
        if nodeA == self.leaf1:
            return (False, resolver.tautologyId)
        if nodeB == self.leaf0:
            return (False, resolver.tautologyId)

        key = ("imply", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key][:2]

        ruleIndex = { }
        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            ruleIndex["UHD"] = nodeA.inferTrueDown
            ruleIndex["ULD"] = nodeA.inferFalseDown
        if highB != lowB:
            ruleIndex["VHU"] = nodeB.inferTrueUp
            ruleIndex["VLU"] = nodeB.inferFalseUp

        (checkHigh, implyHigh) = self.justifyImply(highA, highB)
        if implyHigh != resolver.tautologyId:
            ruleIndex["IMH"] = implyHigh
        (checkLow, implyLow) = self.justifyImply(lowA, lowB)
        if implyLow != resolver.tautologyId:
            ruleIndex["IML"] = implyLow

        check = checkHigh and checkLow
        if check:
            targetClause = resolver.cleanClause([-nodeA.id, nodeB.id])
            comment = "Justification that %s ==> %s" % (nodeA.label(), nodeB.label())
            justification, clauseList = self.implyResolver.run(targetClause, ruleIndex, comment)
        else:
            justification, clauseList = resolver.tautologyId, []

        self.operationCache[key] = (check, justification, clauseList)
        if justification != resolver.tautologyId:
            self.cacheJustifyAdded += 1
        else:
            self.cacheNoJustifyAdded += 1
        return (check, justification)

    def checkImply(self, nodeA, nodeB):
        check, justification = justifyImply(nodeA, nodeB)
        return check
        
    # Given list of nodes, perform reduction operator (and, or, xor)
    def reduceList(self, nodeList, operator, emptyValue):
        fun = emptyValue
        for n in nodeList:
            fun = operator(fun, n)
        return fun

    # Indicate that variable has been quantified
    def markQuantified(self, variable):
        self.quantifiedVariableSet.add(variable)        

    # Use clause to provide canonical list of nodes.  Should all be positive
    def equant(self, node, clause, topLevel = True):
        if topLevel:
            nextc = clause
            while not nextc.isLeaf():
                self.markQuantified(nextc.variable)
                nextc = nextc.low
        if node.isLeaf():
            return node
        while not clause.isLeaf() and node.variable > clause.variable:
            clause = clause.low
        if clause.isLeaf():
            return node
        key = ("equant", node.id, clause.id)
        
        if key in self.operationCache:
            return self.operationCache[key][0]

        newHigh = self.equant(node.high, clause, topLevel = False)
        newLow = self.equant(node.low, clause, topLevel = False)
        quant = node.variable == clause.variable
        if newHigh == newLow:
            newNode = newHigh
        elif quant:
            newNode = self.applyOr(newHigh, newLow) 
        else:
            newNode = self.findOrMake(node.variable, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
        return newNode

    # Use clause to provide canonical list of nodes.  Should all be positive
    def uquant(self, node, clause, topLevel = True):
        if topLevel:
            nextc = clause
            while not nextc.isLeaf():
                self.markQuantified(nextc.variable)
                nextc = nextc.low
        if node.isLeaf():
            return node
        while not clause.isLeaf() and node.variable > clause.variable:
            clause = clause.low
        if clause.isLeaf():
            return node
        key = ("uquant", node.id, clause.id)
        
        if key in self.operationCache:
            return self.operationCache[key][0]

        newHigh = self.uquant(node.high, clause, topLevel = False)
        newLow = self.uquant(node.low, clause, topLevel = False)
        quant = node.variable == clause.variable
        
        if newHigh == newLow:
            newNode = newHigh
        elif quant:
            newNode = self.applyAnd(newHigh, newLow) 
        else:
            newNode = self.findOrMake(node.variable, newHigh, newLow)

        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
        return newNode

    # Compute restriction on node.
    # Variable and phase indicated by literal node
    # Generate justification that (literal &) node  --> newNode
    def applyRestrictDown(self, u, literal):
        if u.isLeaf():
            return (u, resolver.tautologyId)
        rvar = literal.variable
        nvar = u.variable
        phase1 = literal.high == self.leaf1
        if rvar < nvar:
            return (u, resolver.tautologyId)
        elif rvar == nvar:
            result = u.high if phase1 else u.low
            just = u.inferTrueDown if phase1 else u.inferFalseDown
            return (result, just)
        
        key = ("resdown", u.id, literal.id)
        if key in self.operationCache:
            return self.operationCache[key][:2]

        ruleIndex = { }
        uhigh = u.high
        ruleIndex["UHX"] = u.inferTrueDown
        ulow = u.low
        ruleIndex["ULX"] = u.inferFalseDown

        (vhigh, resHigh) = self.applyRestrictDown(uhigh, literal)
        ruleIndex["RESH"] = resHigh
        (vlow, resLow)   = self.applyRestrictDown(ulow, literal)
        ruleIndex["RESL"] = resLow
        
        if vhigh == vlow:
            v = vhigh
        else:
            v = self.findOrMake(nvar, vhigh, vlow)
            ruleIndex["VHX"] = v.inferTrueUp
            ruleIndex["VLX"] = v.inferFalseUp
        
        
        targetClause = resolver.cleanClause([-rvar.id if phase1 else rvar.id, -u.id, v.id])
        if targetClause == resolver.tautologyId:
            justification, clauseList = resolver.tautologyId, []
        else:
            try:
                comment = "Justification that %s%s & %s ==> %s" % ("" if phase1 else "!", rvar.name, u.label(), v.label())
                justification, clauseList = self.restrictResolver.run(targetClause, ruleIndex, comment)
            except resolver.ResolveException:
                targetClause = resolver.cleanClause([-u.id, v.id])
                comment = "Degenerate restriction.  Justification that %s ==> %s" % (u.label(), v.label())
                justification, clauseList = self.restrictResolver.run(targetClause, ruleIndex, comment)
        self.operationCache[key] = (v, justification,clauseList)
        self.cacheJustifyAdded += 1
        return (v, justification)

    # Compute restriction on node.
    # Variable and phase indicated by literal node
    # Generate justification that literal & newNode --> node
    def applyRestrictUp(self, u, literal):
        if u.isLeaf():
            return (u, resolver.tautologyId)
        rvar = literal.variable
        nvar = u.variable
        phase1 = literal.high == self.leaf1
        if rvar < nvar:
            return (u, resolver.tautologyId)
        elif rvar == nvar:
            result = u.high if phase1 else u.low
            just = u.inferTrueUp if phase1 else u.inferFalseUp
            return (result, just)
        
        key = ("resup", u.id, literal.id)
        if key in self.operationCache:
            return self.operationCache[key][:2]

        ruleIndex = { }
        uhigh = u.high
        ruleIndex["UHX"] = u.inferTrueUp
        ulow = u.low
        ruleIndex["ULX"] = u.inferFalseUp

        (vhigh, resHigh) = self.applyRestrictUp(uhigh, literal)
        ruleIndex["RESH"] = resHigh
        (vlow, resLow)   = self.applyRestrictUp(ulow, literal)
        ruleIndex["RESL"] = resLow
        
        if vhigh == vlow:
            v = vhigh
        else:
            v = self.findOrMake(nvar, vhigh, vlow)
            ruleIndex["VHX"] = v.inferTrueDown
            ruleIndex["VLX"] = v.inferFalseDown
        
        targetClause = resolver.cleanClause([-rvar.id if phase1 else rvar.id, u.id, -v.id])
        if targetClause == resolver.tautologyId:
            justification, clauseList = resolver.tautologyId, []
        else:
            try:
                comment = "Justification that %s%s & %s ==> %s" % ("" if phase1 else "!", rvar.name, v.label(), u.label())
                justification, clauseList = self.restrictResolver.run(targetClause, ruleIndex, comment)
            except resolver.ResolveException:
                targetClause = resolver.cleanClause([u.id, -v.id])
                comment = "Degenerate restriction.  Justification that %s ==> %s" % (v.label(), u.label())
                justification, clauseList = self.restrictResolver.run(targetClause, ruleIndex, comment)
                # Record this for use by the prover
                self.prover.restrictDegeneracies.add(justification)
        self.operationCache[key] = (v, justification,clauseList)
        self.cacheJustifyAdded += 1
        return (v, justification)
    
    # Should a GC be triggered?
    def checkGC(self, generateClauses = True):
        newQuants = len(self.quantifiedVariableSet) - self.lastGC
        if newQuants > self.gcThreshold:
            return self.collectGarbage(generateClauses)
        return []


    # Create set nodes that should not be collected
    # Maintain frontier of marked nonleaf nodes
    def doMarking(self, frontier):
        markedSet = set([])
        while len(frontier) > 0:
            node = frontier[0]
            frontier = frontier[1:]
            if node in markedSet:
                continue
            markedSet.add(node)
            if not node.high.isLeaf():
                frontier.append(node.high)
            if not node.low.isLeaf():
                frontier.append(node.low)
        return markedSet

    def cleanCache(self, markedSet, generateClauses):
        clauseList = []
        markedIds = set([node.id for node in markedSet])
        klist = list(self.operationCache.keys())
        for k in klist:
            kill = self.operationCache[k][0] not in markedSet
            # Skip over operation name
            for id in k[1:]:
                kill = kill or id not in markedIds
            if kill:
                if generateClauses:
                    clist = self.operationCache[k][2]
                    clauseList += clist
                self.cacheRemoved += 1
                del self.operationCache[k]
        return clauseList
        
    def cleanNodes(self, markedSet, generateClauses):
        clauseList = []
        klist = list(self.uniqueTable.keys())
        for k in klist:
            node = self.uniqueTable[k]
            # If node is marked, then its children will be, too
            if node not in markedSet:
                if generateClauses:
                    clist = [node.inferTrueUp, node.inferFalseUp, node.inferTrueDown, node.inferFalseDown]
                    clist = [c for c in clist if abs(c) != resolver.tautologyId]
                    clauseList += clist
                self.nodesRemoved += 1
                del self.uniqueTable[k]
        return clauseList


    # Start garbage collection.
    # Provided with partial list of accessible roots
    def collectGarbage(self, generateClauses):
        frontier = []
        if self.rootGenerator is not None:
            frontier += self.rootGenerator()
        frontier = [r for r in frontier if not r.isLeaf()]
        # Marking phase
        markedSet = self.doMarking(frontier)
        clauseList = self.cleanCache(markedSet, generateClauses)
        clauseList += self.cleanNodes(markedSet, generateClauses)
        # Turn off trigger for garbage collection
        self.lastGC = len(self.quantifiedVariableSet)
        self.gcCount += 1
        return clauseList

    # Summarize activity
    def summarize(self):
        if self.verbLevel >= 1:
            self.writer.write("Input variables: %d\n" % self.variableCount)
            self.writer.write("Variables quantified out: %d\n" % len(self.quantifiedVariableSet))
            self.writer.write("Total nodes: %d\n" % self.nodeCount)
            self.writer.write("Total nodes removed by gc: %d\n" % self.nodesRemoved)
            self.writer.write("Maximum live nodes: %d\n" % self.maxLiveCount)
            self.writer.write("Total apply operations: %d\n" % self.applyCount)
            self.writer.write("Total auxilliary apply operations: %d\n" % self.auxApplyCount)            
            self.writer.write("Total cached results not requiring proofs: %d\n" % self.cacheNoJustifyAdded)
            self.writer.write("Total cached results requiring proofs: %d\n" % self.cacheJustifyAdded)
            self.writer.write("Total cache entries removed: %d\n" % self.cacheRemoved)
            self.writer.write("Total GCs performed: %d\n" % self.gcCount)
        if self.verbLevel >= 1:
            self.writer.write("Results from And Operations:\n")
            self.andResolver.summarize()
            self.writer.write("Results from Or Operations:\n")
            self.orResolver.summarize()
            self.writer.write("Results from Implication Testing Operations:\n")
            self.implyResolver.summarize()
            self.writer.write("Results from Restriction Operations:\n")
            self.restrictResolver.summarize()
        if self.verbLevel >= 1:
            self.writer.write("Results from proof generation\n")
            self.prover.summarize()
        
