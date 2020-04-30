# Implementation of simple BDD package

from functools import total_ordering

class BddException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BDD Exception: " + str(self.value)


@total_ordering
class Variable:
    name = None
    level = 0  # For ordering
    leafLevel = -1 # Special value

    def __init__(self, level, name):
        self.level = level
        self.name = str(name)

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

    def __str__(self):
        return self.name

class Node:
    id = 0
    variable = None
    low = None
    high = None
    value = None

    def __init__(self, id, variable, high, low, value):
        self.id = id
        self.variable = variable
        self.high = high
        self.low = low
        self.value = value

    def isLeaf(self):
        return self.variable.level == Variable.leafLevel

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
        
    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

    def __str__(self):
        if self.isLeaf():
            return "leaf-%d" % self.value
        else:
            return "%d:%s->%d,%d" % (self.id, str(self.variable), self.high.id, self.low.id)

class Manager:
    # List of variables, ordered by level
    variables = []
    nextNodeId = 0
    leaf0 = None
    leaf1 = None
    # Mapping from (variable, high, low) to node
    nodeTable = {}
    # Operation cache
    # Key = (opName, operand1 ...) to node
    operationCache = {}
    # Log of operations performed, to enable proof checking
    operationLog = []

    def __init__(self):
        self.variables = []
        leafPseudovariable = Variable(Variable.leafLevel, "Leaf")
        self.nextUniqueId = 1
        self.leaf0 = Node(0, leafPseudovariable, None, None, 0)
        self.leaf1 = Node(1, leafPseudovariable, None, None, 1)
        self.nextNodeId = 2
        self.nodeTable = {}
        self.operationCache = {}
        self.operationLog = []

    def addLog(self, operation, key, result):
        self.operationLog.append((operation, key, result))

    def newVariable(self, name):
        level = len(self.variables) + 1
        var = Variable(level, name)
        self.variables.append(var)
        return var
        
    def findOrMake(self, variable, high, low):
        key = (variable.level, high.id, low.id)
        if key in self.nodeTable:
            return self.nodeTable[key]
        else:
            node = Node(self.nextNodeId, variable, high, low, None)
            self.nextNodeId += 1
            self.nodeTable[key] = node
            self.addLog("node", key, node.id)
            return node
  
    def literal(self, variable, phase):
        if phase == 1:
            return self.findOrMake(variable, self.leaf1, self.leaf0)
        else:
            return self.findOrMake(variable, self.leaf0, self.leaf1)

    def constructClause(self, literalList):
        lits = sorted(literalList, key=lambda n: -n.variable.level)
        root = self.reduceList(lits, self.applyOr, self.leaf0)
        key = [n.id for n in literalList]
        self.addLog("clause", key, root.id)
        return root
    
    def deconstructClause(self, clause):
        lits = []
        while not clause.isLeaf():
            positive = clause.high == self.leaf1
            phase = 1 if positive else 0
            lits.append(self.literal(clause.variable, phase))
            clause = clause.low if positive else clause.high
        return lits

    # Build dictionary mapping nodes in DAG rooted by node to values
    # nodeFunction should be a function mapping a node to a value
    def buildInformation(self, node, nodeFunction, sofarDict = {}):
        if node in sofarDict:
            return sofarDict
        sofarDict[node] = nodeFunction(node)
        if node.isLeaf():
            return sofarDict
        else:
            sofarDict = self.buildInformation(node.high, nodeFunction, sofarDict)
            return self.buildInformation(node.low, nodeFunction, sofarDict)
        
    # Find support for function rooted by node
    def getSupport(self, node):
        varDict = self.buildInformation(node, lambda n: n.variable)
        fullList = sorted(varDict.values())
        vlist = []
        for v in fullList:
            if (len(vlist) == 0 or vlist[-1] != v) and v.level != Variable.leafLevel:
                vlist.append(v)
        return vlist

    def getSize(self, node):
        oneDict = self.buildInformation(node, lambda n: 1)
        return len(oneDict)

    def showLiteral(self, lit):
        positive = lit.high == self.leaf1
        prefix = ' ' if positive else '!'
        return prefix + str(lit.variable)

    def showLiterals(self, litList):
        return "(" + ''.join(self.showLiteral(l) for l in litList) + ")"

    def showLiteralList(self, litLL):
        return '[' + ', '.join(self.showLiterals(ls) for ls in litLL) + ']'

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
    def satisfyStrings(self, node):
        satList = self.satisfy(node)
        stringList = []
        for litList in satList:
            slist = ['-'] * len(self.variables)
            for lit in litList:
                positive = lit.high == self.leaf1
                slist[lit.variable.level-1] = '1' if positive else '0'
            stringList.append(''.join(slist))
        return stringList

    def split(self, node, var, phase):
        result = node.branchHigh(var) if phase == 1 else node.branchLow(var)
        key = (var.level, node.id, phase)
        self.addLog("split", key, result.id)
        return result

    def applyAnd(self, nodeA, nodeB):
        # Constant cases
        if nodeA == self.leaf0:
            return self.leaf0
        if nodeB == self.leaf0:
            return self.leaf0
        if nodeA == self.leaf1:
            return nodeB
        if nodeB == self.leaf1:
            return nodeA
        if nodeA == nodeB:
            return nodeA
        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA

        key = ("and", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = self.split(nodeA, splitVar, 1)
        lowA = self.split(nodeA, splitVar, 0)
        highB = self.split(nodeB, splitVar, 1)
        lowB = self.split(nodeB, splitVar, 0)

        newHigh = self.applyAnd(highA, highB)
        newLow = self.applyAnd(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = newNode
        self.addLog("and", key[1:], newNode.id)
        return newNode

    def applyNot(self, node):
        # Constant case
        if node == self.leaf1:
            return self.leaf0
        if node == self.leaf0:
            return self.leaf1
        key = ("not", node.id)
        if key in self.operationCache:
            return self.operationCache[key]
        var = node.variable
        high = node.high
        low = node.low
        newHigh = self.applyNot(high)
        newLow = self.applyNot(low)
        newNode = self.findOrMake(var, newHigh, newLow)
        self.operationCache[key] = newNode
        self.addLog("not", key[1:], newNode.id)
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

        key = ("or", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = self.split(nodeA, splitVar, 1)
        lowA = self.split(nodeA, splitVar, 0)
        highB = self.split(nodeB, splitVar, 1)
        lowB = self.split(nodeB, splitVar, 0)

        newHigh = self.applyOr(highA, highB)
        newLow = self.applyOr(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = newNode
        self.addLog("or", key[1:], newNode.id)
        return newNode

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

        key = ("xor", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = self.split(nodeA, splitVar, 1)
        lowA = self.split(nodeA, splitVar, 0)
        highB = self.split(nodeB, splitVar, 1)
        lowB = self.split(nodeB, splitVar, 0)

        newHigh = self.applyXor(highA, highB)
        newLow = self.applyXor(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = newNode
        self.addLog("xor", key[1:], newNode.id)
        return newNode
    
    def checkImply(self, nodeA, nodeB):
        # Constant cases.  Must be tested in particular order
        if nodeA == self.leaf0:
            return True
        if nodeB == self.leaf1:
            return True
        if nodeA == self.leaf1:
            return False
        if nodeB == self.leaf0:
            return False
        
        key = ("imply", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = self.split(nodeA, splitVar, 1)
        lowA = self.split(nodeA, splitVar, 0)
        highB = self.split(nodeB, splitVar, 1)
        lowB = self.split(nodeB, splitVar, 0)

        checkHigh = self.checkImply(highA, highB)
        checkLow = self.checkImply(lowA, lowB)
        check = checkHigh and checkLow
        self.operationCache[key] = check
        self.addLog("imply", key[1:], 1 if check else 0)
        return check
        
    # Given list of nodes, perform reduction operator (e.g., and, or, xor)
    def reduceList(self, nodeList, operator, emptyValue):
        fun = emptyValue
        for n in nodeList:
            fun = operator(fun, n)
        return fun

    # Use clause to provide canonical list of nodes.  Should all be positive
    def equant(self, node, clause):
        if node.isLeaf():
            return node
        while not clause.isLeaf() and node.variable > clause.variable:
            clause = clause.low
        if clause.isLeaf():
            return node
        key = ("equant", node, clause)
        
        if key in self.operationCache:
            return self.operationCache[key]

        newHigh = self.equant(node.high, clause)
        newLow = self.equant(node.low, clause)
        quant = node.variable == clause.variable
        newNode = self.applyOr(newHigh, newLow) if quant else self.findOrMake(node.variable, newHigh, newLow)

        self.operationCache[key] = newNode
        return newNode
            
            
            
        
