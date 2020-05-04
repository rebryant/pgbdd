# Implementation of simple BDD package

from functools import total_ordering

class BddException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BDD Exception: " + str(self.value)

# Place holder to allow program to run without proving anything
class DummyProver:

    clauseCount = 0

    def __init__(self):
        self.clauseCount = 0

    def comment(self, comment):
        if comment is not None:
            print("c " + comment)

    def createClause(self, result, antecedent, comment = None):
        self.comment(comment)
        rstring = " ".join([str(v) for v in result])
        astring = " ".join([str(v) for v in antecedent])
        self.clauseCount += 1
        if len(antecedent) == 0:
            print("%d: Assert %s" % (self.clauseCount, rstring))
        else:
            print("%d: Justify %s from %s" % (self.clauseCount, rstring, astring))
        return self.clauseCount

@total_ordering
class Variable:
    name = None
    level = 0  # For ordering
    leafLevel = -1 # Special value
    id = None # Serves as identity of resolution variable

    def __init__(self, level, name = None):
        self.level = level
        self.id = 0 if level == self.leafLevel else level 
        if name is None:
            name = "var-%d" % level
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
    id = 0 # Also serves as identity of ER variable
    variable = None

    def __init__(self, id, variable):
        self.id = id
        self.variable = variable
    
    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id


class LeafNode(Node):
    value = None # 0 or 1
    inferValue = None # Number of unit clause asserting its value

    def __init__(self, id, value, prover):
        Node.__init__(self, id, Variable(Variable.leafLevel, "Leaf"))
        self.value = value
        antecedent = []
        unit = -self.id if self.value == 0 else self.id
        self.inferValue = self.prover.createClause([unit], [], "Unit clause for constant %d" % value)

    def isLeaf(self):
        return True

    def __str__(self):
        return "leaf-%d" % self.value


class VariableNode(Node):
    high = None
    low = None
    # Identity of clauses generated from node
    inferTrueUp = None
    inferTrueDown = None
    inferFalseUp = None
    inferTrueDown = None
    
    def __init__(self, id, variable, high, low, prover):
        Node.__init__(self, id, variable)
        self.high = high
        self.low = low
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        self.inferTrueUp = self.prover.createClause([-vid, -hid, id], [], "ITE assertions for node %d" % id)
        self.inferTrueDown = self.prover.createClause([-vid, -id, hid], [])
        self.inferFalseUp = self.prover.createClause([vid, -lid, id], [])
        self.inferFalseDown = self.prover.createClause([vid, -id, lid], [])

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
        return "%d:%s->%d,%d" % (self.id, str(self.variable), self.high.id, self.low.id)

class Manager:
    prover = None
    # List of variables, ordered by level
    variables = []
    nextNodeId = 0
    # Leaf nodes
    leaf0 = None
    leaf1 = None
    # Mapping from (variable, high, low) to node
    nodeTable = {}
    # Operation cache
    # Key = (opName, operand1 ...) to (node, justification)
    operationCache = {}

    def __init__(self, prover = None, nextNodeId = 0):
        self.prover = DummyProver() if prover is None else prover
        self.variables = []
        self.leaf0 = LeafNode(nextNodeId, 0, prover)
        self.leaf1 = LeafNode(nextNodeId+1, 1, prover)
        self.nextNodeId = nextNodeId + 2
        self.nodeTable = {}
        self.operationCache = {}

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
            node = VariableNode(self.nextNodeId, variable, high, low)
            self.nextNodeId += 1
            self.nodeTable[key] = node
            return node
  
    def literal(self, variable, phase):
        if phase == 1:
            return self.findOrMake(variable, self.leaf1, self.leaf0)
        else:
            return self.findOrMake(variable, self.leaf0, self.leaf1)

    def constructClause(self, clauseId, literalList):
        lits = sorted(literalList, key=lambda n: -n.variable.level)
        root = self.reduceList(lits, self.applyOr, self.leaf0)
        litNodes = [node.id for node in self.deconstructClause(root)]
        antecedents = [clauseId, self.leaf0.inferValue, self.leaf1.inferValue]
        antecedents += [nid.inferTrueUp for nid in litNodes]
        antecedents += [nid.inferFalseUp for nid in litNodes]
        validation = self.prover.createClause([root.id], antecedents)
        return root, validation
    
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

    # Return node + id of clause justifying that nodeA & NodeB ==> result
    # Justification is None if it would be tautology
    def applyAndJustify(self, nodeA, nodeB):
        # Constant cases
        if nodeA == self.leaf0 or nodeB == self.leaf0:
            return (self.leaf0, None)
        if nodeA == self.leaf1:
            return (nodeB, None)
        if nodeB == self.leaf1:
            return (nodeA, None)
        if nodeA == nodeB:
            return (nodeA, None)
        if nodeA.id > nodeB.id:
            nodeA, nodeB = nodeB, nodeA

        antecedents = []

        key = ("and", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        if highA != lowA:
            antecedents += [highA.inferTrueDown, lowA.inferFalseDown]
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)
        if highB != lowB:
            antecedents += [highB.inferTrueDown, lowB.inferFalseDown]


        (newHigh, justHigh) = self.applyAndJustify(highA, highB)
        if justHigh is not None:
            antecedents += [justHigh]
        (newLow, justLow) = self.applyAndJustify(lowA, lowB)
        if justLow is not None:
            antecedents += [justLow]

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode self.findOrMake(splitVar, newHigh, newLow)
            antecedents += [newNode.inferTrueUp, newNode.inferFalseUp]
        result = [-nodeA.id, -nodeB.id, newNode.id]
        justification = self.prover.createClause(result, antecedents,
                                                 "Justification that %d & %d ==> %d" % (nodeA.id, nodeB.id, newNode.id))
        self.operationCache[key] = (newNode, justification)
        return (newNode, justification)

    # Version that runs without generating justification
    def applyAnd(self, nodeA, nodeB):
        newNode, justification = self.applyAndJustify(nodeA, nodeB)
        return newNode

    def applyNot(self, node):
        # Constant case
        if node == self.leaf1:
            return self.leaf0
        if node == self.leaf0:
            return self.leaf1
        key = ("not", node.id)
        if key in self.operationCache:
            return self.operationCache[key][0]
        var = node.variable
        high = node.high
        low = node.low
        newHigh = self.applyNot(high)
        newLow = self.applyNot(low)
        newNode = self.findOrMake(var, newHigh, newLow)
        self.operationCache[key] = (newNode, None)
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
            return self.operationCache[key][0]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyOr(highA, highB)
        newLow = self.applyOr(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = (newNode, None)
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
            return self.operationCache[key][0]

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        newHigh = self.applyXor(highA, highB)
        newLow = self.applyXor(lowA, lowB)
        newNode = newHigh if newHigh == newLow else self.findOrMake(splitVar, newHigh, newLow)
        self.operationCache[key] = (newNode, None)
        return newNode
    
    def justifyImply(self, nodeA, nodeB):
        # Constant cases.  Must be tested in particular order
        # What we're trying to justify
        result = [-self.nodeA.id, self.nodeB.id]
        comment = "Justification that %d ==> %d" % (nodeA.id, nodeB.id)
        if nodeA == self.leaf0:
            justification = self.prover.createClause(result, [self.leaf0.inferValue], comment)
            return (True, justification)
        if nodeB == self.leaf1:
            justification = self.prover.createClause(result, [self.leaf1.inferValue], comment)
            return (True, justification)
        if nodeA == self.leaf1:
            return (False, None)
        if nodeB == self.leaf0:
            return (False, None)
        
        key = ("imply", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        antecedents = []

        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        if highA != lowA:
            antecedents += [highA.inferTrueDown, lowA.inferFalseDown]
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)
        if highB != lowB:
            antecedents += [highB.inferTrueDown, lowB.inferFalseDown]

        (checkHigh, justHigh) = self.applyAndJustify(highA, highB)
        if justHigh is not None:
            antecedents += [justHigh]
        (checkLow, justLow) = self.applyAndJustify(lowA, lowB)
        if justLow is not None:
            antecedents += [justLow]

        check = checkHigh and checkLow
        justification = self.prover.createClause(result, antecedents, comment)
        self.operationCache[key] = (check, justification)
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
            return self.operationCache[key][0]

        newHigh = self.equant(node.high, clause)
        newLow = self.equant(node.low, clause)
        quant = node.variable == clause.variable
        newNode = self.applyOr(newHigh, newLow) if quant else self.findOrMake(node.variable, newHigh, newLow)
        self.operationCache[key] = (newNode, None)
        return newNode
            
            
            
        
