# Implementation of simple BDD package

from functools import total_ordering

import resolver

class BddException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BDD Exception: " + str(self.value)

# Place holder to allow program to run without proving anything
class DummyProver:

    clauseCount = 0

    def __init__(self, fname = None):
        self.clauseCount = 0

    def comment(self, comment):
        pass

    def createClause(self, result, antecedent, comment = None):
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            return result
        self.clauseCount += 1
        return self.clauseCount

    def emitProof(self, proof, ruleIndex, comment = None):
        self.clauseCount += 1
        return self.clauseCount

    def fileOutput(self):
        return False


@total_ordering
class Variable:
    name = None
    level = 0  # For ordering
    leafLevel = -1 # Special value
    id = None # Serves as identity of resolution variable

    def __init__(self, level, name = None, id = None):
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
        Node.__init__(self, id, Variable(Variable.leafLevel, "Leaf"))
        self.value = value
        self.inferValue = self.id

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
    inferTrueDown = None
    
    def __init__(self, id, variable, high, low, prover):
        Node.__init__(self, id, variable)
        self.high = high
        self.low = low
        vid = self.variable.id
        hid = self.high.id
        lid = self.low.id
        self.inferTrueUp = prover.createClause([-vid, -hid, id], [], "ITE assertions for node %s" % self.label())
        self.inferFalseUp = prover.createClause([vid, -lid, id], [])
        self.inferTrueDown = prover.createClause([-vid, -id, hid], [])
        self.inferFalseDown = prover.createClause([vid, -id, lid], [])

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
    verbLevel = 1
    andResolver = None
    implyResolver = None
    # Statistics
    cacheAdded = 0
    applyCount = 0
    nodeCount = 0
    variableCount = 0

    def __init__(self, prover = None, nextNodeId = 0, verbLevel = 1):

        self.verbLevel = verbLevel
        self.prover = DummyProver() if prover is None else prover
        self.variables = []
        self.leaf0 = LeafNode(0)
        self.leaf1 = LeafNode(1)
        self.nextNodeId = nextNodeId
        self.nodeTable = {}
        self.operationCache = {}
        self.andResolver = resolver.AndResolver(verbLevel = self.verbLevel)
        self.implyResolver = resolver.ImplyResolver(verbLevel = self.verbLevel)
        self.cacheAdded = 0
        self.applyCount = 0
        self.nodeCount = 0
        self.variableCount = 0

    def newVariable(self, name, id = None):
        level = len(self.variables) + 1
        var = Variable(level, name, id)
        self.variables.append(var)
        self.variableCount += 1
        return var
        
    def findOrMake(self, variable, high, low):
        key = (variable.level, high.id, low.id)
        if key in self.nodeTable:
            return self.nodeTable[key]
        else:
            node = VariableNode(self.nextNodeId, variable, high, low, self.prover)
            self.nextNodeId += 1
            self.nodeTable[key] = node
            self.nodeCount += 1
            return node
  
    def literal(self, variable, phase):
        if phase == 1:
            return self.findOrMake(variable, self.leaf1, self.leaf0)
        else:
            return self.findOrMake(variable, self.leaf0, self.leaf1)

    def buildClause(self, literalList):
        lits = sorted(literalList, key=lambda n: -n.variable.level)
        return self.reduceList(lits, self.applyOr, self.leaf0)

    def constructClause(self, clauseId, literalList):
        root = self.buildClause(literalList)
        litNodes = self.deconstructClause(root)
        antecedents = [clauseId]
        antecedents += [node.inferTrueUp for node in litNodes 
                        if node.inferTrueUp != resolver.tautologyId]
        antecedents += [node.inferFalseUp for node in litNodes
                        if node.inferFalseUp != resolver.tautologyId]
        validation = self.prover.createClause([root.id], antecedents, "Validate BDD representation of clause %d" % clauseId)
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
        key = ("and", nodeA.id, nodeB.id)
        if key in self.operationCache:
            return self.operationCache[key]

        # Mapping from rule names to clause numbers
        ruleIndex = {}
        # Mapping from variable names to variable numbers
        splitVar = min(nodeA.variable, nodeB.variable)
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            ruleIndex["UTD"] = nodeA.inferTrueDown
            ruleIndex["UFD"] = nodeA.inferFalseDown
        if highB != lowB:
            ruleIndex["VTD"] = nodeB.inferTrueDown
            ruleIndex["VFD"] = nodeB.inferFalseDown

        (newHigh, implyHigh) = self.applyAndJustify(highA, highB)
        if implyHigh != resolver.tautologyId:
            ruleIndex["IMT"] = implyHigh
            
        (newLow, implyLow) = self.applyAndJustify(lowA, lowB)
        if implyLow != resolver.tautologyId:
            ruleIndex["IMF"] = implyLow

        if newHigh == newLow:
            newNode = newHigh
        else:
            newNode = self.findOrMake(splitVar, newHigh, newLow)
            ruleIndex["WTU"] = newNode.inferTrueUp
            ruleIndex["WFU"] = newNode.inferFalseUp

        variableIndex = { "x":splitVar.id,
                          "u":nodeA.id, "u1":highA.id, "u0":lowA.id,
                          "v":nodeB.id, "v1":highB.id, "v0":lowB.id,
                          "w":newNode.id, "w1":newHigh.id, "w0":newLow.id }

        proof = self.andResolver.run(variableIndex, ruleNames = sorted(ruleIndex.keys()))
        if proof == resolver.tautologyId:
            justification = resolver.tautologyId
        else:
            comment = "Justification that %s & %s ==> %s" % (nodeA.label(), nodeB.label(), newNode.label())
            justification = self.prover.emitProof(proof, ruleIndex, comment)
        self.operationCache[key] = (newNode, justification)
        self.cacheAdded += 1
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
        self.cacheAdded += 1
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
        self.cacheAdded += 1
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
        self.cacheAdded += 1
        return newNode
    
    def justifyImply(self, nodeA, nodeB):
        self.applyCount += 1

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
            return self.operationCache[key]

        ruleIndex = { }
        splitVar = min(nodeA.variable, nodeB.variable)  
        highA = nodeA.branchHigh(splitVar)
        lowA =  nodeA.branchLow(splitVar)
        highB = nodeB.branchHigh(splitVar) 
        lowB =  nodeB.branchLow(splitVar)

        if highA != lowA:
            ruleIndex["UTD"] = nodeA.inferTrueDown
            ruleIndex["UFD"] = nodeA.inferFalseDown
        if highB != lowB:
            ruleIndex["VTU"] = nodeB.inferTrueUp
            ruleIndex["VFU"] = nodeB.inferFalseUp

        (checkHigh, implyHigh) = self.justifyImply(highA, highB)
        if implyHigh != resolver.tautologyId:
            ruleIndex["IMT"] = implyHigh
        (checkLow, implyLow) = self.justifyImply(lowA, lowB)
        if implyLow != resolver.tautologyId:
            ruleIndex["IMF"] = implyLow

        variableIndex = { "x":splitVar.id,
                          "u":nodeA.id, "u1":highA.id, "u0":lowA.id,
                          "v":nodeB.id, "v1":highB.id, "v0":lowB.id }

        check = checkHigh and checkLow
        if check:
            proof = self.implyResolver.run(variableIndex, ruleNames = sorted(ruleIndex.keys()))
            if proof == resolver.tautologyId:
                justification = resolver.tautologyId
            else:
                comment = "Justification that %s ==> %s" % (nodeA.label(), nodeB.label())
                justification = self.prover.emitProof(proof, ruleIndex, comment)
        else:
            justification = resolver.tautologyId

        self.operationCache[key] = (check, justification)
        self.cacheAdded += 1
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
        self.cacheAdded += 1
        return newNode
            
    # Summarize activity
    def summarize(self):
        if self.verbLevel >= 1:
            print("Total variables: %d" % self.variableCount)
            print("Total nodes: %d" % self.nodeCount)
            print("Total apply operations: %d" % self.applyCount)            
            print("Total cached results: %d" % self.cacheAdded)
        if self.verbLevel >= 1:
            print("Results from And Operations:")
            self.andResolver.summarize()
            print("Results from Implication Testing Operations:")
            self.implyResolver.summarize()
        if self.verbLevel >= 1:
            print("Results from proof generation")
            self.prover.summarize()
        
