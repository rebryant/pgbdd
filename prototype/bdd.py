# Implementation of simple BDD package

from functools import total_ordering

import sys
import resolver

class BddException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "BDD Exception: " + str(self.value)

# Place holder to allow program to run without proving anything
class DummyProver:

    doLrat = False
    clauseCount = 0
    writer = None

    def __init__(self, fname = None):
        self.clauseCount = 0
        self.writer = sys.stderr

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

    def __hash__(self):
        return hash(self.level)

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
        # id should be first literal in clause for some proof checkers
        self.inferTrueUp = prover.createClause([id, -vid, -hid], [], "ITE assertions for node %s" % self.label())
        self.inferFalseUp = prover.createClause([id, vid, -lid], [])
        antecedents = []
        if prover.doLrat:
            if self.inferTrueUp != resolver.tautologyId:
                antecedents.append(-self.inferTrueUp)
            if self.inferFalseUp != resolver.tautologyId:
                antecedents.append(-self.inferFalseUp)
        self.inferTrueDown = prover.createClause([-id, -vid, hid], antecedents)
        self.inferFalseDown = prover.createClause([-id, vid, lid], antecedents)

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
    implyResolver = None
    # GC support
    # Callback function from driver that will collect accessible roots for GC
    rootGenerator = None
    # How many quantifications had been performed by last GC?
    lastGC = 0
    # How many variables should be quantified to trigger GC?
    gcThreshold = 10
    # Dictionary mapping variables to their IDs
    quantifiedVariableSet = None
    # Statistics
    cacheJustifyAdded = 0
    cacheNoJustifyAdded = 0
    applyCount = 0
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
        self.implyResolver = resolver.ImplyResolver(prover)
        self.quantifiedVariableSet = set([])
        self.lastGC = 0
        self.cacheJustifyAdded = 0
        self.cacheNoJustifyAdded = 0
        self.applyCount = 0
        self.nodeCount = 0
        self.maxLiveCount = 0
        self.variableCount = 0
        self.cacheRemoved = 0
        self.nodesRemoved = 0
        self.gcCount = 0

    def newVariable(self, name, id = None):
        level = len(self.variables) + 1
        var = Variable(level, name, id)
        self.variables.append(var)
        self.variableCount += 1
        return var
        
    def findOrMake(self, variable, high, low):
        key = (variable.level, high.id, low.id)
        if key in self.uniqueTable:
            return self.uniqueTable[key]
        else:
            node = VariableNode(self.nextNodeId, variable, high, low, self.prover)
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

    def buildClause(self, literalList):
        lits = sorted(literalList, key=lambda n: -n.variable.level)
        return self.reduceList(lits, self.applyOr, self.leaf0)

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

    def getSize(self, node):
        oneDict = self.buildInformation(node, lambda n: 1, {})
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
            return self.operationCache[key]

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

        self.operationCache[key] = newNode
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
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
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
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
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

    # Use clause to provide canonical list of nodes.  Should all be positive
    def equant(self, node, clause, topLevel = True):
        if topLevel:
            nextc = clause
            while not nextc.isLeaf():
                self.quantifiedVariableSet.add(nextc.variable)
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
        newNode = self.applyOr(newHigh, newLow) if quant else self.findOrMake(node.variable, newHigh, newLow)
        self.operationCache[key] = (newNode, resolver.tautologyId,[])
        self.cacheNoJustifyAdded += 1
        return newNode
            
    # Should a GC be triggered?
    def checkGC(self):
        newQuants = len(self.quantifiedVariableSet) - self.lastGC
        if newQuants > self.gcThreshold:
            return self.collectGarbage([])
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

    def cleanCache(self, markedSet):
        clauseList = []
        markedIds = set([node.id for node in markedSet])
        klist = list(self.operationCache.keys())
        for k in klist:
            kill = self.operationCache[k][0] not in markedSet
            # Skip over operation name
            for id in k[1:]:
                kill = kill or id not in markedIds
            if kill:
                clist = self.operationCache[k][2]
                clauseList += clist
                self.cacheRemoved += 1
                del self.operationCache[k]
        return clauseList
        
    def cleanNodes(self, markedSet):
        clauseList = []
        klist = list(self.uniqueTable.keys())
        for k in klist:
            node = self.uniqueTable[k]
            # If node is marked, then its children will be, too
            if node not in markedSet:
                clist = [node.inferTrueUp, node.inferFalseUp, node.inferTrueDown, node.inferFalseDown]
                clist = [c for c in clist if abs(c) != resolver.tautologyId]
                clauseList += clist
                self.nodesRemoved += 1
                del self.uniqueTable[k]
        return clauseList


    # Start garbage collection.
    # Provided with partial list of accessible roots
    def collectGarbage(self, rootList):
        frontier = rootList
        if self.rootGenerator is not None:
            frontier += self.rootGenerator()
        frontier = [r for r in frontier if not r.isLeaf()]
        # Marking phase
        markedSet = self.doMarking(frontier)
        clauseList = self.cleanCache(markedSet)
        clauseList += self.cleanNodes(markedSet)
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
            self.writer.write("Total cached results not requiring proofs: %d\n" % self.cacheNoJustifyAdded)
            self.writer.write("Total cached results requiring proofs: %d\n" % self.cacheJustifyAdded)
            self.writer.write("Total cache entries removed: %d\n" % self.cacheRemoved)
            self.writer.write("Total GCs performed: %d\n" % self.gcCount)
        if self.verbLevel >= 1:
            self.writer.write("Results from And Operations:\n")
            self.andResolver.summarize()
            self.writer.write("Results from Implication Testing Operations:\n")
            self.implyResolver.summarize()
        if self.verbLevel >= 1:
            self.writer.write("Results from proof generation\n")
            self.prover.summarize()
        
