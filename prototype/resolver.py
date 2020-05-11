#!/usr/bin/python

import datetime

# Search for resolution tree that will yield target clause

# Special value to represent true/tautology
# It's negation represents false/invalid
tautologyId = 1111111

# Clean up clause.
# Remove duplicates + false
# Detect when tautology
def cleanClause(literalList):
    slist = sorted(literalList, key = abs)
    while len(slist) > 0:
        last = slist[-1]
        if abs(last) != tautologyId:
            break
        elif last == tautologyId:
            return tautologyId
        else:
            slist = slist[:-1]
    if len(slist) == 0:
        return -tautologyId
    elif len(slist) == 1:
        return slist
    else:
        nlist = [slist[0]]
        for i in range(1, len(slist)):
            if slist[i-1] == slist[i]:
                continue
            if slist[i-1] == -slist[i]:
                return tautologyId
            nlist.append(slist[i])
        return nlist

class ResolveException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Resolve Exception: " + str(self.value)


def unitRange(n):
    return list(range(1, n+1))


# Bit vector representation of clauses.
# Supports fast application of resolution
class Clause:
    # Possible special conditions
    normal, invalid, empty, tautology = range(4)
    # Clause category.  Default is normal
    category = 0 
    # Bit vector representation.
    pos = 0  
    neg = 0

    # By default, clauses are normal
    def __init__(self, literalList = [], category = 0):
        self.pos = 0
        self.neg = 0
        self.category = category
        if category != self.normal:
            return
        fixList = cleanClause(literalList)
        if fixList == tautologyId:
            self.category = self.tautology
            return
        elif fixList == -tautologyId:
            self.category = self.empty
            return
        for lit in fixList:
            if lit > 0:
                self.pos = self.pos | (1<<lit)
            if lit < 0:
                self.neg = self.neg | (1<<-lit)

    def isValid(self):
        return self.category != self.invalid
        
    def isTautology(self):
        return self.category == self.tautology

    def isEmpty(self):
        return self.category == self.empty

    def resolveVariables(self, other):
        if self.category == self.normal and other.category == self.normal:
            return (self.pos & other.neg) | (self.neg & other.pos)
        return -1

    def resolvable(self, other):
        r = self.resolveVariables(other)
        # Bit hacking trick to check for single one bit
        return r > 0 and r != 0 and (r & (r-1)) == 0
        
    def resolve(self, other):
        r = self.resolveVariables(other)
        if not (r > 0 and r != 0 and (r & (r-1)) == 0):
            return Clause(category = self.invalid)
        npos = (self.pos | other.pos) & ~r
        nneg = (self.neg | other.neg) & ~r
        if (npos & nneg) != 0:
            return Clause(category = self.tautology)
        if npos == 0 and nneg == 0:
            return Clause(category = self.empty)
        nclause = Clause()
        nclause.category = self.normal
        nclause.pos = npos
        nclause.neg = nneg
        return nclause

    def literalList(self):
        if self.category == self.tautology:
            return [-1, 1]
        if self.category != self.normal:
            return []
        posBits = self.pos >> 1
        negBits = self.neg >> 1
        var = 1
        ls = []
        while (posBits|negBits) != 0:
            p0 = posBits & 1
            n0 = negBits & 1
            if p0 == 1:
                ls.append(var)
            if n0 == 1:
                ls.append(-var)
            var += 1
            posBits = posBits >> 1
            negBits = negBits >> 1
        return ls

    def invalidate(self):
        self.category = self.invalid
        self.pos = 0
        self.neg = 0

    def copyFrom(self, other):
        self.category = other.category
        self.pos = other.pos
        self.neg = other.neg

    def __str__(self):
        if self.isTautology():
            return "Tautology"
        if not self.isValid():
            return "Invalid"
        else:
            slist = [str(l) for l in self.literalList()]
            return "[" + " ".join(slist) + "]"

    def __eq__(self, other):
        return self.category == other.category and self.pos == other.pos and self.neg == other.neg

# Representation of proof
class ProofStep:
    literalList = []
    isLeaf = False

    def __init__(self, literalList):
        self.literalList = literalList

    def postfix(self, showLiterals = False):
        return ""

    def __str__(self):
        return self.postfix()

    def mapLiterals(self, map):
        nlist = []
        for lit in self.literalList:
            if lit < 0:
                nlist.append(-map[-lit])
            else:
                nlist.append(map[lit])
        return nlist

    def remapLiterals(self, map):
        return None

class ProofLeaf(ProofStep):
    name = ""
    
    def __init__(self, literalList, name):
        ProofStep.__init__(self, literalList)
        self.isLeaf = True
        self.name = name

    def postfix(self, showLiterals = False):
        if showLiterals:
            llist = [str(lit) for lit in self.literalList]
            return "%s(%s)" % (self.name, " ".join(llist))
        else:
            return self.name

    def remapLiterals(self, map):
        nliterals = self.mapLiterals(map)
        return ProofLeaf(nliterals, self.name)

class ProofNode(ProofStep):
    children = []

    def __init__(self, clause, children):
        ProofStep.__init__(self, clause)
        self.isLeaf = False
        self.children = children

    def postfix(self, showLiterals = False):
        suffix = "R"
        if showLiterals:
            llist = [str(lit) for lit in self.literalList]
            suffix = "R(%s)" % (" ".join(llist))
        slist = [c.postfix(showLiterals) for c in self.children] + [suffix]
        return " ".join(slist)

    def remapLiterals(self, map):
        nliterals = self.mapLiterals(map)
        nchildren = [c.remapLiterals(map) for c in self.children]
        return ProofNode(nliterals, nchildren)

# Generate all possible resolution trees with N leaves.
# Resolution operation is commutative, but not associative

class Tree:
    # Unique ID for tree
    id = 0
    # Bit vector of clause ids
    atoms = 0
    representation = ""
    clause = None
    isLeaf = False
    
    def __init__(self, id):
        self.id = id
        self.clause = Clause(category = Clause.invalid)

    def __str__(self):
        return self.representation

    def compatible(self, other):
        return (self.atoms & other.atoms) == 0

    def newTree(self, id, other):
        return Node(id, self, other)

    # Convert tree into nested list showing proof structure.
    # Each subpart includes literal list showing resulting clauses
    def getProof(self, ruleDict):
        return None

class Leaf(Tree):
    
    def __init__(self, id):
        Tree.__init__(self, id)
        self.atoms = 1 << id
        self.representation = str(id)
        self.isLeaf = True

    def getProof(self, ruleDict):
        return ProofLeaf(self.clause.literalList(), ruleDict[self.id])


class Node(Tree):
    left = None
    right = None

    def __init__(self, id, left, right):
        Tree.__init__(self, id)
        self.isLeaf = False
        self.left = left
        self.right = right
        self.atoms = left.atoms | right.atoms
        self.representation = "[" + left.representation + " " + right.representation + "]"

    def getProof(self, ruleDict):
        children = [self.left.getProof(ruleDict), self.right.getProof(ruleDict)]
        return ProofNode(self.clause.literalList(), children)

    
# Collection of all resolution trees with specified number of leaves
# Each leaf corresponds to an input clause
class Forest:
    leafCount = 1
    treeList = []
    allAtoms = 0
    verbLevel = 1

    def __init__(self, leafCount, verbLevel = 1):
        self.leafCount = leafCount
        self.verbLevel = verbLevel
        self.treeList = []
        self.allAtoms = 0       

        start = datetime.datetime.now()
        self.generate2()
        fullTreeList = [tree for tree in self.treeList if self.isFull(tree)]
        delta = datetime.datetime.now() - start
        if verbLevel > 0:
            seconds = delta.seconds + 1e-6 * delta.microseconds
            if self.verbLevel >= 1:
                print("Forest: Generated %d trees, of which %d are full in %.2f seconds" % (len(self.treeList), len(fullTreeList), seconds))

    def generate(self):
        for id in unitRange(self.leafCount):
            leaf = Leaf(id)
            if self.verbLevel >= 5:
                print("Generated tree #%d: %s" % (leaf.id, str(leaf)))
            self.treeList.append(leaf)
            self.allAtoms = self.allAtoms | leaf.atoms
        nextId = self.leafCount+1
        nextRight = 1
        while nextRight < len(self.treeList):
            right = self.treeList[nextRight]
            for nextLeft in range(nextRight):
                left = self.treeList[nextLeft]
                if left.compatible(right):
                    newTree = left.newTree(nextId, right)
                    if self.verbLevel >= 5:
                        print("Generated tree #%d: %s" % (newTree.id, str(newTree)))
                    self.treeList.append(newTree)
                    nextId += 1
            nextRight += 1

    def generate2(self):
        # Dictionary of trees, indexed by clause count
        # Each entry is itself a dictionary, indexed by a clause set, giving all trees with that clause set
        treeDict = { count : {} for count in unitRange(self.leafCount) }
        for id in unitRange(self.leafCount):
            leaf = Leaf(id)
            if self.verbLevel >= 5:
                print("Generated tree #%d: %s" % (leaf.id, str(leaf)))
            self.treeList.append(leaf)
            self.allAtoms = self.allAtoms | leaf.atoms
            treeDict[1][leaf.atoms] = [leaf]

        nextId = self.leafCount+1
        # Strategy: Check compatibility for entire categories of trees before merging them
        for tcount in range(2, self.leafCount + 1):
            lbound = tcount // 2
            for lcount in unitRange(lbound):
                rcount = tcount - lcount
                for latoms in treeDict[lcount].keys():
                    for ratoms in treeDict[rcount].keys():
                        if (latoms & ratoms) == 0:
                            natoms = latoms | ratoms
                            if natoms not in treeDict[tcount]:
                                treeDict[tcount][natoms] = []
                            for ltree in treeDict[lcount][latoms]:
                                for rtree in treeDict[rcount][ratoms]:
                                    if lcount < rcount or ltree.id < rtree.id:
                                        newTree = ltree.newTree(nextId, rtree)
                                        self.treeList.append(newTree)
                                        treeDict[tcount][natoms].append(newTree)
                                        if self.verbLevel >= 5:
                                            print("Generated tree #%d: %s" % (newTree.id, str(newTree)))
                                        nextId += 1
                
    def loadClauses(self, clauseList):
        if len(clauseList) > self.leafCount:
            raise ResolveException("Can only handle max of %d input clauses" % self.leafCount)
        for t in self.treeList:
            t.clause.invalidate()
        for i in range(len(clauseList)):
            self.treeList[i].clause.copyFrom(clauseList[i])

    def search(self, target):
        id = 0
        for t in self.treeList:
            id += 1
            if not t.isLeaf:
                cleft = t.left.clause
                cright = t.right.clause
                cres = cleft.resolve(cright)
                if cres.isValid():
                    t.clause.copyFrom(cres)
            if self.verbLevel >= 4:
                print("Tree %d.  Resolvent = %s" % (id, str(t.clause)))
            if t.clause == target:
                return t
            if t.clause.isTautology():
                t.clause.invalidate()
            if t.clause.isEmpty():
                if self.verbLevel >= 1:
                    print("Warning.  Tree leads to empty clause: %s" % str(t))
                t.clause.invalidate()
        # Only get here if failed
        print("Couldn't generate resolution proof")
        return None

    def isFull(self, tree):
        return tree.atoms == self.allAtoms
            
class ProofManager:        
    verbLevel = 1
    forest = None
    # Proof cache is mapping from list of canonical literals to proof rule tree
    proofCache = {}
    # Statistics about each entry in proof cache.  Number of times requested
    proofCounts = {}
    # List of symbolic names for variables
    variableNames = []
    # Clause rule is mapping from rule name to list of symbolic literals
    # Each symbolic literal either vname or !vname
    clauseRules = {}
    # Target clause
    target = None
    
    def __init__(self, variableNames, maxRules, target, verbLevel = 1):
        self.verbLevel = verbLevel
        self.variableNames = variableNames
        self.verbLevel = verbLevel
        self.forest = Forest(maxRules, verbLevel)
        self.proofCache = {}
        self.proofCounts = {}
        self.clauseRules = {}
        self.target = target


    def clearRules(self):
        self.clauseRules = {}

    def addRule(self, ruleName, ruleLiterals):
        self.clauseRules[ruleName] = ruleLiterals

    def proofKey(self, variableList, ruleNames):
        rstring = "+".join(ruleNames)
        vstring = "+".join([str(v) for v in variableList])
        return rstring + ":" + vstring

    # Add special proof rules
    def addProof(self, variableList, ruleNames, proof):
        key = self.proofKey(variableList, ruleNames)
        self.proofCache[key] = proof
        self.proofCounts[key] = 1

    def showCache(self):
        accessCount = 0
        keyList = sorted(self.proofCache.keys())
        for key in keyList:
            rstring, vstring = key.split(":")
            rstring = " ".join(rstring.split("+"))
            vlist = [int(s) for s in vstring.split("+")]
            vslist = ["TAUT" if v == tautologyId else "NIL" if v == -tautologyId else str(v) for v in vlist]
            vstring = ", ".join(vslist)

            pstring = str(self.proofCache[key])
            if self.verbLevel >= 2:
                print("[%s : %s] --> %s (%d uses)" % (rstring, vstring, pstring, self.proofCounts[key]))
            accessCount += self.proofCounts[key]
        if self.verbLevel >= 1:
            print("%d keys.  %d total uses" % (len(keyList), accessCount))

    def lookupProof(self, variableList, ruleNames):
        key = self.proofKey(variableList, ruleNames)
        if key in self.proofCache:
            self.proofCounts[key] += 1
            return self.proofCache[key]
        return None

    # valueMap is dictionary giving variable identifiers associated with named literals
    def findProof(self, valueMap, ruleNames):
        # Build map from external variables to canonical literal values
        forwardMap = {}
        # Build map from canonical literals to external variables
        inverseMap = {}
        # Build map from variable names to canonical literal values
        canonicalMap = {}
        canonicalVariable = 0
        for vname in self.variableNames:
            canonicalVariable += 1
            externalVariable = valueMap[vname]
            if abs(externalVariable) == tautologyId:
                # Preserve true/false
                canonicalMap[vname] = externalVariable
                forwardMap[externalVariable] = externalVariable
                inverseMap[externalVariable] = externalVariable
            elif externalVariable in forwardMap:
                canonicalMap[vname] = forwardMap[externalVariable]
            else:
                canonicalMap[vname] = canonicalVariable
                forwardMap[externalVariable] = canonicalVariable
                inverseMap[canonicalVariable] = externalVariable
        if self.verbLevel >= 3:
            mapStrings = ["%s:%d->%d" % (vname, valueMap[vname], canonicalMap[vname]) for vname in self.variableNames]
            print("Constructed canonical literals: " + " ".join(mapStrings))
        # See if already have proof in cache
        variableList = [canonicalMap[vname] for vname in self.variableNames]
        proof = self.lookupProof(variableList, ruleNames)
        if proof is not None:
            nproof = proof.remapLiterals(inverseMap)
            if self.verbLevel >= 3:
                pstring = nproof.postfix(showLiterals = True)
                print("Found cached proof: " + pstring)
            return nproof
        # Construct target clause
        targetClause = self.makeClause(self.target, canonicalMap)
        if targetClause.isTautology():
            if self.verbLevel >= 3:
                print("Target is tautology")
            return tautologyId
        if targetClause.isEmpty():
            if self.verbLevel >= 3:
                print("Target is empty")
            return -tautologyId
        # Build list of non-degenerate clauses
        clauseList = []
        # Mapping from leaf ID used in forest to rule name
        ruleDict = {}
        ruleCount = 0
        # Create set of clauses for resolution
        for ruleName in self.clauseRules.keys():
            ruleLiterals = self.clauseRules[ruleName]
            c = self.makeClause(ruleLiterals, canonicalMap)
            if not c.isTautology():
                clauseList.append(c)
                ruleCount += 1
                ruleDict[ruleCount] = ruleName
        if self.verbLevel >= 3:
            nameList = [ruleDict[id] for id in unitRange(ruleCount)]
            print("Found %d clauses for proof generation: %s" % (len(nameList), " ".join(nameList)))
        self.forest.loadClauses(clauseList)
        t = self.forest.search(targetClause)
        if t is None:
            print("Couldn't find proof of target")
            return -tautologyId
        proof =  t.getProof(ruleDict)
        self.addProof(variableList, ruleNames, proof)
        nproof = proof.remapLiterals(inverseMap)
        if self.verbLevel >= 3:
            pstring = nproof.postfix(showLiterals = True)
            print("Generated proof: " + pstring)
        return nproof

    # Generate a clause from a symbolic rule
    def makeClause(self, ruleLiterals, canonicalMap):
        literalList = []
        for symLiteral in ruleLiterals:
            negative = symLiteral[0] == '!'
            if negative:
                symLiteral = symLiteral[1:]
            variable = canonicalMap[symLiteral]
            literal = -variable if negative else variable
            literalList.append(literal)
        return Clause(literalList)



class Resolver:
    variableNames = []
    rules = {}
    target = []
    verbLevel = 1
    manager = None

    def __init__(self, variableNames, rules, target, verbLevel = 1):
        self.verbLevel = verbLevel
        self.variableNames = variableNames
        self.rules = rules
        self.target = target
        self.verbLevel = verbLevel
        self.manager = ProofManager(self.variableNames, len(rules), self.target, verbLevel = self.verbLevel)
#        for cname in self.rules.keys():
#            self.manager.addRule(cname, self.rules[cname])

    def summarize(self):
        self.manager.showCache()

    def run(self, valueMap, ruleNames = None):
        if ruleNames is None:
            ruleNames = sorted(self.rules.keys())
        self.manager.clearRules()
        for cname in ruleNames:
            self.manager.addRule(cname, self.rules[cname])
        proof = self.manager.findProof(valueMap, ruleNames)
        return proof

    # Creat a dictionary mapping rule names to tautology
    def freshIndex(self):
        return { name : tautologyId for name in self.rules.keys() }

    def standardMap(self):
        return { self.variableNames[i] : i+1 for i in range(len(self.variableNames)) }


class AndResolver(Resolver):
    
    def __init__(self, verbLevel = 1):
        variableNames = ["x", "u", "u1", "u0", "v", "v1", "v0", "w", "w1", "w0"]
        rules = { "UTD" : ["!x",  "!u",  "u1"],
                  "UFD" : ["x",   "!u",  "u0"],
                  "VTD" : ["!x",  "!v",  "v1"],
                  "VFD" : ["x",   "!v",  "v0"],
                  "WTU" : ["!x",  "!w1", "w"],
                  "WFU" : ["x",   "!w0", "w"],
                  "IMT" : ["!u1", "!v1", "w1"],
                  "IMF" : ["!u0", "!v0", "w0"] }
        target = ["!u", "!v", "w"]
        Resolver.__init__(self, variableNames, rules, target, verbLevel)
        
    def nobranchU(self, valueMap):
        valueMap["u1"] = valueMap["u"]
        valueMap["u0"] = valueMap["u"]        
        return valueMap

    def nobranchV(self, valueMap):
        valueMap["v1"] = valueMap["v"]
        valueMap["v0"] = valueMap["v"]        
        return valueMap

    def nobranchW(self, valueMap):
        valueMap["w1"] = valueMap["w"]
        valueMap["w0"] = valueMap["w"]        
        return valueMap        

    def zeroU1(self, valueMap):
        valueMap["u1"] = -tautology
        valueMap["w1"] = -tautology
        return valueMap        

    def oneU1(self, valueMap):
        valueMap["u1"] = tautology
        valueMap["w1"] = valueMap["v1"]
        return valueMap        

    def zeroU1V0(self, valueMap):
        valueMap["u1"] = -tautology
        valueMap["w1"] = -tautology
        valueMap["v0"] = -tautology
        valueMap["w0"] = -tautology
        valueMap["w"] = -tautology
        return valueMap                

    def equalU1V1(self, valueMap):
        valueMap["v1"] = valueMap["u1"]
        valueMap["w1"] = valueMap["u1"]
        return valueMap

class ImplyResolver(Resolver):
    
    def __init__(self, verbLevel = 1):
        variableNames = ["x", "u", "u1", "u0", "v", "v1", "v0"]
        rules = { 
            "UTD" : ["!x",  "!u",  "u1"],
            "UFD" : ["x",   "!u",  "u0"],
            "VTU" : ["!x",  "!v1", "v"],
            "VFU" : ["x",  "!v0", "v"],
            "IMT" : ["!u1", "v1"],
            "IMF" : ["!u0", "v0"] }
        target = ["!u", "v"]
        Resolver.__init__(self, variableNames, rules, target, verbLevel)
    