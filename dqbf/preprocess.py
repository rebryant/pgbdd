# Preprocessing of DQBF formulas.  Convert them into QBF by 
# performing variable eliminations in a way that minimizes the number of clauses in the modified formula
# Support partition refinement
# Underlying elements can be any objects with an equality ordering, and equality functions

import reader
import enumerate

class PartitionException(Exception):
    msg = ""

    def __init__(self, msg = ""):
        self.msg = msg

    def str(self):
        return "Partition Exception: " + self.msg

# Set of values with associated unique ID
class Pset:
    id = 0
    elements = set([])
    
    def __init__(self, id, elist=[]):
        self.id = id
        self.elements = set(elist)

    def elist(self):
        return sorted([e for e in self.elements])

    def __str__(self):
        return 'S' + str(self.id) + ':{' + ", ".join(str(e) for e in self.elist()) + '}'

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

# Maintain set of unique sets
class PsetSet:
    # List of sets
    psetList = []
    # Set of all atomic elements
    universe = set([])

    def __init__(self):
        self.psetList = []
        self.universe = set([])
        
    # Either find existing set or add new one
    # Return resulting set ID
    def addSet(self, elist):
        eset = set(elist)
        for ps in self.psetList:
            if eset == ps.elements:
                return ps.id
        self.universe |= eset
        nextId = len(self.psetList)
        epset = Pset(nextId, elist)
        self.psetList.append(epset)
        return nextId

    def elists(self):
        return [ps.elist() for ps in self.psetList]

    def __len__(self):
        return len(self.psetList)

    def __getitem__(self, i):
        return self.psetList[i]

    def __iter__(self):
        return iter(self.psetList)

    def __next__(self):
        return next(self.psetList)

    def show(self):
        for s in self.psetList:
            print(str(s))

class Partition:
    # All elements
    psetSet = None
    # Mapping from elements to their set Ids
    elementMap = {}

    def __init__(self, llist = []):
        self.psetSet = PsetSet()
        self.elementMap = {}

        for elist in llist:
            id = self.psetSet.addSet(elist)
            for e in elist:
                self.elementMap[e] = id

    def singletons(self):
        nlist = [[e] for e in self.elementMap.keys()]
        return Partition(nlist)

    # Partition current refinement according split caused by membership in set
    def listRefine(self, elist):
        eset = set(elist)
        if not eset <= self.psetSet.universe:
            raise PartitionException("Cannot refine with non-subset")
        n = len(self.psetSet)
        inlists = [[] for i in range(n)]
        for e in eset:
            idx = self.elementMap[e]
            inlists[idx].append(e)
        inlists = [elist for elist in inlists if len(elist) > 0]
        outlists = [[] for i in range(n)]        
        for e in self.psetSet.universe - eset:
            idx = self.elementMap[e]
            outlists[idx].append(e)
        outlists = [elist for elist in outlists if len(elist) > 0]
        return Partition(inlists + outlists)

    def multiListRefine(self, llist):
        result = self
        for elist in llist:
            result = result.listRefine(elist)
        return result

    # Split partition so that mappings to distinct values get split
    # dmap is mapping from elements to unique Ids of sets
    def mapRefine(self, dmap):
        n = len(self.psetSet)
        dvalues = sorted(set(dmap.values()))
        minv = dvalues[0]
        maxv = dvalues[-1]
        m = maxv - minv + 1
        plists = [[] for i in range(n*m)]
        for i in range(n):
            fromSet = self.psetSet[i]
            for e in fromSet.elements:
                j = dmap[e] - minv
                plists[i*m+j].append(e)
        plists = [p for p in plists if len(p)>0]
        return Partition(plists)

    def elementSet(self, e):
        return self.psetSet[self.elementMap[e]]

    def __len__(self):
        return len(self.psetSet)

    def universe(self):
        return self.psetSet.universe

    def show(self):
        self.psetSet.show()


        

# Generate a block-level decomposition of a mapping from one set of objects to another
class Block:
    srcPartition = None
    destPartition = None
    blockMap = {} # Mapping from source pset to set of destination psets
    blockList = [] # Pairs of psets (src,dest) comprising blocks
    contentionBlockList = [] # Subset of blockList that are candidates for elimination
    contentionDestList = [] # List of destination elements that have contentions

    # Element map is mapping from source elements to list of destination elements
    def __init__(self, elementMap = None, singletons = False):
        self.srcPartition = None
        self.destPartition = None
        self.blockMap = {}
        self.blockList = []
        if elementMap is not None:
            self.processMap(elementMap, singletons)

    def processMap(self, elementMap, singletons):
        # Map from source to unique sets
        elementIdMap = {}
        destPsets = PsetSet()
        srcElements = elementMap.keys()

        # Canonicalize destination sets
        for k in elementMap.keys():
            dlist = elementMap[k]
            elementIdMap[k] = destPsets.addSet(dlist)
        
        # Partition source based on element Id mapping
        self.srcPartition = Partition([srcElements]).mapRefine(elementIdMap)
        
        # Partition destination based on sets of destination elements
        destElements = destPsets.universe
        destLists = destPsets.elists()
        if singletons:
            self.destPartition = Partition([destElements]).singletons()
        else:
            self.destPartition = Partition([destElements]).multiListRefine(destLists)

        # Construct block map
        self.blockMap = { sps : [] for sps in self.srcPartition.psetSet}
        self.blockList = []
        for se in srcElements:
            sps = self.srcPartition.elementSet(se)
            for de in elementMap[se]:
                dps = self.destPartition.elementSet(de)
                if dps not in self.blockMap[sps]:
                    self.blockMap[sps].append(dps)
                    self.blockList.append((sps,dps))
        
        # Find incompatible blocks
        self.contentionBlockList = []
        sblockList = sorted(self.blockMap.keys())
        for s1 in sblockList:
            sd1 = set(self.blockMap[s1])
            cset = set([])
            for s2 in sblockList:
                if s1 == s2:
                    continue
                sd2 = set(self.blockMap[s2])
                list1m2 = []
                list2m1 = []
                for sd in sd1 | sd2:
                    if sd in sd1:
                        if sd not in sd2:
                            list1m2.append(sd)
                    else:
                        list2m1.append(sd)
                if len(list1m2) > 0 and len(list2m1) > 0:
                    set1m2 = set(list1m2)
                    cset |= set1m2
            self.contentionBlockList += [(s1,sd) for sd in sorted(cset)]
        self.contentionBlockList.sort(key=lambda p : (p[0].id, p[1].id))


    # Construct CNF representation of feasibility formula
    # Return list of clauses
    def feasibilityFormula(self):
        # Create mapping from contention blocks to a feasibility variable
        fvarIds = {self.contentionBlockList[i] : i+1 for i in range(len(self.contentionBlockList))}
        sblockList = sorted(self.blockMap.keys())
        clauseList = []
        for i1 in range(len(sblockList)):
            s1 = sblockList[i1]
            sd1 = set(self.blockMap[s1])
            for i2 in range(i1+1, len(sblockList)):
                s2 = sblockList[i2]
                sd2 = set(self.blockMap[s2])
                list1m2 = []
                list2m1 = []
                for sd in sorted(sd1 | sd2):
                    if sd in sd1:
                        if sd not in sd2:
                            list1m2.append(sd)
                    else:
                        list2m1.append(sd)
                if len(list1m2) > 0 and len(list2m1) > 0:
                    for d1 in list1m2:
                        v1 = fvarIds[(s1,d1)]
                        for d2 in list2m1:
                            v2 = fvarIds[(s2,d2)]
                            clauseList.append([v1, v2])
        return clauseList

    def statList(self):
        ssize = len(self.srcPartition.universe())
        dsize = len(self.destPartition.universe())
        sblocks = len(self.srcPartition)
        dblocks = len(self.destPartition)
        blocks = len(self.blockList)
        cblocks = len(self.contentionBlockList)
        return [ssize, sblocks, dsize, dblocks, blocks, cblocks]

    def statFieldList(self):
        return ['sele', 'sblk', 'dele', 'dblk', 'blk', 'cblk']
        
    def show(self):
        print("Blocks")
        for (s,d) in self.blockList:
            print("%s --> %s" % (str(s), str(d)))
        print("Contention blocks")
        for i in range(len(self.contentionBlockList)):
            (s,d) = self.contentionBlockList[i]
            id = i+1
            print("%d: %s --> %s" % (id, str(s), str(d)))


# Estimate number of clauses as perform variable eliminations
class ClauseCounter:
    # Signature consists of subset of the universal variables
    # plus subset of the blocks of existential variables
    # Each represented by an Id of form 'uXX' or 'eXX'

    # Mapping from universal variable to its signature
    uvarMap = {}
    # Mapping from existential block (represented as Pset) to its signature
    eblockMap = {}
    # Mapping from existential variable to its existential block
    evarMap = {}
    # Mapping from signature to count of number of clauses with that signature
    initialClauseCounts = {}
    clauseCounts = {}
    # Number of clauses in original
    inputCount = 0

    def __init__(self, contentionBlockList):
        self.uvarMap = {}
        self.eblockMap = {}
        self.evarMap = {}
        self.clauseCounts = {}
        self.inputCount = 0
        for (eblock,ublock) in contentionBlockList:
            sig = self.signEblock(eblock)
            self.eblockMap[eblock] = sig
            for e in eblock.elements:
                self.evarMap[e] = eblock
            for u in ublock.elements:
                sig = self.signUvar(u)
                self.uvarMap[u] = sig

    def signUvar(self, u):
        return "u%.4d" % u

    def signEblock(self, eblock):
        return "E%.4d" % eblock.id

    # Build signature from components
    def makeSignature(self, sset):
        slist = sorted(sset)
        return "+".join(slist)

    # Decompose signature into set of individual signatures
    def splitSignature(self, sig):
        return set(sig.split('+'))

    def addCount(self, sig, count):
        if sig in self.clauseCounts:
            self.clauseCounts[sig] += count
        else:
            self.clauseCounts[sig] = count

    def addClause(self, clause):
        sset = set([])
        vars = [abs(lit) for lit in clause]
        for v in vars:
            if v in self.uvarMap:
                vsig = self.uvarMap[v]
                sset |= set([vsig])
            elif v in self.evarMap:
                vsig = self.eblockMap[self.evarMap[v]]
                sset |= set([vsig])
        sig = self.makeSignature(sset)
        self.addCount(sig, 1)
        self.inputCount += 1

    def loadClauses(self, clauseList):
        self.clauseCounts = {}
        for c in clauseList:
            self.addClause(c)
        self.initialClauseCounts = { k : v for k,v in self.clauseCounts.items() }
            
    def resetCounts(self):
        self.clauseCounts = { k : v for (k,v) in self.initialClauseCounts.items() }

    def totalCount(self):
        return sum(self.clauseCounts.values())

    # Compute effect of performing variable elimination of universal from block of existentials
    def uvarEliminate(self, uvar, eblock):
        usig = self.uvarMap[uvar]
        esig = self.eblockMap[eblock]
        sigList = list(self.clauseCounts.keys())
        for sig in sigList:
            sset = self.splitSignature(sig)
            if esig in sset and usig not in sset:
                # Must double the clauses, adding uvar
                nsig = self.makeSignature(sset | set([usig]))
                self.addCount(nsig, 2 * self.clauseCounts[sig])
                # Old clauses get eliminated
                del self.clauseCounts[sig]

    # Compute effect of performing variable elimination for entire block
    def blockEliminate(self, bpair):
        eblock, ublock = bpair
        for u in ublock.elements:
            self.uvarEliminate(u, eblock)

    def show(self):
        print("Counts by signature")
        for sig in sorted(self.clauseCounts.keys()):
            print("\t%d\t%s" % (self.clauseCounts[sig], sig)) 
        icnt = self.inputCount
        tot = self.totalCount()
        ratio = float(tot)/icnt
        fields = ['','InCls', str(icnt), 'ToCls', str(tot), 'Ratio', "%.2f" % ratio]
        print('\t'.join(fields))


# Class for doing estimations of clause expansion
class Estimator:

    reader = None # DQCNF reader
    blocks = None # Block partitioning of input
    ccounter = None # Clause counter
    totalCountList = [] # List of all Total counts computed
    bestBlockList = None # List of elimination blocks in optimal solution

    def __init__(self, fname, singletons):
        self.reader = reader.DqcnfReader(fname)
        self.blocks = Block(self.reader.dependencyMap, singletons)
        self.ccounter = ClauseCounter(self.blocks.contentionBlockList)
        self.ccounter.loadClauses(self.reader.clauses)
        
    # Find optimal solution
    # Return #input clauses, #solutions tested, #total clauses for best solution
    def findSolutions(self, verbose = False):
        clauseList = self.blocks.feasibilityFormula()
        e = enumerate.Enumerator(clauseList)
        varList = list(range(1, len(self.blocks.contentionBlockList)+1))
        solutions = e.minSolve(varList)
        self.totalCountList = []
        self.bestBlockList = None
        bestT = 0
        for soln in solutions:
            self.ccounter.resetCounts()
            blist = []
            vlist = []
            for var in soln:
                if var > 0:
                    block = self.blocks.contentionBlockList[var-1]
                    self.ccounter.blockEliminate(block)
                    vlist.append(var)
                    blist.append(block)
            if verbose:
                print("Eliminated blocks %s" % str(vlist))
                self.ccounter.show()
            t = self.ccounter.totalCount()
            self.totalCountList.append(t)
            if bestT == 0.0 or t < bestT:
                bestT = t
                self.bestBlockList = blist
        if verbose:
            icount = self.ccounter.inputCount
            print("Initial: %d.  Totals: %s.  Best = %d" % (icount, str(self.totalCountList), bestT))
        return bestT
        
            
        
        
