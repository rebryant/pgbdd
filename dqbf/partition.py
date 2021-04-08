# Support partition refinement
# Underlying elements can be any objects with an equality ordering, and equality functions

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
    conflictPairList = [] # Incompatible pairs of source psets
    contentionBlockList = [] # Subset of blockList that are candidates for elimination

    # Element map is mapping from source elements to list of destination elements
    def __init__(self, elementMap = None):
        self.srcPartition = None
        self.destPartition = None
        self.blockMap = {}
        self.blockList = []
        if elementMap is not None:
            self.processMap(elementMap)

    def processMap(self, elementMap):
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
        self.conflictPairList = []
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
                    self.conflictPairList.append((s1,s2))
                    cset |= set(list1m2)
            self.contentionBlockList += [(s1,sd) for sd in sorted(cset)]





    def statList(self):
        ssize = len(self.srcPartition.universe())
        dsize = len(self.destPartition.universe())
        sblocks = len(self.srcPartition)
        dblocks = len(self.destPartition)
        blocks = len(self.blockList)
        cblocks = len(self.contentionBlockList)
        cpairs = len(self.conflictPairList)
        return [ssize, sblocks, dsize, dblocks, blocks, cblocks, cpairs]

    def statFieldList(self):
        return ['sele', 'sblk', 'dele', 'dblk', 'blk', 'cblk', 'cpair']
        
    def show(self):
        print("Blocks")
        for (s,d) in self.blockList:
            print("%s --> %s" % (str(s), str(d)))
        print("Contention blocks")
        for (s,d) in self.contentionBlockList:
            print("%s --> %s" % (str(s), str(d)))
