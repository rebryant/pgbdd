# Preprocessing of DQBF formulas.  Convert them into QBF by 
# performing variable eliminations in a way that minimizes the number of clauses in the modified formula
# Support partition refinement
# Underlying elements can be any objects with an equality ordering, and equality functions

import reader
import sys
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

    def __len__(self):
        return len(self.elements)

    def __str__(self):
        return 'S' + str(self.id) + ':{' + ", ".join(str(e) for e in self.elist()) + '}'

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id

# Maintain set of unique sets
class PsetSet:
    # List of sets.  Ordered by Id
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

    # Join sets containing specified elements into single set
    def listJoin(self, elist, ignoreAll):
        eset = set(elist)
        if not eset <= self.psetSet.universe:
            raise PartitionException("Cannot join with non-subset")
        if len(elist) < 2:
            return self
        # This is a placeholder.  Must do proper check of Tseitin variable dependencies"
        if ignoreAll and len(elist) == len(self.elementMap):
            return self
        nlist = []
        rest = []
        for p in self.psetSet:
            if len(p.elements & eset) > 0:
                nlist += p.elist()
            else:
                rest.append(p.elist())
        return Partition([nlist] + rest)

    def multiListJoin(self, llist, ignoreAll = False):
        result = self
        for elist in llist:
            result = result.listJoin(elist, ignoreAll)
        return result

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

    def __init__(self, reader):
        self.reader = reader
        self.blocks = Block(self.reader.dependencyMap)
        self.ccounter = ClauseCounter(self.blocks.contentionBlockList)
        self.ccounter.loadClauses(self.reader.clauses)
        
    # Find optimal solution
    # Return #input clauses, #solutions tested, #total clauses for best solution
    def findSolutions(self, verbose = False, check = False):
        clauseList = self.blocks.feasibilityFormula()
        e = enumerate.Enumerator(clauseList)
        varList = list(range(1, len(self.blocks.contentionBlockList)+1))
        solutions = e.minSolve(varList, check = check)
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
            if bestT == 0 or t < bestT:
                bestT = t
                self.bestBlockList = blist
        if verbose:
            icount = self.ccounter.inputCount
            print("Initial: %d.  Totals: %s.  Best = %d" % (icount, str(self.totalCountList), bestT))
        return bestT
        

# Represent variable added by dependency elimination
class ExpansionVariable:

    id = 0            # Variable number
    rootVariable = 0  # Id of original existential variable
    literalList = []  # Universal literals on which expansion is based

    def __init__(self, id, rootVariable = None, literalList = []):
        self.id = id
        self.rootVariable = id if rootVariable is None else rootVariable
        self.literalList = literalList

    # Create two new expansion variables.  Return as pair (vtrue, vcomp)
    def split(self, id, uvar):
        vtrue = ExpansionVariable(id, self.rootVariable, self.literalList + [uvar])
        vcomp = ExpansionVariable(id+1, self.rootVariable, self.literalList + [-uvar])
        return (vtrue, vcomp)

    def isExpanded(self):
        return len(self.literalList) > 0

    def __str__(self):
        if len(self.literalList) == 0:
            return str(self.rootVariable)
        llist = [("+" if l > 0 else "-") + str(abs(l)) for l in self.literalList]
        return "%d[%s]" % (self.rootVariable, ",".join(llist))


# Represent set of existential variables and their expanded versions
class EvarManager:
    nextId = 0  # Next variable number as expand
    evarMap = {} # Mapping from original variable to its expanded versions

    def __init__(self, reader):
        maxVar = max(max(reader.universalList), max(reader.existentialList))
        self.nextId = maxVar + 1
        self.evarMap = { evar : [ExpansionVariable(evar)] for evar in reader.existentialList }

    # Expand list of original evars by uvar.
    # Creates new expansion variables
    # Creates & returns maps from previous expanded version to true & complemented expansion variables
    def expand(self, uvar, elist):
        trueMap = {}
        compMap = {}
        for evar in elist: 
            nlist = []
            for eevar in self.evarMap[evar]:
                etrue, ecomp = eevar.split(self.nextId+1, uvar)
                self.nextId += 2
                trueMap[eevar.id] = etrue
                compMap[eevar.id] = ecomp
                nlist += [etrue, ecomp]
            self.evarMap[evar] = nlist
        return trueMap, compMap
            

# Represent set of clauses generated by performing dependency eliminations
class ExpandedClause:

    source = [] # Original clause
    clauseList = []

    def __init__(self, clause):
        self.source = clause
        self.clauseList = [clause]

    def comment(self):
        if len(self.clauseList) == 1:
            return ""
        slist = [str(l) for l in self.source]
        return "c %d expansions of [%s]" % (len(self.clauseList), ", ".join(slist))

    def expandClause(self, clause, uvar, trueMap, compMap, dependencyMap):
        foundE = False
        tc = []
        cc = []
        # Make pass to see whether we'll need to keep literal of uvar
        # If not, can do universal reduction
        needUlit = False
        for lit in clause:
            var = abs(lit)
            if  var not in trueMap and var in dependencyMap and uvar in dependencyMap[var]:
                needUlit = True
        for lit in clause:
            var = abs(lit)
            if lit == uvar:
                cc = None
                if needUlit and tc is not None:
                    tc.append(lit)
            elif lit == -uvar:
                tc = None
                if needUlit and cc is not None:
                    cc.append(lit)
            elif var in trueMap:
                foundE = True
                if tc is not None:
                    nvar = trueMap[var].id
                    nlit = nvar if lit > 0 else -nvar
                    tc.append(nlit)
                if cc is not None:
                    nvar = compMap[var].id
                    nlit = nvar if lit > 0 else -nvar
                    cc.append(nlit)
            else:
                if tc is not None:
                    tc.append(lit)
                if cc is not None:
                    cc.append(lit)
        if foundE:
            if cc is None:
                # uvar present in original clause
                return [tc]
            elif tc is None:
                # -uvar present in original clause
                return [cc]
            else:
                # Splitting clause
                if needUlit:
                    tc = [uvar] + tc
                    cc = [-uvar] + cc
                return [tc,cc]
        else:
            # Original clause unchanged
            return [clause]

    def expand(self, uvar, trueMap, compMap, dependencyMap):
        nlist = []
        for c in self.clauseList:
            xclauses = self.expandClause(c, uvar, trueMap, compMap, dependencyMap)
            nlist += xclauses
        self.clauseList = nlist

    def emit(self, outFile, verbose):
        if verbose:
            outFile.write(self.coment() + '\n')
        for clause in self.clauseList:
            slist = [str(lit) for lit in clause] + ['0']
            outFile.write(", ".join(slist) + '\n')

    def __len__(self):
        return len(self.clauseList)

class QuantifierManager:
    # Mapping from each original existential variable to its (decreasing) set of universal dependencies
    dependencyMap = {}
    # When told to organize self, create as much of a quantifier prefix as possible
    # and then leave leftovers as ones to be declared explicitly
    universalPrefix = []
    existentialPrefix = []
    explicitList = []
    otherUniversalList = []

    def __init__(self, reader):
        self.dependencyMap = { evar : set(ulist) for evar,ulist in reader.dependencyMap.items() }

    def removeDependency(self, uvar, evar):
        self.dependencyMap[evar] -= set([uvar])

    def removeDependencies(self, uvar, elist):
        for evar in elist:
            self.removeDependency(uvar, evar)
        
    # Organize as quantifier prefix + leftovers
    def organize(self, verbose):
        self.existentialPrefix = []
        self.universalPrefix = []
        self.explicitList = []
        elist = self.dependencyMap.keys()
        elist.sort(key = lambda evar : len(self.dependencyMap[evar]))
        evar = elist[0]
        # Set of universal variables in prefix to this point
        uset = self.dependencyMap[evar]
        self.universalPrefix = [sorted(uset)]
        self.existentialPrefix = [[evar]]
        self.explicitList = []
        for evar in elist[1:]:
            if self.dependencyMap[evar] == uset:
                self.existentialPrefix[-1].append(evar)
            elif self.dependencyMap[evar] > uset:
                dset = self.dependencyMap[evar] - uset
                self.universalPrefix.append(sorted(dset))
                uset = self.dependencyMap[evar]
                self.existentialPrefix.append([evar])
            else:
                self.explicitList.append(evar)
        oset = set([])
        if len(self.explicitList) > 0:
            print("Explicit list: %s" % str(self.explicitList))
        for evar in self.explicitList:
            for uvar in self.dependencyMap[evar]:
                if uvar not in uset and uvar not in oset:
                    oset |= set([uvar])
        self.otherUniversalList = sorted(oset)
#        if verbose:
#            print("Quantification: %d levels of universal and existential.  %d levels of explicit dependencies." % (len(self.universalPrefix), len(self.explicitList)))


class Expander:    
    emanager = None
    qmanager = None
    expandedClauses = []

    def __init__(self, reader):
        self.emanager = EvarManager(reader)
        self.qmanager = QuantifierManager(reader)
        self.expandedClauses = [ExpandedClause(clause) for clause in reader.clauses]

    # Given set of blocks (each pair (evars, uvars)), do expansion
    def expand(self, blockList):
        edict = {}
        # Collect into list for each uvar
        for (eset, uset) in blockList:
            for u in uset.elist():
                elist = eset.elist()
                if u in edict:
                    edict[u] += elist
                else:
                    edict[u] = elist
        # Process universal variables
        ulist = sorted(edict.keys())
        for u in ulist:
            elist = sorted(edict[u])
            self.qmanager.removeDependencies(u, elist)
            trueMap, compMap = self.emanager.expand(u, elist)
            for eclause in self.expandedClauses:
                eclause.expand(u, trueMap, compMap, self.qmanager.dependencyMap)
        
    def generateHeader(self, outfile, verbose):
        varCount = self.emanager.nextId
        clauseCount = sum([len(eclause) for eclause in self.expandedClauses])
        outfile.write("p cnf %d %d\n" % (varCount, clauseCount))
        return clauseCount

    def generatePrefix(self, outfile, verbose):
        uvarCount = 0
        evarCount = 0
        for uset, eset in zip(self.qmanager.universalPrefix, self.qmanager.existentialPrefix):
            ulist = sorted(uset)
            uvarCount += len(ulist)
            if len(ulist) > 0:
                slist = ['a'] + [str(u) for u in ulist] + ['0']
                outfile.write(" ".join(slist) + '\n')
            elist = sorted(eset)
            if len(elist) > 0:
                alist = []
                for evar in elist:
                    xlist = self.emanager.evarMap[evar]
                    alist += [xvar.id for xvar in xlist]
                    if verbose and len(xlist) > 1:
                        outfile.write("c Expansions of %d:" % evar)
                        for xvar in xlist:
                            outfile.write(" %s:%d" % (str(xvar), xvar.id))
                        outfile.write('\n')
                evarCount += len(alist)
                slist = ['e'] + [str(e) for e in alist] + ['0']
                outfile.write(" ".join(slist) + '\n')
        # Declare remaining universals
        if len(self.qmanager.otherUniversalList) > 0:
            uvarCount += len(self.qmanager.otherUniversalList)
            slist = ['u'] + [str(u) for u in self.qmanager.otherUniversalList] + ['0']
            outfile.write(" ".join(slist) + '\n')
        # Declare explicit existentials
        evarCount += len(self.qmanager.explicitList)
        for evar in self.qmanager.explicitList:
            ulist = self.qmanager.dependencyMap[evar]
            uslist = [str(u) for u in ulist]
            xlist = self.emanager.evarMap[evar]
            for xvar in xlist:
                if verbose and len(xlist) > 1:
                    outfile.write("c Expansion of %d: %s:%d\n" % (evar, str(xvar), xvar.id))
                slist = ['d', str(xvar.id)] + uslist + ['0']
                outfile.write(" ".join(slist) + '\n')
        return (uvarCount, evarCount)
                
    def generateClauses(self, outfile, verbose):
        for eclause in self.expandedClauses:
            cstring = ""
            if verbose:
                cstring = eclause.comment()
                if len(cstring) > 0:
                    outfile.write(cstring + '\n')
            for clause in eclause.clauseList:
                slist = [str(lit) for lit in clause] + ['0']
                outfile.write(" ".join(slist) + '\n')
            if len(cstring) > 0:
                outfile.write("c End of expanded clause\n")

    def generate(self, outroot, verbose = True):
        self.qmanager.organize(verbose)
        suffix = "qdimacs" if len(self.qmanager.explicitList) == 0 else "dqdimacs"
        outname = outroot + '.' + suffix
        try:
            outfile = open(outname, 'w')
        except Exception as ex:
            print("Couldn't open output file '%s'" % outname)
            return
        clauseCount = self.generateHeader(outfile, verbose)
        uvarCount, evarCount = self.generatePrefix(outfile, verbose)
        self.generateClauses(outfile, verbose)
        if verbose:
            print("File %s:  %d evars, %d uvars, %d clauses" % (outname, evarCount, uvarCount, clauseCount))
        outfile.close()
        return (uvarCount, evarCount)

# Attempt splitting into independent subproblems.
# Extension of work by Scholl, et al., AAAI 2019
class Splitter:        
            
    reader = None
    # Partitions of variables such that dependency sets for all variables
    # in an existential partition are wholly contained in corresponding
    # universal partition
    existentialPartition = None
    universalPartition = None
    # Existential variables with empty dependency sets
    independentList = []

    def __init__(self, reader, ignoreTseitin = False):
        self.reader = reader
        self.independentList = []
        upart = Partition([reader.universalList]).singletons()
        llist = reader.dependencyMap.values()
        upart = upart.multiListJoin(llist, ignoreAll = ignoreTseitin)
        self.universalPartition = upart
        if len(upart.psetSet) == 1:
            # Degenerate case
            self.existentialPartition = Partition([reader.existentialList])
            return

        # Build up list of lists for existential partition
        llist = [[] for i in range(len(upart.psetSet))]
        for evar in reader.existentialList:
            ulist = reader.dependencyMap[evar]
            if len(ulist) == 0:
                self.independentList.append(evar)
            else:
                uid = upart.elementMap[ulist[0]]
                llist[uid].append(evar)
        self.existentialPartition = Partition(llist)
            
    def stats(self, outfile=sys.stdout, name="", verbose = 0):
        prefix = "" if name == "" else name + ": "
        pcount = len(self.existentialPartition.psetSet)
        ecount = len(self.reader.existentialList)
        icount = len(self.independentList)
        ucount = len(self.reader.universalList)
        if pcount > 1:
            outfile.write("%s MULTI.  %d partitions.  Universal vars: %d. Existential vars: %d (%d independent).\n" % (prefix, pcount, ucount, ecount, icount))
            if verbose > 1:
                slist = [str(len(pset)) for pset in self.existentialPartition.psetSet]
                outfile.write("  Independent existentials: %d\n" % len(self.independentList))
                outfile.write("  Existential Partitions: %s\n" % ", ".join(slist))
                slist = [str(len(pset)) for pset in self.universalPartition.psetSet]
                outfile.write("  Universal Partitions: %s\n" % ", ".join(slist))
        elif verbose > 1:
            outfile.write("%s SINGLE. Universal vars: %d.  Existential vars: %d (%d independent)\n" % (prefix, ucount, ecount, icount))
        else:
            outfile.write("%s SINGLE\n" % (prefix))
