# Support for representing pseudo Boolean formulas, either
# as set of linear equations (possibly with modular arithmetic)
# or set of linear constraints.
# 
# Modular equations permits solution by Gaussian elimination
# Constraints can be solved by Fourier-Motzin elimination

import sys
import random
import queue

import bdd
import resolver

# Debug: Don't try to justify equational reasoning
noJustify = False

# In case don't have logger
class SimpleWriter:

    def write(self, s):
        sys.stdout.write(s)

# General library for solving pseudo-boolean constraints embedded in
# modular arithmetic

class MathException(Exception):
    form = ""
    msg = ""

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

class ReciprocalException(MathException):
    def __init__(self, num):
        self.form = "No Reciprocal!"
        self.msg = "denominator=%d" % num


class ZeroException(MathException):
    def __init__(self, num):
        self.form = "Zero Divide!"
        self.msg = "numerator=%d" % num


class PivotException(MathException):
    def __init__(self, index):
        self.form = "Pivot=0!"
        self.msg = "index=%d" % index


# Supporting modular arithmetic
# For odd modulus m, use bias k=(m-1)/2
# I.e., Numbers between -k and k to represent range of values
# For even number, will be -k to k+1
class ModMath:

    modulus = 3 # Must be prime
    minValue = -1 # -[(modulus-1)/2] for odd, -[modulus/2-1] for even
    maxValue = 1
    reciprocals = {} # Dictionary mapping x to 1/x
    ## Statistics
    # Number of modular operations
    opcount = 0
    # What values get used in places of interest
    usedValues = {} # 

    def __init__(self, modulus = 3):
        self.reciprocals = {}
        self.modulus = modulus
        self.minValue = -((self.modulus-1)//2)
        self.maxValue = self.minValue + self.modulus - 1
        self.opcount = 0
        for x in range(self.minValue,self.maxValue+1):
            if x == 0:
                continue
            found = False
            for y in range(self.minValue,self.maxValue+1):
                if self.mul(x, y) == 1:
                    self.reciprocals[x] = y
                    found = True
                    break
            if not found:
                raise ReciprocalException(x)
        # Reset count
        self.opcount = 0
        self.usedValues = {}

    # Convert to canonical value
    def mod(self, x):
        mx = x % self.modulus
        if mx > self.maxValue:
            mx -= self.modulus
        return mx

    def values(self):
        return list(range(self.minValue, self.maxValue+1))

    def add(self, x, y):
        self.opcount += 1 
        return self.mod(x+y)

    def mul(self, x, y):
        self.opcount += 1 
        return self.mod(x*y)

    def sub(self, x, y):
        self.opcount += 1 
        return self.mod(x-y)
        
    def neg(self, x):
        return self.mod(-x)

    def recip(self, x):
        if x == 0:
            raise ZeroException(1)
        return self.reciprocals[x]

    def div(self, x, y):
        if y == 0:
            raise ZeroException(y)
        return self.mul(x, self.recip(y))

    def abs(self, x):
        return abs(x)

    def markUsed(self, x):
        self.usedValues[x] = True
        
    def reportUsed(self):
        vlist = sorted(self.usedValues.keys())
        fstring = ", ".join([str(v) for v in vlist])
        return "{" + fstring + "}"

# Equation of form SUM (a_i * x_i)  =  C
# Arithmetic performed over Z_p for prime p
# Only represent nonzero coefficients

class Equation:

    # Variable Count
    N = 10  # Length when format as vector
    # 
    # Mapping for variable Id to coefficient for nonzero coefficient
    nz = {}
    # Class to support math operations
    mbox = None
    cval = 0
    # BDD representation
    root = None
    # Validation step Id
    validation = None

    def __init__(self, N, modulus, cval, mbox = None):
        self.N = N     # Max Variable ID +1
        self.modulus = modulus
        if mbox is None:
            self.mbox = ModMath(modulus)
        elif mbox.modulus != modulus:
            raise Exception("Mismatched moduli")
        else:
            self.mbox = mbox
        self.cval = self.mbox.mod(cval)
        self.nz = {}
        self.root = None
        self.validation = None

    def setNz(self, nz):
        self.nz = nz

    def __getitem__(self, i):
        return self.nz[i] if i in self.nz else 0

    def __setitem__(self, i, v):
        self.mbox.markUsed(v)
        if v == 0:
            if self.nz:
                del self.nz[i]
        else:
            self.nz[i] = v

    def indices(self):
        return sorted(self.nz.keys())

    # Length defined to be the number of nonzeros
    def __len__(self):
        return len(self.nz)

    def formatDense(self):
        vec = [0 for i in range(self.N)]
        for i in self.indices():
            vec[i] = self[i]
        return str(vec + [self.cval])

    def formatSparse(self):
        slist = []
        for i in self.indices():
            v = self[i]
            slist.append("%d:%d" % (i, v))
        slist.append("=%d" % self.cval)
        return '[' + " ".join(slist) + ']'

    # Generate new equation from new set of nonzeros
    # operandList is set of equations used to generate this one
    # Use to generate proof that set of operand equations implies new equation
    def spawn(self, nnz, cval, esys, operandList):
        e = Equation(self.N, self.modulus, cval, self.mbox)
        e.nz = nnz
        e.buildBdd(esys)
        if noJustify:
            return e
        rvList = [(eq.root,eq.validation) for eq in operandList]
        done = False
        while not done and len(rvList) > 2:
            r1,v1 = rvList[0]
            r2,v2 = rvList[1]
            validation = None
            antecedents = [v1,v2]
            nr,imp = esys.manager.applyAndJustify(r1, r2)
            if nr == esys.manager.leaf0:
                comment = "Validation of Empty clause"
                done = True
            else:
                comment = "Validation of %s" % nr.label()
            if imp == resolver.tautologyId:
                if nr == r1:
                    validation = v1
                elif nr == r2:
                    validation = v2
            else:
                antecedents += [imp]
            if validation is None:
                validation = esys.manager.prover.createClause([nr.id], antecedents, comment)
            rvList = [(nr,validation)] + rvList[2:]
        if not done and len(rvList) == 2:
            # Do final conjunction and implication in combination
            r1,v1 = rvList[0]
            r2,v2 = rvList[1]
            antecedents = [v1,v2]
            check, implication = esys.manager.applyAndJustifyImply(r1, r2, e.root)
            if not check:
                esys.writer.write("WARNING: Implication failed when spawning equation %s: %s & %s -/-> %s\n" % (str(e), r1.label(), r2.label(), e.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            done = e.root == esys.manager.leaf0
            if done:
                comment = "Validation of empty clause from infeasible equation"
            else:
                comment = "Validation of equation with BDD root %s" % e.root.label()
            e.validation = esys.manager.prover.createClause([e.root.id], antecedents, comment)
        if not done and len(rvList) == 1:
            (r1, v1) = rvList[0]
            antecedents = [v1]
            check, implication = esys.manager.justifyImply(r1, e.root)
            if not check:
                esys.writer.write("WARNING: Implication failed when spawning equation %s: %s -/-> %s\n" % (str(e), r1.label(), e.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            done = e.root == esys.manager.leaf0
            if done:
                comment = "Validation of empty clause from infeasible equation"
            else:
                comment = "Validation of equation with BDD root %s" % e.root.label()
            e.validation = esys.manager.prover.createClause([e.root.id], antecedents, comment)
        if done:
            esys.writer.write("UNSAT\n")
            esys.manager.summarize()
        return e

    
    # Normalize vector so that element at pivot position == 1
    # By dividing all entries by the existing value
    # Returns new vector
    def normalize(self, pidx, esys):
        pval = self[pidx]
        if pval == 0:
            raise PivotException(pidx)
        if pval == 1:
            return self
        nnz = { i : self.mbox.div(self[i], pval) for i in self.indices() }
        nc = self.mbox.div(self.cval, pval)
        return self.spawn(nnz, nc, esys, [self])
        
    # Helper function for inserting new element in dictionary
    def nzInsert(self, nz, i, v):
        if v == 0 and i in nz:
            del nz[i]
        else:
            nz[i] = v

    # Add other vector to self
    def add(self, other, esys):
        nnz = { i : self[i] for i in self.indices() }
        for i in other.indices():
            nx = self.mbox.add(self[i], other[i])
            self.mbox.markUsed(nx)
            self.nzInsert(nnz, i, nx)
        nc = self.mbox.add(self.cval, other.cval)
        return self.spawn(nnz, nc, esys, [self, other])

    # Subtract other vector from self
    def sub(self, other, esys):
        nnz = { i : self[i] for i in self.indices() }
        for i in other.indices():
            nx = self.mbox.sub(self[i], other[i])
            self.mbox.markUsed(nx)
            self.nzInsert(nnz, i, nx)
        nc = self.mbox.sub(self.cval, other.cval)
        return self.spawn(nnz, nc, esys, [self, other])

    # Generate BDD representation
    def buildBdd(self, esys):
        ilist = self.indices()
        if len(ilist) == 0:
            self.root = esys.manager.leaf1 if self.cval == 0 else esys.manager.leaf0
            return

        ilist.sort(key = lambda id : esys.levelMap[id])

        # Determine at what offsets will need node, starting from root and working down
        needNodes = { i : {} for i in ilist }
        previ = ilist[0]
        needNodes[previ][0] = True
        for nexti in ilist[1:]:
            for offset in needNodes[previ].keys():
                # Will need this offset when variable evaluates to 0
                needNodes[nexti][offset] = True
                # Will need this offset when variable evaluates to 1
                noffset = esys.mbox.add(offset, self[previ])
                needNodes[nexti][noffset] = True
            previ = nexti

        # Now build BDD from bottom up
        rilist = list(ilist)
        rilist.reverse()
        leafList = { offset : (esys.manager.leaf1 if offset == self.cval else esys.manager.leaf0) for offset in esys.mbox.values() }
        nodes = { i : {} for i in rilist }

        lasti = rilist[0]
        for offset in needNodes[lasti].keys():
            low = leafList[offset]
            noffset = esys.mbox.add(offset, self[lasti])
            high = leafList[noffset]
            var = esys.varMap[lasti]
            root = low if low == high else esys.manager.findOrMake(var, high, low)
            nodes[lasti][offset] = root

        nexti = lasti
        for previ in rilist[1:]:
            for offset in needNodes[previ].keys():
                low = nodes[nexti][offset]
                noffset = esys.mbox.add(offset, self[previ])
                high = nodes[nexti][noffset]
                var = esys.varMap[previ]
                root = low if low == high else esys.manager.findOrMake(var, high, low)
                nodes[previ][offset] = root
            nexti = previ
            
        self.root = nodes[ilist[0]][0]

        

    # Perform scaling subtraction
    # Must scale other vector by value at pivot position before subtracting
    def scaleSub(self, other, pidx, esys):
        nnz = { i : self[i] for i in self.indices() }
        sval = 0
        sval = self[pidx]
        if sval != 0:
            for i in other.indices():
                x = self[i]
                dx = self.mbox.mul(sval, other[i])
                nx = self.mbox.sub(x, dx)
                self.mbox.markUsed(nx)
                self.nzInsert(nnz, i, nx)
                nc = self.mbox.sub(self.cval, self.mbox.mul(sval, other.cval))
        return self.spawn(nnz, nc, esys, [self, other])

    # Lexicographic ordering of equations
    def isGreater(self, other):
        for i in range(self.N):
            if self[i] > other[i]:
                return True
            if self[i] < other[i]:
                return False
        return False
    
    # Does this equation have no solution with modular arithmetic
    def isInfeasible(self):
        # All zero coefficients and non-zero constant
        return self.cval != 0 and len(self) == 0


    def __str__(self):
        if self.N <= 0:
            return self.formatDense()
        else:
            return self.formatSparse()


# Maintain set of sparse equations, including index from each index i to those equations having nonzero value there
class EquationSet:
    # Unique ID assigned when registered
    nextId = 1
    # Mapping from id to equation
    equDict = {}
    # Mapping from index to list of equation IDs having nonzero entry at that index
    nzMap = {}
    # Total number of nonzero terms added
    termCount = 0
    # Largest equation added
    termMax = 0

    def __init__(self, elist = [], writer = None):
        self.nextId = 1
        self.writer = SimpleWriter() if writer is None else writer
        self.equDict = {}
        self.nzMap = {}
        self.termCount = 0
        self.termMax = 0
        for e in elist:
            self.addEquation(e)

    def addIndex(self, eid, idx):
        if idx in self.nzMap:
            self.nzMap[idx].append(eid)
        else:
            self.nzMap[idx] = [eid]

    def removeIndex(self, eid, idx):
        nlist = [j for j in self.nzMap[idx] if j != eid]
        if len(nlist) == 0:
            del self.nzMap[idx]
        else:
            self.nzMap[idx] = nlist

    def analyzeEquation(self, e):
        count = len(e)
        self.termCount += count
        self.termMax = max(self.termMax, count)

    def addEquation(self, e):
        eid = self.nextId
        self.nextId += 1
        self.equDict[eid] = e
        for idx in e.nz:
            self.addIndex(eid, idx)
        self.analyzeEquation(e)
        return eid

    def removeEquation(self, eid):
        e = self[eid]
        for idx in e.nz:
            self.removeIndex(eid, idx)
        del self.equDict[eid]

    def lookup(self, idx):
        if idx in self.nzMap:
            return self.nzMap[idx]
        else:
            return []

    def rootList(self):
        return [e.root for e in self.equDict.values()]

    def __getitem__(self, id):
        return self.equDict[id]
        
    def __len__(self):
        return len(self.equDict)

    def currentEids(self):
        return list(self.equDict.keys())

    def currentIndices(self):
        return list(self.nzMap.keys())

    def show(self):
        eidList = sorted(self.currentEids())
        for eid in eidList:
            self.writer.write("   #%d:%s\n" % (eid, str(self[eid])))

    # How many total equations have been generated
    def equationCount(self):
        return self.nextId - 1

# System of equations.
# Support LU decomposition of Gaussian elimination to see if system has any solutions
class EquationSystem:
    # Variable Count
    N = 10
    modulus = 3
    verbose = False
    randomize = False
    # Class to support math operations
    mbox = None
    writer = None

    # Optionally: Reduce some of the equations via summations before solving
    # List of lists, each giving equations IDs to sum
    presums = []

    ## Solver state
    # Eliminated equations
    sset = None
    # Remaining equations
    rset = None

    # Supporting BDD operation
    manager = None
    # Mapping from variable Id to variable
    varMap = None
    # Mapping from variable Id to level
    levelMap = None


    # Tracking number of equations generated since last GC
    equationCount = 0
    # How often should GC be performed?
    gcThreshold = 50

    ## Accumulating data
    # Mapping from variable ID to True
    varUsed = {}
    # Total number of elimination steps
    stepCount = 0
    # Sum of pivot degrees
    pivotDegreeSum = 0
    # Max of pivot degrees
    pivotDegreeMax = 0
    # Total number of vector operations
    combineCount = 0

    def __init__(self, N, modulus, verbose = True, manager = None, writer = None):
        self.N = N
        self.modulus = modulus
        self.verbose = verbose
        self.manager = manager
        if manager is not None:
            self.varMap = { var.id : var for var in manager.variables }
            self.levelMap = { var.id : var.level for var in manager.variables }

        self.writer = SimpleWriter() if writer is None else writer
        self.randomize = False
        self.mbox = ModMath(modulus)
        self.sset = EquationSet(writer = self.writer)
        self.rset = EquationSet(writer = self.writer)
        self.varUsed = {}
        self.stepCount = 0
        self.pivotDegreeSum = 0
        self.pivotDegreeMax = 0
        self.combineCount = 0
        self.equationCount = 0

    # Add new equation to main set
    def addEquation(self, e):
        eid = self.rset.addEquation(e)
        for i in e.nz:
            self.varUsed[i] = True
        if self.manager is not None:
            e.buildBdd(self)
        return eid

    # Add presum list
    def addPresum(self, elist):
        self.presums.append(elist)

    # Reduce set of equationss (given by their eid's) by summing
    def sumReduce(self, elist):
        if len(elist) == 0:
            return
        # This is a hack to enable randomized removal of equal weighted items from priority queue
        # and to make sure that priority queue has totally ordered keys
        # Have enough entries in the list to cover initial equations and partial sums
        olist = list(range(2*len(elist)))
        if self.randomize:
            random.shuffle(olist)
        # Put elements into priority queue according to nnz's
        pq = queue.PriorityQueue()
        for idx in range(len(elist)):
            oid = olist[idx]
            eid = elist[idx]
            e = self.rset[eid]
            self.rset.removeEquation(eid)                
            pq.put((len(e), oid, e))
        # Now start combining them
        idx = len(elist)
        while pq.qsize() > 1:
            (w1, o1, e1) = pq.get()
            (w2, o2, e2) = pq.get()
            ne = e1.add(e2, self)
            oid = olist[idx]
            if pq.qsize() > 0:
                # Gather statistics on this equation, even though won't be added to rset
                self.rset.analyzeEquation(ne)
            pq.put((len(ne), oid, ne))
            idx += 1
        # Reduced queue to single element
        (w, o, e) = pq.get()
        self.rset.addEquation(e)
        self.checkGC()

    # Reduce set of equations by summing
    def presum(self):
        icount = len(self.rset)
        for elist in self.presums:
            self.sumReduce(elist)
        ncount = len(self.rset)
        if ncount < icount:
            self.writer.write("Presumming reduced equations from %d to %d\n" % (icount, ncount))

    # Given possible pivot index
    # find best equation to use as pivot equation and
    # give score for its selection
    # If there are no nonzeros with this index, return None for the equation ID
    def evaluatePivot(self, pidx):
        eidList = self.rset.lookup(pidx)
        bestEid = None
        # Lowest degree row
        bestRd = 0
        # Make sure that any ties are broken arbitrarily
        # rather than as some artifact of the input file
        if self.randomize:
            random.shuffle(eidList)

        for eid in eidList:
            e = self.rset[eid]
            rd = len(e)
            if bestEid is None or rd < bestRd:
                bestEid = eid
                bestRd = rd

        # Score based on worst-case fill generated
        # Also favors unit and singleton equations
        score = (bestRd-1) * (len(eidList)-1)
        return (bestEid, score)

    # Given remaining set of equations, select pivot element and equation id
    def selectPivot(self):
        bestPidx = None
        bestScore = 0
        bestEid = None
        idList = self.rset.currentIndices()
        # Make sure that any ties are broken arbitrarily
        # rather than as some artifact of the input file
        if self.randomize:
            random.shuffle(idList)
        for pidx in idList:
            (eid, score) = self.evaluatePivot(pidx)
            if eid is not None and (bestEid is None or score < bestScore):
                bestPidx = pidx
                bestScore = score
                bestEid = eid
        if bestEid is not None:
            pd = len(self.rset[bestEid])
            self.pivotDegreeSum += pd
            self.pivotDegreeMax = max(self.pivotDegreeMax, pd)
        return (bestPidx, bestEid)

    # Perform one step of LU decomposition
    # Possible return values:
    # "solved", "unsolvable", "normal"
    def solutionStep(self):
        if len(self.rset) == 0:
            return "solved"
        self.stepCount += 1
        (pidx, eid) = self.selectPivot()
        if pidx is None:
            return "solved"

        e = self.rset[eid]
        self.rset.removeEquation(eid)
        self.sset.addEquation(e)
        pval = e[pidx]
        if self.verbose:
            self.writer.write("Pivoting with value %d (element %d).  Using equation #%d\n" % (pval, pidx, eid))
        ne = e.normalize(pidx, self)

        otherEids =  self.rset.lookup(pidx)
        for oeid in otherEids:
            oe = self.rset[oeid]
            self.rset.removeEquation(oeid)
            re = oe.scaleSub(ne, pidx, self)
            if re.isInfeasible():
                return "unsolvable"
            self.rset.addEquation(re)
            self.combineCount += 1
            self.checkGC()
        return "normal"
            
    def solve(self):
        self.sset = EquationSet(writer = self.writer)
        if self.verbose:
            self.writer.write("  Initial state\n")
            self.showState()
        # Scan equations to see if any are infeasible
        for eid in self.rset.currentEids():
            e = self.rset[eid]
            if e.isInfeasible():
                return "unsolvable"
        status = "normal"

        # Perform any presumming
        self.presum()

        while True:
            status = self.solutionStep()
            # "solved", "unsolvable", "normal"
            if status != "normal":
                break
            if self.verbose:
                self.showState()
        if self.verbose:
            self.writer.write("  Solution status:%s\n" % status)
            self.postStatistics(status)
        return status

    def checkGC(self):
        self.equationCount += 1
        if self.equationCount > self.gcThreshold:
            clauseList = self.manager.collectGarbage()
            self.equationCount = 0
            if len(clauseList) > 0:
                self.manager.prover.deleteClauses(clauseList)

    def show(self):
        self.rset.show()
    
    def showState(self):
        self.writer.write("  Processed:\n")
        self.sset.show()
        self.writer.write("  Remaining:\n")
        self.rset.show()

    def showRemainingState(self):
        self.rset.show()
            
    def preStatistics(self):
        ecount = self.rset.equationCount()
        vcount = self.N
        acount = len(self.varUsed)
        tc = self.rset.termCount
        tmax = self.rset.termMax
        tavg = float(tc)/ecount
        self.writer.write("  Problem: %d equations, %d variables, %d nonzero coefficients.  %d total nonzeros (%.2f avg, %d max)\n" % (ecount, vcount, acount, tc, tavg, tmax))

    def postStatistics(self, status):
        # status: "solved", "unsolvable", "normal"
        self.writer.write("  Solution status: %s\n" % (status))
        sscount = self.stepCount
        pavg = float(self.pivotDegreeSum)/sscount
        pmax = self.pivotDegreeMax
        self.writer.write("  Solving: %d steps.  %.2f avg pivot degree (max=%d)\n" % (sscount, pavg, pmax))
        ecount = self.rset.equationCount()
        ccount = self.combineCount
        tc = self.rset.termCount
        tmax = self.rset.termMax
        tavg = float(tc)/ecount
        self.writer.write("    %d total equations.  %d total nonzeros (%.2f avg, %d max).  %d vector operations\n" % (ecount, tc, tavg, tmax, ccount))
        self.writer.write("    %d modular operations.  Used values = %s\n" % (self.mbox.opcount, self.mbox.reportUsed()))


# Support for manipulating constraints of the form
# SUM (a_i * x_i) >= c
# where each a_i is positive or negative integer
# x_i is Boolean

class ConstraintException(Exception):
    form = "Constraint Error"
    msg = ""

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

# Constraint of form SUM (a_i * x_i)  >=  c
# Only represent nonzero coefficients

class Constraint:

    # Variable Count
    N = 10  # Length when format as vector
    # 
    # Mapping for variable Id to coefficient for nonzero coefficient
    nz = {}
    cval = 0
    # BDD representation
    root = None
    # Validation step Id
    validation = None

    def __init__(self, N, cval):
        self.N = N     # Max Variable ID +1
        self.cval = cval
        self.nz = {}
        self.root = None
        self.validation = None

    def setNz(self, nz):
        self.nz = nz

    def __getitem__(self, i):
        return self.nz[i] if i in self.nz else 0

    def __setitem__(self, i, v):
        if v == 0:
            if self.nz:
                del self.nz[i]
        else:
            self.nz[i] = v

    def indices(self):
        return sorted(self.nz.keys())

    # Length defined to be the number of nonzeros
    def __len__(self):
        return len(self.nz)

    def formatDense(self):
        vec = [0 for i in range(self.N)]
        for i in self.indices():
            vec[i] = self[i]
        return str(vec + [self.cval])

    def formatSparse(self):
        slist = []
        for i in self.indices():
            v = self[i]
            slist.append("%d:%d" % (i, v))
        slist.append(">=%d" % self.cval)
        return '[' + " ".join(slist) + ']'

    # Generate new constraint from new set of nonzeros
    def spawn(self, nnz, cval, csys, operandList):
        con = Constraint(self.N, cval)
        con.nz = nnz
        con.buildBdd(csys)
        if noJustify:
            return con
        rvList = [(c.root, c.validation) for c in operandList]
        done = False
        while not done and len(rvList) > 2:
            r1,v1 = rvList[0]
            r2,v2 = rvList[1]
            validation = None
            antecedents = [v1,v2]
            nr, imp = csys.manager.applyAndJustify(r1, r2)
            if nr == csys.manager.leaf0:
                comment = "Validation of Empty clause"
                done = True
            else:
                comment = "Validation of %s" % nr.label()
            if imp == resolver.tautologyId:
                if nr == r1:
                    validation = v1
                elif nr == r2:
                    validation = v2
            else:
                antecedents += [imp]
            if validation is None:
                validation = csys.manager.prover.createClause([nr.id], antecedents, comment)
            rvList = [(nr,validation)] + rvList[2:]
        if not done and len(rvList) == 2:
            # Do final conjunction and implication in combination
            r1,v1 = rvList[0]
            r2,v2 = rvList[1]
            antecedents = [v1,v2]
            check, implication = csys.manager.applyAndJustifyImply(r1, r2, con.root)
            if not check:
                csys.writer.write("WARNING: Implication failed when spawning constraint %s: %s & %s -/-> %s\n" % (str(con), r1.label(), r2.label(), con.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            done = con.root == csys.manager.leaf0
            if done:
                comment = "Validation of empty clause from infeasible constraint"
            else:
                comment = "Validation of constraint with BDD root %s" % con.root.label()
            con.validation = csys.manager.prover.createClause([con.root.id], antecedents, comment)
        if not done and len(rvList) == 1:
            r1,v1 = rvList[0]
            antecedents = [v1]
            check, implication = csys.manager.justifyImply(r1, con.root)
            if not check:
                csys.writer.write("WARNING: Implication failed when spawning constraint %s: %s -/-> %s\n" % (str(con), r1.label(), con.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            done = con.root == csys.manager.leaf0
            if done:
                comment = "Validation of empty clause from infeasible constraint"
            else:
                comment = "Validation of constraint with BDD root %s" % con.root.label()
            con.validation = csys.manager.prover.createClause([con.root.id], antecedents, comment)
        if done:
            csys.writer.write("UNSAT\n")
            csys.manager.summarize()
        return con
        
    # Helper function for inserting new element in dictionary
    def nzInsert(self, nz, i, v):
        if v == 0 and i in nz:
            del nz[i]
        else:
            nz[i] = v

    # Add other constraint to self
    def add(self, other, csys):
        nnz = { i : self[i] for i in self.indices() }
        for i in other.indices():
            nx = self[i] + other[i]
            self.nzInsert(nnz, i, nx)
        nc = self.cval + other.cval
        return self.spawn(nnz, nc, csys, [self, other])

    # Generate at-least-one constraint
    def alo(self, vlist, csys):
        nnz = { i : 1 for i in vlist }
        cval = 1
        return self.spawn(nnz, cval, csys, [self, other])

    # Generate at-most-one constraint
    def amo(self, vlist, csys):
        nnz = { i : -1 for i in vlist }
        cval = -1
        return self.spawn(nnz, cval, csys, [self, other])

    # Generate at-most-zero constraint
    # (i.e., all must be false)
    def amz(self, vlist, csys):
        nnz = { i : -1 for i in vlist }
        cval = 0
        return self.spawn(nnz, cval, csys, [self, other])

    # Generate BDD representation
    def buildBdd(self, csys):
        ilist = self.indices()
        if len(ilist) == 0:
            self.root = csys.manager.leaf1 if self.cval <= 0 else csys.manager.leaf0
            return

        ilist.sort(key = lambda id : csys.levelMap[id])

        # Determine at what offsets will need node, starting from root and working down
        needNodes = { i : {} for i in ilist }
        previ = ilist[0]
        needNodes[previ][0] = True
        for nexti in ilist[1:]:
            for offset in needNodes[previ].keys():
                # Will need this offset when variable evaluates to 0
                needNodes[nexti][offset] = True
                # Will need this offset when variable evaluates to 1
                noffset = offset + self[previ]
                needNodes[nexti][noffset] = True
            previ = nexti

        # Now build BDD from bottom up
        rilist = list(ilist)
        rilist.reverse()

        # Start at leaves.  Determine possible offsets
        lasti = rilist[0]
        needLeaves = {}
        for offset in needNodes[lasti].keys():
            needLeaves[offset] = True
            noffset = offset + self[lasti]
            needLeaves[noffset] = True

        leafList = { offset : (csys.manager.leaf1 if offset >= self.cval else csys.manager.leaf0) for offset in needLeaves.keys() }
        nodes = { i : {} for i in rilist }

        for offset in needNodes[lasti].keys():
            low = leafList[offset]
            noffset = offset + self[lasti]
            high = leafList[noffset]
            var = csys.varMap[lasti]
            root = low if low == high else csys.manager.findOrMake(var, high, low)
            nodes[lasti][offset] = root

        nexti = lasti
        for previ in rilist[1:]:
            for offset in needNodes[previ].keys():
                low = nodes[nexti][offset]
                noffset = offset + self[previ]
                high = nodes[nexti][noffset]
                var = csys.varMap[previ]
                root = low if low == high else csys.manager.findOrMake(var, high, low)
                nodes[previ][offset] = root
            nexti = previ
            
        self.root = nodes[ilist[0]][0]



    # Lexicographic ordering of constraints
    def isGreater(self, other):
        for i in range(self.N):
            if self[i] > other[i]:
                return True
            if self[i] < other[i]:
                return False
        return self.cval > other.cval
    
    # Does this constraint have no solution
    def isInfeasible(self):
        maxsum = 0
        for v in self.nz.values():
            if v > 0:
                maxsum += v
        return maxsum < self.cval

    def __str__(self):
        if self.N <= 0:
            return self.formatDense()
        else:
            return self.formatSparse()


# Maintain set of sparse constraints, including index from each index i to those constraints having nonzero value there
class ConstraintSet:
    # Unique ID assigned when registered
    nextId = 1
    # Mapping from id to constraint
    conDict = {}
    # Mapping from index to list of constraint IDs having nonzero entry at that index
    nzMap = {}
    # Total number of nonzero terms added
    termCount = 0
    # Largest constraint added
    termMax = 0

    def __init__(self, clist = [], writer = None):
        self.nextId = 1
        self.writer = SimpleWriter() if writer is None else writer
        self.conDict = {}
        self.nzMap = {}
        self.termCount = 0
        self.termMax = 0
        for con in clist:
            self.addConstraint(con)

    def addIndex(self, cid, idx):
        if idx in self.nzMap:
            self.nzMap[idx].append(cid)
        else:
            self.nzMap[idx] = [cid]

    def removeIndex(self, cid, idx):
        nlist = [j for j in self.nzMap[idx] if j != cid]
        if len(nlist) == 0:
            del self.nzMap[idx]
        else:
            self.nzMap[idx] = nlist

    def analyzeConstraint(self, con):
        count = len(con)
        self.termCount += count
        self.termMax = max(self.termMax, count)

    def addConstraint(self, con):
        cid = self.nextId
        self.nextId += 1
        self.conDict[cid] = con
        for idx in con.nz:
            self.addIndex(cid, idx)
        self.analyzeConstraint(con)
        return cid

    def removeConstraint(self, cid):
        con = self[cid]
        for idx in con.nz:
            self.removeIndex(cid, idx)
        del self.conDict[cid]

    def lookup(self, idx):
        if idx in self.nzMap:
            return self.nzMap[idx]
        else:
            return []

    def rootList(self):
        return [con.root for con in self.conDict.values()]

    def __getitem__(self, id):
        return self.conDict[id]
        
    def __len__(self):
        return len(self.conDict)

    def currentCids(self):
        return list(self.conDict.keys())

    def currentIndices(self):
        return list(self.nzMap.keys())

    def show(self):
        cidList = sorted(self.currentCids())
        for cid in cidList:
            self.writer.write("   #%d:%s\n" % (cid, str(self[cid])))

    # How many total constraints have been generated
    def constraintCount(self):
        return self.nextId - 1

# System of constraints.
# Support adding constraints to see if can detect conflict
class ConstraintSystem:
    # Variable Count
    N = 10
    verbose = False
    randomize = False
    writer = None

    # Optionally: Reduce some of the constraints via summations before solving
    # List of lists, each giving constraints IDs to sum
    presums = []

    ## Solver state
    # Eliminated constraints
    sset = None
    # Remaining constraints
    rset = None

    # Supporting BDD operation
    manager = None
    # Mapping from variable Id to variable
    varMap = None
    # Mapping from variable Id o level
    levelMap = None

    # Tracking number of constraints generated since last GC
    constraintCount = 0
    # How often should GC be performed?
    gcThreshold = 50

    ## Accumulating data
    # Total number of elimination steps
    stepCount = 0
    # Sum of pivot degrees
    pivotDegreeSum = 0
    # Max of pivot degrees
    pivotDegreeMax = 0
    # Total number of vector operations
    combineCount = 0


    # Mapping from variable ID to True
    varUsed = {}


    def __init__(self, N, verbose = True, manager = None, writer = None):
        self.N = N
        self.verbose = verbose
        self.manager = manager
        if manager is not None:
            self.varMap = { var.id : var for var in manager.variables }
            self.levelMap = { var.id : var.level for var in manager.variables }
        self.writer = SimpleWriter() if writer is None else writer
        self.randomize = False
        self.sset = ConstraintSet(writer = self.writer)
        self.rset = ConstraintSet(writer = self.writer)
        self.varUsed = {}

    # Add new constraint to main set
    def addConstraint(self, con):
        cid = self.rset.addConstraint(con)
        for i in con.nz:
            self.varUsed[i] = True
        if self.manager is not None:
            con.buildBdd(self)
        return cid

    # Add presum list
    def addPresum(self, clist):
        self.presums.append(clist)

    # Reduce set of constraints (given by their cid's) by summing
    def sumReduce(self, clist):
        if len(clist) == 0: 
            return
        # This is a hack to enable randomized removal of equal weighted items from priority queue
        # and to make sure that priority queue has totally ordered keys
        # Have enough entries in the list to cover initial constraints and partial sums
        olist = list(range(2*len(clist)))
        if self.randomize:
            random.shuffle(olist)
        # Put elements into priority queue according to nnz's
        pq = queue.PriorityQueue()
        for idx in range(len(clist)):
            oid = olist[idx]
            cid = clist[idx]
            con = self.rset[cid]
            self.rset.removeConstraint(cid)                
            pq.put((len(con), oid, con))
        # Now start combining them
        idx = len(clist)
        while pq.qsize() > 1:
            (w1, o1, con1) = pq.get()
            (w2, o2, con2) = pq.get()
            ncon = con1.add(con2, self)
            oid = olist[idx]
            if pq.qsize() > 0:
                # Gather statistics on this constraint, even though won't be added to rset
                self.rset.analyzeConstraint(ncon)
            pq.put((len(ncon), oid, ncon))
            idx += 1
        # Reduced queue to single element
        (w, o, con) = pq.get()
        self.rset.addConstraint(con)
        self.checkGC()

    # Reduce set of constraints by summing
    def presum(self):
        icount = len(self.rset)
        for clist in self.presums:
            self.sumReduce(clist)
        ncount = len(self.rset)
        if ncount < icount:
            self.writer.write("Presumming reduced constraints from %d to %d\n" % (icount, ncount))

    # Given possible pivot index, give a score
    def evaluatePivot(self, pidx):
        cidList = self.rset.lookup(pidx)
        posIndices = [cid for cid in cidList if self.rset[cid][pidx] > 0]
        negIndices = [cid for cid in cidList if self.rset[cid][pidx] < 0]
        score = 0
        for pid in posIndices:
            for nid in negIndices:
                score += len(self.rset[pid]) + len(self.rset[nid]) - 2
        return score

    # Given remaining set of constraints, select pivot element and constraint id
    def selectPivot(self):
        bestPidx = None
        bestScore = 0
        idList = self.rset.currentIndices()
        # Make sure that any ties are broken arbitrarily
        # rather than as some artifact of the input file
        if self.randomize:
            random.shuffle(idList)
        for pidx in idList:
            score = self.evaluatePivot(pidx)
            if bestPidx is None or score < bestScore:
                bestPidx = pidx
                bestScore = score
        return bestPidx

    # Perform one step of FM reduction
    # Possible return values:
    # "solved", "unsolvable", "normal"
    def solutionStep(self):
        if len(self.rset) == 0:
            return "solved"
        self.stepCount += 1
        pidx = self.selectPivot()
        if pidx is None:
            return "solved"
        


        cidList = self.rset.lookup(pidx)
        posIndices = [cid for cid in cidList if self.rset[cid][pidx] > 0]
        negIndices = [cid for cid in cidList if self.rset[cid][pidx] < 0]

        if self.verbose:
            self.writer.write("Pivoting at element %d.  %d positive, %d negative constraints\n" % (pidx, len(posIndices), len(negIndices)))
        
        for pid in posIndices:
            pcon = self.rset[pid]
            for nid in negIndices:
                ncon = self.rset[nid]
                scon = pcon.add(ncon, self)
                if scon.isInfeasible():
                    return "unsolvable"
                self.rset.addConstraint(scon)
                self.combineCount += 1
                self.checkGC()

        for cid in cidList:
            self.rset.removeConstraint(cid)

        return "normal"
            
    def solve(self):
        self.sset = ConstraintSet(writer = self.writer)
        if self.verbose:
            self.writer.write("  Initial state\n")
            self.showState()
        # Scan constraints to see if any are infeasible
        for cid in self.rset.currentCids():
            con = self.rset[cid]
            if con.isInfeasible():
                return "unsolvable"
        status = "normal"

        # Perform any presumming
        self.presum()

        while True:
            status = self.solutionStep()
            # "solved", "unsolvable", "normal"
            if status != "normal":
                break
            if self.verbose:
                self.showState()
        if self.verbose:
            self.writer.write("  Solution status:%s\n" % status)
            self.postStatistics(status)
        return status

    def oldSolve(self):
        self.sset = ConstraintSet(writer = self.writer)
        if self.verbose:
            self.writer.write("  Initial state\n")
            self.showState()
        # Scan constraints to see if any are infeasible
        for cid in self.rset.currentCids():
            con = self.rset[cid]
            if con.isInfeasible():
                return "unsolvable\n"
        status = "normal"

        # Perform any presumming
        self.presum()

        self.sumReduce(self.rset.currentCids())

        lastCid = self.rset.currentCids()[0]
        lastCon = self.rset[lastCid]

        status =  "unsolvable" if  lastCon.isInfeasible() else "solvable"

        if self.verbose:
            self.writer.write("  Solution status:%s\n" % status)
            self.postStatistics(status)
        return status

    def checkGC(self):
        self.constraintCount += 1
        if self.constraintCount > self.gcThreshold:
            clauseList = self.manager.collectGarbage()
            self.constraintCount = 0
            if len(clauseList) > 0:
                self.manager.prover.deleteClauses(clauseList)

    def show(self):
        self.rset.show()
    
    def showState(self):
        self.writer.write("  Processed:\n")
        self.sset.show()
        self.writer.write("  Remaining:\n")
        self.rset.show()

    def showRemainingState(self):
        self.rset.show()
            
    def preStatistics(self):
        ccount = self.rset.constraintCount()
        vcount = self.N
        acount = len(self.varUsed)
        tc = self.rset.termCount
        tmax = self.rset.termMax
        tavg = float(tc)/ccount
        self.writer.write("  Problem: %d constraints, %d variables, %d nonzero coefficients.  %d total nonzeros (%.2f avg, %d max)\n" % (ccount, vcount, acount, tc, tavg, tmax))

    def postStatistics(self, status):
        # status: "solved", "unsolvable", "normal"
        self.writer.write("  Solution status: %s\n" % (status))
        ccount = self.rset.constraintCount()
        tc = self.rset.termCount
        tmax = self.rset.termMax
        tavg = float(tc)/ccount
        self.writer.write("    %d total constraints.  %d total nonzeros (%.2f avg, %d max).\n" % (ccount, tc, tavg, tmax))
        
        
