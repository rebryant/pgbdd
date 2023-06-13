#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
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

# Modulus options.  Values > 2 are actual moduli
modulusNone = -1
modulusAuto = 0

# Performance choices
# Use randomization to break ties in pivot selection
randomizePivots = True
# Delay BDD evaluation
delayJustification = True

# In case don't have logger
class SimpleWriter:

    def write(self, s):
        sys.stdout.write(s)

class PseudoBooleanException(Exception):
    form = ""
    msg = ""

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m


class ZeroException(PseudoBooleanException):
    def __init__(self, num):
        self.form = "Zero Divide!"
        self.msg = "numerator=%d" % num

class ReciprocalException(PseudoBooleanException):
    def __init__(self, num):
        self.form = "No reciprocal!"
        self.msg = "value=%d" % num


class PivotException(PseudoBooleanException):
    def __init__(self, index):
        self.form = "Pivot=0!"
        self.msg = "index=%d" % index

class QueueException(PseudoBooleanException):
    def __init__(self, msg):
        self.form = "Empty Priority Queue!"
        self.msg = msg

class FourierMotzinException(PseudoBooleanException):
    def __init__(self, values):
        self.form = "Out-of-range pivot!"
        self.msg = "oob values=%s" % str(values)

class ProofGenerationException(PseudoBooleanException):
    def __init__(self, values):
        self.form = "Proof Generation Failure"
        self.msg = "oob values=%s" % str(values)
    

# Supporting modular arithmetic
# For odd modulus m, use bias k=(m-1)/2
# I.e., Numbers between -k and k to represent range of values
# For even number, will be -k to k+1

# Modulus of <= 0 means do true integer arithmetic.  Reciprocals only valid for -1 and +1
# Allow non-prime moduli, even though not all reciprocals will be valid
class ModMath:
    modulus = modulusAuto
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
        self.setModulus(modulus)
        # Reset count
        self.opcount = 0
        self.usedValues = {}

    def setModulus(self, modulus):
        self.reciprocals = {}
        self.modulus = modulus
        if modulus > 0:
            self.minValue = -((self.modulus-1)//2)
            self.maxValue = self.minValue + self.modulus - 1
        else:
            self.minValue = -1
            self.maxValue = +1
        self.opcount = 0
        
        # Find those reciprocals that exist
        for x in range(self.minValue,self.maxValue+1):
            if x == 0:
                continue
            for y in range(self.minValue,self.maxValue+1):
                if self.mul(x, y) == 1:
                    self.reciprocals[x] = y
                    break


    # Convert to canonical value
    def mod(self, x):
        if self.modulus <= modulusAuto:
            return x
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
        if x not in self.reciprocals:
            raise ReciprocalException(x)
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
    # Id set when add equation to evaluation set
    # Might not match the id used in other sets
    evalId = None
    # Mapping for variable Id to coefficient for nonzero coefficient
    nz = {}
    # Class to support math operations
    mbox = None
    cval = 0
    # BDD representation
    root = None
    # BDD size
    size = None
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
        self.size = 0
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
        e = Equation(self.N, self.modulus, cval, esys.mbox)
        e.nz = nnz
        if delayJustification:
            evid = esys.eset.addEquation(e, assignId = True)
            idlist = [oe.evalId for oe in operandList]
            esys.justificationSteps.append((evid, idlist))
        else:
            esys.justifyEquation(e, operandList)
        return e

    # Restructure the equation with a new mbox and modulus.  Justify that
    # it is implied by previous version
    def restructure(self, esys):
        mbox = esys.mbox
        modulus = mbox.modulus
        ncval = mbox.mod(self.cval)
        e = Equation(self.N, modulus, ncval, mbox)
        e.nz = { i : mbox.mod(self[i]) for i in self.indices() }
        esys.justifyEquation(e, [self])
        return e
        
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

    # Scale vector by constant
    def scale(self, const, esys):
        if const == 1:
            return self
        nnz = {}
        for i in self.indices():
            nx = self.mbox.mul(self[i], const)
            self.mbox.markUsed(nx)
            nnz[i] = nx
        nc = self.mbox.mul(self.cval, const)
        return self.spawn(nnz, nc, esys, [self])

    # Generate BDD representation
    def buildBdd(self, esys):
        ilist = self.indices()
        if len(ilist) == 0:
            self.root = esys.manager.leaf1 if self.cval == 0 else esys.manager.leaf0
            self.size = 1
            return

        ilist.sort(key = lambda id : esys.levelMap[id])
        # Put values into range
        nnz = { i : self.mbox.mod(self.nz[i]) for i in ilist }
        ncval = self.mbox.mod(self.cval)

        # Determine at what offsets will need node, starting from root and working down
        needNodes = { i : {} for i in ilist }
        previ = ilist[0]
        needNodes[previ][0] = True
        for nexti in ilist[1:]:
            for offset in sorted(needNodes[previ].keys()):
                # Will need this offset when variable evaluates to 0
                needNodes[nexti][offset] = True
                # Will need this offset when variable evaluates to 1
                noffset = esys.mbox.add(offset, nnz[previ])
                needNodes[nexti][noffset] = True
            previ = nexti

        # Now build BDD from bottom up
        rilist = list(ilist)
        rilist.reverse()

        if esys.mbox.modulus <= modulusAuto:
            # Unbounded range.  Need to consider all possible offsets
            lasti = rilist[0]
            needLeaves = {}
            for offset in sorted(needNodes[lasti].keys()):
                needLeaves[offset] = True
                noffset = offset + nnz[lasti]
                needLeaves[noffset] = True
            valueList = sorted(needLeaves.keys())
        else:
            valueList = sorted(esys.mbox.values())

        leafList = { offset : (esys.manager.leaf1 if offset == ncval else esys.manager.leaf0) for offset in valueList }
        nodes = { i : {} for i in rilist }

        lasti = rilist[0]
        for offset in sorted(needNodes[lasti].keys()):
            low = leafList[offset]
            noffset = esys.mbox.add(offset, nnz[lasti])
            high = leafList[noffset]
            var = esys.varMap[lasti]
            root = low if low == high else esys.manager.findOrMake(var, high, low)
            nodes[lasti][offset] = root

        nexti = lasti
        for previ in rilist[1:]:
            for offset in sorted(needNodes[previ].keys()):
                low = nodes[nexti][offset]
                noffset = esys.mbox.add(offset, nnz[previ])
                high = nodes[nexti][noffset]
                var = esys.varMap[previ]
                root = low if low == high else esys.manager.findOrMake(var, high, low)
                nodes[previ][offset] = root
            nexti = previ
            
        self.root = nodes[ilist[0]][0]
        self.size = esys.manager.getSize(self.root)
        
    # Remove reference to BDD when no longer needed
    def retireBdd(self):
        self.root = None
        self.size = 0
    
    # Does this equation have no solution with modular arithmetic
    def isInfeasible(self):
        # All zero coefficients and non-zero constant
        return self.cval != 0 and len(self) == 0

    def __str__(self):
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

    def addEquation(self, e, assignId = False):
        eid = self.nextId
        if assignId:
            e.evalId = eid
        self.nextId += 1
        self.equDict[eid] = e
        for idx in e.nz:
            self.addIndex(eid, idx)
        self.analyzeEquation(e)
        return eid

    def removeEquation(self, eid):
        e = self[eid]
        e.id = None
        for idx in e.nz:
            self.removeIndex(eid, idx)
        del self.equDict[eid]

    def lookup(self, idx):
        if idx in self.nzMap:
            return self.nzMap[idx]
        else:
            return []

    def rootList(self):
        ilist = sorted(self.equDict.keys())
        elist = [self.equDict[id] for id in ilist]
        return [e.root for e in elist]

    def __getitem__(self, id):
        return self.equDict[id]
        
    def __len__(self):
        return len(self.equDict)

    def currentEids(self):
        return sorted(list(self.equDict.keys()))

    def currentIndices(self):
        return sorted(list(self.nzMap.keys()))

    def show(self):
        eidList = sorted(self.currentEids())
        for eid in eidList:
            self.writer.write("   #%d:%s\n" % (eid, str(self[eid])))

    # How many total equations have been generated
    def equationCount(self):
        return self.nextId - 1

# Support pivot selection
# Must update scores whenever possible change to any nonzero in same row as pivot.
class PivotHelper:
    # Track set of indices. For each have generation indicating most recent computation of
    # its pivot score.  Earlier ones may still be in queue and should be ignored.
    generationMap = {}
    # Set of indices that have been affected since last pivot selection.
    # Implemented as dictionary mapping indices to True
    touchedSet = {}
    # Priority queue.
    # Holds tuple of form (score, idx, ... , generation)
    pqueue = None
    # evalFunction defines how to create score for index.  Should return tuple
    # with score in first position.
    evalFunction = None

    def __init__(self, evalFunction):
        self.evalFunction = evalFunction
        self.generationMap = {}
        self.touchedSet = {}
        self.pqueue = queue.PriorityQueue()

    def touch(self, ids):
        for id in ids:
            self.touchedSet[id] = True
            if id not in self.generationMap:
                self.generationMap[id] = 0
    
    def deleteIndex(self, id):
        if id in self.generationMap:
            del self.generationMap[id]
        if id in self.touchedSet:
            del self.touchedSet[id]

    def update(self):
        ilist = sorted(self.touchedSet.keys())
        random.shuffle(ilist)
        for id in ilist:
            tup = self.evalFunction(id)
            self.generationMap[id] += 1
            qtup = tup + (self.generationMap[id],)
            self.pqueue.put(qtup)
        self.touchedSet = {}

    def select(self):
        self.update()
        while not self.pqueue.empty():
            qtup = self.pqueue.get()
            id = qtup[1]
            generation = qtup[-1]
            if id is not None and id in self.generationMap and generation == self.generationMap[id]:
                tup = qtup[:-1]
                return tup
        raise QueueException("Queue emptied out without finding pivot")
            

# System of equations.
# Support LU decomposition of Gaussian elimination to see if system has any solutions
class EquationSystem:
    # Variable Count
    N = 10
    modulus = modulusAuto
    verbose = False
    # Class to support math operations
    mbox = None
    writer = None

    ## Solver state
    # Eliminated equations
    sset = None
    # Remaining equations
    rset = None

    # When not doing justifications, record equations and their dependencies for future justification
    # Set of equations involved in evaluation, including the leaf equations
    eset = None
    # Each element is tuple (eid, [opidlist]).  For original equations, opidlist is empty
    justificationSteps = []
    # Supporting BDD operation
    manager = None
    # Mapping from variable Id to variable
    varMap = None
    # Mapping from variable Id to level
    levelMap = None
    # Supporting pivot selection
    pivotHelper = None

    ## Accumulating data
    # Mapping from variable ID to True
    varUsed = {}
    # Number of equations
    # Total number of elimination steps
    stepCount = 0
    # Number of times pivot evaluation computed
    pivotEvaluationCount = 0
    # Sum of pivot degrees
    pivotDegreeSum = 0
    # Max of pivot degrees
    pivotDegreeMax = 0
    # Total number of vector operations
    combineCount = 0

    def __init__(self, N, modulus = modulusAuto, verbose = True, manager = None, writer = None):
        self.N = N
        self.modulus = modulus
        self.verbose = verbose
        self.justificationSteps = []
        self.manager = manager
        if manager is not None:
            self.varMap = { var.id : var for var in manager.variables }
            self.levelMap = { var.id : var.level for var in manager.variables }
        self.writer = SimpleWriter() if writer is None else writer
        self.mbox = ModMath(modulus)
        self.sset = EquationSet(writer = self.writer)
        self.rset = EquationSet(writer = self.writer)
        self.eset = EquationSet(writer = self.writer)
        self.pivotHelper = PivotHelper(self.evaluatePivot)
        self.varUsed = {}
        self.stepCount = 0
        self.pivotEvaluationCount = 0
        self.pivotDegreeSum = 0
        self.pivotDegreeMax = 0
        self.combineCount = 0

    # Add new equation to main set
    def addInitialEquation(self, e):
        eid = self.rset.addEquation(e)
        for i in e.nz:
            self.varUsed[i] = True
        self.pivotHelper.touch(e.indices())
        if delayJustification:
            evid = self.eset.addEquation(e, assignId = True)
            self.justificationSteps.append((evid,[]))
        if self.manager is not None:
            e.buildBdd(self)
        return eid

    # Construct BDD representation of equation and generate its justification
    # operandList is list of equations from which this one was derived
    def justifyEquation(self, e, operandList):
        e.buildBdd(self)
        rvList = [(eq.root,eq.validation) for eq in operandList]
        done = False
        while not done and len(rvList) > 2:
            r1,v1 = rvList[0]
            r2,v2 = rvList[1]
            validation = None
            antecedents = [v1,v2]
            nr,imp = self.manager.applyAndJustify(r1, r2)
            if nr == self.manager.leaf0:
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
                validation = self.manager.prover.createClause([nr.id], antecedents, comment)
            rvList = [(nr,validation)] + rvList[2:]
        if not done: 
            if len(rvList) == 2:
                # Do final conjunction and implication in combination
                r1,v1 = rvList[0]
                r2,v2 = rvList[1]
                antecedents = [v1,v2]
                check, implication = self.manager.applyAndJustifyImply(r1, r2, e.root)
                if not check:
                    raise ProofGenerationException("Implication failed when spawning equation %s: %s % %s -/-> %s\n" % (str(e), r1.label(), r2.label(), e.root.label()))
            else:
                r1, v1 = rvList[0]
                antecedents = [v1]
                check, implication = self.manager.justifyImply(r1, e.root)
                if not check:
                    raise ProofGenerationException("Implication failed when spawning equation %s: %s -/-> %s\n" % (str(e), r1.label(), e.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            done = e.root == self.manager.leaf0
            if done:
                comment = "Validation of empty clause from infeasible equation"
            else:
                comment = "Validation of equation with BDD root %s" % e.root.label()
            e.validation = self.manager.prover.createClause([e.root.id], antecedents, comment)
        if done:
            self.writer.write("UNSAT\n")
            self.manager.summarize()


    # Perform justifications after the fact.
    # Use equation that was found to be infeasible to set new modulus
    def performJustification(self, laste):
        # Mapping from leaf Ids to Ids of modular representations
        emap = { }
        changedModulus = False
        p = self.modulus
        if p == modulusAuto:
            # Choose a new modulus.  It need not be prime
            p = 2
            while laste.cval % p == 0:
                p += 1
            self.mbox.setModulus(p)
            changedModulus = True
        nmod = "none" if p == modulusNone else str(p)
        self.writer.write("Performing justification of %d steps.  Modulus = %s.\n" % (len(self.justificationSteps), nmod))
        # Construct information needed for garbage collection
        lastUse = {}
        for evid, idlist in self.justificationSteps:
            for oevid in idlist:
                lastUse[oevid] = evid
        # Do the justification
        for evid, idlist in self.justificationSteps:
            e = self.eset[evid]
            if len(idlist) == 0:
                # Modulus changed.  Need to construct new BDD
                if changedModulus:
                    ne = e.restructure(self)
                    nevid = self.eset.addEquation(ne)
                    emap[evid] = nevid
                    self.eset.removeEquation(evid)
                    size = e.size
                    e.retireBdd()
                    self.checkGC(size)
            else:
                evidlist = [(emap[oevid] if oevid in emap else oevid) for oevid in idlist]
                oplist = [self.eset[oevid] for oevid in evidlist]
                self.justifyEquation(e, oplist)
                for oevid in idlist:
                    if lastUse[oevid] == evid:
                        # Equation no longer needed
                        cid = emap[oevid] if oevid in emap else oevid
                        ce = self.eset[cid]
                        self.eset.removeEquation(cid)
                        size = ce.size
                        ce.retireBdd()
                        self.checkGC(size)
                        



    # Given possible pivot index
    # find best equation to use as pivot equation and
    # give score for its selection
    # If there are no nonzeros with this index, return None for the equation ID
    def evaluatePivot(self, pidx):
        self.pivotEvaluationCount += 1
        eidList = self.rset.lookup(pidx)
        if len(eidList) == 0:
            # Not a valid pivot
            return (0, None, None)
        bestEid = None
        # Lowest degree row
        bestRd = 0
        # Make sure that any ties are broken arbitrarily
        # rather than as some artifact of the input file
        if randomizePivots:
            random.shuffle(eidList)

        for eid in eidList:
            e = self.rset[eid]
            rd = len(e)
            if bestEid is None or rd < bestRd:
                bestEid = eid
                bestRd = rd

        # Score based on worst-case fill generated
        # Also favors unit and singleton equations
        score = float((bestRd-1) * (len(eidList)-1))
        if randomizePivots:
            # Add noise to score to break ties in pivot selection
            score += random.random()
        # Return tuple that can be placed in priority queue
        return (score, pidx, bestEid)

    # Given remaining set of equations, select pivot element and equation id
    def selectPivot(self):
        (score, pidx, eid) = self.pivotHelper.select()
        if eid is not None:
            pd = len(self.rset[eid])
            self.pivotDegreeSum += pd
            self.pivotDegreeMax = max(self.pivotDegreeMax, pd)
        return (pidx, eid)

    # Given remaining set of equations, select pivot element and equation id
    def selectPivotOld(self):
        bestPidx = None
        bestScore = 0.0
        bestEid = None
        idList = self.rset.currentIndices()
        for pidx in idList:
            (score, xidx, eid) = self.evaluatePivot(pidx)
            if eid is not None and (bestEid is None or score < bestScore):
                bestPidx = pidx
                bestScore = score
                bestEid = eid
        if bestEid is not None:
            pd = len(self.rset[bestEid])
            self.pivotDegreeSum += pd
            self.pivotDegreeMax = max(self.pivotDegreeMax, pd)
#        self.writer.write("Selecting pivot (%d,%d).  Score = %.4f\n" % (bestPidx, bestEid, bestScore))
        return (bestPidx, bestEid)

    # Perform one step of LU decomposition
    # Return (status, finalequation), where status is
    # "solved", "unsolvable", "normal", "toobig"
    def solutionStep(self):
        if len(self.rset) == 0:
            return ("solved", None)
        self.stepCount += 1
        (pidx, eid) = self.selectPivot()
        if pidx is None:
            return ("solved", None)

        e = self.rset[eid]
        self.pivotHelper.touch(e.indices())
        pval = e[pidx]
        if self.verbose:
            self.writer.write("Pivoting with value %d (element %d).  Using equation #%d\n" % (pval, pidx, eid))
        self.rset.removeEquation(eid)
        self.sset.addEquation(e)
        otherEids =  self.rset.lookup(pidx)
        for oeid in otherEids:
            oe = self.rset[oeid]
            self.pivotHelper.touch(oe.indices())
            eval = e[pidx]
            oeval = oe[pidx]
            se = e.scale(oeval, self)
            soe = oe.scale(eval, self)
            re = soe.sub(se, self)
            if re.isInfeasible():
                return ("unsolvable", re)
            self.rset.addEquation(re)
            self.rset.removeEquation(oeid)
            if not delayJustification:
                size = oe.size
                oe.retireBdd()
                self.checkGC(size)
            self.combineCount += 1
        if not delayJustification:
            size = e.size
            e.retireBdd()
            self.checkGC(size)
        self.pivotHelper.deleteIndex(pidx)
        return ("normal", None)
            
    def solve(self, nzLimit):
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

        while True:
            try:
                status, laste = self.solutionStep()
            except PseudoBooleanException as ex:
                self.writer.write("  Solver failed: %s\n" % (str(ex)))
                return "failed"
            # "solved", "unsolvable", "normal"
            if status != "normal":
                break
            if self.verbose:
                self.showState()
        if self.verbose:
            self.writer.write("  Solution status:%s\n" % status)
            self.postStatistics(status)
        if status == "unsolvable" and delayJustification:
            if nzLimit is not None and self.rset.termCount > nzLimit:
                self.writer.write("Aborting proof generation.  NZ count = %d\n" % self.rset.termCount)
                status = "toobig"
            else:
                self.writer.write("Attempting proof generation.  NZ count = %d\n" % self.rset.termCount)
                self.performJustification(laste)
        return status

    def checkGC(self, newDeadCount):
        clauseList = self.manager.checkGC(newDeadCount)
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
        pavg = float(self.pivotDegreeSum)/sscount if sscount > 0 else 0.0
        pmax = self.pivotDegreeMax
        self.writer.write("  Solving: %d steps.  %.2f avg pivot degree (max=%d)\n" % (sscount, pavg, pmax))
        ecount = self.rset.equationCount()
        ccount = self.combineCount
        tc = self.rset.termCount
        tmax = self.rset.termMax
        tavg = float(tc)/ecount if ecount > 0 else 0.0
        self.writer.write("    %d total equations.  %d total nonzeros (%.2f avg, %d max).  %d vector operations\n" % (ecount, tc, tavg, tmax, ccount))
#        self.writer.write("    %d modular operations.  Used values = %s\n" % (self.mbox.opcount, self.mbox.reportUsed()))


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
    # BDD size
    size = 0
    # Validation step Id
    validation = None

    def __init__(self, N, cval):
        self.N = N     # Max Variable ID +1
        self.cval = cval
        self.nz = {}
        self.root = None
        self.size = 0
        self.validation = None

    def setNz(self, nz):
        self.nz = nz

    def __getitem__(self, i):
        return self.nz[i] if i in self.nz else 0

    def __setitem__(self, i, v):
        if v == 0:
            if i in self.nz:
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
        if not done:
            if len(rvList) == 2:
                # Do final conjunction and implication in combination
                r1,v1 = rvList[0]
                r2,v2 = rvList[1]
                antecedents = [v1,v2]
                check, implication = csys.manager.applyAndJustifyImply(r1, r2, con.root)
                if not check:
                    raise ProofGenerationException("Implication failed when spawning constraint %s: %s & %s -/-> %s\n" % (str(con), r1.label(), r2.label(), con.root.label()))
            else:
                r1,v1 = rvList[0]
                antecedents = [v1]
                check, implication = csys.manager.justifyImply(r1, con.root)
                if not check:
                    raise ProofGenerationException("Implication failed when spawning constraint %s: %s -/-> %s\n" % (str(con), r1.label(), con.root.label()))
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

    # Scale a constraint by a constant
    def scale(self, const, csys):
        if const == 1:
            return self
        nnz = { i : const * self[i] for i in self.indices() }
        nc = const * self.cval
        return self.spawn(nnz, nc, csys, [self])

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

    def isAlo(self):
        if self.cval != 1:
            return False
        for coeff in self.nnz.values():
            if coeff != 1:
                return False
            break
        return True

    def isAmo(self):
        if self.cval != -1:
            return False
        for coeff in self.nnz.values():
            if coeff != -1:
                return False
            break
        return True


    # Generate BDD representation
    def buildBdd(self, csys):
        ilist = self.indices()
        if len(ilist) == 0:
            self.root = csys.manager.leaf1 if self.cval <= 0 else csys.manager.leaf0
            self.size = 1
            return

        ilist.sort(key = lambda id : csys.levelMap[id])

        # Determine at what offsets will need node, starting from root and working down
        needNodes = { i : {} for i in ilist }
        previ = ilist[0]
        needNodes[previ][0] = True
        for nexti in ilist[1:]:
            for offset in sorted(needNodes[previ].keys()):
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
        for offset in sorted(needNodes[lasti].keys()):
            needLeaves[offset] = True
            noffset = offset + self[lasti]
            needLeaves[noffset] = True

        leafList = { offset : (csys.manager.leaf1 if offset >= self.cval else csys.manager.leaf0) for offset in needLeaves.keys() }
        nodes = { i : {} for i in rilist }

        for offset in sorted(needNodes[lasti].keys()):
            low = leafList[offset]
            noffset = offset + self[lasti]
            high = leafList[noffset]
            var = csys.varMap[lasti]
            root = low if low == high else csys.manager.findOrMake(var, high, low)
            nodes[lasti][offset] = root

        nexti = lasti
        for previ in rilist[1:]:
            for offset in sorted(needNodes[previ].keys()):
                low = nodes[nexti][offset]
                noffset = offset + self[previ]
                high = nodes[nexti][noffset]
                var = csys.varMap[previ]
                root = low if low == high else csys.manager.findOrMake(var, high, low)
                nodes[previ][offset] = root
            nexti = previ
            
        self.root = nodes[ilist[0]][0]
        self.size = csys.manager.getSize(self.root)
    
    # Does this constraint have no solution
    def isInfeasible(self):
        maxsum = 0
        for v in self.nz.values():
            if v > 0:
                maxsum += v
        return maxsum < self.cval

    def isTrivial(self):
        return self.cval <= 0 and len(self) == 0

    def opbString(self, forceEquality = False):
        result = ""
        for (k,v) in self.nz.items():
            result += "%d x%d " % (v, k)
        rel = "=" if forceEquality else ">="
        result += "%s %d" % (rel, self.cval)
        return result

    def __str__(self):
        if self.N < 0:
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
        ilist = sorted(self.conDict.keys())
        clist = [self.conDict[id] for id in ilist]
        return [con.root for con in clist]

    def __getitem__(self, id):
        return self.conDict[id]
        
    def __len__(self):
        return len(self.conDict)

    def currentCids(self):
        return sorted(list(self.conDict.keys()))

    def currentIndices(self):
        return sorted(list(self.nzMap.keys()))

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
    writer = None

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
        if randomizePivots:
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
        values = [self.rset[cid][pidx] for cid in cidList]
#        oobValues = [v for v in values if abs(v) > 1]
#        if len(oobValues) > 0:
#            raise FourierMotzinException(oobValues)

        if self.verbose:
            self.writer.write("Pivoting at element %d.  %d positive, %d negative constraints\n" % (pidx, len(posIndices), len(negIndices)))
        
        for pid in posIndices:
            pcon = self.rset[pid]
            pval = pcon[pidx]
            for nid in negIndices:
                ncon = self.rset[nid]
                nnval = -ncon[pidx]
                spcon = pcon.scale(nnval, self)
                sncon = ncon.scale(pval, self)
                scon = spcon.add(sncon, self)
                if scon.isInfeasible():
                    return "unsolvable"
                if not scon.isTrivial():
                    self.rset.addConstraint(scon)
                self.combineCount += 1

        for cid in cidList:
            size = self.rset[cid].size
            self.rset.removeConstraint(cid)
            self.checkGC(size)

        return "normal"
            
    def solve(self, nzLimit):
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

        while True:
            try:
                status = self.solutionStep()
            except PseudoBooleanException as ex:
                self.writer.write("Solver Failed: %s\n" % str(ex))
                return "failed"
            # "solved", "unsolvable", "normal"
            if status != "normal":
                break
            if self.verbose:
                self.showState()
        if self.verbose:
            self.writer.write("  Solution status:%s\n" % status)
            self.postStatistics(status)
        return status

    def checkGC(self, newDeadCount):
        clauseList = self.manager.checkGC(newDeadCount)
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
        
        
