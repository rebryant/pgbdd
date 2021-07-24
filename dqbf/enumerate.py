# Enumerate or sample minimal solution to a monotone CNF
# Clauses can only contain positive literals

import random

# Dynamic management of clause
class Clause:
    listStack = []
    activeList = []
    isTrue = False
    isFalse = False
    
    def __init__(self, clause):
        self.listStack = []
        self.activeList = clause
        self.isTrue = False
        self.isFalse = len(clause) == 0

    def __str__(self):
        if self.isFalse:
            return "FALSE"
        elif self.isTrue:
            return "TRUE"
        else:
            return str(self.activeList)

    def findForced(self):
        if not self.isTrue and len(self.activeList) == 1:
            return self.activeList[0]
        else:
            return None

    def satisfy(self, var):
        if self.isTrue or self.isFalse:
            return
        alist = []
        for v in self.activeList:
            if v == var:
                self.isTrue = True
                alist = []
                break
            else:
                alist.append(v)
        self.activeList = alist


    def falsify(self, var):
        if self.isTrue or self.isFalse:
            return
        alist = []
        for v in self.activeList:
            if v != var:
                alist.append(v)
        self.activeList = alist                
        self.isFalse = len(self.activeList) == 0


    def push(self):
        state = (list(self.activeList), self.isTrue, self.isFalse)
        self.listStack.append(state)

    def pop(self):
        if len(self.listStack) == 0:
            raise Exception("Empty clause stack")
        state = self.listStack[-1]
        self.listStack = self.listStack[:-1]
        self.activeList, self.isTrue, self.isFalse = state

class Enumerator:
    clauseList = []
    forcedVarSet = set([])
    isFalse = False
    isTrue = False
    statusStack = []
    # Performance tuning parameters
    # Maximum number of backtracks when generating all solutions
    btLimit = 1000
    # Counter to track backtracks
    btCount = 0
    # Cutoff between enumeration and sampling
    enumerationThreshold = 20
    limitThreshold = 50
    # Upper limit on number of random solutions generated
    mediumSamplingLimit = 30
    largeSamplingLimit = 5
    # Batch size for sampling
    samplingBatchSize = 5

    def show(self):
        print("Solver state.  Stack depth %d.  Falsified? %s.  Tautology? %s.  Forced Variables: %s" % (len(self.statusStack), str(self.isFalse), str(self.isTrue), str(sorted(self.forcedVarSet))))
        if not self.isFalse and not self.isTrue:
            cclist = [str(cc) for cc in self.clauseList]
            print(" ".join(cclist))

    def __init__(self, clist):
        self.clauseList = []
        self.forcedVarSet = set([])
        self.isFalse = False
        self.isTrue = len(clist) == 0
        forced = set([])
        for c in clist:
            cc = Clause(c)
            self.clauseList.append(cc)
            fv = cc.findForced()
            if fv is not None:
                forced |= set([fv])
            self.isFalse = self.isFalse or cc.isFalse
        self.propagate(forced)
        self.statusStack = []

    def setTrue(self, var):
        allTrue = True
        for cc in self.clauseList:
            cc.satisfy(var)
            allTrue = allTrue and cc.isTrue
        self.isTrue = allTrue

    def propagate(self, forcedSet):
        for fv in forcedSet:
            self.setTrue(fv)
        self.forcedVarSet |= forcedSet

    # Set variable to false and propagate unit clauses
    def setFalse(self, var):
        foundFalse = False
        nforced = set([])
        for cc in self.clauseList:
            cc.falsify(var)
            foundFalse = foundFalse or cc.isFalse
            fv = cc.findForced()
            if fv is not None:
                nforced |= set([fv])
        self.isFalse = foundFalse
        if not self.isFalse:
            self.propagate(nforced)

    def saveState(self):
        for cc in self.clauseList:
            cc.push()
        saveForced = set([v for v in self.forcedVarSet])
        state = (saveForced, self.isFalse, self.isTrue)
        self.statusStack.append(state)


    def restoreState(self):
        for cc in self.clauseList:
            cc.pop()
        state = self.statusStack[-1]
        self.statusStack = self.statusStack[:-1]
        self.forcedVarSet, self.isFalse, self.isTrue = state

    def singleSolve(self, varList):
        self.saveState()
        result = []
        for var in varList:
            if var in self.forcedVarSet:
                self.forcedVarSet -= set([var])
                result.append(var)
            else:
                self.setFalse(var)
                result.append(-var)
        if not self.isTrue:
            raise Exception("singleSolve: Reached end of variable list without solution")
        self.restoreState()
        return tuple(sorted(result, key = lambda lit : abs(lit)))

    def allSolve(self, varList):
        if self.isTrue:
            soln = tuple([(v if v in self.forcedVarSet else -v) for v in varList])
            return [soln]
        if self.isFalse:
            return []

        # Find unforced variable
        prefix = []
        var = None
        while var is None and len(varList) > 0:
            var = varList[0]
            varList = varList[1:]
            if var in self.forcedVarSet:
                self.forcedVarSet -= set([var])
                prefix.append(var)
        if var is None:
            raise Exception("Setting to 0.  Ran out of variables to split on")

        subList0 = self.solverStep(-var, varList)
        list0 = [tuple(prefix + [-var] + list(soln)) for soln in subList0] 
        if self.btCount >= self.btLimit:
            return list0

        self.btCount += 1
        subList1 = self.solverStep(var, varList)
        set0 = set(subList0)
        newList1 = [soln for soln in subList1 if soln not in set0]
        list1 = [tuple(prefix + [var] + list(soln)) for soln in newList1]

        result = list0 + list1
        return result

    def solverStep(self, literal, varList):
        self.saveState()
        var = abs(literal)
        if literal < 0:
            self.setFalse(var)
        else:
            self.setTrue(var)
        subList = self.allSolve(varList)
        self.restoreState()
        return subList

    def catalogSolution(self, sset, soln):
        if soln not in sset:
            sset |= set([soln])

    def samplingLimit(self, varList):
        if len(varList) <= self.limitThreshold:
            return self.mediumSamplingLimit
        return self.largeSamplingLimit

    # Generate solutions by random sampling
    def sampleSolve(self, sset, varList):
        vlist = list(varList)
        while len(sset) < self.samplingLimit(varList):
            startCount = len(sset)
            for r in range(self.samplingBatchSize):
                random.shuffle(vlist)
                soln = self.singleSolve(vlist)
                self.catalogSolution(sset, soln)
            if len(sset) == startCount:
                return


    def minSolve(self, varList, check = False):
        varList.sort()
        sset = set([])
        self.catalogSolution(sset, self.singleSolve(varList))
        if len(varList) <= self.enumerationThreshold:
            self.btCount = 0
            alist = self.allSolve(varList)
            for soln in alist:
                self.catalogSolution(sset, soln)
        else:
            self.sampleSolve(sset, varList)
        result = sorted(sset)
        if check:
            badCount = 0
            for soln in result:
                if not self.checkSolution(soln):
                    badCount += 1
            if badCount > 0:
                print("%d/%d solutions invalid" % (badCount, len(result)))
        return result

    def checkSolution(self, soln):
        posLits = [lit for lit in soln if lit > 0]
        icount = 0
        firstBad = None
        for c in self.clauseList:
            found = False
            for lit in c.activeList:
                if lit in posLits:
                    found = True
                    break
            if not found:
                icount += 1
                if icount == 1:
                    firstBad = c
        if icount > 0:
            print("Invalid solution.  %d/%d not satisifed.  First bad clause = %s.  Positive solution literals = %s" % (icount, len(self.clauseList), str(firstBad), str(posLits)))
        return icount > 0


class OldEnumerator:

    # List of clauses.  Special case.  If contain empty clause, it will be the only one
    clauseList = []
    
    # Create new set.
    def __init__(self, clauseList):
        # Check for empty clause
        for c in clauseList:
            if len(c) == 0:
                self.clauseList = [c]
                return
        self.clauseList = [sorted(c) for c in clauseList]

    def isTautology(self):
        return len(self.clauseList) == 0
    
    def isFalse(self):
        return len(self.clauseList) == 1 and len(self.clauseList[0]) == 0

    # Perform unit propagation with literal -var.
    # var must be first literal in clause
    # Assume there are no empty clauses
    def unitFalse(self, var):
        nclauseList = []
        for c in self.clauseList:
            nc = c
            if c[0] == var:
                nc = c[1:]
            nclauseList.append(nc)
        return OldEnumerator(nclauseList)

    # Perform unit propagation with literal var.
    # var must be first literal in clause
    # Assume there are no empty clauses
    def unitTrue(self, var):
        nclauseList = []
        for c in self.clauseList:
            if c[0] != var:
                nclauseList.append(c)
        return OldEnumerator(nclauseList)
    
    # Return all minimal solutions to formula
    def minSolve(self, varList, solutionLimit=None):
        if self.isTautology():
            return [tuple([-v for v in varList])]
        elif self.isFalse():
            return []
        v = varList[0]
        nvarList = varList[1:]
        # Recursively find solutions when first variable set to 0 and 1
        solve0 = self.unitFalse(v).minSolve(nvarList, solutionLimit)
        result0 = [(-v,) + soln for soln in solve0]

        if solutionLimit is not None and len(result0) >= solutionLimit:
            return result0

        solve1 = self.unitTrue(v).minSolve(nvarList, solutionLimit)
        set0 = set(solve0)
        # Only add solution for var=1 if not solution with var=0 
        new1 = [soln for soln in solve1 if soln not in set0]
        result1 = [(v,) + soln for soln in new1]
        result = result0 + result1
        if solutionLimit is not None and len(result) > solutionLimit:
            result = result[:solutionLimit]
        return result
        

        
        
                
