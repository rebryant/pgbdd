#!/usr/bin/python

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# Last edit: Feb. 16, 2021
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


# Home-brewed checker for QBF proofs.
import sys
import getopt
import datetime

def usage(name):
    print("Usage: %s [-v] -m (s|r|d) -i FILE.qcnf -p FILE.qproof" % name)
    print("   -m MODE   Set proof mode (s = satisfaction, r = refutation.  Default is to work either way)")
    print("   -v        Print more helpful diagnostic information if there is an error")

######################################################################################
# Checker format
######################################################################################
# Notation
#  Id: Clause Id
#  Var: Variable
#  Lit: Literal +/- Var
#  Level: Quantification level

# [Lit*]: Clause consisting of specified literals
# C[Id]: Clause with given Id
# Var(Lit): Variable for specified literal

### All proof types

# - l Level Var+ 0
#    Shift input variables to specified level
#    All shifts must occur before any other command type
#    Check that resulting ordering of input variables is a refinement of the initial ordering
#    A minimal shift would be to move each variable at level l to 2l-1 to make room for existential variables

# - x Level Var+ 0
#    Introduce extension variable(s) at specified quantification level
#    Make sure each Var is not already defined, and that only existential variables are at this level

### Refutation and dual proofs

# Id ar Lit* 0 Id+ 0
#    Add clause C[Id] = [Lit*] by resolution.
#    Must check that antecedents resolve to clause
#    Also incorporates subsumption, i.e., if C' subset C, the C' ==> C.
#    Must check that antecedents resolve to clause C' that is
#     (perhaps improper) subset of C[Id]


# Id ab Lit+ 0 -Id* 0
#    Add blocked clause C[Id] = [Lit+].  Blocking literal L must be first
#    Negative Ids are those clauses containing -L
#    Must make sure no other clauses contain -L
#    Must make sure every clause containing -L contains literal L'
#      such that L' in [Lit+]

# Id u Lit Id'

#    Universal reduction.  Remove literal Lit from clause Id' to get
#      C[Id] = C[Id'] - { Lit }
#    Must check that Var(Lit) is greater than Var(Lit') for any Lit'
#      in C[Id']
#    OK if Lit is not in clause

### Refutation-only proofs

# - d Id+ 0
#    Delete clauses.  Must make sure they are live

### Satisfaction and dual proofs

# - dr Id Id+ 0
#    Delete clause C[Id] by resolution.
#    Also incorporates subsumption, i.e., if C' subset C, the C' ==> C.
#    Must check that antecedents resolve to clause C' that is
#     (perhaps improper) subset of C[Id]

# - dd Var Id+ 0 Id* 0
#    Delete all clauses in first list by
#    Davis-Putnam reduction on variable Var (Also called "Existential elimination")
#    Second list consists of all resolvents from first list
#      w.r.t. resolution variable Var
#    No clauses other than those in first list can contain Var or -Var
#    None of these can contain a universal literal > Var

### Satisfaction-only proofs

# Id a Lit* 0
#    Add clause C[Id] = [Lit*].

######################################################################################

def trim(s):
    while len(s) > 0 and s[-1] in ' \r\n\t':
        s = s[:-1]
    return s

# Clean up clause.
# Remove duplicates
# Sort in reverse order of variable number
# Don't allow clause to have opposite literals
def cleanClause(literalList):
    slist = sorted(literalList, key = lambda v: -abs(v))
    if len(slist) <= 1:
        return slist
    nlist = [slist[0]]
    for i in range(1, len(slist)):
        if slist[i-1] == slist[i]:
            continue
        if slist[i-1] == -slist[i]:
            return None
        nlist.append(slist[i])
    return nlist

def regularClause(clause):
    return clause is not None

def showClause(clause):
    if clause is None:
        return "NONE"
    return str(clause)

class ResolveException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Resolve Exception: " + str(self.value)

# Given two clauses, each processed by cleanClause,
# attempt to resolve them.
# Return resolvent if normal, None if tautology.
def resolveClauses(clause1, clause2):
    if not regularClause(clause1):
        msg = "Cannot do resolution on clause %s" % showClause(clause1)
        raise ResolveException(msg)
    if not regularClause(clause2):
        msg = "Cannot do resolution on clause %s" % showClause(clause2)
        raise ResolveException(msg)
    result = []
    resolutionVariable = None
    while True:
        if len(clause1) == 0:
            if resolutionVariable is None:
                msg = "No resolution variable found"
                raise ResolveException(msg)
            else:
                result += clause2
            break
        if len(clause2) == 0:
            if resolutionVariable is None:
                msg = "No resolution variable found"
                raise ResolveException(msg)
            else:
                result += clause1
            break
        l1 = clause1[0]
        l2 = clause2[0]
        rc1 = clause1[1:]
        rc2 = clause2[1:]
        if abs(l1) == abs(l2):
            clause1 = rc1
            clause2 = rc2
            if l1 == l2:
                result.append(l1)
            else:
                if resolutionVariable is None:
                    resolutionVariable = abs(l1)
                else:
                    # Tautology
                    return None
        elif abs(l1) > abs(l2):
            clause1 = rc1
            result.append(l1)
        else:
            clause2 = rc2
            result.append(l2)
    return result


# Clause comparison.  Assumes both have been processed by cleanClause
def testClauseEquality(clause1, clause2):
    if clause1 is None or clause2 is None:
        return False
    if len(clause1) != len(clause2):
        return False
    for l1, l2 in zip(clause1, clause2):
        if l1 != l2:
            return False
    return True

# Clause comparison.  Assumes both have been processed by cleanClause
def testClauseSubset(clause1, clause2):
    if clause1 is None or clause2 is None:
        return False
    idx1 = 0
    idx2 = 0
    while idx1 < len(clause1):
        if idx2 >= len(clause2):
            return False
        head1 = clause1[idx1]
        head2 = clause2[idx2]
        if abs(head1) > abs(head2):
            return False
        elif head1 == head2:
            idx1 += 1
            idx2 += 1
        elif abs(head1) < abs(head2):
            idx2 += 1
    return True


# Clause comparison.  Assumes both have been processed by cleanClause
def testClauseEqualityOld(clause1, clause2):
    if clause1 is None or clause2 is None:
        return False
    if len(clause1) != len(clause2):
        return False
    while True:
        if len(clause1) == 0:
            return True
        else:
            l1 = clause1[0]
            l2 = clause2[0]
            clause1 = clause1[1:]
            clause2 = clause2[1:]
            if l1 != l2:
                return False

# Read QCNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
class QcnfReader():
    file = None
    clauses = []
    # List of input variables.
    # Each is triple of form (varNumber, qlevel, isExistential)
    varList = []
    nvar = 0
    failed = False
    errorMessage = ""
    
    def __init__(self, fname):
        self.failed = False
        self.errorMessage = ""
        try:
            self.file = open(fname, 'r')
        except Exception:
            self.fail("Could not open file '%s'" % fname)
            return
        self.readCnf()
        print("Read %d clauses from file %s" % (len(self.clauses), fname))
        self.file.close()
        
    def fail(self, msg):
        self.failed = True
        self.errorMessage = msg

    def readCnf(self):
        self.nvar = 0
        # Dictionary of variables that have been declared.
        # Maps from var to line number
        foundDict = {}
        lineNumber = 0
        nclause = 0
        self.varList = []
        qlevel = 1
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
                pass
            elif line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    self.fail("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                    return
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    self.fail("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
                    return
            elif line[0] == 'a' or line[0] == 'e':
                # Variable declaration
                isExistential = line[0] == 'e'
                try:
                    vars = [int(s) for s in line[1:].split()]
                except:
                    self.fail("Line %d.  Non-integer field" % lineNumber)
                    return
                # Last one should be 0
                if vars[-1] != 0:
                    self.fail("Line %d.  Clause line should end with 0" % lineNumber)
                    return
                vars = vars[:-1]
                for v in vars:
                    if v <= 0 or v > self.nvar:
                        self.fail("Line %d.  Invalid variable %d" % (lineNumber, v))
                        return
                    if v in foundDict:
                        self.fail("Line %d.  Variable %d already declared on line %d" % (lineNumber, v, foundDict[v]))
                        return
                    foundDict[v] = lineNumber
                    self.varList.append((v, qlevel, isExistential))
                # Prepare for next set of input variables
                qlevel += 2
            else:
                if nclause == 0:
                    self.fail("Line %d.  No header line.  Not cnf" % (lineNumber))
                    return
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    self.fail("Line %d.  Non-integer field" % lineNumber)
                    return
                # Last one should be 0
                if lits[-1] != 0:
                    self.fail("Line %d.  Clause line should end with 0" % lineNumber)
                    return
                lits = lits[:-1]
                vars = sorted([abs(l) for l in lits])
                if len(vars) == 0:
                    self.fail("Line %d.  Empty clause" % lineNumber)                    
                    return
                if vars[-1] > self.nvar or vars[0] == 0:
                    self.fail("Line %d.  Out-of-range literal" % lineNumber)
                    return
                for i in range(len(vars) - 1):
                    if vars[i] == vars[i+1]:
                        self.fail("Line %d.  Opposite or repeated literal" % lineNumber)
                        return
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            self.fail("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
            return
        # See if there are any undeclared variables
        outerVars = [v for v in range(1, self.nvar+1) if v not in foundDict]
        if len(outerVars) > 0:
            # These must be added as existential variables in first quantifier block
            ovarList = [(v, 1, True) for v in outerVars]
            nvarList = [(v, qlevel+1, isExistential) for (v, qlevel, isExistential) in self.varList]
            self.varList = ovarList + nvarList


# Clause processing
class ClauseManager:
    # Mapping from Id to clause.  Deleted clauses represented by None
    clauseDict = {}
    # For each literal, count of clauses containing it
    literalCountDict = {}
    # For each literal, set of clauses containing it (only in verbose mode)
    literalSetDict = {}
    # Track whether have empty clause
    addedEmpty = False
    # Counters
    liveClauseCount = 0
    maxLiveClauseCount = 0
    totalClauseCount = 0
    # Clauses that haven't been deleted (only in verbose mode)
    liveClauseSet = set([])

    def __init__(self, verbose):
        self.verbose = verbose
        self.clauseDict = {}
        self.literalCountDict = {}
        self.literalSetDict = {}
        self.addedEmpty = False
        self.liveClauseCount = 0
        self.maxLiveClauseCount = 0
        self.totalClauseCount = 0
        self.liveClauseSet = set([])

    def findClause(self, id):
        if id not in self.clauseDict:
            return (None, "Clause #%d never defined" % id)
        elif self.clauseDict[id] is None:
            return (None, "Clause #%d has been deleted" % id)
        else:
            return (self.clauseDict[id], "")

    # Add clause.  Should have been processed with cleanClause
    # Return (T/F, reason)
    def addClause(self, clause, id = None):
        if not regularClause(clause):
            return (False, "Cannot add clause %s" % showClause(clause))
        newId = len(self.clauseDict)+1
        if id is not None and id != newId:
            return (False, "Invalid clause Id.  Was expecting %d but got %s" % (newId, id))
        self.clauseDict[newId] = clause
        if len(clause) == 0:
            self.addedEmpty = True
        self.liveClauseCount += 1
        self.totalClauseCount += 1
        if self.verbose:
            self.liveClauseSet.add(newId)
        self.maxLiveClauseCount = max(self.liveClauseCount, self.maxLiveClauseCount)
        # Add literals
        for lit in clause:
            if lit in self.literalCountDict:
                self.literalCountDict[lit] += 1
                if self.verbose:
                    self.literalSetDict[lit].add(newId)
            else:
                self.literalCountDict[lit] = 1
                if self.verbose:
                    self.literalSetDict[lit] = set([newId])
        return (True, "")
        
    # Delete clause.
    # Return (T/F, reason)
    def deleteClause(self, id):
        clause, msg = self.findClause(id)
        if clause is None:
            return (False, "Cannot delete clause %d: %s" % (id, msg))
        self.clauseDict[id] = None
        self.liveClauseCount -= 1
        if self.verbose:
            self.liveClauseSet.remove(id)
        for lit in clause:
            self.literalCountDict[lit] -= 1
            if self.verbose:
                self.literalSetDict[lit].remove(id)
        return (True, "")
        
    # Check that clause is generated by set of antecedents
    # Assumes clause has been processed by cleanClause
    # Return (T/F, Reason)
    def checkResolution(self, clause, idList, subsetOK):
        rids = list(idList)
        rids.reverse()
        if rids[0] not in self.clauseDict:
            return (False, "Clause #%d does not exist" % rids[0])
        rclause, msg = self.findClause(rids[0])
        if rclause is None:
            return (False, "Resolution failed: %s" % msg)
        for nid in rids[1:]:
            nclause, msg = self.findClause(nid)
            if nclause is None:
                return (False, "Resolution failed: %s" % msg)
            try:
                rclause = resolveClauses(rclause, nclause)
            except ResolveException as ex:
                return (False, "Failed to resolve clause #%d (%s) with partial result %s (%s)" % (nid, showClause(nclause), showClause(rclause), str(ex)))
        if subsetOK and testClauseSubset(rclause, clause) or testClauseEquality(clause, rclause):
            return (True, "")
        else:
            key = "allowed" if subsetOK else "not allowed"
            return (False, "Antecedents resolve to %s, not to %s. Subset %s." % (showClause(rclause), showClause(clause), key))
                
    # Check that clause is blocked w.r.t. its first literal
    # Return (T/F, Reason)
    def checkBlocked(self, clause, blockList):
        if clause is None:
            return (False, "Invalid clause")
        if len(clause) == 0:
            return (False, "Empty clause")
        lit = clause[0]
        subclause = clause[1:]
        nlit = -lit
        if nlit not in self.literalCountDict:
            if len(blockList) == 0:
                return (True, "")
            else:
                return (False, "No clauses recorded having literal %d.  Expected %d" % nlit, len(blockList))
        if len(blockList) != self.literalCountDict[nlit]:
            msg = "Literal %d contained in %d clauses"  % (nlit, self.literalCountDict[nlit])
            if self.verbose:
                msg += " (%s)" % str(list(self.literalSetDict[nlit]))
            msg += ".  %d given" % (len(blockList))
            return (False, msg)
        for nid in blockList:
            id = abs(nid)
            bclause, msg = self.findClause(id)
            if bclause is None:
                return (False, msg)
            found = False
            for clit in subclause:
                if -clit in bclause:
                    found = True
                    break
            if not found:
                return (False, "Couldn't find complementary literal in clause #%d" % id)
        return (True, "")

    # Check that resolventList gives all resolvents from sourceList by resolution on var
    def checkDavisPutnam(self, var, sourceList, resolventList, varDict):
        (vlevel, isExistential) = varDict[var]
        plist = []
        nlist = []
        for id in sourceList:
            clause, msg = self.findClause(id)
            if clause is None:
                return (False, msg)
            # Check all universal variables in clause
            for clit in clause:
                cvar = abs(clit)
                if cvar not in varDict:
                    return (False, "Unknown variable %d in clause #%d" % (cvar, id))
                (clevel, cex) = varDict[cvar]
                if not cex and clevel > vlevel:
                    return (False, "Higher universal variable %d in clause for D-P reduction on %d" % (cvar, var))
            if var in clause:
                plist.append(clause)
            elif -var in clause:
                nlist.append(clause)
            else:
                return (False, "Clause #%d includes neither %d nor -%d" % (id, var, var))
        if len(plist) != self.literalCountDict[var]:
            msg = "Expecting %d clauses containing literal %d.  Found %d" % (len(plist), var, self.literalCountDict[var])
            if self.verbose:
                msg += " (%s)" % (str(list(self.literalSetDict[var])))
            return (False, msg)
        if len(nlist) != self.literalCountDict[-var]:
            msg = "Expecting %d clauses containing literal -%d.  Found %d" % (len(nlist), var, self.literalCountDict[-var])
            if self.verbose:
                msg += " (%s)" % (str(list(self.literalSetDict[-var])))
            return (False, msg)


        checkList = []
        for id in resolventList:
            clause, msg = self.findClause(id)
            if clause is None:
                return (False, msg)
            checkList.append(clause)

        for pclause in plist:
            for nclause in nlist:
                rclause = resolveClauses(pclause, nclause)
                if rclause is not None:
                    found = False
                    for mclause in checkList:
                        if testClauseEquality(rclause, mclause):
                            found = True
                            break
                    if not found:
                        return (False, "Couldn't find resolvent %s in candidate clauses" % showClause(rclause))
        return (True, "")


class ProofException(Exception):
    def __init__(self, value, lineNumber = None):
        self.value = value
        self.lineNumber = lineNumber

    def __str__(self):
        nstring = " (Line %d)" % self.lineNumber if self.lineNumber is not None else ""
        return ("Proof Exception%s: " % nstring) + str(self.value)

class Prover:
    verbose = False
    lineNumber = 0
    # Clause Manager
    cmgr = None
    # List of input variables.
    # Mapping from variable number to (qlevel, isExistential)
    varDict = {}
    # Version of varDict created after shift variables
    shiftedVarDict = {}
    failed = False
    # Levels for variables.  Each is mapping from level to list of variables in that level
    initialLevels = {}
    shiftedLevels = {}
    ruleCounters = {}
    subsetOK = False

    def __init__(self, qreader, verbose = False):
        self.verbose = verbose
        self.lineNumber = 0
        self.cmgr = ClauseManager(verbose)
        self.varDict = { v : (q, e) for (v, q, e) in qreader.varList }
        self.shiftedVarDict = {}
        self.failed = False
        self.subsetOK = False
        self.ruleCounters = {'a' : 0, 'ab' : 0, 'ar' : 0, 'd' : 0, 'dr' : 0, 'dd' : 0, 'l' : 0, 'u' : 0, 'x' : 0 }
        for clause in qreader.clauses:
            nclause = cleanClause(clause)
            if not regularClause(nclause):
                self.failProof("Cannot add %s as input clause" % showClause(clause))
                break
            (ok, msg) = self.cmgr.addClause(nclause, id = None)
            if not ok:
                self.failProof(msg)
                break

    def flagError(self, msg):
        print("ERROR.  Line %d: %s" % (self.lineNumber, msg))
        self.failed = True

    def prove(self, fname):
        foundLevels = False
        doneLevels = False
        if self.failed:
            self.failProof("Problem with QCNF file")
            return
        try:
            pfile = open(fname)
        except:
            self.failProof("Couldn't open proof file '%s" % fname)
            return
        for line in pfile:
            self.lineNumber += 1
            fields = line.split()
            if len(fields) == 0 or fields[0][0] == 'c':
                continue
            try:
                id = None if fields[0] == '-' else int(fields[0])
            except:
                self.flagError("First element must be dash or integer.  Got '%s'" % fields[0])
                break
            if len(fields) == 1:
                self.flagError("No command present")
                break
            cmd = fields[1]
            if cmd not in self.ruleCounters:
                self.invalidCommand(cmd)
                break
            self.ruleCounters[cmd] += 1
            rest = fields[2:]
            # Dispatch on command
            # Level command requires special consideration, since it only occurs at beginning of file
            if cmd == 'l':
                if doneLevels:
                    self.flagError("Cannot declare level after any other command")
                    break
                if not foundLevels:
                    foundLevels = True
                self.doLevel(rest)
                continue
            elif foundLevels and not doneLevels:
                if not self.checkLevels():
                    break
                self.varDict = self.shiftedVarDict
            doneLevels = True
            if cmd == 'a':
                self.doAdd(id, rest)
            elif cmd == 'ab':
                self.doAddBlocked(id, rest)
            elif cmd == 'ar':
                self.doAddResolution(id, rest)
            elif cmd == 'd':
                self.doDelete(rest)
            elif cmd == 'dd':
                self.doDeleteDavisPutnam(rest)
            elif cmd == 'dr':
                self.doDeleteResolution(rest)
            elif cmd == 'u':
                self.doUniversalReduction(id, rest)
            elif cmd == 'x':
                self.doExtend(rest)
            else:
                self.invalidCommand(cmd)
            if self.failed:
                break
        pfile.close()
        self.checkProof()
            
    def invalidCommand(self, cmd):
        self.flagError("Invalid command '%s' in proof" % cmd)

    def doLevel(self, rest):
        if len(rest) < 3:
            self.flagError("Expected level, variable(s), and terminating zero")
            return
        try:
            ifields = [int(r) for r in rest]
        except:
            self.flagError("Expected integer level and variable(s)")
            return
        if ifields[-1] != 0:
            self.flagError("Expected expected terminating zero")
            return
        level = ifields[0]
        vars = ifields[1:-1]
        for v in vars:
            if v not in self.varDict:
                self.flagError("Invalid variable: %d" % v)
                return
            (q, e) = self.varDict[v]
            self.shiftedVarDict[v] = (level, e)

    def doAdd(self, id, rest):
        self.invalidCommand('a')

    def doAddBlocked(self, id, rest):
        self.invalidCommand('ab')
        
    def doAddResolution(self, id, rest):
        self.invalidCommand('ar')

    def doDelete(self, rest):
        self.invalidCommand('d')

    def doDeleteDavisPutnam(self, rest):
        self.invalidCommand('dd')
        
    def doDeleteResolution(self, rest):
        self.invalidCommand('dr')

    def doUniversalReduction(self, id, rest):
        self.invalidCommand('u')

    def doExtend(self, rest):
        if len(rest) < 3:
            self.flagError("Expected level and variable(s)")
            return
        try:
            level = int(rest[0])
        except:
            self.flagError("Expecting level as number")
            return
        try:
            zero = int(rest[-1])
        except:
            self.flagError("Expecting terminating zero")
            return
        if zero != 0:
            self.flagError("Expecting terminating zero")            
        for vs in rest[1:-1]:
            try:
                var = int(vs)
            except:
                self.flagError("Can't parse '%s' as variable" % vs)
                return
            if var in self.varDict:
                self.flagError("Variable %d already declared" % var)
                return
            self.varDict[var] = (level, True)

    # Check to make sure two lists are equal.  Return (in1-not-in2,in2-not-in1)
    def diffLists(self, ls1, ls2):
        ls1 = sorted(ls1)
        ls2 = sorted(ls2)
        ls1not2 = []
        ls2not1 = []
        idx1 = 0
        idx2 = 0
        while idx1 < len(ls1) and idx2 < len(ls2):
            v1 = ls1[idx1]
            v2 = ls2[idx2]
            if v1 == v2:
                idx1 += 1
                idx2 += 1
            elif v1 < v2:
                ls1not2.append(v1)
                idx1 += 1
            else:
                ls2not1.append(v2)
                idx2 += 1
        while idx1 < len(ls1):
            ls1not2.append(ls1[idx1])
            idx1 += 1
        while idx2 < len(ls2):
            ls2not1.append(ls2[idx2])
            idx2 += 1
        return (ls1not2, ls2not1)

    # Make sure shifted variables compatible with original
    def checkLevels(self):
        ilevels = []
        ivarList = {}

        ilist = self.varDict.keys()
        slist = self.shiftedVarDict.keys()
        (inots, snoti) = self.diffLists(ilist, slist)
        if len(inots) > 0:
            self.flagError("Mismatch.  Shifted versions of variables not declared: %s" % str(inots))
            return False
        if len(snoti) > 0:
            self.flagError("Mismatch.  Invalid variables given shifted levels: %s" % str(snoti))
            return False

        for v in self.varDict.keys():
            (level, e) = self.varDict[v]
            if level not in ilevels:
                ilevels.append(level)
                ivarList[level] = [v]
            else:
                ivarList[level].append(v)
        ilevels.sort()

        slevels = []
        svarList = {}
        for v in self.shiftedVarDict.keys():
            (level, e) = self.shiftedVarDict[v]
            if level not in slevels:
                slevels.append(level)
                svarList[level] = [v]
            else:
                svarList[level].append(v)
        slevels.sort()
            
        sindex = 0
        for ilevel in ilevels:
            ivars = ivarList[ilevel]
            svars = []
            while len(svars) < len(ivars):
                svars = svars + svarList[slevels[sindex]]
                sindex += 1
            (inots, snoti) = self.diffLists(ivars, svars)
            if len(inots) > 0:
                self.flagError("Mismatch.  Input level %d.  Shifted versions of variables not declared: %s" % (ilevel, str(inots)))
                return False
            if len(snoti) > 0:
                self.flagError("Mismatch.  Input level %d.  Invalid variables given shifted levels: %s" % (ilevel, str(snoti)))
                return False
        return True

    def failProof(self, reason):
        self.failed = True
        msg = "PROOF FAILED"
        if reason != "":
            msg += ": " + reason
        print(msg)

    def passProof(self, name = None):
        if name is not None:
            print("%s PROOF SUCCESSFUL" % name)
        else:
            print("PROOF SUCCESSFUL")            

    def checkProof(self):
        self.failProof("This prover can't prove anything")
        self.summarize()
            
    def summarize(self):
        clist = sorted(self.ruleCounters.keys())
        tcount = 0
        print("%d total clauses" % self.cmgr.totalClauseCount)
        print("%d maximum live clauses" % self.cmgr.maxLiveClauseCount)
        print("Command occurences:")
        for cmd in clist:
            count = self.ruleCounters[cmd]
            if count > 0:
                tcount += count
                print("    %2s   : %d" % (cmd, count))
        print("    TOTAL: %d" % (tcount))
        

    # Get integers until encounter 0.
    # return (list of integers, rest of input list, message)
    def getIntegerList(self, slist):
        ilist = []
        msg = ""
        count = 0
        for sval in slist:
            try:
                val = int(sval)
            except:
                return (None, slist[count:], "'%s' not valid integer" % sval)
            if val == 0:
                return(ilist, slist[count+1:], msg)
            else:
                ilist.append(val)
                count += 1
        # Didn't get terminating zero
        return (None, slist, "Terminating zero not found")
        
class DualProver(Prover):
    addedEmpty = False

    def __init__(self, qreader, verbose):
        Prover.__init__(self, qreader, verbose)
        self.subsetOK = True
        self.addedEmpty = False
    
    def doAddBlocked(self, id, rest):
        (clause, rest, msg) = self.getIntegerList(rest)
        if clause is None:
            self.flagError(msg)
            return
        nclause = cleanClause(clause)
        if not regularClause(nclause):
            self.flagError("Cannot add %s as blocked clause" % showClause(clause))
            return
        (blockList, rest, msg) = self.getIntegerList(rest)
        if blockList is None:
            self.flagError(msg)
            return
        if len(rest) > 0:
            self.flagError("Extraneous values at end of line")
            return
        (ok, msg) = self.cmgr.checkBlocked(clause, blockList)
        if not ok:
            self.flagError(msg)
            return
        (ok, msg) = self.cmgr.addClause(nclause, id)
        if not ok:
            self.flagError(msg)
            return
        
    def doAddResolution(self, id, rest):
        (clause, rest, msg) = self.getIntegerList(rest)
        if clause is None:
            self.flagError(msg)
            return
        nclause = cleanClause(clause)
        if not regularClause(nclause):
            self.flagError("Cannot add %s by resolution" % showClause(clause))
            return
        (antecedents, rest, msg) = self.getIntegerList(rest)
        if antecedents is None:
            self.flagError(msg)
            return
        if len(rest) > 0:
            self.flagError("Extraneous values at end of line")
            return
        (ok, msg) = self.cmgr.checkResolution(nclause, antecedents, self.subsetOK)
        if not ok:
            self.flagError(msg)
            return
        (ok, msg) = self.cmgr.addClause(nclause, id)
        if not ok:
            self.flagError(msg)
            return

    def doUniversalReduction(self, id, rest):
        if len(rest) != 2:
            self.flagError("Expected literal and clause Id")
            return
        try:
            ulit = int(rest[0])
            oid = int(rest[1])
        except:
            self.flagError("Expecting literal and clause Id as two numbers")
            return
        uvar = abs(ulit)
        if uvar not in self.varDict:
            self.flagError("Universal variable %d does not exist" % uvar)
            return
        (vlevel, isExistential) = self.varDict[uvar]
        if isExistential:
            self.flagError("Variable %d is existential" % uvar)
            return
        if oid not in self.cmgr.clauseDict:
            self.flagError("Clause #%d does not exist" % oid)
            return
        oclause, msg = self.cmgr.findClause(oid)
        if oclause is None:
            self.flagError(msg)
            return
        nclause = []
        for clit in oclause:
            cvar = abs(clit)
            if clit == ulit:
                continue
            if uvar == cvar:
                self.flagError("Universal literal %d complemented in clause #%d" % (ulit, oid))
                return
            (qlevel, isExistential) = self.varDict[cvar]
            if isExistential and qlevel > vlevel:
                self.flagError("Existential literal %d is too high (%d) in quantification order compared to universal literal %d (%d)" % (clit, qlevel, ulit, vlevel))
                return
            nclause.append(clit)
        (ok, msg) = self.cmgr.addClause(nclause, id)
        if not ok:
            self.flagError(msg)
            return

    def doDeleteDavisPutnam(self, rest):
        if len(rest) == 0:
            self.flagError("Need DP variable")
            return
        try:
            var = int(rest[0])
        except:
            self.flagError("Invalid DP variable '%s'" % rest[0])
            return
        if var not in self.varDict:
            self.flagError("Nonexistent DP variable %d" % var)
            return
        (qlevel, isExistential) = self.varDict[var]
        if not isExistential:
            self.flagError("Cannot perform D-P reduction on universal variable %d" % var)
            return
        (dlist, rest, msg) = self.getIntegerList(rest[1:])
        if dlist is None:
            self.flagError(msg)
            return
        (rlist, rest, msg) = self.getIntegerList(rest)
        if rlist is None:
            self.flagError(msg)
            return
        if len(rest) > 0:
            self.flagError("Extraneous values at end of line")
            return
        (ok, msg) = self.cmgr.checkDavisPutnam(var, dlist, rlist, self.varDict)
        if not ok:
            self.flagError(msg)
            return
        for id in dlist:
            (ok, msg) = self.cmgr.deleteClause(id)
            if not ok:
                self.flagError(msg)
                return

    def doDeleteResolution(self, rest):
        if len(rest) < 3:
            self.flagError("Need deletion Id and antecedents")
            return
        try:
            did = int(rest[0])
        except:
            self.flagError("Invalid deletion Id '%s'" % rest[0])
            return
        if did not in self.cmgr.clauseDict:
            self.flagError("Nonexistent clause for deletion")
            return
        dclause, msg = self.cmgr.findClause(did)
        if dclause is None:
            self.flagError(msg)
        (antecedents, rest, msg) = self.getIntegerList(rest[1:])
        if antecedents is None:
            self.flagError(msg)
            return
        if len(rest) > 0:
            self.flagError("Extraneous values at end of line")
            return
        if did in antecedents:
            self.flagError("Resolvent cannot be in antecedent")
            return
        (ok, msg) = self.cmgr.checkResolution(dclause, antecedents, self.subsetOK)
        if not ok:
            self.flagError(msg)
            return
        (ok, msg) = self.cmgr.deleteClause(did)
        if not ok:
            self.flagError(msg)
            return

    def checkProof(self):
        if self.failed:
            self.failProof("")
        elif self.cmgr.addedEmpty:
            self.passProof("REFUTATION")
        elif self.cmgr.liveClauseCount == 0:
            self.passProof("SATISFACTION")
        else:
            msg = "No empty clause has been added, and there are still %d live clauses" % (self.cmgr.liveClauseCount)
            if self.verbose:
                msg += ": %s" % (str(list(self.cmgr.liveClauseSet)))
            self.failProof(msg)
        self.summarize()

            
class RefutationProver(DualProver):

    def __init__(self, qreader, verbose):
        DualProver.__init__(self, qreader, verbose)

    def doAdd(self, id, rest):
        self.invalidCommand('a')

    def doDelete(self, rest):
        (idList, rest, msg) = self.getIntegerList(rest)
        if idList is None:
            self.flagError(msg)
            return
        if len(rest) > 0:
            self.flagError("Extraneous values at end of line")
            return
        for id in idList:
            (ok, msg) = self.cmgr.deleteClause(id)
            if not ok:
                self.flagError(msg)
                return

    def checkProof(self):
        if self.failed:
            self.failProof("")
        elif self.cmgr.addedEmpty:
            self.passProof("REFUTATION")
        else:
            self.failProof("Have not added empty clause")
        self.summarize()

class SatisfactionProver(DualProver):

    def __init__(self, qreader, verbose):
        DualProver.__init__(self, qreader, verbose)
        self.subsetOK = True

    def doDelete(self, rest):
        self.invalidCommand('d')

    def doAdd(self, id, rest):
        (clause, rest, msg) = self.getIntegerList(rest)
        if clause is None:
            self.flagError(msg)
            return
        if len(rest) > 0:
            self.flagError("Extraneous values at end of line")
            return
        nclause = cleanClause(clause)
        (ok, msg) = self.cmgr.addClause(nclause, id)
        if not ok:
            self.flagError(msg)
            return
    
    def checkProof(self):
        if self.failed:
            self.failProof("")
        elif self.cmgr.liveClauseCount == 0:
            self.passProof("SATISFACTION")
        else:
            msg = "There are still %d live clauses" % (self.cmgr.liveClauseCount)
            if self.verbose:
                msg += ": %s" % (str(list(self.cmgr.liveClauseSet)))
            self.failProof(msg)
        self.summarize()

def run(name, args):
    qcnfName = None
    proofName = None
    refutationOnly = False
    satisfactionOnly = False
    verbose = False
    optList, args = getopt.getopt(args, "hm:vi:p:")
    for (opt, val) in optList:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-m':
            if val == 's':
                satisfactionOnly = True
            elif val == 'r':
                refutationOnly = True
            elif val == 'd':
                pass
            else:
                print("Unknown proof mode '%s'" % val)
                usage(name)
                return
        elif opt == '-v':
            verbose = True
        elif opt == '-i':
            qcnfName = val
        elif opt == '-p':
            proofName = val
        else:
            usage(name)
            return
    if qcnfName is None:
        print("Need QCNF file name")
        return
    if proofName is None:
        print("Need proof file name")
        return
    start = datetime.datetime.now()
    qreader = QcnfReader(qcnfName)
    if qreader.failed:
        print("Error reading QCNF file: %s" % qreader.errorMessage)
        print("PROOF FAILED")
        return
    if refutationOnly:
        prover = RefutationProver(qreader, verbose)
    elif satisfactionOnly:
        prover = SatisfactionProver(qreader, verbose)
    else:
        prover = DualProver(qreader, verbose)
    prover.prove(proofName)
    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    print("Elapsed time for check: %.2f seconds" % seconds)

    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
