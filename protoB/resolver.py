#!/usr/bin/python

import datetime
import sys

# Resolution engine tailored to generating proofs 
# having a "V" structure, consisting of two linear chains merging together

# Special value to represent true/tautology
# It's negation represents false/invalid
tautologyId = 1000 * 1000 * 1000

# Clean up clause.
# Remove duplicates + false
# Detect when tautology
# Make sure that literal with highest-numbered variable stays at front
# (by sorting in reverse order of literal number)
def cleanClause(literalList):
    slist = sorted(literalList, key = lambda v: -abs(v))
    while len(slist) > 0:
        # Tautology and Null will be in front
        first = slist[0]
        if abs(first) != tautologyId:
            break
        elif first == tautologyId:
            return tautologyId
        else:
            slist = slist[1:]
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

def regularClause(clause):
    return clause is not None and clause != tautologyId and clause != -tautologyId

def showClause(clause):
    if clause is None:
        return "NONE"
    if clause == tautologyId:
        return "TAUT"
    elif clause == -tautologyId:
        return "NIL"
    return str(clause)

class ResolveException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Resolve Exception: " + str(self.value)

# Given two clauses, each processed by cleanClause,
# attempt to resolve them.
# Return result if successful, or None if fails
def resolveClauses(clause1, clause2):
    if not regularClause(clause1):
        msg = "Cannot do resolution on clause %s" % showClause(clause1)
        raise ResolveException(msg)
    if not regularClause(clause2):
        msg = "Cannot do resolution on clause %s" % showClause(clause2)
        raise ResolveException(msg)
#    sc1 = showClause(clause1)
#    sc2 = showClause(clause2)
    result = []
    resolutionVariable = None
    while True:
        if len(clause1) == 0:
            if resolutionVariable is None:
                result = None
            else:
                result += clause2
            break
        if len(clause2) == 0:
            if resolutionVariable is None:
                result = None
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
                    return None # Multiple complementary literals
        elif abs(l1) > abs(l2):
            clause1 = rc1
            result.append(l1)
        else:
            clause2 = rc2
            result.append(l2)
#    print("R(%s, %s) --> %s" % (sc1, sc2, showClause(result)))
    return result

def testClauseEquality(clause1, clause2):
    if clause1 is None or clause2 is None:
        return False
    if not regularClause(clause1):
        return clause1 == clause2
    if not regularClause(clause2):
        return False
    while True:
        if len(clause1) == 0:
            return len(clause2) == 0
        elif len(clause2) == 0:
            return False
        else:
            l1 = clause1[0]
            l2 = clause2[0]
            clause1 = clause1[1:]
            clause2 = clause2[1:]
            if l1 != l2:
                return False


# Given ordered list of clauses (indicated by clause IDs), attempt resolution on each successive one.
# clauseDict is mapping from clause ID to literal list
# Return resulting clause + list of clauses used during resolution in reverse order
def chainResolve(clauseList, clauseDict):
    if len(clauseList) == 0:
        raise ResolveException("Cannot do chain resolution on empty list of clauses")
    id = clauseList[0]
    antecedents = [id]
    result = clauseDict[id]
    for id in clauseList[1:]:
        clause = clauseDict[id]
        nresult = resolveClauses(result, clause)
        if nresult is None:
            # This little tiebreaking hack works for the cases
            # encountered with BDD operations
            if len(clause) <= len(result) and len(antecedents) == 1:
                antecedents = [id]
                result = clause
        else:
            antecedents.append(id)
            result = nresult
    antecedents.reverse()
    return result, antecedents

# Given ordered list of clauses (indicated by clause IDs), attempt resolution on each successive one.
# clauseDict is mapping from clause ID to literal list
# Return list of possibilities, each consisting of pair (clause, antecedents)
def multiChainResolve(clauseList, clauseDict):
    if len(clauseList) == 0:
        raise ResolveException("Cannot do chain resolution on empty list of clauses")
    id = clauseList[0]
    pairList = [(clauseDict[id], [id])]
    for id in clauseList[1:]:
        clauseAdded = False
        npairList = []
        clause = clauseDict[id]
        for (result, antecedent) in pairList:
            nresult = resolveClauses(result, clause)
            if nresult is None:
                npairList.append((result, antecedent))  # Keep the old one
                if not clauseAdded:
                    npairList.append((clause, [id]))        # Add new clause as possibility
                    clauseAdded = True
            else:
                npairList.append((nresult, [id] + antecedent))
        pairList = npairList
    return pairList

# Record information about resolutions
# Build signature consisting of rule names of clauses generated
# Also histogram of number of clauses generated by each call
# by multiChainResolve
class Profiler:
    prover = None
    signatureDict = {}
    counts = []
    maxCount = 0

    def __init__(self, prover):
        self.prover = prover
        self.signatureDict = {}
        self.counts = [0] * 4
        self.maxCount = 0

    def profile(self, pairList, ruleIndex):
        self.counts[len(pairList)] += 1
        self.maxCount = max(self.maxCount, len(pairList))
        if self.prover.verbLevel <= 1:
            return
        sigList = []
        for (r, a) in pairList:
            # Find names of clauses used in antecedent list a
            anames = []
            for k in ruleIndex.keys():
                if ruleIndex[k] in a:
                    anames.append(k)
            anames.sort()
            sigList.append('+'.join(anames))
        sigList.sort()
        sig = '|'.join(sigList)
        if sig in self.signatureDict:
            self.signatureDict[sig] += 1
        else:
            self.signatureDict[sig] = 1

    def summarize(self):
        self.prover.writer.write("Chain resolution histogram:")
        sum = 0
        count = 0
        for c in range(1, self.maxCount+1):
            count += self.counts[c]
            sum += c * self.counts[c]
            self.prover.writer.write(" %d:%d" % (c, self.counts[c]))
        avg = float(sum)/count
        self.prover.writer.write(" Avg:%.2f\n" % avg)
        if self.prover.verbLevel <= 1:
            return
        self.prover.writer.write("Chain resolution signatures:\n")
        sigList = sorted(self.signatureDict.keys())
        for sig in sigList:
            self.prover.writer.write("%s : %d\n" % (sig, self.signatureDict[sig]))        
        
    

class VResolver:
    prover = None
    rule1Names = []
    rule2Names = []
    antecedentCount = 0
    clauseCount = 0
    runCount = 0
    profiler = None
    
    def __init__(self, prover, rule1Names, rule2Names):
        self.prover = prover
        self.rule1Names = rule1Names
        self.rule2Names = rule2Names
        self.antecedentCount = 0
        self.clauseCount = 0
        self.runCount = 0
        self.tryCount = 0
        self.profiler = Profiler(prover)

    def showRules(self, ruleIndex):
        rlist = ["%s:%d" % (k, ruleIndex[k]) for k in ruleIndex.keys()]
        return "[" + ", ".join(rlist) + "]"

    def run(self, targetClause, ruleIndex, comment):
        self.runCount += 1
        clauseDict = self.prover.clauseDict
        chain1 = []
        for n in self.rule1Names:
            if n in ruleIndex:
                if ruleIndex[n] != tautologyId:
                    chain1.append(ruleIndex[n])
        if len(chain1) == 0:
            tgt = showClause(targetClause)
            msg = "No applicable rules in chain 1 (rule index = %s).  Target = %s" % (self.showRules(ruleIndex), tgt)
            raise ResolveException(msg)
        pairList1 = multiChainResolve(chain1, clauseDict)
        self.profiler.profile(pairList1, ruleIndex)
        chain2 = []
        for n in self.rule2Names:
            if n in ruleIndex:
                if ruleIndex[n] != tautologyId:
                    chain2.append(ruleIndex[n])
        if len(chain2) == 0:
            tgt = showClause(targetClause)
            msg = "No applicable rules in chain 2 (rule index = %s).  Target = %s" % (self.showRules(ruleIndex), tgt)
            raise ResolveException(msg)
        pairList2 = multiChainResolve(chain2, clauseDict)
        self.profiler.profile(pairList2, ruleIndex)
        localTryCount = 0
        for (r1, a1) in pairList1:
            localTryCount += 1
            self.tryCount += 1
            for (r2, a2) in pairList2:
                r = resolveClauses(r1, r2)
                if testClauseEquality(r, targetClause):
                    return self.generateProof(r, r1, a1, r2, a2, comment)
        msg = "Could not justify clause %s.  Tried %d possibilities (rule index = %s)" % (showClause(targetClause), localTryCount, self.showRules(ruleIndex))
        raise ResolveException(msg)
            
    def generateProof(self, r, r1, a1, r2, a2, comment):
        self.antecedentCount += len(a1) + len(a2)
        self.prover.proofCount += 1
        self.clauseCount += 1
        if len(a1) == 1:
            id = self.prover.createClause(r, a1 + a2, comment, isInput = False)
            return id, [id]
        elif len(a2) == 1:
            id = self.prover.createClause(r, a2 + a1, comment, isInput = False)
            return id, [id]
        else:
            id1 = self.prover.createClause(r1, a1, comment, isInput = False)
            id = self.prover.createClause(r, [id1] + a2, comment = None, isInput = False)
            self.clauseCount += 1
            return id, [id1, id]


    def summarize(self):
        if self.prover.verbLevel >= 1 and self.runCount > 0:
            antecedentAvg = float(self.antecedentCount) / float(self.runCount)
            clauseAvg = float(self.clauseCount) / float(self.runCount)
            tryAvg = float(self.tryCount) / float(self.runCount)
            self.prover.writer.write("  Avg antecedents / proof = %.2f.  Avg clauses / proof = %.2f.  Avg tries / proof = %.2f\n" % (antecedentAvg, clauseAvg, tryAvg))
            self.profiler.summarize()


class AndResolver(VResolver):

    def __init__(self, prover):
        rule1Names = ["ANDH", "UHD", "VHD", "WHU"]
        rule2Names = ["ANDL", "ULD", "VLD", "WLU"]
        VResolver.__init__(self, prover, rule1Names, rule2Names)

class ImplyResolver(VResolver):

    def __init__(self, prover):
        rule1Names = ["IMH", "UHD", "VHU"]
        rule2Names = ["IML", "ULD", "VLU"]
        VResolver.__init__(self, prover, rule1Names, rule2Names)
