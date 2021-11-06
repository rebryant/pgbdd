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


# Resolution engine tailored to generating proofs 
# having a "V" structure, consisting of two linear chains merging together

# Special value to represent true/tautology
# Its negation represents false/invalid
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

class VResolver:
    prover = None
    clauseDict = None
    rule1Names = []
    rule2Names = []
    rule1Key = ""
    rule2Key = ""
    antecedentCount = 0
    clauseCount = 0
    runCount = 0

    def __init__(self, prover, rule1Names, rule2Names, rule1Key, rule2Key):
        self.prover = prover
        self.clauseDict = prover.clauseDict
        self.rule1Names = rule1Names
        self.rule2Names = rule2Names
        self.rule1Key = rule1Key
        self.rule2Key = rule2Key
        self.antecedentCount = 0
        self.clauseCount = 0
        self.runCount = 0

    def showRules(self, ruleIndex):
        rlist = ["%s:%d" % (k, ruleIndex[k]) for k in ruleIndex.keys() if ruleIndex[k] != tautologyId]
        return "[" + ", ".join(rlist) + "]"

    def cleanIndex(self, ruleIndex):
        for k in list(ruleIndex.keys()):
            if ruleIndex[k] == tautologyId:
                del ruleIndex[k]

    def run(self, targetClause, splitVariable, ruleIndex, comment):
        self.runCount += 1
        self.cleanIndex(ruleIndex)
        if self.rule1Key not in ruleIndex:
            # Try for single line proof
            targ =  targetClause
            idList = []
            for id in self.rule1Names:
                if id in ruleIndex:
                    idList.append(ruleIndex[id])
            for id in self.rule2Names:
                if id in ruleIndex:
                    idList.append(ruleIndex[id])
            alist = self.RupCheck(targ, idList)
            if alist is not None:
                id = self.generateProofStep(targ, alist, comment)
                return id, [id]

        if self.rule2Key not in ruleIndex:
            # Try for single line proof
            targ =  targetClause
            idList = []
            for id in self.rule2Names:
                if id in ruleIndex:
                    idList.append(ruleIndex[id])
            for id in self.rule1Names:
                if id in ruleIndex:
                    idList.append(ruleIndex[id])
            alist = self.RupCheck(targ, idList)
            if alist is not None:
                id = self.generateProofStep(targ, alist, comment)
                return id, [id]
            
        if True:
            # Must split into two-line proof
            targ =  [-splitVariable] + targetClause
            idList = []
            for id in self.rule1Names:
                if id in ruleIndex:
                    idList.append(ruleIndex[id])
            alist = self.RupCheck(targ, idList)
            if alist is None:
                clist = [str(key) for key in idList]
                raise ResolveException("Couldn't prove positive target: %s using candidates %s" % (str(targ), str(clist)))
            else:
                id1 = self.generateProofStep(targ, alist, comment)
            targ = targetClause
            idList = [id1]
            for id in self.rule2Names:
                if id in ruleIndex:
                    idList.append(ruleIndex[id])
            alist = self.RupCheck(targ, idList)
            if alist is None:
                clist = [key + ":" + str(ruleIndex[key]) for key in idList]
                raise ResolveException("Couldn't prove final target: %s using candidates %s" % (str(targ), str(clist)))
            else:
                id = self.generateProofStep(targ, alist, None)
                return id, [id1, id]
    
    def generateProofStep(self, target, antecedents, comment):
        self.prover.proofCount += 1
        self.antecedentCount += len(antecedents)
        self.clauseCount += 1
        return self.prover.createClause(target, antecedents, comment, isInput = False)


    def summarize(self):
        if self.prover.verbLevel >= 1 and self.runCount > 0:
            antecedentAvg = float(self.antecedentCount) / float(self.runCount)
            clauseAvg = float(self.clauseCount) / float(self.runCount)
            self.prover.writer.write("  Avg antecedents / proof = %.2f.  Avg clauses / proof = %.2f.\n" % (antecedentAvg, clauseAvg))

    # Given list of possible antecedent IDs, see if can justify target clause
    # If so, return modified version of clause Ids containing those involved in propagation
    def RupCheck(self, targetClause, clauseIdList):
        clauseDict = self.clauseDict
        units = [-lit for lit in targetClause]
        relevantIdList = []
        for id in clauseIdList:
            if id not in clauseDict:
                continue
            # Make copy so that can modify
            clause = list(clauseDict[id])
            idx = 0
            while idx < len(clause):
                lit = clause[idx]
                if -lit in units:
                    if len(clause) == 1:
                        # Conflict detected
                        relevantIdList.append(id)
                        return relevantIdList
                    # Remove lit from clause by swapping in last one
                    clause[idx] = clause[-1]
                    clause = clause[:-1]
                elif lit in units:
                    # Clause becomes a tautology.  Not useful anymore
                    break
                else:
                    idx += 1
            if (len(clause) == 1):
                # Unit propagation
                units.append(clause[0])
                relevantIdList.append(id)
        # Reverse unit propagation failed
        return None
            

class AndResolver(VResolver):

    def __init__(self, prover):
        rule1Names = ["WHU", "UHD", "VHD", "ANDH"]
        rule2Names = ["WLU", "ULD", "VLD", "ANDL"]
        rule1Key = "ANDH"
        rule2Key = "ANDL"
        VResolver.__init__(self, prover, rule1Names, rule2Names, rule1Key, rule2Key)

class ImplyResolver(VResolver):

    def __init__(self, prover):
        rule1Names = ["UHD", "VHU", "IMH"]
        rule2Names = ["ULD", "VLU", "IML"]
        rule1Key = "IMH"
        rule2Key = "IML"
        VResolver.__init__(self, prover, rule1Names, rule2Names, rule1Key, rule2Key)


        
