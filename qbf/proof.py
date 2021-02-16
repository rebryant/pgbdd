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

# Resolution Prover for QBF solver

import sys
import bdd
import resolver


class ProverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Prover Exception: " + str(self.value)

class ProverMode:
    (noProof, refProof, satProof, dualProof) = list(range(4))
    modeNames = ["No Proof", "Refutation Proof", "Satisfaction Proof", "Dual Proof"]

class Prover:

    inputClauseCount = 0
    clauseCount = 0
    proofCount = 0
    file = None
    writer = None
    opened = False
    verbLevel = 1
    clauseDict = {}  # Mapping from clause ID to list of literals in clause
    antecedentDict = {}  # Mapping from clause ID to list of antecedents
    mode = None
    doQrat = True
    ### Support for satisfaction proofs
    # Mapping from Id to qlevel.  Items inserted by BDD manager
    idToQlevel = {}
    # Map from qlevel to added resolution clauses
    qlevelClauses = {}
    # Map from qlevel to extension variables.  For each level, have dictionary
    # mapping variable Ids to list of defining clauses
    qlevelEvars = {}
    # Mapping from variable Id to level
    evarQlevels = {}
    # Restrict justifications that encounter degenerate case
    restrictDegeneracies = set([])

    def __init__(self, fname = None, writer = None, mode = None, verbLevel = 1):
        if mode is None:
            self.mode = ProverMode.noProof
        else:
            self.mode = mode
        self.verbLevel = verbLevel
        self.doQrat = False
        if fname is None:
            self.opened = False
            self.file = sys.stdout
        else:
            self.opened = True
            try:
                self.file = open(fname, 'w')
            except Exception:
                raise ProverException("Could not open file '%s'" % fname)
            fields = fname.split('.')
            self.doQrat = fields[-1] == 'qrat'
        self.writer = sys.stderr if writer is None else writer
        self.clauseCount = 0
        self.proofCount = 0
        self.idToQlevel = {}
        self.qlevelClauses = {}
        self.qlevelEvars = {}
        self.evarQlevels = {}
        self.restrictDegeneracies = set([])


    def inputDone(self):
        self.inputClauseCount = self.clauseCount

    def comment(self, comment):
        if self.mode == ProverMode.noProof:
            return
        if self.verbLevel > 1 and comment is not None:
            self.file.write("c " + comment + '\n')

    def expungeClause(self, id):
        if id in self.clauseDict:
            del self.clauseDict[id]
        if id in self.antecedentDict:
            del self.antecedentDict[id]

    # Remove universal literal from clause in QRAT proof
    def qratUniversal(self, id, ulit):
        oclause = self.clauseDict[id]
        nclause = [lit for lit in oclause if lit != ulit]
        slist = ['u'] + [str(i) for i in ([ulit] + nclause + [0])]
        self.file.write(" ".join(slist) + '\n')
        self.clauseDict[id] = nclause
        return id

    def createClause(self, result, antecedent = [], comment = None, isInput = False, isUniversal = False, ulit = None):
        self.comment(comment)
        result = resolver.cleanClause(result, nosort = isUniversal)
        if result == resolver.tautologyId:
            return result
        self.clauseCount += 1
        antecedent = list(antecedent)
        middle = ['u'] if isUniversal else []
        rest = result + [0]
        if self.mode in [ProverMode.refProof, ProverMode.dualProof] and not self.doQrat:
            rest += antecedent + [0]
        ilist = [self.clauseCount] if not self.doQrat else []
        ilist += middle + rest
        slist = [str(i) for i in ilist]
        istring = " ".join(slist)
        if isInput:
            self.comment(istring)
        else:
            self.file.write(istring + '\n')
        if isUniversal and ulit is not None:
            result = [lit for lit in result if lit != ulit]
        self.clauseDict[self.clauseCount] = result
        if len(antecedent) > 0:
            self.antecedentDict[self.clauseCount] = antecedent
        return self.clauseCount

    # Only called with refutation proofs
    def deleteClauses(self, clauseList):
        if self.doQrat:
            for id in clauseList:
                slist = ['d'] + [str(lit) for lit in self.clauseDict[id]] + ['0']
                istring = ' '.join(slist)
                self.file.write(istring + '\n')
        else:
            for id in clauseList:
                self.expungeClause(id)
            slist = ['-', 'd'] + [str(id) for id in clauseList] + ['0']
            istring = " ".join(slist)
            self.file.write(istring + '\n')

    def generateStepQP(self, fields, addNumber = True, comment = None):
        self.comment(comment)
        if addNumber:
            self.clauseCount += 1
            fields = [str(self.clauseCount)] + fields
        else:
            fields = ['-'] + fields
        if self.doQrat is False:
            self.file.write(' '.join(fields) + '\n')
        return self.clauseCount

    ## Refutation and satisfaction steps

    # Declare variable levels when not default
    def generateLevels(self, varList):
        if self.doQrat:
            # No level shifting in qrat
            return
        levelDict = {}
        for (v, l, e) in varList:
            if l in levelDict:
                levelDict[l].append(v)
            else:
                levelDict[l] = [v]
        levels = sorted(levelDict.keys())
        for l in levels:
            fields = ['-', 'l', str(l)] + [str(v) for v in levelDict[l]] + ['0']
            self.file.write(' '.join(fields) + '\n')

    def proveExtend(self, var, level, comment = None):
        fields = ['x', str(level), str(var), '0']
        if level not in self.qlevelEvars:
            self.qlevelEvars[level] = {}
        self.qlevelEvars[level][var] = []
        self.evarQlevels[var] = level
        self.generateStepQP(fields, False, comment)

    ## Refutation, satisfaction and dual steps, but with different actions

    def proveAddResolution(self, result, antecedent, comment = None):
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        afields = [str(a) for a in antecedent]
        cmd =  'ar' if self.mode in [ProverMode.refProof, ProverMode.dualProof] else 'a'
        fields = [cmd] + rfields + ['0']
        if self.mode in [ProverMode.refProof, ProverMode.dualProof]:
            afields = [str(a) for a in antecedent]
            fields += afields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        if len(result) > 0 and self.mode in [ProverMode.satProof, ProverMode.refProof, ProverMode.dualProof]:
            qlevel = max([self.idToQlevel[abs(lit)] for lit in result])
            if qlevel in self.qlevelClauses:
                self.qlevelClauses[qlevel].append(stepNumber)
            else:
                self.qlevelClauses[qlevel] = [stepNumber]
        self.clauseDict[stepNumber] = result
        self.antecedentDict[stepNumber] = antecedent
        if self.doQrat:
            self.file.write(' '.join(rfields) + ' 0\n')
        return stepNumber

    def proveAddBlocked(self, clause, blockers, comment = None):
        result = resolver.cleanClause(clause)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        cmd =  'ab' if self.mode in [ProverMode.refProof, ProverMode.dualProof] else 'a'
        fields = [cmd] + rfields + ['0']
        if self.mode in [ProverMode.refProof, ProverMode.dualProof]:
            bfields = [str(-abs(b)) for b in blockers]
            fields += bfields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        self.clauseDict[stepNumber] = result
        var = abs(clause[0])
        # Record defining clause
        qlevel = self.evarQlevels[var]
        self.qlevelEvars[qlevel][var].append(stepNumber)
        if self.doQrat:
            return self.createClause(result, blockers, comment)
        return stepNumber

    ## Refutation and dual steps

    def proveUniversal(self, lit, oldId, comment = None):
        fields = ['u', str(lit), str(oldId)]
        stepNumber = self.generateStepQP(fields, True, comment)
        oclause = self.clauseDict[oldId]
        nclause = [l for l in oclause if l != lit]
        self.clauseDict[stepNumber] = nclause
        return stepNumber

    ## Satisfaction-only steps

    def proveAdd(self, result, comment = None):
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        fields = ['a'] + rfields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        self.clauseDict[stepNumber] = result
        if self.doQrat:
            return self.createClause(result, comment)
        return stepNumber

    ## Satisfaction and dual steps

    def proveDeleteResolution(self, id, antecedent = None, comment = None):
        if self.doQrat:
            lfields = [str(lit) for lit in self.clauseDict[id]]
            self.file.write('d ' + ' '.join(lfields) + ' 0\n')
            self.expungeClause(id)
            return 
        if antecedent is None:
            antecedent = self.antecedentDict[id]
        afields = [str(a) for a in antecedent]
        fields = ['dr', str(id)] + afields + ['0']
        self.generateStepQP(fields, False, comment)
        self.expungeClause(id)

    def proveDeleteDavisPutnam(self, var, deleteIdList, causeIdList, comment = None):
        dlist = [str(id) for id in deleteIdList]
        if self.doQrat:
            for id in deleteIdList:
                list1 = [lit for lit in self.clauseDict[id] if abs(lit) == var]
                list2 = [lit for lit in self.clauseDict[id] if abs(lit) != var]
                slist = [str(lit) for lit in (list1+list2)]
                self.file.write('d ' + ' '.join(slist) + ' 0\n')
        else:
            clist = [str(id) for id in causeIdList]
            fields = ['dd', str(var)] + dlist + ['0'] + clist + ['0']
            self.generateStepQP(fields, False, comment)
        for id in deleteIdList:
            if id not in self.clauseDict:
                print("INTERNAL ERROR.  Cannot delete clause #%d.  Not in clause dictionary" % id)
                continue
            self.expungeClause(id)

    # Clause removal
    def qcollect(self, qlevel):
        # Delete all clauses for qlevels >= qlevel
        qlevels = sorted(self.qlevelClauses.keys(), key=lambda q:-q)
        for q in qlevels:
            # self.file.write ("level?\n")
            if q < qlevel:
                break
            idList = self.qlevelClauses[q]
            idList.reverse()
            comment = "Deleting resolution clauses with qlevel %d" % q
            for id in idList:
                # self.file.write ("clause\n")
                if id in self.antecedentDict:
                    # self.file.write ("true\n")
                    self.proveDeleteResolution(id, self.antecedentDict[id], comment)
                    comment = None
            self.qlevelClauses[q] = []

        qlevels = sorted(self.qlevelEvars.keys(), key=lambda q:-q)
        for q in qlevels:
            if q < qlevel:
                break
            evarList = sorted(self.qlevelEvars[q].keys(), key=lambda i : -i)
            comment = "Deleting defining clauses for extension variables with qlevel %d" % q
            for evar in evarList:
                dlist = self.qlevelEvars[q][evar]
                self.proveDeleteDavisPutnam(evar, dlist, [], comment)
                comment = None
            self.qlevelEvars[q] = {}


    def summarize(self):
        if self.verbLevel >= 1:
            self.writer.write("Total Clauses: %d\n" % self.clauseCount)
            self.writer.write("Input clauses: %d\n" % self.inputClauseCount)
            acount = self.clauseCount - self.inputClauseCount - self.proofCount
            self.writer.write("Added clauses without antecedents: %d\n" % acount)
            self.writer.write("Added clauses requiring proofs: %d\n" % (self.proofCount))

    def __del__(self):
        if self.opened:
            self.file.close()
