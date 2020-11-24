# Resolution Prover for QBF solver

import bdd
import resolver


class ProverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Prover Exception: " + str(self.value)

class ProverMode:
    (noProof, refProof, satProof) = list(range(3))
    modeNames = ["No Proof", "Refutation Proof", "Satisfaction Proof"]

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
        if self.verbLevel > 1 and comment is not None:
            self.file.write("c " + comment + '\n')

    def createClause(self, result, antecedent, comment = None, isInput = False, isUniversal = False):
        self.comment(comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            return result
        self.clauseCount += 1
        antecedent = list(antecedent)
        middle = ['u'] if isUniversal else []
        rest = result + [0]
        if self.mode == ProverMode.refProof and not self.doQrat:
            rest += antecedent + [0]
        ilist = [self.clauseCount] if not self.doQrat else []
        ilist += middle + rest
        slist = [str(i) for i in ilist]
        istring = " ".join(slist)
        if isInput:
            self.comment(istring)
        else:
            self.file.write(istring + '\n')
        self.clauseDict[self.clauseCount] = result
        self.antecedentDict[self.clauseCount] = antecedent
        return self.clauseCount

    def deleteClauses(self, clauseList):
        if self.mode == ProverMode.refProof:
            for id in clauseList:
                del self.clauseDict[id]
            middle = ['d']
            rest = clauseList + [0]
            ilist = [self.clauseCount] + middle + rest
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            self.file.write(istring + '\n')
        else:
            for id in clauseList:
                middle = ['d']
                rest = clauseList + [0] + self.antecedentDict[id] + [0]
            ilist = [self.clauseCount] + middle + rest
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            self.file.write(istring + '\n')
            del self.clauseDict[id]
            del self.antecedentDict[id]

    def generateStepQP(self, fields, addNumber = True, comment = None):
        self.comment(comment)
        if addNumber:
            self.clauseCount += 1
            fields = [str(self.clauseCount)] + fields
        else:
            fields = ['-'] + fields
        self.file.write(' '.join(fields) + '\n')
        return self.clauseCount

    ## Refutation and satisfaction steps

    # Declare variable levels when not default
    def generateLevels(self, varList):
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
        if self.doQrat:
            # Don't need to declare extension variables
            return
        fields = ['x', str(level), str(var), '0']
        if level not in self.qlevelEvars:
            self.qlevelEvars[level] = {}
        self.qlevelEvars[level][var] = []
        self.evarQlevels[var] = level
        self.generateStepQP(fields, False, comment)

    ## Refutation and satisfaction steps, but with different actions

    def proveAddResolution(self, result, antecedent, comment = None):
        if self.doQrat:
            return self.createClause(result, antecedent, comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        afields = [str(a) for a in antecedent]
        cmd =  'ar' if self.mode == ProverMode.refProof else 'a'
        fields = [cmd] + rfields + ['0'] 
        if self.mode == ProverMode.refProof:
            afields = [str(a) for a in antecedent]
            fields += afields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        if self.mode == ProverMode.satProof:
            qlevel = max([self.idToQlevel[abs(lit)] for lit in result])
            if qlevel in self.qlevelClauses:
                self.qlevelClauses[qlevel].append(stepNumber)
            else:
                self.qlevelClauses[qlevel] = [stepNumber]
        self.clauseDict[stepNumber] = result
        self.antecedentDict[stepNumber] = antecedent
        return stepNumber

    def proveAddBlocked(self, clause, blockers, comment = None):
        if self.doQrat:
            return self.createClause(clause, blockers, comment)
        result = resolver.cleanClause(clause)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        cmd =  'ab' if self.mode == ProverMode.refProof else 'a'
        fields = [cmd] + rfields + ['0']
        if self.mode == ProverMode.refProof:
            bfields = [str(-abs(b)) for b in blockers]
            fields += bfields + ['0']
        stepNumber = self.generateStepQP(fields, True, comment)
        self.clauseDict[stepNumber] = result
        var = abs(clause[0])
        # Record blocking clause
        qlevel = self.evarQlevels[var]
        self.qlevelEvars[qlevel][var].append(stepNumber)
        return stepNumber

    ## Refutation-only steps

    def proveUniversal(self, lit, oldId, comment = None):
        fields = ['u', str(lit), str(oldId)]
        stepNumber = self.generateStepQP(fields, True, comment)
        oclause = self.clauseDict[oldId]
        nclause = [l for l in oclause if l != lit]
        self.clauseDict[stepNumber] = nclause
        return stepNumber

    def proveDelete(self, idList, comment = None):
        ilist = [str(id) for id in idList]
        fields = ['d'] + ilist + ['0']
        self.generateStepQP(fields, False, comment)
        for id in idList:
            self.clauseDict[id] = None
            if id in self.antecedentDict:
                del self.antecedentDict[id]

    ## Satisfaction-only steps
                                
    def proveAdd(self, result, comment = None):
        if self.doQrat:
            return self.createClause(result, comment)
        result = resolver.cleanClause(result)
        if result == resolver.tautologyId:
            self.comment(comment)
            return result
        rfields = [str(r) for r in result]
        fields = ['a'] + rfields + ['0'] 
        stepNumber = self.generateStepQP(fields, True, comment)
        self.clauseDict[stepNumber] = result
        return stepNumber

    def proveDeleteResolution(self, id, antecedent = None, comment = None):
        if self.doQrat:
            return self.proveDelete([id], comment)
        if antecedent is None:
            antecedent = self.antecedentDict[id]
        afields = [str(a) for a in antecedent]
        fields = ['dr', str(id)] + afields + ['0']
        self.generateStepQP(fields, False, comment)
        if id in self.clauseDict:
            del self.clauseDict[id]
        if id in self.antecedentDict:
            del self.antecedentDict[id]

    def proveDeleteDavisPutnam(self, var, deleteIdList, causeIdList, comment = None):
        dlist = [str(id) for id in deleteIdList]
        clist = [str(id) for id in causeIdList]
        fields = ['dd', str(var)] + dlist + ['0'] + clist + ['0']
        self.generateStepQP(fields, False, comment)
        for id in deleteIdList:
            del self.clauseDict[id]
            if id in self.antecedentDict:
                del self.antecedentDict[id]

    def qcollect(self, qlevel):
        # Delete all clauses for qlevels >= qlevel
        qlevels = sorted(self.qlevelClauses.keys(), key=lambda q:-q)
        for q in qlevels:
            if q < qlevel:
                break
            if q in self.qlevelClauses:
                idList = self.qlevelClauses[q]
                idList.reverse()
                comment = "Deleting resolution clauses with qlevel %d" % q
                for id in idList:
                    if id in self.antecedentDict:
                        self.proveDeleteResolution(id, self.antecedentDict[id], comment)
                        comment = None
                self.qlevelClauses[q] = []
            if q in self.qlevelEvars:
                evarList = self.qlevelEvars[q].keys()
                evarList.sort(key = lambda i : -i)
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
