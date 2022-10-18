#!/usr/local/bin/python3
# Simple, proof-generating SAT solver based on BDDs

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

import sys
import getopt
import datetime
import random
import signal

import bdd
import resolver
import stream
import pseudoboolean

# Increase maximum recursion depth
sys.setrecursionlimit(10 * sys.getrecursionlimit())

def usage(name):
    sys.stderr.write("Usage: %s [-h] [-b] [-B BPERM] [-v LEVEL] [-r SEED] [-i CNF] [-o file.{proof,lrat,lratb}] [-M t|b|p] [-p PERMUTE] [-s SCHEDULE] [-m MODULUS] [-L logfile] [-t TLIM] [-Z NZLIM]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -b          Process terms via bucket elimination ordered by variable levels\n")
    sys.stderr.write("  -B BPERM    Process terms via bucket elimination ordered by permutation file BPERM\n")
    sys.stderr.write("  -v LEVEL    Set verbosity level\n")
    sys.stderr.write("  -r SEED     Set random seed (for breaking ties during pivot selection)\n")
    sys.stderr.write("  -i CNF      Name of CNF input file\n")
    sys.stderr.write("  -o pfile    Name of proof output file (.drat = DRAT text, .lrat = LRAT text, .lratb = LRAT binary)\n")
    sys.stderr.write("  -M (t|b|p)  Pipe proof to stdout (p = tracecheck, t = LRAT text, b = LRAT binary)\n")
    sys.stderr.write("  -p PERMUTE  Name of file specifying mapping from CNF variable to BDD level\n")
    sys.stderr.write("  -s SCHEDULE Name of action schedule file\n")
    sys.stderr.write("  -m MODULUS  Specify modulus for equation solver (Either number or 'a' for auto-detect, 'i' for integer mode)\n")
    sys.stderr.write("  -L logfile  Append standard error output to logfile\n")
    sys.stderr.write("  -t TLIM     Set time limit for execution\n")
    sys.stderr.write("  -Z NZLIM    Set limit on number on nonzeros in when solving equations/constraints\n")

# Verbosity levels
# 0: Totally silent
# 1: Key statistics only
# 2: Summary information
# 3: Proof information
# 4: ?
# 5: Tree generation information

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# Read CNF file.
# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class CnfReader():
    file = None
    commentLines = []
    clauses = []
    nvar = 0
    verbLevel = 1
    
    def __init__(self, fname = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            opened = True
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise CnfException("Could not open file '%s'" % fname)
        self.clauses = []
        self.commentLines = []
        try:
            self.readCnf()
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    def readCnf(self):
        lineNumber = 0
        nclause = 0
        self.nvar = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            fields = line.split()
            if len(fields) == 0:
                continue
            elif line[0] == 'c':
                if self.verbLevel > 1:
                    self.commentLines.append(line)
            elif line[0] == 'p':
                fields = line[1:].split()
                if len(fields) != 3 or fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
            else:
                if nclause == 0:
                    raise CnfException("Line %d.  No header line.  Not cnf" % (lineNumber))
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if lits[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                lits = lits[:-1]
                vars = sorted([abs(l) for l in lits])
                if len(vars) == 0:
                    raise CnfException("Line %d.  Empty clause" % lineNumber)                    
                if vars[-1] > self.nvar or vars[0] == 0:
                    raise CnfException("Line %d.  Out-of-range literal" % lineNumber)
                for i in range(len(vars) - 1):
                    if vars[i] == vars[i+1]:
                        raise CnfException("Line %d.  Opposite or repeated literal" % lineNumber)
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            raise CnfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))


# Abstract representation of Boolean function
class Term:

    manager = None
    root = None
#    support = None    # Variables in support represented by clause (omitted)
    size = 0
    validation = None # Clause id providing validation

    def __init__(self, manager, root, validation):
        self.manager = manager
        self.root = root
#        self.support = self.manager.getSupport(root)
        self.size = self.manager.getSize(root)
        self.validation = validation

    # Generate conjunction of two terms
    def combine(self, other):
        validation = None
        antecedents = [self.validation, other.validation]
        newRoot, implication = self.manager.applyAndJustify(self.root, other.root)
        if newRoot == self.manager.leaf0:
            comment = "Validation of Empty clause"
        else:
            comment = "Validation of %s" % newRoot.label()
        if implication == resolver.tautologyId:
            if newRoot == self.root:
                validation = self.validation
            elif newRoot == other.root:
                validation = other.validation
        else:
            antecedents += [implication]
        if validation is None:
            validation = self.manager.prover.createClause([newRoot.id], antecedents, comment)
        return Term(self.manager, newRoot, validation)

    def quantify(self, literals, prover):
        antecedents = [self.validation]
        newRoot = self.manager.equant(self.root, literals)
        check, implication = self.manager.justifyImply(self.root, newRoot)
        if not check:
            raise bdd.BddException("Implication failed %s -/-> %s" % (self.root.label(), newRoot.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        validation = self.manager.prover.createClause([newRoot.id], antecedents, "Validation of %s" % newRoot.label())
        return Term(self.manager, newRoot, validation)

    def equalityTest(self, other):
        root1 = self.root
        root2 = other.root
        return root1 == root2
                                

class PermutationException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Permutation Exception: " + str(self.value)


class Permuter:
    forwardMap = {}
    reverseMap = {}
    
    def __init__(self, valueList = [], permutedList = []):
        self.forwardMap = {}
        self.reverseMap = {}
        identity = False
        if len(permutedList) == 0:
            permutedList = valueList
            identity = True
        if len(valueList) != len(permutedList):
            raise PermutationException("Unequal list lengths: %d, %d" % (len(valueList), len(permutedList)))
        for v, p in zip(valueList, permutedList):
            self.forwardMap[v] = p
            self.reverseMap[p] = v
        if identity:
            return
        # Check permutation
        for v in valueList:
            if v not in self.reverseMap:
                raise PermutationException("Not permutation: Nothing maps to %s" % str(v))
        for v in permutedList:
            if v not in self.forwardMap:
                raise PermutationException("Not permutation: %s does not map anything" % str(v))
            
            
    def forward(self, v):
        if v not in self.forwardMap:
            raise PermutationException("Value %s not in permutation" % (str(v)))
        return self.forwardMap[v]

    def reverse(self, v):
        if v not in self.reverseMap:
            raise PermutationException("Value %s not in permutation range" % (str(v)))
        return self.reverseMap[v]
    
    def __len__(self):
        return len(self.forwardMap)
        
    def permMin(self, v1, v2):
        pv1 = self.reverse(v1)
        pv2 = self.reverse(v2)
        return v1 if pv1 < pv2 else v2

    def permMinList(self, ls):
        if len(ls) == 0:
            return None
        m = ls[0]
        for v in ls[1:]:
            m = self.permMin(v, m)
        return m

class ProverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Prover Exception: " + str(self.value)


# Hack to allow writing binary data to standard output
class StdOutWriter:

    def write(self, data):
        if sys.version_info < (3,0):
            sys.stdout.write(data)
        elif type(data) is str:
            sys.stdout.buffer.write(bytearray(data, 'ascii'))
        else:
            sys.stdout.buffer.write(data)

    def close(self):
        pass

# Ignore any writes
class NullWriter:

    def write(self, data):
        pass

    def close(self):
        pass


class Prover:

    inputClauseCount = 0
    clauseCount = 0
    lastClauseId = 0
    proofCount = 0
    file = None
    writer = None
    opened = False
    verbLevel = 1
    doLrat = False
    doBinary = False
    clauseDict = None

    def __init__(self, fname = None, writer = None, verbLevel = 1, doLrat = False, doBinary = False):
        self.verbLevel = verbLevel
        if fname is None:
            self.opened = False
            self.file = StdOutWriter()
        elif fname == "":
            self.file = NullWriter()
        else:
            self.opened = True
            try:
                self.file = open(fname, 'wb' if doBinary else 'w')
            except Exception:
                raise ProverException("Could not open file '%s'" % fname)
        self.writer = sys.stderr if writer is None else writer
        self.doLrat = doLrat
        self.doBinary = doBinary
        self.clauseCount = 0
        self.lastClauseId = 0
        self.proofCount = 0
        if not doLrat:
            self.clauseDict = {}

    def inputDone(self):
        self.inputClauseCount = self.clauseCount

    def fileOutput(self):
        return self.opened

    def comment(self, comment):
        if self.verbLevel > 1 and comment is not None and not self.doBinary:
            self.file.write("c " + comment + '\n')

    def createClause(self, result, antecedent, comment = None, isInput = False, alreadyClean = False):
        if not alreadyClean:
            result = resolver.cleanClause(result)
        self.lastClauseId += 1
        if result == resolver.tautologyId:
            # Want to skip ID if tautology
            return result
        cid = self.lastClauseId
        self.clauseCount += 1
        self.comment(comment)
        if self.doLrat:
            first = [cid]
            middle = [ord('a')] if self.doBinary else []
            rest = result + [0] + antecedent + [0]
        else:
            first = []
            middle = []
            rest = result + [0]
        ilist = first + middle + rest
        if self.doBinary:
            if not isInput:
                bytes = stream.CompressArray(ilist).bytes
                self.file.write(bytes)
        else:
            slist = [str(i) for i in ilist]
            istring = " ".join(slist)
            if isInput:
                self.comment(istring)
            else:
                self.file.write(istring + '\n')
        if not self.doLrat:
            self.clauseDict[cid] = result
        return cid

    def deleteClauses(self, clauseList):
        if self.doLrat:
            middle = [ord('d')] if self.doBinary else ['d']
            rest = clauseList + [0]
            ilist = [self.clauseCount] + middle + rest
            if self.doBinary:
                bytes = stream.CompressArray(ilist).bytes
                self.file.write(bytes)
            else:
                slist = [str(i) for i in ilist]
                istring = " ".join(slist)
                self.file.write(istring + '\n')
        else:
            for cid in clauseList:
                clause = self.clauseDict[cid]
                middle = [ord('d')] if self.doBinary else ['d']
                rest = clause + [0]
                ilist = middle + rest
                if self.doBinary:
                    bytes = stream.CompressArray(ilist).bytes
                    self.file.write(bytes)
                else:
                    slist = [str(i) for i in ilist]
                    istring = " ".join(slist)
                    self.file.write(istring + '\n')
                
                



    def summarize(self):
        if self.verbLevel >= 1:
            self.writer.write("Total Clauses: %d\n" % self.clauseCount)
            self.writer.write("Input clauses: %d\n" % self.inputClauseCount)
            if self.verbLevel >= 2:
                acount = self.clauseCount - self.inputClauseCount - self.proofCount
                self.writer.write("Added clauses without antecedents: %d\n" % acount)
                self.writer.write("Added clauses requiring proofs: %d\n" % (self.proofCount))

    def __del__(self):
        if self.opened:
            self.file.close()



class SolverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Solver Exception: " + str(self.value)


class Solver:
    
    verbLevel = 1
    manager = None
    # How many terms have been generated
    termCount = 0
    # Mapping from input Ids to BDD representation of literal
    litMap = {}

    # Dictionary of terms corresponding to input clauses.
    # These will be removed from activeClauses when used
    # but they can be reactivated
    inputIds = {}
    # Dictionary of Ids of terms remaining to be combined
    activeIds = {}
    unsat = False
    permuter = None
    prover = None
    writer = None
    # Turn on to have information about node include number of solutions
    countSolutions = True

    # Support for equations
    modulus = pseudoboolean.modulusAuto
    equationSystem = None
    # Support for constraints
    constraintSystem = None


    def __init__(self, fname = None, prover = None, permuter = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if prover is None:
            prover = Prover(verbLevel = verbLevel)
        self.prover = prover
        self.writer = prover.writer
        try:
            reader = CnfReader(fname, verbLevel = verbLevel)
        except Exception as ex:
            self.writer.write("Aborted: %s\n" % str(ex))
            raise ex
        clauseCount = 0
        # Print input clauses
        for clause in reader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount, isInput = True)

        if clauseCount == 0:
            self.writer.write("No clauses in CNF File\n")
            raise SolverException("Empty CNF file")

        self.prover.inputDone()

        self.manager = bdd.Manager(prover = self.prover, rootGenerator = self.rootGenerator,
                                   nextNodeId = reader.nvar+1, verbLevel = verbLevel)
        # Generate BDD representations of literals
        if permuter is None:
            # Default is identity permutation
            permuter = Permuter(list(range(1, reader.nvar+1)))
        self.permuter = permuter
        # Construct literal map
        self.litMap = {}
        for level in range(1, reader.nvar+1):
            inputId = self.permuter.forward(level)
            var = self.manager.newVariable(name = "V%d" % inputId, id = inputId)
            t = self.manager.literal(var, 1)
            self.litMap[ inputId] = t
            e = self.manager.literal(var, 0)
            self.litMap[-inputId] = e
        # Generate BDD representations of clauses
        self.termCount = 0
        self.inputIds = {}
        self.activeIds = {}
        for clause in reader.clauses:
            self.termCount += 1
            litList = [self.litMap[v] for v in clause]
            root, validation = self.manager.constructClause(self.termCount, litList)
            term = Term(self.manager, root, validation)
            self.inputIds[self.termCount] = term
            self.activeIds[self.termCount] = term
        self.unsat = False

    # Simplistic version of scheduling
    def choosePair(self):
        ids = sorted(self.activeIds.keys())
        return ids[0], ids[1]

    # Attempt to retrieve term
    def getTerm(self, id):
        if id in self.activeIds:
            return self.activeIds[id]
        elif id in self.inputIds:
            return self.inputIds[id]
        else:
            return None

    # Remove term.  Can trigger GC, so be sure that all
    # active BDDs have been captured as terms
    def removeTerm(self, id):
        term = None
        if id in self.activeIds:
            term = self.activeIds[id]
            del self.activeIds[id]
        if id not in self.inputIds:
            if term is not None:
                term.root = None
            clauseList = self.manager.checkGC(term.size)
            if len(clauseList) > 0:
                self.prover.deleteClauses(clauseList)

    def combineTerms(self, id1, id2):
        termA = self.getTerm(id1)
        termB = self.getTerm(id2)
        newTerm = termA.combine(termB)
        self.termCount += 1
        comment = "T%d (Node %s) & T%d (Node %s)--> T%s (Node %s)" % (id1, termA.root.label(), id2, termB.root.label(),
                                                                      self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        if self.prover.fileOutput() and self.verbLevel >= 3:
            self.writer.write("Combine: %s\n" % (comment))
        self.activeIds[self.termCount] = newTerm
        self.removeTerm(id1)
        self.removeTerm(id2)
        if newTerm.root == self.manager.leaf0:
            if self.prover.fileOutput() and self.verbLevel >= 1:
                self.writer.write("UNSAT\n")
            self.unsat = True
            self.manager.summarize()
            return -1
        return self.termCount

    def quantifyTerm(self, id, varList):
        term = self.getTerm(id)
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        newTerm = term.quantify(clause, self.prover)
        self.termCount += 1
        vstring = " ".join(sorted([str(v) for v in varList]))
        comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        self.activeIds[self.termCount] = newTerm
        self.removeTerm(id)
        return self.termCount

    def runNoSchedule(self):
        nid = 0
        while (len(self.activeIds) > 1):
            i, j = self.choosePair()
            nid = self.combineTerms(i, j)
            if nid < 0:
                return
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")
        if self.verbLevel >= 1:
            for s in self.manager.satisfyStrings(self.activeIds[nid].root, limit = 20):
                self.writer.write("  " + s)
        
    def runSchedule(self, scheduler, modulus, nzLimit):
        self.modulus = modulus
        idStack = []
        lineCount = 0
        for line in scheduler:
            line = trim(line)
            lineCount += 1
            fields = line.split()
            if len(fields) == 0:
                continue
            cmd = fields[0]
            if self.verbLevel >= 3:
                self.writer.write("Processing schedule command #%d: %s\n" % (lineCount, line))
            if cmd == '#':
                continue
            if cmd == 'i':  # Information request
                if len(idStack) == 0:
                    raise SolverException("Line #%d.  Nothing on stack" % lineCount)
                # Use rest of string as documentation
                line = trim(line)
                cstring = line[1:] if  len(line) >= 1 else ""
                root =  self.activeIds[idStack[-1]].root
                size = self.manager.getSize(root)
                if self.verbLevel >= 1:
                    if self.countSolutions:
                        count = self.manager.satisfyCount(root)
                        self.writer.write("Node %d.  Size = %d, Solutions = %d.%s\n" % (root.id, size, count, cstring))
                    else:
                        self.writer.write("Node %d.  Size = %d.%s\n" % (root.id, size, cstring))
                continue
            if cmd[0] != '=' and cmd != '>=':
                try:
                    values = [int(v) for v in fields[1:]]
                except:
                    raise SolverException("Line #%d.  Invalid field '%s'" % (lineCount, line))
            if cmd == 'c':  # Put listed clauses onto stack
                idStack += values
            elif cmd == 'a':  # Pop n+1 clauses from stack.  Form their conjunction.  Push result back on stack
                count = values[0]
                if count+1 > len(idStack):
                    raise SolverException("Line #%d.  Invalid conjunction count %d.  Only have %d on stack" %
                                          (lineCount, count, len(idStack)))
                for i in range(count):
                    id1 = idStack[-1]
                    id2 = idStack[-2]
                    idStack = idStack[:-2]
                    nid = self.combineTerms(id1, id2)
                    if nid < 0:
                        # Hit unsat case
                        return "unsatisfiable"
                    else:
                        idStack.append(nid)
            elif cmd == 'q':
                if len(idStack) < 1:
                    raise SolverException("Line #%d.  Stack is empty" % (lineCount))
                id = idStack[-1]
                idStack = idStack[:-1]
                nid = self.quantifyTerm(id, values)
                idStack.append(nid)
            elif cmd[0] == '=':
                # Equation
                modulus = self.modulus
                if len(cmd) > 1:
                    try:
                        modulus = int(cmd[1:])
                    except:
                        raise SolverException("Line #%d.  Couldn't read equation modulus from command '%s'" % (lineCount, cmd))
                if self.equationSystem is None:
                    nvar = len(self.litMap) // 2
                    self.equationSystem = pseudoboolean.EquationSystem(nvar, modulus, verbose = self.verbLevel >= 3, manager = self.manager, writer = self.writer)
                    self.modulus = modulus
                elif self.equationSystem.modulus != modulus:
                    raise SolverException("Line #%d.  Don't support multiple moduli.  Existing %d.  New %d" % (lineCount, self.equationSystem.modulus, modulus))
                const = int(fields[1])
                nvar = self.equationSystem.N
                mbox = self.equationSystem.mbox
                e = pseudoboolean.Equation(nvar, modulus, const, mbox)
                for field in fields[2:]:
                    parts = field.split('.')
                    coeff = int(parts[0])
                    var = int(parts[1])
                    e[var] = coeff
                eid = self.equationSystem.addInitialEquation(e)
                if len(idStack) < 1:
                    raise SolverException("Line #%d.  Stack is empty" % (lineCount))
                id = idStack[-1]
                idStack = idStack[:-1]
                termBdd = self.activeIds[id].root
                termValidation = self.activeIds[id].validation
                equBdd = e.root
                if termBdd == equBdd:
                    e.validation = termValidation
                    continue
                antecedents = [termValidation]
                check, implication = self.manager.justifyImply(termBdd, equBdd)
                if not check:
                    raise bdd.BddException("Implication of equation #%d from term failed %s -/-> %s" % (eid, termBdd.label(), equBdd.label()))
#                    self.writer.write("WARNING: Implication of equation #%d from term failed %s -/-> %s\n" % (eid, termBdd.label(), equBdd.label()))
                if implication != resolver.tautologyId:
                    antecedents += [implication]
                e.validation = self.manager.prover.createClause([equBdd.id], antecedents, "Validation of equation #%d BDD %s" % (eid, equBdd.label()))
                self.removeTerm(id)
            elif cmd == '>=':  
                if self.constraintSystem is None:
                    nvar = len(self.litMap) // 2
                    self.constraintSystem = pseudoboolean.ConstraintSystem(nvar, verbose = self.verbLevel >= 3, manager = self.manager, writer = self.writer)
                const = int(fields[1])
                nvar = self.constraintSystem.N
                con = pseudoboolean.Constraint(nvar, const)
                for field in fields[2:]:
                    parts = field.split('.')
                    coeff = int(parts[0])
                    var = int(parts[1])
                    con[var] = coeff
                cid = self.constraintSystem.addConstraint(con)
                if len(idStack) < 1:
                    raise SolverException("Line #%d.  Stack is empty" % (lineCount))
                id = idStack[-1]
                idStack = idStack[:-1]
                termBdd = self.activeIds[id].root
                antecedents = [self.activeIds[id].validation]
                conBdd = con.root
                check, implication = self.manager.justifyImply(termBdd, conBdd)
                if not check:
                    raise bdd.BddException("Implication of constraint #%d from term failed %s -/-> %s" % (cid, termBdd.label(), conBdd.label()))
#                    self.writer.write("WARNING: Implication of constraint #%d from term failed %s -/-> %s\n" % (cid, termBdd.label(), conBdd.label()))
                if implication != resolver.tautologyId:
                    antecedents += [implication]
                con.validation = self.manager.prover.createClause([conBdd.id], antecedents, "Validation of constraint #%d BDD %s" % (cid, conBdd.label()))
                self.removeTerm(id)
            else:
                raise SolverException("Line %d.  Unknown scheduler action '%s'" % (lineCount, cmd))

        # Reach end of scheduler
        if self.equationSystem is not None:
            status = self.equationSystem.solve(nzLimit)
            if status == 'failed':
                self.writer.write("FAILED.  Equation system could not be solved\n")
            elif status == 'unsolvable':
                self.writer.write("Equation system proved formula UNSAT\n")
                self.equationSystem.postStatistics(status)
            elif status == 'toobig':
                self.writer.write("Equation system UNSAT, but too big for proof\n")
            else:
                self.writer.write("UNRESOLVED.  Equation solver indicates the formula may be SAT\n")
            return status
        elif self.constraintSystem is not None:
            status = self.constraintSystem.solve(nzLimit)
            if status == 'failed':
                self.writer.write("FAILED.  Constraint system could not be solved\n")
            elif status == 'unsolvable':
                self.writer.write("Constraint system proved formula UNSAT\n")
                self.constraintSystem.postStatistics(status)
            elif status == 'toobig':
                self.writer.write("Constraint system UNSAT, but too big for proof\n")
            else:
                self.writer.write("UNRESOLVED.  Constraint solver indicates the formula may be SAT:\n")
                self.constraintSystem.show()
            return status
        
    def placeInBucket(self, buckets, id):
        term = self.activeIds[id]
        level = term.root.variable.level
        if level == bdd.Variable.leafLevel:
            buckets[0].append(id)
        else:
            buckets[level].append(id)

    # Bucket elimination
    def runBucketSchedule(self):
        maxLevel = len(self.manager.variables)
        buckets = { level : [] for level in range(0, maxLevel + 1) }
        # Insert ids into lists according to top variable in BDD
        ids = sorted(self.activeIds.keys())
        for id in ids:
            self.placeInBucket(buckets, id)
        for blevel in range(0, maxLevel + 1):
            if self.verbLevel >= 3:
                self.writer.write("Working on bucket for level %d.  %d items\n" % (blevel, len(buckets[blevel])))
            # Conjunct all terms in bucket
            while len(buckets[blevel]) > 1:
                id1 = buckets[blevel][0]
                id2 = buckets[blevel][1]
                buckets[blevel] = buckets[blevel][2:]
                newId = self.combineTerms(id1, id2)
                if newId < 0:
                    # Hit unsat case
                    return "unsatisfiable"
                self.placeInBucket(buckets, newId)
            # Quantify top variable for this bucket
            if blevel > 0 and len(buckets[blevel]) > 0:
                id = buckets[blevel][0]
                buckets[blevel] = []
                var = self.manager.variables[blevel-1]
                vid = var.id
                newId = self.quantifyTerm(id, [vid])
                self.placeInBucket(buckets, newId)
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")

        term = self.activeIds[id]
        level = term.root.variable.level
        if level == bdd.Variable.leafLevel:
            buckets[0].append(id)
        else:
            buckets[level].append(id)
        return "satisfiable"

    def placeInBucketPerm(self, buckets, id, bperm):
        term = self.activeIds[id]
        if term.root.variable.level == bdd.Variable.leafLevel:
            buckets[0].append(id)
        else:
            idList = self.manager.getSupportIds(term.root)
            vid = bperm.permMinList(idList)
            bid = bperm.reverse(vid)
            buckets[bid].append(id)

    # Bucket elimination using permuted list of Ids to order buckets
    def runBucketSchedulePerm(self, bperm):
        maxBid = len(self.manager.variables)
        buckets = { bid : [] for bid in range(0, maxBid + 1) }
        # Insert ids into lists according to top variable in BDD
        ids = sorted(self.activeIds.keys())
        for id in ids:
            self.placeInBucketPerm(buckets, id, bperm)
        for bid in range(0, maxBid + 1):
            vid = 0 if bid == 0 else bperm.forward(bid)
            if self.verbLevel >= 3:
                self.writer.write("Working on bucket %d (variable Id %d).  %d items\n" % (bid, vid, len(buckets[bid])))
            # Conjunct all terms in bucket
            while len(buckets[bid]) > 1:
                id1 = buckets[bid][0]
                id2 = buckets[bid][1]
                buckets[bid] = buckets[bid][2:]
                newId = self.combineTerms(id1, id2)
                if newId < 0:
                    # Hit unsat case
                    return "unsatisfiable"
                self.placeInBucketPerm(buckets, newId, bperm)
            # Quantify variable for this bucket
            if bid > 0 and len(buckets[bid]) > 0:
                id = buckets[bid][0]
                buckets[bid] = []
                newId = self.quantifyTerm(id, [vid])
                self.placeInBucketPerm(buckets, newId, bperm)
        if self.verbLevel >= 0:
            self.writer.write("SAT\n")
        return "satisfiable"

    # Provide roots of active nodes to garbage collector
    def rootGenerator(self):
        ilist = sorted(self.activeIds.keys())
        tlist = [self.activeIds[id] for id in ilist]
        rootList = [t.root for t in tlist]
        if self.equationSystem is not None:
            rootList += self.equationSystem.rset.rootList()
            rootList += self.equationSystem.eset.rootList()
        if self.constraintSystem is not None:
            rootList += self.constraintSystem.rset.rootList()
        return rootList

def readPermutation(fname, writer = None):
    valueList = []
    permutedList = []
    vcount = 0
    lineCount = 0
    if writer is None:
        writer = sys.stderr
    try:
        infile = open(fname, 'r')
    except:
        writer.write("Could not open permutation file '%s'\n" % fname)
        return None
    for line in infile:
        lineCount += 1
        fields = line.split()
        if len(fields) == 0:
            continue
        if fields[0][0] == '#':
            continue
        try:
            values = [int(v) for v in fields]
        except Exception:
                writer.write("Line #%d.  Invalid list of variables '%s'\n" % (lineCount, line))
                return None
        for v in values:
            vcount += 1
            valueList.append(vcount)
            permutedList.append(v)
    infile.close()
    try:
        permuter = Permuter(valueList, permutedList)
    except Exception as ex:
        writer.write("Invalid permutation: %s\n" % str(ex))
        return None
    return permuter
        
def readScheduler(fname, writer = None):
    lineCount = 0
    actionList = []
    if writer is None:
        writer = sys.stderr
    try:
        infile = open(fname, 'r')
    except:
        writer.write("Could not open schedule file '%s'\n" % fname)
        return None
    for line in infile:
        lineCount += 1
        fields = line.split()
        if len(fields) == 0:
            line = ""
        if fields[0][0] == '#':
            line = ""
        actionList.append(line)
    return actionList

# Time limit must be global variable.  0 = no limit
timelimit = 0

def ahandler(signum, frame):
    print("Program timed out after %d seconds" % timelimit)
    sys.exit(1)

def setlimit(tlim):
    global timelimit
    timelimit = tlim
    signal.signal(signal.SIGALRM, ahandler)
    signal.alarm(tlim)


def run(name, args):
    cnfName = None
    proofName = None
    doLrat = False
    doBinary = False
    permuter = None
    bpermuter = None
    doBucket = False
    scheduler = None
    verbLevel = 1
    logName = None
    modulus = pseudoboolean.modulusAuto
    nzLimit = None

    optlist, args = getopt.getopt(args, "hbB:v:r:i:o:M:p:s:m:L:t:Z:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        if opt == '-b':
            doBucket = True
        elif opt == '-B':
            bpermuter = readPermutation(val)
            if bpermuter is None:
                return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-r':
            random.seed(int(val))
        elif opt == '-i':
            cnfName = val
        elif opt == '-t':
            setlimit(int(val))
        elif opt == '-o':
            proofName = val
            extension = proofName.split('.')[-1]
            if extension == 'lrat' or extension == 'lratb':
                doLrat = True
                doBinary = extension[-1] == 'b'
        elif opt == '-M':
            proofName = None
            if val == 'b':
                doLrat = True
                doBinary = True
            elif val == 't':
                doLrat = True
        elif opt == '-p':
            permuter = readPermutation(val)
            if permuter is None:
                return
        elif opt == '-s':
            scheduler = readScheduler(val)
            if scheduler is None:
                return
        elif opt == '-m':
            if val == 'a':
                modulus = pseudoboolean.modulusAuto
            elif val == 'i':
                modulus = pseudoboolean.modulusNone
            else:
                modulus = int(val)
        elif opt == '-L':
            logName = val
        elif opt == '-Z':
            nzLimit = int(val)
        else:
            sys.stderr.write("Unknown option '%s'\n" % opt)
            usage(name)
            return

    writer = stream.Logger(logName)

    if (doBucket or bpermuter is not None) and scheduler is not None:
        writer.write("Cannot have both bucket scheduling and defined scheduler\n")
        return
    if (doBucket and bpermuter is not None):
        writer.write("Cannot do bucket scheduling on levels and with defined permutation\n")
        return

    try:
        prover = Prover(proofName, writer = writer, verbLevel = verbLevel, doLrat = doLrat, doBinary = doBinary)
    except Exception as ex:
        writer.write("Couldn't create prover (%s)\n" % str(ex))
        return

    start = datetime.datetime.now()
    solver = Solver(cnfName, prover = prover, permuter = permuter, verbLevel = verbLevel)
    if doBucket:
        status = solver.runBucketSchedule()
    elif bpermuter is not None:
        status = solver.runBucketSchedulePerm(bpermuter)
    elif scheduler is not None:
        status = solver.runSchedule(scheduler, modulus, nzLimit)
    else:
        status = solver.runNoSchedule()

    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    if verbLevel > 0:
        writer.write("Elapsed time for SAT: %.2f seconds (status = %s)\n" % (seconds, str(status).upper()))
    if writer != sys.stderr:
        writer.close()
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

    

    
