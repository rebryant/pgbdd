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


# Code for generating CNF, LRAT, DRAT, schedule, and order files
class WriterException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Writer Exception: " + str(self.value)


# Generic writer
class Writer:
    outfile = None
    suffix = None
    verbose = False
    expectedVariableCount = None
    isNull = False
    froot = ""

    def __init__(self, count, froot, suffix = None, verbose = False, isNull = False):
        self.expectedVariableCount = count
        self.froot = froot
        self.verbose = verbose
        self.isNull = isNull
        if isNull:
            return
        if suffix is not None:
            self.suffix = suffix 
            fname = froot if self.suffix is None else froot + "." + self.suffix
        try:
            self.outfile = open(fname, 'w')
        except:
            print("Couldn't open file '%s'. Aborting" % fname)
            sys.exit(1)

    def trim(self, line):
        while len(line) > 0 and line[-1] == '\n':
            line = line[:-1]
        return line

    def vcount(self):
        return self.expectedVariableCount

    def show(self, line):
        if self.isNull:
            return
        line = self.trim(line)
        if self.verbose:
            print(line)
        if self.outfile is not None:
            self.outfile.write(line + '\n')

    def finish(self):
        if self.isNull:
            return
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None

# Creating CNF.  This version requires specifying the number of variables and clauses up-front
class CnfWriter(Writer):
    clauseCount = 0
    outputList = []

    def __init__(self, count, froot, verbose = False):
        Writer.__init__(self, count, froot, suffix = "cnf", verbose = verbose)
        self.clauseCount = 0
        self.outputList = []

    # With CNF, must accumulate all of the clauses, since the file header
    # requires providing the number of clauses.

    def doComment(self, line):
        self.outputList.append("c " + line)

    def doClause(self, literals):
        for lit in literals:
            var = abs(lit)
            if var <= 0 or var > self.expectedVariableCount:
                raise WriterException("Variable %d out of range 1--%d" % (var, self.expectedVariableCount))
        ilist = literals + [0]
        self.outputList.append(" ".join([str(i) for i in ilist]))
        self.clauseCount += 1
        return self.clauseCount

    def finish(self):
        if self.isNull:
            return
        if self.outfile is None:
            return
        self.show("p cnf %d %d" % (self.expectedVariableCount, self.clauseCount))
        for line in self.outputList:
            self.show(line)
        self.outfile.close()
        self.outfile = None


# Creating CNF incrementally.  Don't know number of variables in advance
class LazyCnfWriter:

    variableCount = 0
    # Set of tuples (T/F, item)
    # Boolean T for clause F for comment
    # item: list of literals for clause, string for comment
    items = []
    froot = ""
    verbose = False

    def __init__(self, froot, verbose = False):
        self.variableCount = 0
        self.items = []
        self.froot = froot
        self.verbose = verbose


    def newVariable(self):
        self.variableCount += 1
        return self.variableCount

    def vcount(self):
        return self.variableCount

    def newVariables(self, n):
        return [self.newVariable() for i in range(n)]
    
    def doComment(self, line):
        self.items.append((False, line))

    def doClause(self, lits):
        self.items.append((True, lits))

    def finish(self):
        writer = CnfWriter(self.variableCount, self.froot, self.verbose)
        for (isClause, value) in self.items:
            if isClause:
                writer.doClause(value)
            else:
                writer.doComment(value)
        writer.finish()
        print("c File '%s.cnf' has %d variables and %d clauses" % (self.froot, self.variableCount, writer.clauseCount))

# Creating LRAT proof
class LratWriter(Writer):

    # Must initialize this to the number of clauses in the original CNF file
    clauseCount = 0

    def __init__(self, clauseCount, froot, verbose = False):
        Writer.__init__(self, None, froot, suffix = "lrat", verbose = verbose)
        self.clauseCount = clauseCount

    def doComment(self, line):
        self.show("c " + line)

    def doStep(self, lits, ids):
        self.clauseCount += 1
        ilist = [self.clauseCount] + lits + [0] + ids + [0]
        self.show(" ".join([str(i) for i in ilist]))
        return self.clauseCount

    def doDelete(self, ids):
        ilist = [self.clauseConunt] + ids + [0]
        self.show(" ".join([str(i) for i in ilist]))

# Creating DRAT proof
class DratWriter(Writer):

    def __init__(self, froot, verbose = False):
        Writer.__init__(self, None, froot, suffix = "drat", verbose = verbose)

    def doComment(self, line):
        self.show("c " + line)

    def doStep(self, lits):
        ilist = lits + [0]
        self.show(" ".join([str(i) for i in ilist]))
    
class OrderWriter(Writer):
    variableList = []

    def __init__(self, count, froot, verbose = False, suffix = None, isNull = False):
        if suffix is None:
            suffix = "order"
        Writer.__init__(self, count, froot, suffix = suffix, verbose = verbose, isNull = isNull)
        self.variableList = []

    def doOrder(self, vlist):
        self.show(" ".join([str(c) for c in vlist]))        
        self.variableList += vlist

    def finish(self):
        if self.isNull:
            return
        if self.expectedVariableCount != len(self.variableList):
            print("Warning: Incorrect number of variables in ordering")
            print("  Expected %d.  Got %d" % (self.expectedVariableCount, len(self.variableList)))

        expected = range(1, self.expectedVariableCount+1)
        self.variableList.sort()
        for (e, a) in zip(expected, self.variableList):
            if e != a:
               raise WriterException("Mismatch in ordering.  Expected %d.  Got %d" % (e, a))
        print("c File '%s.order' written" % (self.froot))
        Writer.finish(self)

class ScheduleWriter(Writer):
    # Track potential errors
    stackDepth = 0
    decrementAnd = False
    expectedFinal = 1

    def __init__(self, count, froot, verbose = False, isNull = False):
        Writer.__init__(self, count, froot, suffix = "schedule", verbose = verbose, isNull = isNull)
        self.stackDepth = 0
        self.decrementAnd = False
    
    def getClauses(self, clist):
        self.show("c %s" % " ".join([str(c) for c in clist]))
        self.stackDepth += len(clist)

    # First time with new tree, want one fewer and operations
    def newTree(self):
        self.decrementAnd = True

    def doAnd(self, count):
        if self.decrementAnd:
            count -= 1
        self.decrementAnd = False
        if count == 0:
            return
        if count+1 > self.stackDepth:
            print("Warning: Cannot perform %d And's.  Only %d elements on stack" % (count, self.stackDepth))
        self.show("a %d" % count)
        self.stackDepth -= count

    def doStore(self, name):
        self.show("s %s" % name)

    def doRetrieve(self, name):
        self.show("r %s" % name)

    def doDelete(self, name):
        self.show("d %s" % name)

    def doEquality(self):
        self.show("e")

    def doQuantify(self, vlist):
        if self.isNull:
            return
        if self.stackDepth == 0:
            print ("Warning: Cannot quantify.  Stack empty")
#            raise WriterException("Cannot quantify.  Stack empty")
        self.show("q %s" % " ".join([str(c) for c in vlist]))

    # Issue equation or constraint.
    def doPseudoBoolean(self, vlist, clist, const, isEquation=True):
        if self.isNull:
            return
        # Anticipate that shifting everything from CNF evaluation to pseudoboolean reasoning
        self.expectedFinal = 0
        if self.stackDepth == 0:
            print ("Warning: Cannot quantify.  Stack empty")
        if len(vlist) != len(clist):
            raise WriterException("Invalid equation or constraint.  %d variables, %d coefficients" % (len(vlist), len(clist)))
        cmd = "=" if isEquation else ">="
        slist = [cmd, str(const)]
        slist += [("%d.%d" % (c,v)) for (c,v) in zip(clist, vlist)]
        self.show(" ".join(slist))
        self.stackDepth -= 1

    def doComment(self, cstring):
        self.show("# " + cstring)

    def doInformation(self, cstring):
        self.show("i " + cstring)

    def finish(self):
        if self.isNull:
            return
        if self.stackDepth != self.expectedFinal:
            print("Warning: Invalid schedule.  Finish with %d elements on stack" % self.stackDepth)
        Writer.finish(self)
        
class PermutationWriter(Writer):
    rowCount = 1
    columnCount = 1
    
    def __init__(self, rows, cols, froot, suffix):
        self.rowCount = rows
        self.columnCount = cols
        Writer.__init__(self, rows * cols, froot, suffix)
 
    def emit(self, vals):
        svals = [str(v) for v in vals]
        self.show(" ".join(svals))

    def rowMajor(self):
        vals = list(range(1, self.rowCount*self.columnCount+1))
        self.emit(vals)

    def columnMajor(self):
        vals = []
        for cidx in range(1, self.columnCount+1):
            cvals = [r*self.columnCount + cidx for r in range(self.rowCount)]
            vals += cvals
        self.emit(vals)
