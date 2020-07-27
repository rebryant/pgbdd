# Code for generating CNF, order, and schedule files
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

    def __init__(self, count, froot, suffix = None, verbose = False):
        self.expectedVariableCount = count
        self.verbose = verbose
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

    def show(self, line):
        line = self.trim(line)
        if self.verbose:
            print(line)
        if self.outfile is not None:
            self.outfile.write(line + '\n')

    def finish(self):
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None


# Creating CNF
class CnfWriter(Writer):
    clauseCount = 0
    outputList = []

    def __init__(self, count, froot, verbose = False):
        Writer.__init__(self, count, froot, suffix = "cnf", verbose = verbose)
        self.clauseCount = 0
        self.ouputList = []

    # With CNF, must accumulate all of the clauses, since the file header
    # requires providing the number of clauses.

    def doComment(self, line):
        self.outputList.append("c " + line)

    def doClause(self, literals):
        ilist = literals + [0]
        self.outputList.append(" ".join([str(i) for i in ilist]))
        self.clauseCount += 1
        return self.clauseCount

    def finish(self):
        if self.outfile is None:
            return
        self.show("p cnf %d %d" % (self.expectedVariableCount, self.clauseCount))
        for line in self.outputList:
            self.show(line)
        self.outfile.close()
        self.outfile = None
     
    
class ScheduleWriter(Writer):
    # Track potential errors
    stackDepth = 0
    decrementAnd = False

    def __init__(self, count, froot, verbose = False):
        Writer.__init__(self, count, froot, suffix = "schedule", verbose = verbose)
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
        if count+1 > self.stackDepth:
            print("Warning: Cannot perform %d And's.  Only %d elements on stack" % (count, self.stackDepth))
#            raise WriterException("Cannot perform %d And's.  Only %d elements on stack" % (count, self.stackDepth))
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
        if self.stackDepth == 0:
            print ("Warning: Cannot quantify.  Stack empty")
#            raise WriterException("Cannot quantify.  Stack empty")
        self.show("q %s" % " ".join([str(c) for c in vlist]))

    def doComment(self, cstring):
        self.show("# " + cstring)

    def doInformation(self, cstring):
        self.show("i " + cstring)

    def finish(self):
        if self.stackDepth != 1:
            print("Warning: Invalid schedule.  Finish with %d elements on stack" % self.stackDepth)
#            raise WriterException("Invalid schedule.  Finish with %d elements on stack" % self.stackDepth)
        Writer.finish(self)

class OrderWriter(Writer):
    variableList = []

    def __init__(self, count, froot, verbose = False):
        Writer.__init__(self, count, froot, suffix = "order", verbose = verbose)
        self.variableList = []

    def doOrder(self, vlist):
        self.show(" ".join([str(c) for c in vlist]))        
        self.variableList += vlist

    def finish(self):
        if self.expectedVariableCount != len(self.variableList):
#            raise WriterException("Incorrect number of variables in ordering %d != %d" % (
#                len(self.variableList), self.expectedVariableCount))
            print("Warning: Incorrect number of variables in ordering")
            print("  Expected %d.  Got %d" % (self.expectedVariableCount, len(self.variableList)))

        expected = range(1, self.expectedVariableCount+1)
        self.variableList.sort()
        for (e, a) in zip(expected, self.variableList):
            if e != a:
               raise WriterException("Mismatch in ordering.  Expected %d.  Got %d" % (e, a))
        Writer.finish(self)
