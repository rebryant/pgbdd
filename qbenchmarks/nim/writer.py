# Code for generating QCNF, orders, and clusters
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
    variableCount = None

    def __init__(self, froot, suffix = None, verbose = False):
        self.variableCount = 0
        self.verbose = verbose
        if suffix is not None:
            self.suffix = suffix 
            fname = froot if self.suffix is None else froot + "." + self.suffix
        try:
            self.outfile = open(fname, 'w')
        except:
            print("Couldn't open file '%s'. Aborting" % fname)
            sys.exit(1)

    def countVariables(self, count):
        self.variableCount += count

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
class QcnfWriter(Writer):
    clauseCount = 0
    outputList = []
    # Quantification type for each level
    quantifications = {}
    # Mapping from level to list of variables
    variableLists = {}
    # List of comments for each level of variables
    variableCommentLists = {}

    def __init__(self, froot, verbose = False):
        Writer.__init__(self, froot, suffix = "qcnf", verbose = verbose)
        self.clauseCount = 0
        self.ouputList = []
        self.quantifications = {}
        self.variableLists = {}
        self.varableCommentLists = {}

    # With CNF, must accumulate all of the clauses, since the file header
    # requires providing the number of clauses.

    def addVariables(self, level, vlist, isExistential):
        self.countVariables(len(vlist))
        if level in self.quantifications:
            if self.quantifications[level] != isExistential:
                print("Attempting to add variables %s.  Quantification %s" % (str(vlist), "existential" if isExistential else "universal"))
                print("Existing variables at level %d: %s.  Quantification %s" % (level, str(self.variableLists[level]), "existential" if self.quantifications[level] else "universal"))
                raise WriterException("Attempt different quantifications at level %d" % level)
            self.variableLists[level] += vlist
        else:
            self.quantifications[level] = isExistential
            self.variableLists[level] = list(vlist)

    def addVariable(self, level, var, isExistential):
        self.countVariables(1)
        if level in self.quantifications:
            if self.quantifications[level] != isExistential:
                print("Attempting to add variable %d.  Quantification %s" % (var, "existential" if isExistential else "universal"))
                print("Existing variables at level %d: %s.  Quantification %s" % (level, str(self.variableLists[level]), "existential" if self.quantifications[level] else "universal"))
                raise WriterException("Attempt different quantifications at level %d" % level)
            self.variableLists[level].append(var)
        else:
            self.quantifications[level] = isExistential
            self.variableLists[level] = [var]

            
    def doComment(self, line):
        self.outputList.append("c " + line)

    def doVariableComment(self, level, line):
        if level not in self.variableCommentLists:
            self.variableCommentLists[level] = []
        self.variableCommentLists[level].append(line)

    def doClause(self, literals):
        ilist = literals + [0]
        self.clauseCount += 1
        self.outputList.append(" ".join([str(i) for i in ilist]))

    def finish(self):
        if self.outfile is None:
            return
        self.show("p cnf %d %d" % (self.variableCount, self.clauseCount))
        levels = sorted(self.quantifications.keys())
        if len(levels) > 0 and levels[0] == -1:
            levels = levels[1:] + [-1]
        for level in levels:
            if level in self.variableCommentLists:
                for line in self.variableCommentLists[level]:
                    self.show("c " + line + '\n')
            qchar = 'e' if self.quantifications[level] else 'a'
            slist = [str(v) for v in self.variableLists[level]]
            line = qchar + ' ' + ' '.join(slist) + ' 0'
            self.show(line)
        for line in self.outputList:
            self.show(line)
        self.outfile.close()
        self.outfile = None
    

class OrderWriter(Writer):
    variableList = []

    def __init__(self, count, froot, verbose = False, suffix = None):
        if suffix is None:
            suffix = "order"
        Writer.__init__(self, froot, suffix = suffix, verbose = verbose)
        self.countVariables(count)
        self.variableList = []

    def doOrder(self, vlist):
        self.show(" ".join([str(c) for c in vlist]))        
        self.variableList += vlist

    def finish(self):
        if self.variableCount != len(self.variableList):
#            raise WriterException("Incorrect number of variables in ordering %d != %d" % (
#                len(self.variableList), self.variableCount))
            print("Warning: Incorrect number of variables in ordering")
            print("  Expected %d.  Got %d" % (self.variableCount, len(self.variableList)))

        expected = range(1, self.variableCount+1)
        self.variableList.sort()
        for (e, a) in zip(expected, self.variableList):
            if e != a:
               raise WriterException("Mismatch in ordering.  Expected %d.  Got %d" % (e, a))
        self.writer.finish(self)

class ClusterWriter(Writer):

    def __init__(self, count, froot, verbose = False, suffix = None):
        if suffix is None:
            suffix = "cluster"
        Writer.__init__(self, froot, suffix = suffix, verbose = verbose)
        self.countVariables(count)
        self.variableList = []

    def doCluster(self, vlist):
        self.show(" ".join([str(c) for c in vlist]))        
        self.variableList += vlist

    def finish(self):
        if self.variableCount != len(self.variableList):
#            raise WriterException("Incorrect number of variables in ordering %d != %d" % (
#                len(self.variableList), self.variableCount))
            print("Warning: Incorrect number of variables in cluster")
            print("  Expected %d.  Got %d" % (self.variableCount, len(self.variableList)))

        expected = range(1, self.variableCount+1)
        self.variableList.sort()
        for (e, a) in zip(expected, self.variableList):
            if e != a:
               raise WriterException("Mismatch in clustered variables.  Expected %d.  Got %d" % (e, a))
        self.writer.finish(self)
    
