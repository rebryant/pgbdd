# Miscellaneous utilities to support QBF solver

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


import sys

def trim(s):
    while len(s) > 0 and s[-1] in ' \r\n\t':
        s = s[:-1]
    return s


###########################################################################################
## Print information on output while maintaining separate log file
###########################################################################################
class Logger:
    outFile = None

    def __init__(self, outName = None):
        self.outFile = None
        if outName is not None:
            try:
                self.outFile = open(outName, 'a')
            except:
                sys.stderr.write("Couldn't open log file '%s'\n", outName)
                self.outFile = None

    def write(self, text):
        sys.stdout.write(text)
        if self.outFile is not None:
            self.outFile.write(text)

    def close(self):
        if self.outFile is not None:
            self.outFile.close()


###########################################################################################
## Read QCNF file
###########################################################################################
class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# Read DQCNF file.
# Creates 1) list of universal variables 2) list of existential variables and 3) a mapping from
# existentials to lists of universals

# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class DqcnfReader():
    file = None
    clauses = []
    universalList = []
    existentialList = []
    dependencyMap = {}
    nvar = 0
    tautologyOK = True
    
    def __init__(self, fname = None):
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
        try:
            self.readCnf()
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    # Read DQCNF file.
    def readCnf(self):
        self.nvar = 0
        # Dictionary of variables that have been declared.
        # Maps from var to line number
        foundDict = {}
        lineNumber = 0
        nclause = 0
        clauseCount = 0
        self.clauses = []
        self.universalList = []
        self.existentialList = []
        # Map from existential var to its dependency set
        self.dependencyMap = {}
        self.nvar = 0

        for line in self.file:
            lineNumber += 1
            line = trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
                continue
            if len(line[0]) > 1:
                raise CnfException("Line %d.  Only allow single character commands" % (lineNumber, line))
            if line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
            elif line[0] in ['a', 'e', 'd']:
                vtype = line[0]
                # Variable declaration
                try:
                    vars = [int(s) for s in line[1:].split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if vars[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                vars = vars[:-1]
                # First make sure all vars are legitimate
                if vtype == 'd':
                    v = vars[0]
                    dvars = vars[1:]
                    if v <= 0 or v > self.nvar:
                        raise CnfException("Line %d.  Invalid variable %d" % (lineNumber, v))
                    foundDict[v] = lineNumber
                    self.existentialList.append(v)
                    for u in dvars:
                        if u not in foundDict or u not in self.universalList:
                            flist = sorted(foundDict.keys())
                            print("Declared so far: %s.  Universal: %s" % str(flist), str(self.universalList))
                            raise CnfException("Line %d.  Invalid dependency variable %d" % (lineNumber, u))
                    self.dependencyMap[v] = dvars
                else:
                    for v in vars:
                        if v <= 0 or v > self.nvar:
                            raise CnfException("Line %d.  Invalid variable %d" % (lineNumber, v))
                        if v in foundDict:
                            raise CnfException("Line %d.  Variable %d already declared on line %d" % (lineNumber, v, foundDict[v]))
                        foundDict[v] = lineNumber
                        if vtype == 'a':
                            self.universalList.append(v)
                        else:
                            self.existentialList.append(v)
                            self.dependencyMap[v] = list(self.universalList)

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
                        plit = vars[i]
                        nlit = -vars[i]
                        if plit in lits and nlit in lits:
                            if self.tautologyOK:
                                # Skip this clause
                                continue
                            raise CnfException("Line %d.  Opposite literals (%d,%d)" % (lineNumber, plit, nlit))
                        elif plit in lits:
                            raise CnfException("Line %d.  Repeated literal %d" % (lineNumber, plit))
                        else:
                            raise CnfException("Line %d.  Repeated literal %d" % (lineNumber, nlit))
                self.clauses.append(lits)
                clauseCount += 1

        if clauseCount != nclause:
            raise CnfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
        # See if there are any undeclared variables
        outerVars = [v for v in range(1, self.nvar+1) if v not in foundDict]
        for v in outerVars:
            # These must be added as existential variables in first quantifier block
            self.existentialList.append(v)
            self.dependencyMap[v] = []

