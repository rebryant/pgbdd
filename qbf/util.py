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


class PermutationException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Permutation Exception: " + str(self.value)


###########################################################################################
## Read QCNF file
###########################################################################################
class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# Read QCNF file.
# Save variables as list of tuples with form (varNumber, qlevel, isExistential)
# Save list of clauses, each is a list of literals (zero at end removed)
# Also saves comment lines
class QcnfReader():
    file = None
    clauses = []
    # List of input variables.
    # Each is triple of form (varNumber, qlevel, isExistential)
    varList = []
    nvar = 0
    # Were any of the quantifier blocks stretched into multiple levels
    stretched = False
    
    def __init__(self, fname = None, permuter = None, stretchExistential = False, stretchUniversal = False):
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
            self.readCnf(permuter, stretchExistential, stretchUniversal)
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    # Read QCNF file.  Optionally, have split quantifier blocks into ones with single
    # variables.
    # Only use odd levels to keep room for extension variables at even levels
    def readCnf(self, permuter = None, stretchExistential = False, stretchUniversal = False):
        self.nvar = 0
        self.stretched = False
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
                continue
            elif line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
            elif line[0] == 'a' or line[0] == 'e':
                # Variable declaration
                isExistential = line[0] == 'e'
                try:
                    vars = [int(s) for s in line[1:].split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if vars[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                vars = vars[:-1]
                # First make sure all vars are legitimate
                for v in vars:
                    if v <= 0 or v > self.nvar:
                        raise CnfException("Line %d.  Invalid variable %d" % (lineNumber, v))
                    if v in foundDict:
                        raise CnfException("Line %d.  Variable %d already declared on line %d" % (lineNumber, v, foundDict[v]))
                    foundDict[v] = lineNumber
                # Now add them, either as a group, or sequentially
                if isExistential and stretchExistential or (not isExistential and stretchUniversal):
                    if len(vars) > 1:
                        self.stretched = True
                    if permuter is not None:
                        vars = permuter.sortList(vars) 
                    for v in vars:
                        self.varList.append((v, qlevel, isExistential))
                        qlevel += 2
                else:
                    for v in vars:
                        self.varList.append((v, qlevel, isExistential))
                    # Prepare for next set of input variables
                    qlevel += 2
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
        # See if there are any undeclared variables
        outerVars = [v for v in range(1, self.nvar+1) if v not in foundDict]
        if len(outerVars) > 0:
            # These must be added as existential variables in first quantifier block
            ovarList = [(v, 1, True) for v in outerVars]
            nvarList = [(v, qlevel+2, isExistential) for (v, qlevel, isExistential) in self.varList]
            self.varList = ovarList + nvarList
        # Debugging info:

        vdict = {q+1 : [] for q in range(qlevel)}
        tdict = {q : False for q in range(qlevel)}
        for (v, q, e) in self.varList:
            vdict[q].append(v)
            tdict[q] = e


###########################################################################################
## Permutations of 1..n
###########################################################################################
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
            
    # Flip order of permuted values
    def mirror(self):
        valueList = sorted(self.forwardMap.keys())
        permutedList = [self.forwardMap[v] for v in valueList]
        valueList.reverse()
        return Permuter(valueList, permutedList)
            
    def forward(self, v):
        if v not in self.forwardMap:
            raise PermutationException("Value %s not in permutation" % (str(v)))
        return self.forwardMap[v]

    def permLess(self, v1, v2):
        pv1 = self.reverse(v1)
        pv2 = self.reverse(v2)
        return pv1 < pv2

    def sortList(self, ls):
        return sorted(ls, key = lambda x: self.reverse(x))


    def reverse(self, v):
        if v not in self.reverseMap:
            raise PermutationException("Value %s not in permutation range" % (str(v)))
        return self.reverseMap[v]
    
    def __len__(self):
        return len(self.forwardMap)

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
            
