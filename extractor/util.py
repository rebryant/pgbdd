#!/usr/bin/python

# Utility routines for extractors

import sys

verbLevel = 1
errfile = sys.stderr
careful = False

def ewrite(s, level):
    if level <= verbLevel:
        errfile.write(s)

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
class CnfReader():
    file = None
    clauses = []
    nvar = 0
    # What was wrong with file
    reason = None
    
    def __init__(self, fname = None, maxclause = None, rejectClause = None):
        if fname is None:
            opened = False
            self.file = sys.stdin
        else:
            opened = True
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise CnfException("Could not open file '%s'\n" % fname)
        self.nvar = 0
        self.clauses = []
        self.reason = None
        try:
            self.readCnf(maxclause, rejectClause)
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    def readCnf(self, maxclause = None, rejectClause = None):
        lineNumber = 0
        nclause = 0
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
                continue
            elif line[0] == 'p':
                fields = line[1:].split()
                if len(fields) != 3 or fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    self.nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
                if maxclause is not None and nclause > maxclause:
                    self.reason = "%d clauses exceeds limit of %d" % (nclause, maxclause)
                    return
            else:
                if nclause == 0:
                    raise CnfException("Line %d.  No header line.  Not cnf" % (lineNumber))
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if careful and lits[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                lits = lits[:-1]
                # Sort literals by variable
                lits.sort(key = lambda l: abs(l))
                if careful:
                    vars = [abs(l) for l in lits]
                    if len(vars) == 0:
                        raise CnfException("Line %d.  Empty clause" % lineNumber)                    
                    if vars[-1] > self.nvar or vars[0] == 0:
                        raise CnfException("Line %d.  Out-of-range literal" % lineNumber)
                    for i in range(len(vars) - 1):
                        if vars[i] == vars[i+1]:
                            raise CnfException("Line %d.  Opposite or repeated literal" % lineNumber)
                # See if this clause indicates that the CNF cannot be converted
                if rejectClause is not None:
                    self.reason = rejectClause(lits, clauseCount+1)
                    if self.reason is not None:
                        return
                self.clauses.append(lits)
                clauseCount += 1
        if clauseCount != nclause:
            raise CnfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
        return

