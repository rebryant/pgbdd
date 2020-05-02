# Parsing of CNF files in DIMACS format
import sys

class CnfException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "CNF Exception: " + str(self.value)

# General purpose reader of DIMACS format CNF files
# Must supply functions defining proper action for 
# variable count, regular lines, and comment lines
class CnfReader():
    cnfName = None
    file = None
    countAction = None
    clauseAction = None
    commentAction = None
    saveClauses = False
    clauseLines = []
    
    def __init__(self, countAction, clauseAction, commentAction = None, fname = None):
        self.cnfName = fname
        if fname is None:
            opened = False
            self.saveClauses = True
            self.file = sys.stdin
        else:
            opened = True
            self.saveClauses = False
            try:
                self.file = open(fname, 'r')
            except Exception:
                raise CnfException("Could not open file '%s'" % fname)
        self.countAction = countAction
        self.clauseAction = clauseAction
        self.commentAction = commentAction
        self.clauseLines = []
        try:
            self.readCnf()
        except Exception as ex:
            if opened:
                self.file.close()
            raise ex
        
    def trim(self, s):
        while len(s) > 0 and s[-1] in '\r\n':
            s = s[:-1]
        return s

    def readCnf(self):
        lineNumber = 0
        nclause = 0
        nvar = 0
        clauseCount = 0
        for line in self.file:
            lineNumber += 1
            line = self.trim(line)
            if len(line) == 0:
                continue
            elif line[0] == 'c':
                if self.commentAction is not None:
                    self.commentAction(line)
            elif line[0] == 'p':
                fields = line[1:].split()
                if fields[0] != 'cnf':
                    raise CnfException("Line %d.  Bad header line '%s'.  Not cnf" % (lineNumber, line))
                try:
                    nvar = int(fields[1])
                    nclause = int(fields[2])
                except Exception:
                    raise CnfException("Line %d.  Bad header line '%s'.  Invalid number of variables or clauses" % (lineNumber, line))
                self.countAction(nvar, nclause)
            else:
                if self.saveClauses:
                    self.clauseLines.append(line)
                # Check formatting
                try:
                    lits = [int(s) for s in line.split()]
                except:
                    raise CnfException("Line %d.  Non-integer field" % lineNumber)
                # Last one should be 0
                if lits[-1] != 0:
                    raise CnfException("Line %d.  Clause line should end with 0" % lineNumber)
                vars = sorted([abs(l) for l in lits[:-1]])
                if len(vars) == 0:
                    raise CnfException("Line %d.  Empty clause" % lineNumber)                    
                if vars[-1] > nvar or vars[0] == 0:
                    raise CnfException("Line %d.  Out-of-range literal" % lineNumber)
                for i in range(len(vars) - 1):
                    if vars[i] == vars[i+1]:
                        raise CnfException("Line %d.  Opposite or repeated literal" % lineNumber)
                self.clauseAction(line)
                clauseCount += 1
        if clauseCount != nclause:
            raise CnfException("Line %d: Got %d clauses.  Expected %d" % (lineNumber, clauseCount, nclause))
