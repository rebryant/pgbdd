
def trim(s):
    while len(s) > 0 and s[-1] in ' \r\n\t':
        s = s[:-1]
    return s

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
#        print("Input variables:")
#        for i in range(qlevel):
#            q = i+1
#            if len(vdict[q]) > 0:
#                print("Level %d.  %s.  Vars = %s" % (q, "Existential" if tdict[q] else "Universal", str(vdict[q])))
