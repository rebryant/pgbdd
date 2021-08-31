#!/usr/bin/python

# Convert CNF file containing only at-most-1 and at-least-1 declarations into
# schedule file that converts these into pseudo-Boolean constraints

import getopt
import sys
import glob

verbLevel = 1
errfile = sys.stderr
careful = False

def ewrite(s, level):
    if level <= verbLevel:
        errfile.write(s)

def usage(name, errfile):
    ewrite("Usage: %s [-h] [-c] [-e] [-v VLEVEL] [-i IN.cnf] [-o OUT.schedule] [-p PATH] [-m MAXCLAUSE]\n" % name, 0)
    ewrite("  -h       Print this message\n", 0)
    ewrite("  -v VERB  Set verbosity level (1-4)\n", 0)
    ewrite("  -c       Careful checking of CNF\n", 0)
    ewrite("  -e       Merge constraints into equations if possible\n", 0)
    ewrite("  -i IFILE Single input file\n", 0)
    ewrite("  -i OFILE Single output file\n", 0)
    ewrite("  -p PATH  Process all CNF files with matching path prefix\n", 0)
    ewrite("  -m MAXC  Skip files with larger number of clauses\n", 0)

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
                raise CnfException("Could not open file '%s'" % fname)
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


# Constraint or equation
class Formula:
    varList = []
    coeffList = []
    const = 0
    # Input clauses that generate this constraint
    clauseList = []
    isEquation = False

    def __init__(self, varList, coeffList, const, clauseList, isEquation):
        self.varList = varList
        self.coeffList = coeffList
        self.const = const
        self.clauseList = clauseList
        self.isEquation = isEquation

    # Attempt to merge AMO and ALO constraints into single equation
    # Assume they have identical variable lists, but check other requirements
    # Return None if cannot merge
    def e1Merge(self, other):
        varList = self.varList
        alo, amo = (self, other) if self.coeffList[0] > 0 else (other, self)
        if alo.const != 1 or amo.const != -1:
            return None
        for alc, amc in zip(alo.coeffList, amo.coeffList):
            if alc != 1 or amc != -1:
                return None
        coeffList = alo.coeffList
        const = alo.const
        clauseList = alo.clauseList + amo.clauseList
        return Formula(varList, coeffList, const, clauseList, True)

    def __str__(self):
        slist = ["%d.%d" % (v, c) for c,v in zip(self.varList, self.coeffList)]
        symbol = "=" if self.isEquation else ">="
        return ("%s %d " % (symbol, self.const)) + " ".join(slist)

    def generate(self, outfile):
        slist = [str(c) for c in self.clauseList]
        outfile.write("c " + " ".join(slist) + "\n")
        if len(self.clauseList) > 1:
            outfile.write("a %d\n" % (len(self.clauseList) - 1))
        outfile.write(str(self) + "\n")
        

class ConstraintFinder:
    # Clauses.  Mapping from ID to clause
    # Removed as they get classified
    clauseDict = {}
    # Mapping from list of variables to the clauses containing exactly those variables
    msgPrefix = ""
    constraintList = []
    # Statistics
    ucount = 0
    aloCount = 0
    amoCount = 0
    eqCount = 0

    def __init__(self, clauseList, iname):
        # Create of clause list, but sorting by variable
        self.clauseDict = { idx+1 : clauseList[idx] for idx in range(len(clauseList)) }
        self.msgPrefix = "" if iname is None else "File %s: " % iname
        self.constraintList = []
        self.ucount = 0
        self.aloCount = 0
        self.amoCount = 0
        self.eqCount = 0

    def findUnits(self):
        startCount = len(self.constraintList)
        idList = sorted(self.clauseDict.keys())
        for cid in idList:
            clause = self.clauseDict[cid]
            if len(clause) > 1:
                continue
            lit = clause[0]
            var = abs(lit)
            varList = [var]
            if lit < 0:
                coeffList = [-1]
                const = 0
            else:
                coeffList = [1]
                const = 1
            clauseList = [cid]
            self.constraintList.append(Formula(varList, coeffList, const, clauseList, False))
            del self.clauseDict[cid]
        self.ucount = len(self.constraintList)-startCount


    def findAlos(self):
        startCount = len(self.constraintList)
        idList = sorted(self.clauseDict.keys())
        for cid in idList:
            clause = self.clauseDict[cid]
            ok = True
            for lit in clause:
                if lit < 0:
                    ok = False
                    break
            if not ok:
                continue
            varList = clause
            coeffList = [1] * len(clause)
            const = 1
            clauseList = [cid]
            self.constraintList.append(Formula(varList, coeffList, const, clauseList, False))
            del self.clauseDict[cid]
        self.aloCount = len(self.constraintList)-startCount

    def findAmos(self):
        startCount = len(self.constraintList)
        # Mapping from variable to map from adjacent variables to True/False
        # Map in both directions
        edgeMap = {}
        # Mapping from sorted var tuples to clause id
        idSet = {}
        idList = sorted(self.clauseDict.keys())
        # Build graph
        for cid in idList:
            clause = self.clauseDict[cid]
            if len(clause) != 2:
                continue
            if clause[0] > 0 or clause[1] > 0:
                continue
            v1, v2 = abs(clause[0]), abs(clause[1])
            idSet[(v1,v2)] = cid
            if v1 not in edgeMap:
                edgeMap[v1] = {}
            edgeMap[v1][v2] = True
            if v2 not in edgeMap:
                edgeMap[v2] = {}
            edgeMap[v2][v1] = True
        while len(idSet) > 0:
            # Mapping from variable to True/False
            cliqueMap = {}
            # Grab an edge
            for v,vx in idSet.keys():
                break
            cliqueMap[v] = True
            # Now expand into clique
            for ov in edgeMap[v].keys():
                include = True
                for cv in cliqueMap.keys():
                    if ov != cv and cv not in edgeMap[ov]:
                        include = False
                        break
                if include:
                    cliqueMap[ov] = True
            # Now have clique variables.  Put this together
            varList = sorted(cliqueMap.keys())
            coeffList = [-1] * len(varList)
            const = -1
            clauseList = []
            for i1 in range(len(varList)):
                v1 = varList[i1]
                for i2 in range(i1+1, len(varList)):
                    v2 = varList[i2]
                    pair = (v1,v2)
                    cid = idSet[pair]
                    clauseList.append(cid)
                    del self.clauseDict[cid]
                    del idSet[pair]
                    del edgeMap[v1][v2]
                    del edgeMap[v2][v1]
            con = Formula(varList, coeffList, const, clauseList, False)
            self.constraintList.append(con)
        self.amoCount = len(self.constraintList)-startCount

    def find(self, makeEquations):
        self.findUnits()
        self.findAlos()
        self.findAmos()
        if makeEquations:
            # Create mapping from variables to constraints
            vdict = {}
            for con in self.constraintList:
                tup = tuple(con.varList)
                if tup in vdict:
                    vdict[tup].append(con)
                else:
                    vdict[tup] = [con]
            nclist = []
            for tup in vdict.keys():
                merged = False
                if len(vdict[tup]) == 2:
                    con1, con2 = vdict[tup]
                    eq = con1.e1Merge(con2)
                    if eq is not None:
                        nclist.append(eq)
                        merged = True
                        self.aloCount -= 1
                        self.amoCount -= 1
                        self.eqCount += 1
                if not merged:
                    nclist += vdict[tup]
            self.constraintList = nclist


    def generate(self, oname, errfile, makeEquations):
        self.find(makeEquations)
        ccount = len(self.clauseDict)
        if ccount > 0:
            if verbLevel >= 3:
                clist = sorted(self.clauseDict.keys())
                slist = [str(c) for c in clist]
                ewrite("%sCould not classify %d clauses: [%s]\n" % (self.msgPrefix, ccount, " ".join(slist)), 3)
            else:
                ewrite("%sCould not classify %d clauses\n" % (self.msgPrefix, ccount), 2)
            return False
        if oname is None:
            outfile = sys.stdout
        else:
            try:
                outfile = open(oname, 'w')
            except:
                ewrite("%sCouldn't open output file '%s'\n" % (self.msgPrefix, oname), 0)
                return False
        for con in self.constraintList:
            con.generate(outfile)
        ccount = len(self.constraintList)
        ewrite("%s%d formulas (%d unit, %d ALO, %d AMO, %d equations)\n" % (self.msgPrefix, ccount, self.ucount, self.aloCount, self.amoCount, self.eqCount), 1)
        if oname is not None:
            outfile.close()
        return True
        
# Reasons to reject an entire CNF file due to clause that cannot match constraints
def rejectClause(lits, cid):
    # Mixed clause
    if min(lits) < 0 and max(lits) > 0:
        return "Clause #%d.  Mixed polarity" % cid
    # Too many negative literals
    if lits[0] < 0 and len(lits) > 2:
        return "Clause #%d.  Too many negative literals" % cid
    return None

def extract(iname, oname, maxclause, makeEquations):
    try:
        reader = CnfReader(iname, maxclause = maxclause, rejectClause = rejectClause)
        if reader.reason is not None:
            ewrite("File %s: Could not be classified (%s)\n" % (iname, reader.reason), 2)
            return False
    except Exception as ex:
        ewrite("Couldn't read CNF file: %s" % str(ex), 0)
        return
    cg = ConstraintFinder(reader.clauses, iname)
    return cg.generate(oname, errfile, makeEquations)


def replaceExtension(path, ext):
    fields = path.split('.')
    if len(fields) == 1:
        return path + '.' + ext
    else:
        fields[-1] = ext
    return ".".join(fields)

def run(name, args):
    global verbLevel
    global errfile
    global careful
    iname = None
    oname = None
    path = None
    maxclause = None
    ok = True
    makeEquations = False

    optlist, args = getopt.getopt(args, "hcev:i:o:p:m:")
    for (opt, val) in optlist:
        if opt == '-h':
            ok = False
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-c':
            careful = True
        elif opt == '-e':
            makeEquations = True
        elif opt == '-i':
            iname = val
        elif opt == '-o':
            oname = val
            errfile = sys.stdout
        elif opt == '-p':
            path = val
            errfile = sys.stdout
        elif opt == '-m':
            maxclause = int(val)
    if not ok:
        usage(name, errfile)
        return
    if path is None:
        ecode = 0 if  extract(iname, oname, maxclause, makeEquations) else 1
        sys.exit(ecode)
    else:
        if iname is not None or oname is not None:
            ewrite("Cannot specify path + input or output name", 0)
            usage(name)
            sys.exit(0)
        scount = 0
        flist = sorted(glob.glob(path + '*.cnf'))
        for iname in flist:
            oname = replaceExtension(iname, 'schedule')
            if extract(iname, oname, maxclause, makeEquations):
                scount += 1
        ewrite("Extracted Constraint representation of %d/%d files\n" % (scount, len(flist)), 1)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
            
            
