#!/usr/bin/python

# Convert CNF file containing only xor declarations into
# schedule file that converts these into pseudo-Boolean equations

import getopt
import sys
import glob

verbLevel = 1
errfile = sys.stderr

def ewrite(s, level):
    if level <= verbLevel:
        errfile.write(s)

def usage(name, errfile):
    ewrite("Usage: %s [-q] [-h] [-i IN.cnf] [-o OUT.schedule] [-d DIR]\n" % name, 0)

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

class Xor:
    # Input clauses
    clauses = []
    # Mapping from list of variables to the clauses containing exactly those variables
    varMap = {}
    msgPrefix = ""

    def __init__(self, clauses, iname):
        self.clauses = clauses
        self.varMap = {}
        self.msgPrefix = "" if iname is None else "File %s: " % iname
        for idx in range(1, len(clauses)+1):
            clause = self.getClause(idx)
            vars = tuple(sorted([abs(l) for l in clause]))
            if vars in self.varMap:
                self.varMap[vars].append(idx)
            else:
                self.varMap[vars] = [idx]
            
    def getClause(self, idx):
        if idx < 1 or idx > len(self.clauses):
            raise self.msgPrefix + "Invalid clause index %d.  Allowed range 1 .. %d" % (idx, len(self.clauses))
        return self.clauses[idx-1]
                    
    # Given set of clauses over common set of variables,
    # classify as "xor", "xnor" or None
    def classifyClauses(self, clist):
        if len(clist) == 0:
            return None
        if len(clist) != 2**(len(clist[0])-1):
            return None
        isXor = True
        isXnor = True
        # Make list of variable phases
        phases = []
        isXor = True
        isXnor = True
        pvals = []
        for clause in clist:
            plist = [1 if lit > 0 else 0 for lit in clause]
            # Xor will have even number of negative literals
            maybeXor = ((len(plist) - sum(plist))) % 2 == 0
            isXor = isXor and maybeXor
            isXnor = isXnor and not maybeXor
            pval = sum([plist[i] * 2**i for i in range(len(plist))])
            pvals.append(pval)
        pset = set(pvals)
        if len(pset) != len(clist):
            result = None
        elif isXor:
            result = "xor"
        elif isXnor:
            result = "xnor"
        else:
            result = None
#        print("Classified clauses %s.  pvals = %s.  Type = %s" % (str(clist), str(pset), str(result)))
        return result
        
    def generate(self, oname, errfile):
        idlists = list(self.varMap.values())
        totalCount = 0
        unkCount = 0
        tlist = []
        for idlist in idlists:
            clist = [self.getClause(id) for id in idlist]
            totalCount += len(clist)
            t = self.classifyClauses(clist)
            tlist.append(t)
            if t is None:
                unkCount += len(clist)
                slist = [str(c) for c in clist]
                ewrite("%sCould not classify clauses %s\n" % (self.msgPrefix, ", ".join(slist)), 2)
        if unkCount > 0:
            ewrite("%sFailed to classify %d/%d clauses\n" % (self.msgPrefix, unkCount, totalCount), 1)
            return False
        if oname is None:
            outfile = sys.stdout
        else:
            try:
                outfile = open(oname, 'w')
            except:
                ewrite("%sCouldn't open output file '%s'\n" % (self.msgPrefix, oname), 1)
                return False
        for (idlist, t) in zip(idlists, tlist):
            slist = [str(id) for id in idlist]
            outfile.write("c %s\n" % " ".join(slist))
            if len(idlist) > 1:
                outfile.write("a %d\n" % (len(idlist)-1))
            const = 1 if t == 'xor' else 0
            vars = [abs(lit) for lit in self.getClause(idlist[0])]
            stlist = ['1.%d' % v for v in vars]
            outfile.write("=2 %d %s\n" % (const, " ".join(stlist)))
        if oname is not None:
            outfile.close()
        ewrite("%s%d equations extracted\n" % (self.msgPrefix, len(idlists)), 1)
        return True
            
        
def extract(iname, oname):
    try:
        reader = CnfReader(iname)
    except Exception as ex:
        ewrite("Couldn't read CNF file: %s" % str(ex), 1)
        return
    xor = Xor(reader.clauses, iname)
    return xor.generate(oname, errfile)


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
    iname = None
    oname = None
    path = None
    ok = True

    optlist, args = getopt.getopt(args, "hv:i:o:p:")
    for (opt, val) in optlist:
        if opt == '-h':
            ok = False
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            iname = val
        elif opt == '-o':
            oname = val
            errfile = sys.stdout
        elif opt == '-p':
            path = val
    if not ok:
        usage(name, errfile)
        return
    if path is None:
        ecode = 0 if  extract(iname, oname) else 1
        sys.exit(ecode)
    else:
        if iname is not None or oname is not None:
            ewrite("Cannot specify path + input or output name", 0)
            usage(name)
            sys.exit(0)
        flist = sorted(glob.glob(path + '*.cnf'))
        for iname in flist:
            oname = replaceExtension(iname, 'schedule')
            extract(iname, oname)

        
def xorMaker(n, invert = False):
    if n == 1:
        return [[-1]] if invert else [[1]]
    cpos = xorMaker(n-1, False)
    cneg = xorMaker(n-1, True)
    if invert:
        cpos, cneg = cneg, cpos
    return [c + [-n] for c in cneg] + [c + [n] for c in cpos]

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
            
            
