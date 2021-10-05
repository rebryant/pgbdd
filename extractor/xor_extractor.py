#!/usr/bin/python

# Convert CNF file containing only xor declarations into
# schedule file that converts these into pseudo-Boolean equations

import getopt
import sys
import glob

import xutil


def usage(name):
    xutil.ewrite("Usage: %s [-v VLEVEL] [-h] [-c] [-i IN.cnf] [-o OUT.schedule] [-d DIR] [-m MAXCLAUSE]\n" % name, 0)
    xutil.ewrite("  -h       Print this message\n", 0)
    xutil.ewrite("  -v VERB  Set verbosity level (1-4)\n", 0)
    xutil.ewrite("  -c       Careful checking of CNF\n", 0)
    xutil.ewrite("  -i IFILE Single input file\n", 0)
    xutil.ewrite("  -i OFILE Single output file\n", 0)
    xutil.ewrite("  -p PATH  Process all CNF files with matching path prefix\n", 0)
    xutil.ewrite("  -m MAXC  Skip files with larger number of clauses\n", 0)


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
            clause.sort(key = lambda lit : abs(lit))
            vars = tuple(sorted([abs(l) for l in clause]))
            if vars in self.varMap:
                self.varMap[vars].append(idx)
            else:
                self.varMap[vars] = [idx]
            
    def getClause(self, idx):
        if xutil.careful and (idx < 1 or idx > len(self.clauses)):
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
        return result
        
    def generate(self, oname):
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
                slist = [str(id) for id in idlist]
                xutil.ewrite("%sCould not classify clauses [%s]\n" % (self.msgPrefix, ", ".join(slist)), 3)
                if not xutil.careful:
                    break
                if xutil.verbLevel >= 4:
                    for id in idlist:
                        clause = self.getClause(id)
                        xutil.ewrite("    Clause #%d:%s\n" % (id, str(clause)), 4)
        if unkCount > 0:
            xutil.ewrite("%s%d total clauses.  Failed to classify %d clauses\n" % (self.msgPrefix, len(self.clauses), unkCount), 2)
            return False
        if oname is None:
            outfile = sys.stdout
        else:
            try:
                outfile = open(oname, 'w')
            except:
                xutil.ewrite("%sCouldn't open output file '%s'\n" % (self.msgPrefix, oname), 1)
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
        xutil.ewrite("%s%d equations extracted\n" % (self.msgPrefix, len(idlists)), 1)
        return True
            
        
def extract(iname, oname, maxclause):
    try:
        reader = xutil.CnfReader(iname, maxclause = maxclause, rejectClause = None)
        if len(reader.clauses) == 0:
            xutil.ewrite("File %s contains more than %d clauses\n" % (iname, maxclause), 2)
            return False
    except Exception as ex:
        xutil.ewrite("Couldn't read CNF file: %s" % str(ex), 1)
        return
    xor = Xor(reader.clauses, iname)
    return xor.generate(oname)


def replaceExtension(path, ext):
    fields = path.split('.')
    if len(fields) == 1:
        return path + '.' + ext
    else:
        fields[-1] = ext
    return ".".join(fields)

def run(name, args):
    iname = None
    oname = None
    path = None
    maxclause = None
    ok = True

    optlist, args = getopt.getopt(args, "hcv:i:o:p:m:")
    for (opt, val) in optlist:
        if opt == '-h':
            ok = False
        elif opt == '-v':
            xutil.verbLevel = int(val)
        elif opt == '-c':
            xutil.careful = True
        elif opt == '-i':
            iname = val
        elif opt == '-o':
            oname = val
            xutil.errfile = sys.stdout
        elif opt == '-p':
            path = val
            xutil.errfile = sys.stdout
        elif opt == '-m':
            maxclause = int(val)
    if not ok:
        usage(name)
        return
    if path is None:
        ecode = 0 if  extract(iname, oname, maxclause) else 1
        sys.exit(ecode)
    else:
        if iname is not None or oname is not None:
            xutil.ewrite("Cannot specify path + input or output name", 0)
            usage(name)
            sys.exit(0)
        scount = 0
        flist = sorted(glob.glob(path + '*.cnf'))
        for iname in flist:
            oname = replaceExtension(iname, 'schedule')
            if extract(iname, oname, maxclause):
                scount += 1
        xutil.ewrite("Extracted XOR representation of %d/%d files\n" % (scount, len(flist)), 1)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
            
            
