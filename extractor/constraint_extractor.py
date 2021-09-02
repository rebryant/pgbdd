#!/usr/bin/python

# Convert CNF file containing only at-most-1 and at-least-1 declarations into
# schedule file that converts these into pseudo-Boolean constraints

import getopt
import sys
import glob
import util

def usage(name):
    util.ewrite("Usage: %s [-h] [-c] [-v VLEVEL] [-i IN.cnf] [-o OUT.schedule] [-p PATH] [-m MAXCLAUSE]\n" % name, 0)
    util.ewrite("  -h       Print this message\n", 0)
    util.ewrite("  -v VERB  Set verbosity level (1-4)\n", 0)
    util.ewrite("  -c       Careful checking of CNF\n", 0)
    util.ewrite("  -i IFILE Single input file\n", 0)
    util.ewrite("  -i OFILE Single output file\n", 0)
    util.ewrite("  -p PATH  Process all CNF files with matching path prefix\n", 0)
    util.ewrite("  -m MAXC  Skip files with larger number of clauses\n", 0)


# Constraint or equation
class Formula:
    varList = []
    coeffList = []
    const = 0
    # Input clause Ids that generate this constraint
    clauseList = []
    # Variables to quantify out
    qvarList = []
    isEquation = False

    def __init__(self, varList, coeffList, const, clauseList, qvarList, isEquation):
        self.varList = varList
        self.coeffList = coeffList
        self.const = const
        self.clauseList = clauseList
        self.qvarList = qvarList
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
        qvarList = alo.qvarList + amo.qvarList
        return Formula(varList, coeffList, const, clauseList, qvarList, True)

    def __str__(self):
        slist = ["%d.%d" % (v, c) for c,v in zip(self.varList, self.coeffList)]
        symbol = "=" if self.isEquation else ">="
        return ("%s %d " % (symbol, self.const)) + " ".join(slist)

    def generate(self, outfile):
        slist = [str(c) for c in self.clauseList]
        outfile.write("c " + " ".join(slist) + "\n")
        if len(self.clauseList) > 1:
            outfile.write("a %d\n" % (len(self.clauseList) - 1))
        if len(self.qvarList) > 1:
            slist = [str(v) for v in self.qvarList]
            outfile.write("q %s\n" % " ".join(slist))
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
            self.constraintList.append(Formula(varList, coeffList, const, clauseList, [], False))
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
            self.constraintList.append(Formula(varList, coeffList, const, clauseList, [], False))
            del self.clauseDict[cid]
        self.aloCount = len(self.constraintList)-startCount

    # Classify vars regarding how they occur in binary clauses
    # Generate mapping from variable to pair (pos,neg), where each element of the pair is True or False
    def classifyVars(self):
        polarityDict = {}
        for clause in self.clauseDict.values():
            if len(clause) != 2:
                continue
            for lit in clause:
                var = abs(lit)
                pos,neg = False, False
                if var in polarityDict:
                    pos,neg = polarityDict[var]
                if lit < 0:
                    neg = True
                else:
                    pos = True
                polarityDict[var] = (pos,neg)
        return polarityDict

    def findEncodedAmos(self):
        startCount = len(self.constraintList)
        # Classify variables as problem variables or encoding variables
        polarityDict = self.classifyVars()
        # Encoding variables occur both positively and negatively
        # Build map from each encoding variable to the clauses that contain it
        evarMap = { var : [] for var in polarityDict.keys() if polarityDict[var] == (True,True) }
        # Build map from each program variable to the clauses that contain it
        pvarMap = { var : [] for var in polarityDict.keys() if polarityDict[var] == (False,True) }
        for cid in self.clauseDict.keys():
            clause = self.clauseDict[cid]
            assigned = False
            for lit in clause:
                var = abs(lit)
                if var in evarMap:
                    evarMap[var].append(cid)
                elif var in pvarMap:
                    pvarMap[var].append(cid)
        # Build up clusters, each containing set of encoding and program variables
        # Do so by following chains of encoding variables
        while len(evarMap) > 0:
            # Maps from variables to True/False
            pmap = {}
            emap = {}
            # Mapping from clause Ids to True/False
            idmap = {}
            # Grab an encoding variable as starting point
            for ev in evarMap.keys():
                break
            traceList = [ev]
            # Follow transitive closure from pairs of encoding variables
            while len(traceList) > 0:
                ev = traceList[0]
                traceList = traceList[1:]
                emap[ev] = True
                for cid in evarMap[ev]:
                    idmap[cid] = True
                    clause = self.clauseDict[cid]
                    for lit in clause:
                        var = abs(lit)
                        if var == ev or var in emap or var in pmap:
                            continue
                        if var in evarMap:
                            traceList.append(var)
                        else:
                            pmap[var] = True
                del evarMap[ev]

            # Now add remaining clauses that contain only variables in cluster
            for pv in pmap.keys():
                for cid in pvarMap[pv]:
                    if cid not in self.clauseDict:
                        continue
                    clause = self.clauseDict[cid]
                    inCluster = True
                    for lit in clause:
                        var = abs(lit)
                        if var not in pmap and var not in emap:
                            inCluster = False
                    if inCluster:
                        idmap[cid] = True

            varList = sorted(pmap.keys())
            coeffList = [-1] * len(varList)
            const = -1
            qvarList = sorted(emap.keys())
            clauseList = sorted(idmap.keys())
            for cid in clauseList:
                del self.clauseDict[cid]
            con = Formula(varList, coeffList, const, clauseList, qvarList, False)
            self.constraintList.append(con)
        self.amoCount += len(self.constraintList)-startCount
                        

    def findDirectAmos(self):
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
            clauseList.sort()
            con = Formula(varList, coeffList, const, clauseList, [], False)
            self.constraintList.append(con)
        self.amoCount += len(self.constraintList)-startCount

    def find(self):
        self.findUnits()
        self.findAlos()
        self.findEncodedAmos()
        self.findDirectAmos()
        # Combine constraints into equations when possible
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


    def generate(self, oname):
        self.find()
        ccount = len(self.clauseDict)
        if ccount > 0:
            if util.verbLevel >= 3:
                clist = sorted(self.clauseDict.keys())
                slist = [str(c) for c in clist]
                util.ewrite("%sCould not classify %d clauses: [%s]\n" % (self.msgPrefix, ccount, " ".join(slist)), 3)
            else:
                util.ewrite("%sCould not classify %d clauses\n" % (self.msgPrefix, ccount), 2)
            return False
        if oname is None:
            outfile = sys.stdout
        else:
            try:
                outfile = open(oname, 'w')
            except:
                util.ewrite("%sCouldn't open output file '%s'\n" % (self.msgPrefix, oname), 0)
                return False
        for con in self.constraintList:
            con.generate(outfile)
        ccount = len(self.constraintList)
        util.ewrite("%s%d formulas (%d unit, %d ALO, %d AMO, %d equations)\n" % (self.msgPrefix, ccount, self.ucount, self.aloCount, self.amoCount, self.eqCount), 1)
        if oname is not None:
            outfile.close()
        return True
        
# Reasons to reject an entire CNF file due to clause that cannot match constraints
# Only for direct encodings of AMO
def directRejectClause(lits, cid):
    # Mixed clause
    if min(lits) < 0 and max(lits) > 0:
        return "Clause #%d.  Mixed polarity" % cid
    # Too many negative literals
    if lits[0] < 0 and len(lits) > 2:
        return "Clause #%d.  Too many negative literals" % cid
    return None

def extract(iname, oname, maxclause):
    try:
        reader = util.CnfReader(iname, maxclause = maxclause, rejectClause = None)
        if reader.reason is not None:
            util.ewrite("File %s: Could not be classified (%s)\n" % (iname, reader.reason), 2)
            return False
    except Exception as ex:
        util.ewrite("Couldn't read CNF file: %s" % str(ex), 0)
        return
    cg = ConstraintFinder(reader.clauses, iname)
    return cg.generate(oname)


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
            util.verbLevel = int(val)
        elif opt == '-c':
            util.careful = True
        elif opt == '-i':
            iname = val
        elif opt == '-o':
            oname = val
            util.errfile = sys.stdout
        elif opt == '-p':
            path = val
            util.errfile = sys.stdout
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
            util.ewrite("Cannot specify path + input or output name", 0)
            usage(name)
            sys.exit(0)
        scount = 0
        flist = sorted(glob.glob(path + '*.cnf'))
        for iname in flist:
            oname = replaceExtension(iname, 'schedule')
            if extract(iname, oname, maxclause):
                scount += 1
        util.ewrite("Extracted Constraint representation of %d/%d files\n" % (scount, len(flist)), 1)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
            
            