# Tools for working with PBIP proofs.
# PBIP that a set of Pseudo-Boolean (PB) constraints is unsatisfiable
# via a sequence of implication steps
# The tool pbip_check.py converts a PBIP proof into a clausal proof in LRAT format
# The tool pbip_cnf.py generates a CNF file containing clausal representation of the input PB constraints
# The tool pbip_order.py generates a permutation of the CNF file to ensure that all
# problem variables occur first in the file.


import solver
import bdd
import pseudoboolean
import resolver


def trim(s):
    while len(s) > 0 and s[0] in ' \t':
        s = s[1:]
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s


# Return list of constraints from line of OBP
class PbipException(Exception):
    form = ""
    line = ""

    def __init__(self, line, msg):
        self.form = "PBIP error"
        if line == "":
            self.msg = msg
        else:
            self.msg = "line = '%s', %s" % (line, msg)

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

# Read string representation of OPB constraint
# Return list of Constraint objects
# List contains one constraint for operations <, <=, >, >=
# and a pair of constraints for =
def parseObp(line):
    fields = line.split()
    # Get rid of trailing semicolon
    if len(fields) == 0:
        raise PbipException(line, "Empty")
    if fields[-1] == ';':
        fields = fields[:-1]
    elif fields[-1][-1] == ';':
        fields[-1] = fields[-1][:-1]
    if len(fields) < 2 or len(fields) % 2 != 0:
        raise PbipException(line, "Invalid number of fields")
    try:
        cval = int(fields[-1])
    except:
        raise PbipException(line, "Invalid constant %s" % fields[-1])
    rel = fields[-2]
    if rel not in ['<', '<=', '=', '>=', '>']:
        raise PbipException(line, "Invalid relation %s" % rel)
    cfields = fields[:-2]
    coeffs = []
    vars = []
    for i in range(len(cfields)//2):
        scoeff = cfields[2*i]
        try:
            coeff = int(scoeff)
        except:
            raise PbipException(line, "Invalid coefficient %s" % scoeff)
        svar = cfields[2*i+1]
        if svar[0] == 'x':
            try:
                var = int(svar[1:])
            except:
                raise PbipException(line, "Invalid term %s" % svar)
        else:
            raise PbipException(line, "Invalid term %s" % svar)
        coeffs.append(coeff)
        vars.append(var)
    # Normalize
    if rel == '<':
        rel = '<='
        cval -= 1
    if rel == '>':
        rel = '>='
        cval += 1
    if rel == '<=':
        rel = '>='
        cval = -cval
        coeffs = [-c for c in coeffs]
    nz = { v : c for v,c in zip(vars,coeffs) }
    con1 = pseudoboolean.Constraint(len(nz), cval)
    con1.setNz(nz)
    if rel == '>=':
        return [con1]
    else:
        cval = -cval
        coeffs = [-c for c in coeffs]
        nz = { v : c for v,c in zip(vars,coeffs) }
        con2 = pseudoboolean.Constraint(len(nz), cval)
        con2.setNz(nz)
        return [con1, con2]
    
class PbipReader:
    fname = ""
    lineCount = 0
    infile = None
    verbLevel = 1
    
    def __init__(self, fname, verbLevel):
        try:
            self.fname = fname
            self.infile = open(fname, 'r')
        except:
            print("Can't open input file %s" % fname)
            raise PbipException("", "Invalid input file")
        self.lineCount = 0
        self.verbLevel = verbLevel

    def finish(self):
        if self.infile is not None:
            self.infile.close()
            self.infile = None
        

    # Return (command, list of PB constraints, plus list of hints)
    def readLine(self):
        command = ""
        clist = []
        hlist = []
        for line in self.infile:
            self.lineCount += 1
            line = trim(line)
            if len(line) == 0:
                continue
            if line[0] == '*':
                continue
            command = line[0]
            if command not in ['i', 'a']:
                raise PbipException("", "File %s Line %d: Invalid command '%s'" % (self.fname, self.lineCount, command))
            cline  = trim(line[1:])
            pos = cline.find(';')
            if pos < 0:
                raise PbipException("", "File %s Line %d: No semicolon found" % (self.fname, self.lineCount))
            cstring = cline[:pos]
            hstring = cline[pos+1:]
            try:
                clist = parseObp(cstring)
            except PbipException as ex:
                raise PbipException("", "File %s Line %d: %s" % (self.fname, self.lineCount, str(ex)))
            hfields = hstring.split()
            try:
                hlist = [int(f) for f in hfields]
            except:
                raise PbipException("", "File %s Line %d: Couldn't parse hint list '%s'" % (self.fname, self.lineCount, hstring))
            break
        if self.verbLevel >= 3:
            print("c Read PBIP line #%d" % self.lineCount)
            print("c   Constraints:")
            for con in clist:
                print("c     %s" % str(con))
            print("c   Hints: %s" % str(hlist))
        return (command, clist, hlist)

 
        

class Pbip:
    verbLevel = 1
    valid = True
    creader = None
    preader = None
    permuter = None
    # Set of constraints
    cset = None
    # Array mapping from PBIP file constraints to cset constraints (offset by 1)
    # Each is a list containing Ids of 1 or 2 constraints
    constraintList = []
    # Trusted BDD representations of constraints
    # Each TBDD is pair (root, validation)
    tbddList = []
    # Enable use as constraint system
    prover = None
    manager = None
    litMap = {}
    varMap = {}
    levelMap = {}
    
    def __init__(self, cnfName, pbipName, lratName, verbLevel):
        self.verbLevel = verbLevel
        self.valid = True
        self.creader = solver.CnfReader(cnfName, verbLevel)
        self.preader = PbipReader(pbipName, verbLevel)
        self.cset = pseudoboolean.ConstraintSet()
        self.constraintList = []
        self.tbddList = []
        lratName = None if lratName == "" else lratName
        self.prover = solver.Prover(fname=lratName, writer = solver.StdOutWriter(), verbLevel = verbLevel, doLrat = True)
        # Print input clauses
        clauseCount = 0
        for clause in self.creader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount, isInput = True)
        self.prover.inputDone()
        self.manager = bdd.Manager(prover = self.prover, nextNodeId = self.creader.nvar+1, verbLevel = verbLevel)
        self.litMap = {}
        for level in range(1, self.creader.nvar+1):
            inputId = level
            var = self.manager.newVariable(name = "V%d" % inputId, id = inputId)
            t = self.manager.literal(var, 1)
            self.litMap[ inputId] = t
            e = self.manager.literal(var, 0)
            self.litMap[-inputId] = e
        self.varMap = { var.id : var for var in self.manager.variables }
        self.levelMap = { var.id : var.level for var in self.manager.variables }

    def doStep(self):
        command, clist, hlist = self.preader.readLine()
        if command == '':
            return True
        for con in clist:
            con.buildBdd(self)
        self.constraintList.append(clist)
        if len(clist) == 2:
            nroot = bdd.applyAnd(clist[0], clist[1])
        else:
            nroot = clist[0].root
        self.tbddList.append((nroot,None))
        pid = len(self.constraintList)
        if command == 'i':
            self.doInput(pid, hlist)
        elif command == 'a':
            self.doAssertion(pid, hlist)
        else:
            raise PbipException("", "Unexpected command '%s'" % command)
        return False
        
    def placeInBucket(self, buckets, root, validation):
        supportIds = self.manager.getSupportIds(root)
        for id in supportIds:
            if id in buckets:
                buckets[id].append((root, validation))
                return
        buckets[0].append((root, validation))

    def conjunctTerms(self, r1, v1, r2, v2):
        nroot, implication = self.manager.applyAndJustify(r1, r2)
        validation = None
        antecedents = [v1, v2]
        if nroot == self.manager.leaf0:
            comment = "Validation of empty clause from %s & %s" % (r1.label(), r2.label())
        else:
            comment = "Validation of %s & %s --> %s" % (r1.label(), r2.label(), nroot.label())
        if implication == resolver.tautologyId:
            if nroot == r1:
                validation = v1
            elif nroot == r2:
                validation = v2
        else:
            antecedents += [implication]
        if validation is None:
            validation = self.manager.prover.createClause([nroot.id], antecedents, comment)
        return nroot, validation

    def quantifyRoot(self, root, validation, id):
        antecedents = [validation]
        vfun = self.litMap[id]
        nroot = self.manager.equant(root, vfun)
        ok, implication = self.manager.justifyImply(root, nroot)
        if not ok:
            raise PbipException("", "Implication failed during quantification of %s" % (root.label()))
        if implication != resolver.tautologyId:
            antecedents += [implication]
        comment = "Quantification of node %s by variable %s --> node %s" % (root.label(), str(vfun.variable), nroot.label())
        validation = self.manager.prover.createClause([nroot.id], antecedents, comment)
        return nroot, validation

    # Bucket reduction assumes all external variables come first in variable ordering
    def bucketReduce(self, buckets):
        ids = sorted(list(buckets.keys()))
        if ids[0] == 0:
            ids = ids[1:] + [0]
        for id in ids:
            if self.verbLevel >= 4:
                print("Processing bucket #%d.  Size = %d" % (id, len(buckets[id])))
            while len(buckets[id]) > 1:
                (r1,v1) = buckets[id][0]
                (r2,v2) = buckets[id][1]
                buckets[id] = buckets[id][2:]
                nroot,validation = self.conjunctTerms(r1, v1, r2, v2)
                self.placeInBucket(buckets, nroot, validation)
            if len(buckets[id]) == 1:
                root, validation = buckets[id][0]
                if id == 0:
                    return (root, validation)
                nroot, nvalidation = self.quantifyRoot(root, validation, id)
                if self.verbLevel >= 4:
                    print("Processed bucket #%d.  Root = %s" % (id, root.label()))
                self.placeInBucket(buckets, nroot, nvalidation)
        raise PbipException("", "Unexpected exit from bucketReduce.  buckets = %s" % str(buckets))


    def doInput(self, pid, hlist):
        clist= self.constraintList[pid-1]
        externalIdSet = set([])
        internalIdSet = set([])
        for con in clist:
            for ivar in con.nz.keys():
                id = self.manager.variables[ivar-1].id
                externalIdSet.add(id)
        # Set up buckets containing trusted BDD representations of clauses
        # Each tbdd is pair (root, validation)
        # Indexed by variable id
        # Special bucket 0 for terms that depend only on external variables
        buckets = { 0 : []}

        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP Input #%d.  Input clauses %s" % (pid, str(hlist)))
        for hid in hlist:
            iclause = self.creader.clauses[hid-1]
            clause = [self.litMap[lit] for lit in iclause]
            root, validation = self.manager.constructClause(hid, clause)
            if self.verbLevel >= 4:
                print("Created BDD with root %s, validation %s for input clause #%d" % (root.label(), str(validation), hid))
            for lit in iclause:
                ivar = abs(lit)
                id = self.manager.variables[ivar-1].id
                if id not in externalIdSet and id not in internalIdSet:
                    internalIdSet.add(id)
                    buckets[id] = []
            self.placeInBucket(buckets, root, validation)
        (broot, bvalidation) = self.bucketReduce(buckets)
        root = self.tbddList[pid-1][0]
        if root == broot:
            cid = bvalidation
        else:
            if self.verbLevel >= 3:
                print("Testing %s ==> %s" % (str(broot), str(root)))
            (ok, implication) = self.manager.justifyImply(broot, root)
            if not ok:
                print("ERROR: Couldn't justify step #%d.  Input not implied" % (pid))
                self.valid = False
                antecedents = []
            else:
                antecedents = [cid for cid in [implication, bvalidation] if cid != resolver.tautologyId]
            comment = "Justification of input constraint #%d" % pid
            cid = self.prover.createClause([root.id], antecedents, comment=comment)
        self.tbddList[pid-1] = (root, cid)
        if self.verbLevel >= 2:
            print("c Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Unit clause #%d [%d]" % (pid, broot.label(), root.label(), cid, root.id))
            self.prover.comment("Processed PBIP input #%d.  Constraint root = %s, Generated root = %s Unit clause #%d [%d]" % (pid, broot.label(), root.label(), cid, root.id))

    def doAssertion(self, pid, hlist):
        root = self.tbddList[pid-1][0]
        if self.verbLevel >= 2:
            self.prover.comment("Processing PBIP assertion #%d.  Hints = %s" % (pid, str(hlist)))
        antecedents = []
        if len(hlist) == 1:
            (r1,v1) = self.tbddList[hlist[0]-1]
            (ok, implication) = self.manager.justifyImply(r1, root)
            if not ok:
                print("ERROR: Couldn't justify Step #%d.  Not implied by Step #%d" % (pid, hlist[0]))
                self.valid = False
            else:
                antecedents = [cid for cid in [v1, implication] if cid != resolver.tautologyId]
        else:
            (r1,v1) = self.tbddList[hlist[0]-1]
            (r2,v2) = self.tbddList[hlist[1]-1]
            (ok, implication) = self.manager.applyAndJustifyImply(r1, r2, root)
            if not ok:
                print("ERROR: Couldn't justify Step #%d.  Not implied by Steps #%d and #%d" % (pid, hlist[0], hlist[1]))
                self.valid = False
            else:
                antecedents = [cid for cid in [v1, v2, implication] if cid != resolver.tautologyId]
        comment = "Justification of assertion #%d" % pid
        cid = self.prover.createClause([root.id], antecedents, comment)
        self.tbddList[pid-1] = (root, cid)
        if self.verbLevel >= 2:
            print("c Processed PBIP assertion #%d.  Root %s Unit clause #%d [%d]" % (pid, root.label(), cid, root.id))
            self.prover.comment("Processed PBIP assertion #%d.  Root %s Unit clause #%d [%d[" % (pid, root.label(), cid, root.id))

    def run(self):
        while not self.doStep():
            pass
        decided = False
        if not self.valid:
            print("c INVALID")
            decided = True
        elif len(self.constraintList) > 0:
            lastCon = self.constraintList[-1][-1]
            if lastCon.isInfeasible():
                decided = True
                print("c UNSAT")
        if not decided:
            print("Final status unknown")
        self.manager.summarize()


