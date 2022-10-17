#!/usr/bin/python3

import sys
import datetime
import getopt

import solver
import bdd
import pseudoboolean

def usage(name):
    print("Usage %s: [-h] [-v VERB] -i FILE.cnf -p FILE.pbip [-o FILE.lrat]")
    print("  -h           Print this message")
    print("  -v VERB      Set verbosity level")
    print("  -i FILE.cnf  Input CNF file")
    print("  -p FILE.pbip Input proof file")
    print("  -o FILE.lrat Output proof file")

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
            print("Read PBIP line #%d" % self.lineCount)
            print("  Constraints:")
            for con in clist:
                print("   %s" % str(con))
            print("  Hints: %s" % str(hlist))
        return (command, clist, hlist)

class Pbip:
    verbLevel = 1
    creader = None
    preader = None
    # Set of constraints
    cset = None
    # Array mapping from PBIP file constraints to cset constraints (offset by 1)
    # Each is a list containing Ids of 1 or 2 constraints
    constraintList = []
    # BDD representations of constraints
    bddList = []
    # Enable use as constraint system
    prover = None
    manager = None
    varMap = {}
    levelMap = {}
    
    def __init__(self, cnfName, pbipName, lratName, verbLevel):
        self.verbLevel = verbLevel
        self.creader = solver.CnfReader(cnfName, verbLevel)
        self.preader = PbipReader(pbipName, verbLevel)
        self.cset = pseudoboolean.ConstraintSet()
        self.constraintList = []
        self.bddList = []
        self.prover = None
        if lratName != "":
            self.prover = solver.prover(fname=lratName, verbLevel = verbLevel, doLrat = True)
        self.manager = bdd.Manager(prover = self.prover, verbLevel = verbLevel)
        for level in range(1, self.creader.nvar+1):
            inputId = level
            var = self.manager.newVariable(name = "V%d" % inputId, id = inputId)
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
            nroot = clist[0]
        self.bddList.append(nroot)
        pid = len(self.constraintList)
        if command == 'i':
            self.doInput(pid, hlist)
        elif command == 'a':
            self.doAssertion(pid, hlist)
        else:
            raise PbipException("", "Unexpected command '%s'" % command)
        return False
        
    def doInput(self, pid, hlist):
        print("Processed PBIP input #%d.  Hints = %s" % (pid, str(hlist)))

    def doAssertion(self, pid, hlist):
        print("Processed PBIP assertion #%d.  Hints = %s" % (pid, str(hlist)))

    def run(self):
        while not self.doStep():
            pass
        foundUnsat = False
        if len(self.constraintList) > 0:
            lastCon = self.constraintList[-1][-1]
            if lastCon.isInfeasible():
                foundUnsat = True
                print("UNSAT")
        if not foundUnsat:
            print("Final status unknown")
        self.manager.summarize()


def run(name, argList):
    verbLevel = 1
    cnfName = ""
    pbipName = ""
    lratName = ""

    optlist, args = getopt.getopt(argList, "hv:i:p:o:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-p':
            pbipName = val
        elif opt == '-o':
            lratName = val
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    if cnfName == "":
        print("ERROR: Must give name of CNF file")
        usage(name)
        return
    if pbipName == "":
        print("ERROR: Must give name of PBIP file")
        usage(name)
        return

    pbip = Pbip(cnfName, pbipName, lratName, verbLevel)
    pbip.run()

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
