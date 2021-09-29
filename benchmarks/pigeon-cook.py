#!/usr/bin/python

# Generate PHP problem and/or Cook's extended-resolution proof of unsatisfiability

def usage(name):
    print("%s: [-h] [-v] -r ROOT -n N" % name)
    print("  -h      Print this message")
    print("  -v      Add descriptive comments")
    print("  -r ROOT Root name of file.  Generates ROOT.cnf, ROOT.lrat")
    print("  -n N    Number of holes.  There will be N+1 pigeons")

import sys
import getopt
import writer

def unitRange(n):
    return range(1,n+1)


# Representation of PHP of a given size
class PHP:
    # How many holes.  Pigeons = holes + 1
    hcount = 0
    # Variable numbers.  Dictionary indexed by (pigeon,hole)
    variables = {}  
    # At-least-one clause IDs.  Indexed by pigeon
    pigeonClauses = {}
    # At-most-one clause IDs.  Indexed by (pigeon1, pigeon2, hole)
    holeClauses = {}
    # Add comments?
    verbose = False
    # Total number of variables (input + proof)
    variableCount = 0
    # Total number of clauses (input + proof)
    clauseCount = 0

    def __init__(self, hcount, verbose=False, variableCount = 0, clauseCount = 0):
        self.hcount = hcount
        self.verbose = verbose
        self.variables = {}
        self.pigeonClause = {}
        self.holeClauses = {}
        self.variableCount = variableCount
        self.clauseCount = clauseCount

    def addVariable(self):
        self.variableCount += 1
        return self.variableCount

    def generateCnf(self, froot):
        hcount = self.hcount
        ecount = (hcount+1) + (hcount+1)*(hcount)//2
        cnfWriter = writer.CnfWriter(ecount, froot, self.verbose)
        for p in unitRange(hcount+1):
            for h in unitRange(hcount):
                v = self.addVariable()
                self.variables[(p,h)] = v
            if self.verbose:
                slist = [str(self.variables[(p, h)]) for h in unitRange(hcount)]
                cnfWriter.doComment("PHP(%d): Variables for pigeon %d: %s" % (hcount, p, " ".join(slist)))
        for p in unitRange(hcount+1):
            if self.verbose:
                cnfWriter.doComment("PHP(%d): At least one constraint for pigeon %d" % (hcount, p))
            lits = [self.variables[(p, h)] for h in unitRange(hcount)]
            self.pigeonClauses[p] = cnfWriter.doClause(lits)
        for h in unitRange(hcount):
            if self.verbose:
                cnfWriter.doComment("PHP(%d): At most one constraints for hole %d" % (hcount, h))
            for p1 in unitRange(hcount):
                for p2 in range(p1+1, hcount+2):
                    lits = [-self.variables[(p1,h)], -self.variables[(p2,h)]]
                    self.holeClauses[(p1,p2,h)] = cnfWriter.doClause(lits)
        self.clauseCount = cnfWriter.clauseCount
        cnfWriter.finish()
        return (self.variableCount, self.clauseCount)

    def generateProof(self, froot):
        proofWriter = writer.LratWriter(self.clauseCount, froot, verbose = self.verbose)
        php = self
        while php.hcount > 1:
            php = php.downscale(proofWriter)
        lits = []
        ids = [php.pigeonClauses[1], php.pigeonClauses[2], php.holeClauses[(1, 2, 1)]]
        if php.verbose:
            proofWriter.doComment("PHP(1) is trivially unsatisfiable")
        proofWriter.doStep(lits, ids)
        proofWriter.finish()
        return (php.variableCount, proofWriter.clauseCount)
            

    # Shrink to next lower PHP
    def downscale(self, proofWriter):
        hcount = self.hcount
        # Dictionary of defining clauses for new variables
        # Indexed by (p,h,t), where t is one of {'p1', 'p2', 'n1', 'n2'}
        dclauses = {}
        nphp = PHP(hcount-1, verbose = self.verbose, variableCount = self.variableCount, clauseCount = self.clauseCount)
        for p in unitRange(hcount):
            for h in unitRange(hcount-1):
                v = nphp.addVariable()
                nphp.variables[(p,h)] = v
            if self.verbose:
                slist = [str(nphp.variables[(p, h)]) for h in unitRange(hcount-1)]
                proofWriter.doComment("PHP(%d): Variables for pigeon %d: %s" % (hcount-1, p, " ".join(slist)))
            for h in unitRange(hcount-1):
                if self.verbose:
                    proofWriter.doComment("PHP(%d): Defining clauses for q(%d,%d)" % (hcount-1, p, h))
                lits = [nphp.variables[(p,h)], -self.variables[(p,h)]]
                ids = []
                dclauses[(p,h,'p1')] = proofWriter.doStep(lits, ids)
                lits = [nphp.variables[(p,h)], -self.variables[(p,hcount)], -self.variables[(hcount+1,h)]]
                dclauses[(p,h,'p2')] = proofWriter.doStep(lits, ids)

                ids = [-dclauses[(p,h,'p1')], -dclauses[(p,h,'p2')]]
                lits = [-nphp.variables[(p,h)], self.variables[(p,h)], self.variables[(p,hcount)]]        
                dclauses[(p,h,'n1')] = proofWriter.doStep(lits, ids)
                lits = [-nphp.variables[(p,h)], self.variables[(p,h)], self.variables[(hcount+1,h)]]
                dclauses[(p,h,'n2')] = proofWriter.doStep(lits, ids)
        for p in unitRange(hcount):
            if self.verbose:
                proofWriter.doComment("PHP(%d): At least one constraint for pigeon %d" % (hcount-1, p))
            lits = [nphp.variables[(p, h)] for h in unitRange(hcount-1)]
            ids = [dclauses[(p,h,'p1')] for h in unitRange(hcount-1)] + [self.pigeonClauses[p]] + [dclauses[(p,h,'p2')] for h in unitRange(hcount-1)] + [self.holeClauses[(p,hcount+1,hcount)]]
            nphp.pigeonClauses[p] = proofWriter.doStep(lits, ids)
        for h in unitRange(hcount-1):
            if self.verbose:
                proofWriter.doComment("PHP(%d): At most one constraints for hole %d" % (hcount-1, h))
            for p1 in unitRange(hcount-1):
                for p2 in range(p1+1, hcount+1):
                    # Requires intermediate step
                    lits = [self.variables[(hcount+1,h)], -nphp.variables[(p1,h)], -nphp.variables[(p2,h)]]
                    ids = [dclauses[(p1,h,'n2')], dclauses[(p2,h,'n2')], self.holeClauses[(p1,p2,h)]]
                    ic = proofWriter.doStep(lits, ids)
                    lits = [-nphp.variables[(p1,h)], -nphp.variables[(p2,h)]]
                    ids = [ic, self.holeClauses[(p1,hcount+1,h)], self.holeClauses[(p2,hcount+1,h)], dclauses[(p1,h,'n1')], dclauses[(p2,h,'n1')], self.holeClauses[(p1,p2,hcount)]]
                    nphp.holeClauses[(p1,p2,h)] = proofWriter.doStep(lits, ids)
        return nphp



def run(name, args):
    verbose = False
    hcount = 0
    rootName = None

    optlist,args = getopt.getopt(args, "hvr:n:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-r':
            rootName = val
        elif opt == '-n':
            hcount = int(val)
    if hcount == 0:
        print("Must specify number of holes")
        usage(name)
        return
    if rootName is None:
        print("Must specify root name")
        usage(name)
    
    php = PHP(hcount, verbose)
    (vcount, ccount) = php.generateCnf(rootName)
    print("Input Variables: %d" % (vcount))
    print("Input Clauses: %d" % (ccount))
    (vcount, ccount) = php.generateProof(rootName)
    print("Total Variables: %d" % (vcount))
    print("Total Clauses: %d" % (ccount))


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
