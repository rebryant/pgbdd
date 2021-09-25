#!/usr/bin/python

import sys
import getopt
import random
import modsolve
import constraints

# Generate and solve equational or constraint embedding of mutilated chessboard problem
def usage(name):
    print("Usage: %s [-h] [-v] [-c] [-p] [-m MOD] [-n ROW] [-c COL] [-s SQUARES] [-w nhvb] [-r SEEDS]" % name) 
    print("  -h         Print this message")
    print("  -v         Run in verbose mode")
    print("  -c         Use constraints rather than equations")
    print("  -p         Perform presumming")
    print("  -m MOD     Specify modulus")
    print("  -n ROW     Specify number of rows in board")
    print("  -c COL     Specify number of columns in board (default is square)")
    print("  -s SQUARES Omit squares.")
    print("             String of form VH:VH:..:VH, where V in {u, m, d, e, o} and H in {l, m, r, e, o}")
    print("             u=up, m=middle, d=down, e=random even, o = random odd, l=left, r=right.  Default is 'ul:dr'")
    print("  -w WRAP    Optionally wrap grid horizontally (h), vertically (v) both (b), or none (n)")
    print("  -r SEEDS   Set random seed.  Either single number S, or S1:S2 for board generation and solving")


        
# Encoding of mutilated chessboard problem as linear equations
class Board:
    rows = 4
    cols = 4
    # List of squares to omit.  Each specified by (r,c)
    rsquares = []
    udvars = {}
    lrvars = {}
    esys = None

    # ssquares is string describing squares to remove.  Documented in usage()
    # Optionally allow grid to wrap horizontally or vertically, giving cylinder or torus
    def __init__(self, rows, cols, ssquares, wrap_horizontal, wrap_vertical):
        self.rows = rows
        self.cols = cols
        self.rsquares = self.get_squares(ssquares)
        self.wrap_horizontal = wrap_horizontal
        self.wrap_vertical = wrap_vertical
        self.udvars = {}
        self.lrars = {}

        # Assign variable IDs
        var = 0
        rlim = self.rows if wrap_vertical else self.rows-1
        for r in range(rlim):
            for c in range(self.cols):
                self.udvars[(r,c)] = var
                var += 1
        clim = self.cols if wrap_horizontal else self.cols-1
        for r in range(self.rows):
            for c in range(clim):
                self.lrvars[(r,c)] = var
                var += 1

    # Parse string specifying which strings to omit
    def get_squares(self, ssquares):
        if ssquares.lower() == 'none':
            return []
        flist = []
        rlist = []
        fields = ssquares.split(":")
        parity = 0  # Support for shifting halfway point on alternating selections
        while len(fields) > 0:
            field = fields[0]
            random_selection = 'e' in field or 'o' in field
            if field == "":
                continue
            field = field.lower()
            r = 0
            c = 0
            ok = True
            if len(field) != 2:
                ok = False
            else:
                lmreo = field[1]
                if lmreo == 'l':
                    c = 0
                elif lmreo == 'm':
                    c = self.cols//2 + parity
                elif lmreo == 'r':
                    c = self.cols-1
                elif lmreo == 'e':
                    c = 2 * random.randint(0, self.cols//2 -1)
                elif lmreo == 'o':
                    c = 1 + 2 * random.randint(0, self.cols//2 -1)
                else:
                    ok = False

                umdeo = field[0]
                if umdeo == 'u':
                    r = 0
                elif umdeo == 'm':
                    r = self.rows//2 + parity
                elif umdeo == 'd':
                    r = self.rows-1
                elif umdeo == 'e':
                    r = 2 * random.randint(0, self.rows//2 -1)
                elif umdeo == 'o':
                    r = 1 + 2 * random.randint(0, self.rows//2 -1)
                else:
                    ok = False
            if ok:
                if random_selection:
                    if (r,c) not in flist+rlist:
                        rlist.append((r,c))
                        fields = fields[1:]
                else:
                    flist.append((r,c))
                    fields = fields[1:]
            else:
                raise Exception("Can't parse square specifier '%s'" % field)
            parity = 1 - parity

        return flist+rlist

    def omit(self, r, c):
        for (xr,xc) in self.rsquares:
            if r == xr and c == xc:
                return True
        return False

    def even_odd_counts(self):
        even_count = 0
        odd_count = 0
        for r in range(self.rows):
            for c in range(self.cols):
                if not self.omit(r,c):
                    if (r+c) % 2 == 0:
                        even_count += 1
                    else:
                        odd_count += 1
        return (even_count, odd_count)

    def maybe_solvable(self):
        e, o = self.even_odd_counts()
        return e == o

    # Return list of variables surrounding given square
    def vars(self, r, c):
        vlist = []
        if self.wrap_vertical:
            rup = r-1 if r > 0 else self.rows-1
            vlist.append(self.udvars[(rup, c)])
            rdown   = r if r < self.rows else 0
            vlist.append(self.udvars[(rdown, c)])
        else:
            if r > 0:
                vlist.append(self.udvars[(r-1,c)])
            if r < self.rows-1:
                vlist.append(self.udvars[(r,c)])
        if self.wrap_horizontal:
            cleft = c-1 if c > 0 else self.cols-1
            vlist.append(self.lrvars[(r, cleft)])
            cright  = c if c < self.cols else 0
            vlist.append(self.lrvars[(r, cright)])
        else:
            if c > 0:
                vlist.append(self.lrvars[(r,c-1)])
            if c < self.cols-1:
                vlist.append(self.lrvars[(r,c)])
        return vlist
                         
    def equations(self, modulus, verbose, presum):
        rmax = self.rows if self.wrap_vertical else self.rows-1
        cmax = self.cols if self.wrap_horizontal else self.cols-1
        N = self.rows * cmax + rmax * self.cols
        esys = modsolve.EquationSystem(N, modulus, verbose)
        # Track equations for squares based on parity of r+c
        even_equations = []
        odd_equations = []
        for r in range(self.rows):
            for c in range(self.cols):
                vars = self.vars(r,c)
                if self.omit(r,c):
                    for v in vars:
                        e = modsolve.Equation(N, modulus, 0, esys.mbox)
                        e[v] = 1
                        eid = esys.add_equation(e)
                        if (r+c) % 2 ==  0:
                            even_equations.append(eid)
                        else:
                            odd_equations.append(eid)
                else:
                    e = modsolve.Equation(N, modulus, 1, esys.mbox)
                    for v in vars:
                        e[v] = 1
                    eid=esys.add_equation(e)
                    if (r+c) % 2 ==  0:
                        even_equations.append(eid)
                    else:
                        odd_equations.append(eid)
        if presum:
            esys.add_presum(even_equations)
            esys.add_presum(odd_equations)
        return esys

    def constraints(self, verbose, presum):
        rmax = self.rows if self.wrap_vertical else self.rows-1
        cmax = self.cols if self.wrap_horizontal else self.cols-1
        N = self.rows * cmax + rmax * self.cols
        csys = constraints.ConstraintSystem(N, verbose)
        # Track constraints for squares based on minority and majority
        # square classes, where these are based on parity of r+c
        majority_constraints = []
        minority_constraints = []
        (even_count, odd_count) = self.even_odd_counts()
        even_majority = even_count >= odd_count
        con = constraints.Constraint(N, 0)
        # Make pass through to find variables forced to zero
        zdict = {}
        for r in range(self.rows):
            for c in range(self.cols):
                if self.omit(r,c):
                    vars = self.vars(r,c)
                    for v in vars:
                        zdict[v] = True
        for r in range(self.rows):
            for c in range(self.cols):
                even = (r+c) % 2 == 0
                is_major = even == even_majority
                vars = { v for v in self.vars(r,c) if v not in zdict }
                if self.omit(r,c):
                    continue
                elif is_major:
                    ncon = con.alo(vars)
                else:
                    ncon = con.amo(vars)
                cid = csys.add_constraint(ncon)
                if is_major:
                    majority_constraints.append(cid)
                else:
                    minority_constraints.append(cid)
        if presum:
            csys.add_presum(majority_constraints)
            csys.add_presum(minority_constraints)
        return csys
        

def mc_solve(verbose, constrain, presum, modulus, rows, cols, ssquares, wrap_horizontal, wrap_vertical, seed2):
    b = Board(rows, cols, ssquares, wrap_horizontal, wrap_vertical)
    ssquares = str(b.rsquares)
    if constrain:
        print("Board: %d X %d.  Omitting squares %s" % (rows, cols, ssquares))
    else:
        print("Board: %d X %d.  Modulus = %d.  Omitting squares %s" % (rows, cols, modulus, ssquares))
    print("     Wrapping: Horizontal %s.  Vertical %s" % (wrap_horizontal, wrap_vertical))
    xsys = b.constraints(verbose, presum) if constrain else b.equations(modulus, verbose, presum)
    if seed2 is not None:
        xsys.randomize = True
        random.seed(seed2)
    if not verbose:
        xsys.pre_statistics()
    status = xsys.solve()
    if not verbose:
        xsys.post_statistics(status, b.maybe_solvable())

def run(name, args):
    verbose = False
    presum = False
    modulus = 3
    constrain = False
    rows = 8
    cols = None
    ssquares = "ul:dr"
    wrap_horizontal = False
    wrap_vertical = False
    randomize = False
    seed2 = None
    optlist, args = getopt.getopt(args, "hvcpm:n:c:s:w:r:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-c':
            constrain = True
        elif opt == '-p':
            presum = True
        elif opt == '-m':
            modulus = int(val)
        elif opt == '-n':
            rows = int(val)
        elif opt == '-c':
            cols = int(val)
        elif opt == '-s':
            ssquares = val
        elif opt == '-v':
            verbose = True
        elif opt == '-w':
            ok = False
            if val in "hb":
                wrap_horizontal = True
                ok = True
            if val in "vb":
                ok = True
                wrap_vertical = True
            if val == "n":
                ok = True
            if not ok:
                print("Invalid wrapping parameter '%s'.  Must be h, v, b, or n" % val)
                return
        elif opt == '-r':
            randomize = True
            fields = val.split(':')
            seeds = [int(field) for field in fields]
            seed1 = seeds[0]
            random.seed(seed1)
            seed2 = seeds[1] if len(seeds) > 1 else seed1

    if cols is None:
        cols = rows

    mc_solve(verbose, constrain, presum, modulus, rows, cols, ssquares, wrap_horizontal, wrap_vertical, seed2)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


                         
        

    


