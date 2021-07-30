#!/usr/bin/python

import sys
import getopt
import random
import modsolve

# Generate and solve embedding of mutilated chessboard problem
def usage(name):
    print("Usage: %s [-h] [-v] [-m MOD] [-n ROW] [-c COL] [-s SQUARES] [-w nhvb] [-r SEEDS]" % name) 
    print("  -h         Print this message")
    print("  -v         Run in verbose mode")
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

    def maybe_solvable(self):
        white_count = 0
        black_count = 0
        for r in range(self.rows):
            for c in range(self.cols):
                if not self.omit(r,c):
                    if (r % 2) == (c % 2):
                        white_count += 1
                    else:
                        black_count += 1
        return white_count == black_count

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
                         
    def equations(self, modulus, verbose):
        rmax = self.rows if self.wrap_vertical else self.rows-1
        cmax = self.cols if self.wrap_horizontal else self.cols-1
        N = self.rows * cmax + rmax * self.cols
        esys = modsolve.EquationSystem(N, modulus, verbose)
        for r in range(self.rows):
            for c in range(self.cols):
                vars = self.vars(r,c)
                if self.omit(r,c):
                    for v in vars:
                        e = modsolve.Equation(N, modulus, 0, esys.mbox)
                        e[v] = 1
                        esys.add_equation(e)
                else:
                    e = modsolve.Equation(N, modulus, 1, esys.mbox)
                    for v in vars:
                        e[v] = 1
                    esys.add_equation(e)
        return esys

        

def mc_solve(verbose, modulus, rows, cols, ssquares, wrap_horizontal, wrap_vertical, seed2):
    b = Board(rows, cols, ssquares, wrap_horizontal, wrap_vertical)
    ssquares = str(b.rsquares)
    print("Board: %d X %d.  Modulus = %d.  Omitting squares %s" % (rows, cols, modulus, ssquares))
    print("     Wrapping: Horizontal %s.  Vertical %s" % (wrap_horizontal, wrap_vertical))
    esys = b.equations(modulus, verbose)
    if seed2 is not None:
        esys.randomize = True
        random.seed(seed2)
    if not verbose:
        esys.pre_statistics()
    status = esys.solve()
    if not verbose:
        esys.post_statistics(status, b.maybe_solvable())

def run(name, args):
    verbose = False
    modulus = 3
    rows = 8
    cols = None
    ssquares = "ul:dr"
    wrap_horizontal = False
    wrap_vertical = False
    randomize = False
    seed2 = None
    optlist, args = getopt.getopt(args, "hvm:n:c:s:w:r:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
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

    mc_solve(verbose, modulus, rows, cols, ssquares, wrap_horizontal, wrap_vertical, seed2)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


                         
        

    


