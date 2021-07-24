#!/usr/bin/python

import sys
import getopt

# Generate and solve embedding of mutilated chessboard problem
def usage(name):
    print("Usage: %s [-h] [-v] [-m MOD] [-n N] [-c CORNERS]" % name) 
    print("  -h         Print this message")
    print("  -v         Run in verbose mode")
    print("  -m MOD     Specify modulus")
    print("  -n N       Specify size of board")
    print("  -c CORNERS Include corners.  String of form CC:CC:..:CC, where CC in {ul, ll, ur, lr}")


# General library for solving pseudo-boolean constraints embedded in
# modular arithmetic

class MathException(Exception):
    form = ""
    msg = ""

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

class ReciprocalException(MathException):
    def __init__(self, num):
        self.form = "No Reciprocal!"
        self.msg = "denominator=%d" % num


class ZeroException(MathException):
    def __init__(self, num):
        self.form = "Zero Divide!"
        self.msg = "numerator=%d" % num


class PivotExecption(MathException):
    def __init__(self, index):
        self.form = "Pivot=0!"
        self.msg = "index=%d" % index


# Supporting modular arithmetic
class ModMath:

    modulus = 2 # Must be prime
    reciprocals = {} # Dictionary mapping x to 1/x
    opcount = 0 # Statistics

    def __init__(self, modulus = 2):
        self.reciprocals = {}
        self.modulus = modulus
        self.opcount = 0
        for x in range(1,self.modulus):
            found = False
            for y in range(self.modulus):
                if self.mul(x, y) == 1:
                    self.reciprocals[x] = y
                    found = True
                    break
            if not found:
                raise ReciprocalException(x)
        # Reset count
        self.opcount = 0

    def add(self, x, y):
        self.opcount += 1 
        return (x+y) % self.modulus

    def mul(self, x, y):
        self.opcount += 1 
        return (x*y) % self.modulus

    def sub(self, x, y):
        self.opcount += 1 
        return (self.modulus + x - y) % self.modulus
        
    def recip(self, x):
        if x == 0:
            raise ZeroException(1)
        return self.reciprocals[x]

    def div(self, x, y):
        if y == 0:
            raise ZeroException(y)
        return self.mul(x, self.recip(y))

# Equation of form SUM (a_i * x_i)  =  C
# Only represent nonzero coefficients
class Equation:

    # Variable Count
    N = 10  # Length when format as vector
    # 
    # Mapping for variable Id to coefficient for nonzero coefficient
    nz = {}
    # Class to support math operations
    mbox = None
    cval = 0

    def __init__(self, N, modulus, cval, mbox = None):
        self.N = N
        self.modulus = modulus
        self.cval = cval
        self.nz = {}
        if mbox is None:
            self.mbox = ModMath(modulus)
        elif mbox.modulus != modulus:
            raise Exception("Mismatched moduli")
        else:
            self.mbox = mbox

    def set_nz(self, nz):
        self.nz = nz

    def __getitem__(self, i):
        return self.nz[i] if i in self.nz else 0

    def __setitem__(self, i, v):
        if v == 0:
            if self.nz:
                del self.nz[i]
        else:
            self.nz[i] = v

    # Length defined to be the number of nonzeros
    def __len__(self):
        return len(self.nz)

    def make_vector(self):
        vec = [0 for i in range(self.N)]
        for i in self.nz.keys():
            vec[i] = self.nz[i]
        return vec + [self.cval]

    # Generate new equation from new set of nonzeros
    def spawn(self, nnz, cval):
        e = Equation(self.N, self.modulus, cval, self.mbox)
        e.nz = nnz
        return e

    # Normalize vector so that element at pivot position == 1
    # By dividing all entries by the existing value
    # Returns new vector
    def normalize(self, pidx):
        pval = self[pidx]
        if pval == 0:
            raise PivotException(pidx)
        nnz = { i : self.mbox.div(self.nz[i], pval) for i in self.nz.keys() }
        nc = self.mbox.div(self.cval, pval)
        return self.spawn(nnz, nc)
        
    # Helper function for inserting new element in dictionary
    def nz_insert(self, nz, i, v):
        if v == 0 and i in nz:
            del nz[i]
        else:
            nz[i] = v

    # Add other vector to self
    def add(self, other):
        nnz = { i : self.nz[i] for i in self.nz.keys() }
        for i in other.nz.keys():
            self.nz_insert(nnz, i, self.mbox.add(self[i], other.nz[i]))
        nc = self.mbox.add(self.cval, other.cval)
        return self.spawn(nnz, nc)

    # Subtract other vector from self
    def sub(self, other):
        nnz = { i : self.nz[i] for i in self.nz.keys() }
        for i in other.nz.keys():
            self.nz_insert(nnz, i, self.mbox.sub(self[i], other.nz[i]))
        nc = self.mbox.sub(self.cval, other.cval)
        return self.spawn(nnz, nc)

    # Perform scaling subtraction
    # Must scale other vector by value at pivot pivot position before subtracting
    def scale_sub(self, other, pidx):
        nnz = { i : self.nz[i] for i in self.nz.keys() }
        sval = 0
        sval = self[pidx]
        if sval != 0:
            for i in other.nz.keys():
                x = self[i]
                dx = self.mbox.mul(sval, other.nz[i])
                nx = self.mbox.sub(x, dx)
                self.nz_insert(nnz, i, nx)
        nc = self.mbox.sub(self.cval, self.mbox.mul(sval, other.cval))
        return self.spawn(nnz, nc)

    # Lexicographic ordering of equations
    def is_greater(self, other):
        for i in range(self.N):
            if self[i] > other[i]:
                return True
            if self[i] < other[i]:
                return False
        return False
    
    # Is this an equation with no solution?
    def is_null(self):
        return self.cval != 0 and len(self) == 0

    def __str__(self):
        return str(self.make_vector())


# System of equations.
# Support LU decomposition of Gaussian elimination to see if system has any solutions
class EquationSystem:
    # Variable Count
    N = 10
    modulus = 3
    verbose = False

    # Class to support math operations
    mbox = None
    # Set of original equations
    elist = []

    ## Solver state
    # Eliminated equations
    slist = []
    # Remaining equations
    rlist = []


    def __init__(self, N, modulus, verbose = True):
        self.N = N
        self.modulus = modulus
        self.verbose = verbose
        self.mbox = ModMath(modulus)
        self.elist = []
        
    # Insert equation into sorted list
    # This is purely to aid visualization
    def ordered_insert(self, e, ls):
        sofar = []
        rest = ls
        inserted = False
        while len(rest) > 0:
            if not inserted and e.is_greater(rest[0]):
                inserted = True
                sofar.append(e)
            else:
                sofar.append(rest[0])
                rest = rest[1:]
        if not inserted:
            sofar.append(e)
        return sofar

    def unordered_insert(self, e, ls):
        return ls + [e]

    def list_insert(self, e, ls):
        return self.ordered_insert(e, ls) if self.verbose else self.unordered_insert(e, ls)

    # Do ordered insertion of equation
    def add_equation(self, e):
        self.elist = self.list_insert(e, self.elist)
    
    # Is set of equations left after solution steps solvable
    def solvable(self):
        for e in self.rlist:
            if e.is_null():
                return False
        return True

    # Compute number of columns in remaining rows having nonzero coefficient
    # At position var
    def column_degree(self, var):
        d = 0
        for e in self.rlist:
            if var in e.nz:
                d += 1
        return d

    # Given remaining set of equations, select pivot element
    def select_pivot(self):
        bestI = None
        bestD = 0
        for i in range(self.N):
            d = self.column_degree(i)
            if d > 0 and (bestI is None or d < bestD):
                bestI = i
                bestD = d
        return bestI

    # Given pivot element, move best equation to top of rlist
    def choose_equation(self, pidx):
        bestJ = None
        bestD = 0
        for j in range(len(self.rlist)):
            e = self.rlist[j]
            if pidx in e.nz:
                d = len(e)
                if bestJ is None or d < bestD:
                    bestJ = j
                    bestD = d
                    # Greedy
                    #break
        topE = self.rlist[bestJ]
        mid = self.rlist[:bestJ]
        rest = self.rlist[bestJ+1:]
        self.rlist = [topE] + mid + rest
        return bestJ
                
    # Perform one step of LU decomposition
    # Return True if decomposition either completed or can't continue
    def solution_step(self):
        if len(self.rlist) == 0:
            return True
        pidx = self.select_pivot()
        if pidx is None:
            return True
        j = self.choose_equation(pidx)
        e = self.rlist[0]
        if self.verbose:
            print("Pivoting with element %d.  Using row %d" % (pidx, j))
        self.rlist = self.rlist[1:]
        e = e.normalize(pidx)
        self.slist = self.list_insert(e, self.slist)
        self.rlist = [ne.scale_sub(e, pidx) for ne in self.rlist]
        return False
        
            
    def solve(self):
        self.slist = []
        self.rlist = self.elist
        if self.verbose:
            print("Initial state")
            self.show_state()

        while True:
            if self.solution_step():
                break
            if self.verbose:
                self.show_state()
        if self.verbose:
            self.post_statistics()
        return self.solvable()

    def show(self):
        for e in self.elist:
            print("   " + str(e))
    
    def show_state(self):
        print("Processed:")
        for e in self.slist:
            print("   " + str(e))
        print("Remaining:")
        for e in self.rlist:
            print("   " + str(e))
        
    def pre_statistics(self):
        print("%d equations" % len(self.elist))

    def post_statistics(self):
        ok = self.solvable()
        msg = "System Solvable" if ok else "System Unsolvable"
        print(msg)
        print("%d modular operations" % self.mbox.opcount)
        
# Encoding of mutilated chessboard problem as linear equations
class Board:
    rows = 4
    cols = 4
    # List of squares to omit.  Each specified by (r,c)
    rsquares = []
    udvars = {}
    lrvars = {}
    esys = None

    # rcorners is list of squares to exclude.  Can use -1 for rows-1 or cols-1
    def __init__(self, rows, cols = None, rcorners = ""):
        self.rows = rows
        self.cols = rows if cols is None else cols
        self.rsquares = self.get_squares(rcorners)
        self.udvars = {}
        self.lrars = {}
        # Assign variable IDs
        var = 0
        for r in range(self.rows-1):
            for c in range(self.cols):
                self.udvars[(r,c)] = var
                var += 1
        for r in range(self.rows):
            for c in range(self.cols-1):
                self.lrvars[(r,c)] = var
                var += 1

    def get_squares(self, rcorners):
        rlist = []
        fields = rcorners.split(":")
        for field in fields:
            field = field.lower()
            if field == 'ul':
                rlist.append((0,0))
            elif field == 'll':
                rlist.append((self.rows-1,0))
            elif field == 'ur':
                rlist.append((0,self.cols-1))
            elif field == 'lr':
                rlist.append((self.rows-1,self.cols-1))
            else:
                raise Exception("Can't parse corner specifier '%s'" % field)
        return rlist


    def omit(self, r, c):
        for (xr,xc) in self.rsquares:
            if r == xr and c == xc:
                return True
        return False

    # Return list of variables surrounding given square
    def vars(self, r, c):
        vlist = []
        if r > 0:
            vlist.append(self.udvars[(r-1,c)])
        if r < self.rows-1:
            vlist.append(self.udvars[(r,c)])
        if c > 0:
            vlist.append(self.lrvars[(r,c-1)])
        if c < self.cols-1:
            vlist.append(self.lrvars[(r,c)])
        return vlist
                         
    def equations(self, modulus, verbose):
        N = self.rows * (self.cols-1) + (self.rows-1) * self.cols
        esys = EquationSystem(N, modulus, verbose)
        for r in range(self.rows):
            for c in range(self.cols):
                vars = self.vars(r,c)
                if self.omit(r,c):
                    for v in vars:
                        e = Equation(N, modulus, 0, esys.mbox)
                        e[v] = 1
                        esys.add_equation(e)
                else:
                    e = Equation(N, modulus, 1, esys.mbox)
                    for v in self.vars(r,c):
                        e[v] = 1
                    esys.add_equation(e)
        return esys

        

def solve(verbose, modulus, n, rcorners):
    b = Board(n, n, rcorners)
    esys = b.equations(modulus, verbose)
    solvable = esys.solve()
    if not verbose:
        esys.post_statistics()

def run(name, args):
    verbose = False
    modulus = 3
    n = 8
    rcorners = "ul:lr"
    optlist, args = getopt.getopt(args, "hvm:n:c:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-m':
            modulus = int(val)
        elif opt == '-n':
            n = int(val)
        elif opt == '-c':
            rcorners = val
    print("N = %d.  Modulus = %d.  Omitting corners %s" % (n, modulus, rcorners))
    solve(verbose, modulus, n, rcorners)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


                         
        

    


