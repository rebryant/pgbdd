#!/usr/bin/python

import sys
import getopt

# Generate and solve embedding of mutilated chessboard problem
def usage(name):
    print("Usage: %s [-h] [-v] [-v] [-m MOD] [-n N] [-s SQUARES] [-w hvb" % name) 
    print("  -h         Print this message")
    print("  -v         Run in verbose mode")
    print("  -u         Stop when cannot find unit pivot")
    print("  -m MOD     Specify modulus")
    print("  -n N       Specify size of board")
    print("  -s SQUARES Omit squares.")
    print("             String of form VH:VH:..:VH, where V in {u, m, d} and H in {l, m, r}")
    print("             Default is 'ul:dr'")
    print("  -w WRAP    Optionally wrap grid horizontally (h), vertically (v) or both (b)")


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
    ## Statistics
    # Number of modular operations
    opcount = 0
    # What values get used in places of interest
    used_values = {} # 

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
        self.used_values = {}

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

    def mark_used(self, x):
        self.used_values[x] = True
        
    def report_used(self):
        vlist = sorted(self.used_values.keys())
        fstring = ", ".join([str(v) for v in vlist])
        return "{" + fstring + "}"

    def unit_valued(self, x):
        return x in [0, 1, self.modulus-1]

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
        self.mbox.mark_used(v)
        if v == 0:
            if self.nz:
                del self.nz[i]
        else:
            self.nz[i] = v

    # Length defined to be the number of nonzeros
    def __len__(self):
        return len(self.nz)

    def format_dense(self):
        vec = [0 for i in range(self.N)]
        for i in self.nz.keys():
            vec[i] = self.nz[i]
        return str(vec + [self.cval])

    def format_sparse(self):
        slist = []
        for i in sorted(self.nz.keys()):
            v = self.nz[i]
            slist.append("%d:%d" % (i, v))
        slist.append("=%d" % self.cval)
        return '[' + " ".join(slist) + ']'

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
            nx = self.mbox.add(self[i], other.nz[i])
            self.mbox.mark_used(nx)
            self.nz_insert(nnz, i, nx)
        nc = self.mbox.add(self.cval, other.cval)
        return self.spawn(nnz, nc)

    # Subtract other vector from self
    def sub(self, other):
        nnz = { i : self.nz[i] for i in self.nz.keys() }
        for i in other.nz.keys():
            nx = self.mbox.sub(self[i], other.nz[i])
            self.mbox.mark_used(nx)
            self.nz_insert(nnz, i, nx)
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
                self.mbox.mark_used(nx)
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
    
    # Could other equation be added/or subtracted without going outside unit bounds
    def is_compatible(self, other):
        ok_neg = True
        ok_pos = True
        for i in self.nz.keys():
            if i not in other.nz:
                continue # No conflict
            mx = self.nz[i]
            ox = other.nz[i]
            if not self.mbox.unit_valued(mx) or not self.mbox.unit_valued(ox):
                # Lost cause
                return False
            if mx == ox:
                ok_neg = False
            if mx == self.mbox.sub(0, ox):
                ok_pos = False
            if not (ok_neg or ok_pos):
                break
        return ok_pos or ok_neg

    # Is this an equation with no solution?
    def is_null(self):
        return self.cval != 0 and len(self) == 0

    # Check that all elements in equation are unit-valued
    def unit_valued(self):
        for v in self.nz.values():
            if not self.mbox.unit_valued(v):
                return False
        return True

    def __str__(self):
        if self.N <= 40:
            return self.format_dense()
        else:
            return self.format_sparse()


# Maintain set of sparse equations, including index from each index i to those equations having nonzero value there
class EquationSet:
    # Unique ID assigned when registered
    next_id = 0
    # Mapping from id to equation
    equ_dict = {}
    # Mapping from index to list of equation IDs having nonzero entry at that index
    nz_map = {}

    def __init__(self, elist = []):
        self.next_id = 1
        self.equ_dict = {}
        self.nz_map = {}
        for e in elist:
            self.add_equation(e)

    def add_index(self, eid, idx):
        if idx in self.nz_map:
            self.nz_map[idx].append(eid)
        else:
            self.nz_map[idx] = [eid]

    def remove_index(self, eid, idx):
        nlist = [j for j in self.nz_map[idx] if j != eid]
        if len(nlist) == 0:
            del self.nz_map[idx]
        else:
            self.nz_map[idx] = nlist


    def add_equation(self, e):
        id = self.next_id
        self.next_id += 1
        self.equ_dict[id] = e
        for idx in e.nz:
            self.add_index(id, idx)

    def remove_equation(self, eid):
        e = self[eid]
        for idx in e.nz:
            self.remove_index(eid, idx)
        del self.equ_dict[eid]

    def lookup(self, idx):
        if idx in self.nz_map:
            return self.nz_map[idx]
        else:
            return []

    def __getitem__(self, id):
        return self.equ_dict[id]
        
    def __len__(self):
        return len(self.equ_dict)

    def current_eids(self):
        return self.equ_dict.keys()

    def current_indices(self):
        return self.nz_map.keys()

    def clone(self):
        # Make clean copy of all data structures
        nes = EquationSet()
        nes.next_id = self.next_id
        nes.equ_dict = { id : self.equ_dict[id] for id in self.equ_dict.keys() }
        nes.nz_map = { idx : list(self.nz_map[idx]) for idx in self.nz_map.keys() }
        return nes

    def show(self):
        eid_list = sorted(self.current_eids())
        for eid in eid_list:
            print("   #%d:%s" % (eid, str(self[eid])))


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
    eset = {}

    ## Solver state
    # Eliminated equations
    sset = {}
    # Remaining equations
    rset = {}

    ## Accumulating data
    # List of pivot values
    pivot_list = []
    # Mapping from variable ID to True
    var_used = {}
    # Total number of equations
    equation_count = 0
    # Total number of elimination steps
    step_count = 0
    # Sum of pivot degrees
    pivot_degree_sum = 0
    # Max of pivot degrees
    pivot_degree_max = 0
    # Total number of nonzero terms in all equations
    term_count = 0
    # Max number of nonzero terms in equations
    term_max = 0
    # Total number of vector operations
    combine_count = 0


    def __init__(self, N, modulus, verbose = True):
        self.N = N
        self.modulus = modulus
        self.verbose = verbose
        self.mbox = ModMath(modulus)
        self.eset = EquationSet()
        self.sset = EquationSet()
        self.rset = EquationSet()
        self.pivot_list = []
        self.var_used = {}
        self.equation_count = 0
        self.step_count = 0
        self.pivot_degree_sum = 0
        self.pivot_degree_max = 0
        self.term_count = 0        
        self.term_max = 0        
        self.combine_count = 0
        

    # Add new equation to main set
    def add_equation(self, e):
        self.eset.add_equation(e)
        self.equation_count += 1
        tcount = len(e)
        self.term_max = max(self.term_max, tcount)
        for i in e.nz:
            self.var_used[i] = True

    # Is set of equations left after solution steps solvable
    def solvable(self):
        for eid in self.rset.current_eids():
            e = self.rset[eid]
            if e.is_null():
                return False
        return True

    # Compute number of columns in remaining rows having nonzero coefficient
    # At position var
    def column_degree(self, idx, unit_only):
        eid_list = self.rset.lookup(idx)
        ok = True
        if unit_only:
            for eid in eid_list:
                e = self.rset[eid]
                v = e[idx]
                if not self.mbox.unit_valued(v):
                    ok = False
                    break
        return len(eid_list) if ok else 0

    # Given remaining set of equations, select pivot element
    def select_pivot_old(self, unit_only):
        best_idx = None
        best_d = 0
        for i in self.rset.current_indices():
            d = self.column_degree(i, unit_only)
            if d > 0 and (best_idx is None or d < best_d):
                best_idx = i
                best_d = d
        if best_idx is not None:
            self.pivot_degree_sum += best_d
            self.pivot_degree_max = max(self.pivot_degree_max, best_d)
        return best_idx

    # Given pivot element, return eid of best one for elimination
    def choose_equation(self, pidx):
        best_eid = None
        best_d = 0
        eid_list = self.rset.lookup(pidx)
        for eid in eid_list:
            e = self.rset[eid]
            d = len(e)
            if best_eid is None or d < best_d:
                best_eid = eid
                best_d = d
        return best_eid
                
    # Given possible pivot index
    # Return (degree, eid) giving number of entries in column
    # and equation id
    # With unit_only set, will return (None, None) cannot find equation
    # that maintains UPB property
    def evaluate_pivot(self, pidx, unit_only):
        eid_list = self.rset.lookup(pidx)
        best_eid = None
        best_rd = 0
        if unit_only:
            for eid in eid_list:
                e = self.rset[eid]
                rd = len(e)
                viable = True
                for oid in eid_list:
                    if eid == oid:
                        continue
                    oe = self.rset[oid]
                    if not e.is_compatible(oe):
                        viable = False
                        break
                if viable and best_eid is None or rd < best_rd:
                    best_eid = eid
                    best_rd = rd
        else:
            for eid in eid_list:
                e = self.rset[eid]
                rd = len(e)
                if best_eid is None or rd < best_rd:
                    best_eid = eid
                    best_rd = rd
        degree = 0 if best_eid is None else len(eid_list)
        return (degree, best_eid)

    # Given remaining set of equations, select pivot element and equation id
    def select_pivot(self, unit_only):
        best_idx = None
        best_d = 0
        best_eid = None
        for idx in self.rset.current_indices():
            (d, eid) = self.evaluate_pivot(idx, unit_only)
            if eid is not None and (best_eid is None or d < best_d):
                best_idx = idx
                best_d = d
                best_eid = eid
        if best_idx is not None:
            self.pivot_degree_sum += best_d
            self.pivot_degree_max = max(self.pivot_degree_max, best_d)
        return (best_idx, best_eid)


    # Perform one step of LU decomposition
    # Possible return values:
    # "solved", "unit_stopped", "unsolvable", "normal"
    def solution_step(self, unit_only):
        if len(self.rset) == 0:
            return "solved"
        self.step_count += 1
        (pidx, eid) = self.select_pivot(unit_only)
        if pidx is None:
            if unit_only:
                (pidx, eid) = self.select_pivot(False)
                if pidx is not None:
                    return "unit_stopped"
            return "solved" if self.solvable() else "unsolvable"

        e = self.rset[eid]
        self.rset.remove_equation(eid)
        self.sset.add_equation(e)
        pval = e[pidx]
        self.pivot_list.append(pval)
        if self.verbose:
            print("Pivoting with value %d (element %d).  Using equation #%d" % (pval, pidx, eid))
        ne = e.normalize(pidx)

        other_eids =  self.rset.lookup(pidx)
        for oeid in other_eids:
            oe = self.rset[oeid]
            self.rset.remove_equation(oeid)
            re = oe.scale_sub(ne, pidx)
            self.rset.add_equation(re)
            self.combine_count += 1
        return "normal"
            
    def solve(self, unit_only):
        self.sset = EquationSet()
        self.rset = self.eset.clone()
        if self.verbose:
            print("  Initial state")
            self.show_state()
        status = "normal"
        while True:
            status = self.solution_step(unit_only)
            # "solved", "unit_stopped", "unsolvable", "normal"
            if status != "normal":
                break
            if self.verbose:
                self.show_state()
        if self.verbose:
            print("  Solution status:%s" % status)
            self.post_statistics(status, False)
        return status

    def show(self):
        self.eset.show()
    
    def show_state(self):
        print("  Processed:")
        self.sset.show()
        print("  Remaining:")
        self.rset.show()

    def show_remaining_state(self):
        self.rset.show()
            
    def pre_statistics(self):
        ecount = self.equation_count
        vcount = len(self.var_used)
        tavg = float(self.term_count)/ecount
        tmax = self.term_max
        print("  Problem: %d equations, %d variables.  %.2f avg vars/equation (max=%d)" % (ecount, vcount, tavg, tmax))

    def post_statistics(self, status, maybe_solvable):
        # status: "solved", "unit_stopped", "unsolvable", "normal"
        expected = "solvable" if maybe_solvable else "unsolvable"
        print("  Solution status: %s (expected = %s)" % (status, expected))
        if status == "unit_stopped":
            print("Stopped with remaining equations:")
            self.show_remaining_state()
        sscount = self.step_count
        pavg = float(self.pivot_degree_sum)/sscount
        pmax = self.pivot_degree_max
        print("  Solving: %d steps.  %.2f avg pivot degree (max=%d)" % (sscount, pavg, pmax))
        pslist = []
        for s in range(1, len(self.pivot_list)+1):
            p = self.pivot_list[s-1]
            if not self.mbox.unit_valued(p):
                pslist.append("%d:%d" % (s,p))
        if len(pslist) > 0:
            print("  Non-unit pivots: [%s]" % (' '.join(pslist)))
        ecount = self.equation_count
        ccount = self.combine_count
        tavg = float(self.term_count)/ecount
        tmax = self.term_max
        print("    %d total equations.  %.2f avg vars/equation (max=%d).  %d vector operations" % (ecount, tavg, tmax, ccount))
        sscount = self.step_count
        pavg = float(self.pivot_degree_sum)/sscount
        print("    %d modular operations.  Used values = %s" % (self.mbox.opcount, self.mbox.report_used()))

        
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

        print("     Wrapping: Horizontal %s.  Vertical %s" % (self.wrap_horizontal, self.wrap_vertical))

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
    def get_squares(self, rcorners):
        rlist = []
        fields = rcorners.split(":")
        for field in fields:
            if field == "":
                continue
            field = field.lower()
            r = 0
            c = 0
            ok = True
            if len(field) != 2:
                ok = False
            else:
                lmr = field[1]
                if lmr == 'l':
                    c = 0
                elif lmr == 'm':
                    c = self.cols/2
                elif lmr == 'r':
                    c = self.cols-1
                else:
                    ok = False

                umd = field[0]
                if umd == 'u':
                    r = 0
                elif umd == 'm':
                    r = self.rows/2
                elif umd == 'd':
                    r = self.rows-1
                else:
                    ok = False
            if ok:
                rlist.append((r,c))
            else:
                raise Exception("Can't parse square specifier '%s'" % field)
        return rlist


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
            rdown = r-1 if r > 0 else self.rows-1
            vlist.append(self.udvars[(rdown, c)])
            rup   = r if r < self.rows else 0
            vlist.append(self.udvars[(rup, c)])
        else:
            if r > 0:
                vlist.append(self.udvars[(r-1,c)])
            if r < self.rows-1:
                vlist.append(self.udvars[(r,c)])
        if self.wrap_horizontal:
            cleft = c-1 if c > 0 else self.cols-1
            vlist.append(self.lrvars[(r, cleft)])
            cright  = c+1 if c < self.cols-1 else 0
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
                    for v in vars:
                        e[v] = 1
                    esys.add_equation(e)
        return esys

        

def solve(verbose, modulus, n, ssquares, wrap_horizontal, wrap_vertical, unit_only):
    b = Board(n, n, ssquares, wrap_horizontal, wrap_vertical)
    esys = b.equations(modulus, verbose)
    if not verbose:
        esys.pre_statistics()
    status = esys.solve(unit_only)
    if not verbose:
        esys.post_statistics(status, b.maybe_solvable())

def run(name, args):
    verbose = False
    unit_only = False
    modulus = 3
    n = 8
    ssquares = "ul:dr"
    wrap_horizontal = False
    wrap_vertical = False
    optlist, args = getopt.getopt(args, "hvum:n:s:w:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-u':
            unit_only = True
        elif opt == '-m':
            modulus = int(val)
        elif opt == '-n':
            n = int(val)
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
            if not ok:
                print("Invalid wrapping parameter '%s'.  Must be h, v, or b" % val)
                return
    ocorners = ssquares.split(":")
    scorners = '[' + ", ".join(ocorners) + ']'
    print("N = %d.  Modulus = %d.  Omitting squares %s" % (n, modulus, scorners))
    solve(verbose, modulus, n, ssquares, wrap_horizontal, wrap_vertical, unit_only)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


                         
        

    


