# Support for solving system of linear equations over Z_p for prime p

import sys
import getopt
import random
import queue

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


class PivotException(MathException):
    def __init__(self, index):
        self.form = "Pivot=0!"
        self.msg = "index=%d" % index


# Supporting modular arithmetic
# For odd modulus m, use bias k=(m-1)/2
# I.e., Numbers between -k and k to represent range of values
# For even number, will be -k to k+1
class ModMath:

    modulus = 3 # Must be prime
    min_value = -1 # -[(modulus-1)/2] for odd, -[modulus/2-1] for even
    max_value = 1
    reciprocals = {} # Dictionary mapping x to 1/x
    ## Statistics
    # Number of modular operations
    opcount = 0
    # What values get used in places of interest
    used_values = {} # 

    def __init__(self, modulus = 3):
        self.reciprocals = {}
        self.modulus = modulus
        self.min_value = -((self.modulus-1)//2)
        self.max_value = self.min_value + self.modulus - 1
        self.opcount = 0
        for x in range(self.min_value,self.max_value+1):
            if x == 0:
                continue
            found = False
            for y in range(self.min_value,self.max_value+1):
                if self.mul(x, y) == 1:
                    self.reciprocals[x] = y
                    found = True
                    break
            if not found:
                raise ReciprocalException(x)
        # Reset count
        self.opcount = 0
        self.used_values = {}

    # Convert to canonical value
    def mod(self, x):
        mx = x % self.modulus
        if mx > self.max_value:
            mx -= self.modulus
        return mx

    def add(self, x, y):
        self.opcount += 1 
        return self.mod(x+y)

    def mul(self, x, y):
        self.opcount += 1 
        return self.mod(x*y)

    def sub(self, x, y):
        self.opcount += 1 
        return self.mod(x-y)
        
    def neg(self, x):
        return self.mod(-x)

    def recip(self, x):
        if x == 0:
            raise ZeroException(1)
        return self.reciprocals[x]

    def div(self, x, y):
        if y == 0:
            raise ZeroException(y)
        return self.mul(x, self.recip(y))

    def abs(self, x):
        return abs(x)

    def mark_used(self, x):
        self.used_values[x] = True
        
    def report_used(self):
        vlist = sorted(self.used_values.keys())
        fstring = ", ".join([str(v) for v in vlist])
        return "{" + fstring + "}"

# Equation of form SUM (a_i * x_i)  =  C
# Arithmetic performed over Z_p for prime p
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
        self.N = N     # Max Variable ID +1
        self.modulus = modulus
        if mbox is None:
            self.mbox = ModMath(modulus)
        elif mbox.modulus != modulus:
            raise Exception("Mismatched moduli")
        else:
            self.mbox = mbox
        self.cval = self.mbox.mod(cval)
        self.nz = {}

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

    def indices(self):
        return sorted(self.nz.keys())

    # Length defined to be the number of nonzeros
    def __len__(self):
        return len(self.nz)

    def format_dense(self):
        vec = [0 for i in range(self.N)]
        for i in self.indices():
            vec[i] = self[i]
        return str(vec + [self.cval])

    def format_sparse(self):
        slist = []
        for i in self.indices():
            v = self[i]
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
        nnz = { i : self.mbox.div(self[i], pval) for i in self.indices() }
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
        nnz = { i : self[i] for i in self.indices() }
        for i in other.indices():
            nx = self.mbox.add(self[i], other[i])
            self.mbox.mark_used(nx)
            self.nz_insert(nnz, i, nx)
        nc = self.mbox.add(self.cval, other.cval)
        return self.spawn(nnz, nc)

    # Subtract other vector from self
    def sub(self, other):
        nnz = { i : self[i] for i in self.indices() }
        for i in other.indices():
            nx = self.mbox.sub(self[i], other[i])
            self.mbox.mark_used(nx)
            self.nz_insert(nnz, i, nx)
        nc = self.mbox.sub(self.cval, other.cval)
        return self.spawn(nnz, nc)


    # Perform scaling subtraction
    # Must scale other vector by value at pivot position before subtracting
    def scale_sub(self, other, pidx):
        nnz = { i : self[i] for i in self.indices() }
        sval = 0
        sval = self[pidx]
        if sval != 0:
            for i in other.indices():
                x = self[i]
                dx = self.mbox.mul(sval, other[i])
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
    
    # Does this equation have no solution with modular arithmetic
    def is_infeasible(self):
        # All zero coefficients and non-zero constant
        return self.cval != 0 and len(self) == 0

    # Build dictionary mapping index to maximum number of BDD nodes at that position
    def bdd_widths(self):
        m = self.modulus
        return { i : m for i in self.indices() }

    # Compute max size of BDD representation
    def bdd_size(self):
        widths = self.bdd_widths()
        return sum(widths.values())


    def __str__(self):
        if self.N <= 40:
            return self.format_dense()
        else:
            return self.format_sparse()


# Maintain set of sparse equations, including index from each index i to those equations having nonzero value there
class EquationSet:
    # Unique ID assigned when registered
    next_id = 1
    # Mapping from id to equation
    equ_dict = {}
    # Mapping from index to list of equation IDs having nonzero entry at that index
    nz_map = {}
    # Total number of nonzero terms added
    term_count = 0
    # Largest equation added
    term_max = 0
    # Total number of BDD nodes generated
    bdd_node_count = 0
    # Largest BDD
    bdd_node_max = 0

    def __init__(self, elist = []):
        self.next_id = 1
        self.equ_dict = {}
        self.nz_map = {}
        self.term_count = 0
        self.term_max = 0
        self.bdd_node_count = 0
        self.bdd_node_max = 0
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

    def analyze_equation(self, e):
        count = len(e)
        self.term_count += count
        self.term_max = max(self.term_max, count)
        bsize = e.bdd_size()
        self.bdd_node_count += bsize
        self.bdd_node_max = max(bsize, self.bdd_node_max)

    def add_equation(self, e):
        eid = self.next_id
        self.next_id += 1
        self.equ_dict[eid] = e
        for idx in e.nz:
            self.add_index(eid, idx)
        self.analyze_equation(e)
        return eid

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
        nes.term_count = self.term_count
        nes.term_max = self.term_max
        nes.bdd_node_count = self.bdd_node_count
        nes.bdd_node_max = self.bdd_node_max
        return nes

    def show(self):
        eid_list = sorted(self.current_eids())
        for eid in eid_list:
            print("   #%d:%s" % (eid, str(self[eid])))

    # How many total equations have been generated
    def equation_count(self):
        return self.next_id - 1

    def bdd_avg(self):
        return float(self.bdd_node_count) / self.equation_count()


# System of equations.
# Support LU decomposition of Gaussian elimination to see if system has any solutions
class EquationSystem:
    # Variable Count
    N = 10
    modulus = 3
    verbose = False
    randomize = False
    # Class to support math operations
    mbox = None
    # Set of original equations
    eset = {}

    # Optionally: Reduce some of the equations via summations before solving
    # List of lists, each giving equations IDs to sum
    presums = []

    ## Solver state
    # Eliminated equations
    sset = {}
    # Remaining equations
    rset = {}

    ## Accumulating data
    # Mapping from variable ID to True
    var_used = {}
    # Total number of elimination steps
    step_count = 0
    # Sum of pivot degrees
    pivot_degree_sum = 0
    # Max of pivot degrees
    pivot_degree_max = 0
    # Total number of vector operations
    combine_count = 0
    # Estimated number of BDD ops for verifier
    bdd_ops = 0

    def __init__(self, N, modulus, verbose = True):
        self.N = N
        self.modulus = modulus
        self.verbose = verbose
        self.randomize = False
        self.mbox = ModMath(modulus)
        self.eset = EquationSet()
        self.sset = EquationSet()
        self.rset = EquationSet()
        self.var_used = {}
        self.step_count = 0
        self.pivot_degree_sum = 0
        self.pivot_degree_max = 0
        self.combine_count = 0
        self.bdd_ops = 0
        

    # Add new equation to main set
    def add_equation(self, e):
        eid = self.eset.add_equation(e)
        for i in e.nz:
            self.var_used[i] = True
        return eid

    # Add presum list
    def add_presum(self, elist):
        self.presums.append(elist)

    # Reduce set of equationss (given by their eid's) by summing
    def sum_reduce(self, elist):
        if len(elist) == 0:
            return
        # This is a hack to enable randomized removal of equal weighted items from priority queue
        # and to make sure that priority queue has totally ordered keys
        # Have enough entries in the list to cover initial equations and partial sums
        olist = list(range(2*len(elist)))
        if self.randomize:
            random.shuffle(olist)
        # Put elements into priority queue according to nnz's
        pq = queue.PriorityQueue()
        for idx in range(len(elist)):
            oid = olist[idx]
            eid = elist[idx]
            e = self.rset[eid]
            self.rset.remove_equation(eid)                
            pq.put((len(e), oid, e))
        # Now start combining them
        idx = len(elist)
        while pq.qsize() > 1:
            (w1, o1, e1) = pq.get()
            (w2, o2, e2) = pq.get()
            ne = e1.add(e2)
            self.bdd_ops += self.bdd_estimator([e1, e2, ne])
            oid = olist[idx]
            if pq.qsize() > 0:
                # Gather statistics on this equation, even though won't be added to rset
                self.rset.analyze_equation(ne)
            pq.put((len(ne), oid, ne))
            idx += 1
        # Reduced queue to single element
        (w, o, e) = pq.get()
        self.rset.add_equation(e)

    # Reduce set of equations by summing
    def presum(self):
        icount = len(self.rset)
        for elist in self.presums:
            self.sum_reduce(elist)
        ncount = len(self.rset)
        if ncount < icount:
            print("Presumming reduced equations from %d to %d" % (icount, ncount))

    # Given possible pivot index
    # find best equation to use as pivot equation and
    # give score for its selection
    # If there are no nonzeros with this index, return None for the equation ID
    def evaluate_pivot(self, pidx):
        eid_list = self.rset.lookup(pidx)
        best_eid = None
        # Lowest degree row
        best_rd = 0
        # Make sure that any ties are broken arbitrarily
        # rather than as some artifact of the input file
        if self.randomize:
            random.shuffle(eid_list)

        for eid in eid_list:
            e = self.rset[eid]
            rd = len(e)
            if best_eid is None or rd < best_rd:
                best_eid = eid
                best_rd = rd

        # Score based on worst-case fill generated
        # Also favors unit and singleton equations
        score = (best_rd-1) * (len(eid_list)-1)
        return (best_eid, score)

    # Given remaining set of equations, select pivot element and equation id
    def select_pivot(self):
        best_pidx = None
        best_score = 0
        best_eid = None
        id_list = self.rset.current_indices()
        # Make sure that any ties are broken arbitrarily
        # rather than as some artifact of the input file
        if self.randomize:
            random.shuffle(id_list)
        for pidx in id_list:
            (eid, score) = self.evaluate_pivot(pidx)
            if eid is not None and (best_eid is None or score < best_score):
                best_pidx = pidx
                best_score = score
                best_eid = eid
        if best_eid is not None:
            pd = len(self.rset[best_eid])
            self.pivot_degree_sum += pd
            self.pivot_degree_max = max(self.pivot_degree_max, pd)
        return (best_pidx, best_eid)


    # Estimate the number of BDD operations required for a validation step with BDDs
    def bdd_estimator(self, elist):
        # Build up dictionary giving product of BDD widths at each level
        wdict = elist[0].bdd_widths()
        for e in elist[1:]:
            ewdict = e.bdd_widths()
            for i in e.indices():
                wdict[i] = wdict[i] * ewdict[i] if i in wdict else ewdict[i]
        return sum(wdict.values())

    # Perform one step of LU decomposition
    # Possible return values:
    # "solved", "unsolvable", "normal"
    def solution_step(self):
        if len(self.rset) == 0:
            return "solved"
        self.step_count += 1
        (pidx, eid) = self.select_pivot()
        if pidx is None:
            return "solved"

        e = self.rset[eid]
        self.rset.remove_equation(eid)
        self.sset.add_equation(e)
        pval = e[pidx]
        if self.verbose:
            print("Pivoting with value %d (element %d).  Using equation #%d" % (pval, pidx, eid))
        ne = e.normalize(pidx)
        self.bdd_ops += self.bdd_estimator([ne])

        other_eids =  self.rset.lookup(pidx)
        for oeid in other_eids:
            oe = self.rset[oeid]
            self.rset.remove_equation(oeid)
            re = oe.scale_sub(ne, pidx)
            if re.is_infeasible():
                return "unsolvable"
            self.rset.add_equation(re)
            self.combine_count += 1
            # Estimate number of BDD operations for verification
            self.bdd_ops += self.bdd_estimator([ne, oe, re])
        return "normal"
            
    def solve(self):
        self.sset = EquationSet()
        self.rset = self.eset.clone()
        if self.verbose:
            print("  Initial state")
            self.show_state()
        # Scan equations to see if any are infeasible
        for eid in self.rset.current_eids():
            e = self.rset[eid]
            if e.is_infeasible():
                return "unsolvable"
        status = "normal"

        # Perform any presumming
        self.presum()

        while True:
            status = self.solution_step()
            # "solved", "unsolvable", "normal"
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
        ecount = self.eset.equation_count()
        vcount = self.N
        acount = len(self.var_used)
        tc = self.eset.term_count
        tmax = self.eset.term_max
        tavg = float(tc)/ecount
        print("  Problem: %d equations, %d variables, %d nonzero coefficients.  %d total nonzeros (%.2f avg, %d max)" % (ecount, vcount, acount, tc, tavg, tmax))

    def post_statistics(self, status, maybe_solvable):
        # status: "solved", "unsolvable", "normal"
        expected = "solvable" if maybe_solvable else "unsolvable"
        print("  Solution status: %s (expected = %s)" % (status, expected))
        sscount = self.step_count
        pavg = float(self.pivot_degree_sum)/sscount
        pmax = self.pivot_degree_max
        print("  Solving: %d steps.  %.2f avg pivot degree (max=%d)" % (sscount, pavg, pmax))
        ecount = self.rset.equation_count()
        ccount = self.combine_count
        tc = self.rset.term_count
        tmax = self.rset.term_max
        tavg = float(tc)/ecount
        print("    %d total equations.  %d total nonzeros (%.2f avg, %d max).  %d vector operations" % (ecount, tc, tavg, tmax, ccount))
        bcount = self.bdd_ops
        ncount = self.rset.bdd_node_count
        navg = self.rset.bdd_avg()
        nmax = self.rset.bdd_node_max
        print("    %d estimated BDD operations.  %d total BDD nodes (%.2f avg, %d max)" % (bcount, ncount, navg, nmax))
        print("    %d modular operations.  Used values = %s" % (self.mbox.opcount, self.mbox.report_used()))

