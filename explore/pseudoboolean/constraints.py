# Support for manipulating constraints of the form
# SUM (a_i * x_i) >= c
# where each a_i is positive or negative integer
# x_i is Boolean

import sys
import getopt
import random
import queue

class ConstraintException(Exception):
    form = "Constraint Error"
    msg = ""

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

# Constraint of form SUM (a_i * x_i)  >=  c
# Only represent nonzero coefficients

class Constraint:

    # Variable Count
    N = 10  # Length when format as vector
    # 
    # Mapping for variable Id to coefficient for nonzero coefficient
    nz = {}
    cval = 0

    def __init__(self, N, cval):
        self.N = N     # Max Variable ID +1
        self.cval = cval
        self.nz = {}

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
        slist.append(">=%d" % self.cval)
        return '[' + " ".join(slist) + ']'

    # Generate new constraint from new set of nonzeros
    def spawn(self, nnz, cval):
        con = Constraint(self.N, cval)
        con.nz = nnz
        return con
        
    # Helper function for inserting new element in dictionary
    def nz_insert(self, nz, i, v):
        if v == 0 and i in nz:
            del nz[i]
        else:
            nz[i] = v

    # Add other constraint to self
    def add(self, other):
        nnz = { i : self[i] for i in self.indices() }
        for i in other.indices():
            nx = self[i] + other[i]
            self.nz_insert(nnz, i, nx)
        nc = self.cval + other.cval
        return self.spawn(nnz, nc)

    # Generate at-least-one constraint
    def alo(self, vlist):
        nnz = { i : 1 for i in vlist }
        cval = 1
        return self.spawn(nnz, cval)

    # Generate at-most-one constraint
    def amo(self, vlist):
        nnz = { i : -1 for i in vlist }
        cval = -1
        return self.spawn(nnz, cval)

    # Generate at-most-zero constraint
    # (i.e., all must be false)
    def amz(self, vlist):
        nnz = { i : -1 for i in vlist }
        cval = 0
        return self.spawn(nnz, cval)

    # Lexicographic ordering of constraints
    def is_greater(self, other):
        for i in range(self.N):
            if self[i] > other[i]:
                return True
            if self[i] < other[i]:
                return False
        return self.cval > other.cval
    
    # Does this constraint have no solution
    def is_infeasible(self):
        maxsum = 0
        for v in self.nz.values():
            if v > 0:
                maxsum += v
        return maxsum < self.cval

    # Build dictionary mapping index to maximum number of BDD nodes at that position
    def bdd_widths(self):
        max_to = { }
        min_to = { }
        pos_sum = 0
        neg_sum = 0

        for i in self.indices():
            if self[i] > 0:
                pos_sum += self[i]
            else:
                neg_sum += self[i]
            max_to[i] = pos_sum
            min_to[i] = neg_sum

        widths = { }
        for i in self.indices():
            up = min(max_to[i], min_to[i] + self.cval - neg_sum)
            down = max(min_to[i], max_to[i] + self.cval - pos_sum)
            widths[i] = max(1, up-down+1)

        return widths

    # Compute max size of BDD representation
    def bdd_size(self):
        widths = self.bdd_widths()
        return sum(widths.values())

    def __str__(self):
        if self.N <= 40:
            return self.format_dense()
        else:
            return self.format_sparse()


# Maintain set of sparse constraints, including index from each index i to those constraints having nonzero value there
class ConstraintSet:
    # Unique ID assigned when registered
    next_id = 1
    # Mapping from id to constraint
    con_dict = {}
    # Mapping from index to list of constraint IDs having nonzero entry at that index
    nz_map = {}
    # Total number of nonzero terms added
    term_count = 0
    # Largest constraint added
    term_max = 0
    # Total number of BDD nodes generated
    bdd_node_count = 0
    # Largest BDD
    bdd_node_max = 0

    def __init__(self, clist = []):
        self.next_id = 1
        self.con_dict = {}
        self.nz_map = {}
        self.term_count = 0
        self.term_max = 0
        self.bdd_node_count = 0
        self.bdd_node_max = 0
        for con in clist:
            self.add_constraint(con)

    def add_index(self, cid, idx):
        if idx in self.nz_map:
            self.nz_map[idx].append(cid)
        else:
            self.nz_map[idx] = [cid]

    def remove_index(self, cid, idx):
        nlist = [j for j in self.nz_map[idx] if j != cid]
        if len(nlist) == 0:
            del self.nz_map[idx]
        else:
            self.nz_map[idx] = nlist

    def analyze_constraint(self, con):
        count = len(con)
        self.term_count += count
        self.term_max = max(self.term_max, count)
        bsize = con.bdd_size()
        self.bdd_node_count += bsize
        self.bdd_node_max = max(bsize, self.bdd_node_max)

    def add_constraint(self, con):
        cid = self.next_id
        self.next_id += 1
        self.con_dict[cid] = con
        for idx in con.nz:
            self.add_index(cid, idx)
        self.analyze_constraint(con)
        return cid

    def remove_constraint(self, cid):
        con = self[cid]
        for idx in con.nz:
            self.remove_index(cid, idx)
        del self.con_dict[cid]

    def lookup(self, idx):
        if idx in self.nz_map:
            return self.nz_map[idx]
        else:
            return []

    def __getitem__(self, id):
        return self.con_dict[id]
        
    def __len__(self):
        return len(self.con_dict)

    def current_cids(self):
        return self.con_dict.keys()

    def current_indices(self):
        return self.nz_map.keys()

    def clone(self):
        # Make clean copy of all data structures
        ncs = ConstraintSet()
        ncs.next_id = self.next_id
        ncs.con_dict = { id : self.con_dict[id] for id in self.con_dict.keys() }
        ncs.nz_map = { idx : list(self.nz_map[idx]) for idx in self.nz_map.keys() }
        ncs.term_count = self.term_count
        ncs.term_max = self.term_max
        ncs.bdd_node_count = self.bdd_node_count
        ncs.bdd_node_max = self.bdd_node_max
        return ncs

    def show(self):
        cid_list = sorted(self.current_cids())
        for cid in cid_list:
            print("   #%d:%s" % (cid, str(self[cid])))

    # How many total constraints have been generated
    def constraint_count(self):
        return self.next_id - 1

    def bdd_avg(self):
        return float(self.bdd_node_count) / self.constraint_count()


# System of constraints.
# Support adding constraints to see if can detect conflict
class ConstraintSystem:
    # Variable Count
    N = 10
    verbose = False
    randomize = False
    # Set of original constraints
    conset = {}

    # Optionally: Reduce some of the constraints via summations before solving
    # List of lists, each giving constraints IDs to sum
    presums = []

    ## Solver state
    # Eliminated constraints
    sset = {}
    # Remaining constraints
    rset = {}

    ## Accumulating data
    # Mapping from variable ID to True
    var_used = {}
    # Estimated number of BDD ops for verifier
    bdd_ops = 0


    def __init__(self, N, verbose = True):
        self.N = N
        self.verbose = verbose
        self.randomize = False
        self.conset = ConstraintSet()
        self.sset = ConstraintSet()
        self.rset = ConstraintSet()
        self.var_used = {}
        self.bdd_ops = 0

    # Add new constraint to main set
    def add_constraint(self, con):
        cid = self.conset.add_constraint(con)
        for i in con.nz:
            self.var_used[i] = True
        return cid

    # Add presum list
    def add_presum(self, clist):
        self.presums.append(clist)

    # Reduce set of constraints (given by their cid's) by summing
    def sum_reduce(self, clist):
        if len(clist) == 0: 
            return
        # This is a hack to enable randomized removal of equal weighted items from priority queue
        # and to make sure that priority queue has totally ordered keys
        # Have enough entries in the list to cover initial constraints and partial sums
        olist = list(range(2*len(clist)))
        if self.randomize:
            random.shuffle(olist)
        # Put elements into priority queue according to nnz's
        pq = queue.PriorityQueue()
        for idx in range(len(clist)):
            oid = olist[idx]
            cid = clist[idx]
            con = self.rset[cid]
            self.rset.remove_constraint(cid)                
            pq.put((len(con), oid, con))
        # Now start combining them
        idx = len(clist)
        while pq.qsize() > 1:
            (w1, o1, con1) = pq.get()
            (w2, o2, con2) = pq.get()
            ncon = con1.add(con2)
            self.bdd_ops += self.bdd_estimator([con1, con2, ncon])
            oid = olist[idx]
            if pq.qsize() > 0:
                # Gather statistics on this constraint, even though won't be added to rset
                self.rset.analyze_constraint(ncon)
            pq.put((len(ncon), oid, ncon))
            idx += 1
        # Reduced queue to single element
        (w, o, con) = pq.get()
        self.rset.add_constraint(con)
        

    # Reduce set of constraints by summing
    def presum(self):
        icount = len(self.rset)
        for clist in self.presums:
            self.sum_reduce(clist)
        ncount = len(self.rset)
        if ncount < icount:
            print("Presumming reduced constraints from %d to %d" % (icount, ncount))

# Estimate the number of BDD operations required for a validation step with BDDs
    def bdd_estimator(self, clist):
        # Build up dictionary giving product of BDD widths at each level
        wdict = clist[0].bdd_widths()
        for con in clist[1:]:
            cwdict = con.bdd_widths()
            for i in con.indices():
                wdict[i] = wdict[i] * cwdict[i] if i in wdict else cwdict[i]
        return sum(wdict.values())


    def solve(self):
        self.sset = ConstraintSet()
        self.rset = self.conset.clone()
        if self.verbose:
            print("  Initial state")
            self.show_state()
        # Scan constraints to see if any are infeasible
        for cid in self.rset.current_cids():
            con = self.rset[cid]
            if con.is_infeasible():
                return "unsolvable"
        status = "normal"

        # Perform any presumming
        self.presum()

        self.sum_reduce(self.rset.current_cids())

        last_cid = self.rset.current_cids()[0]
        last_con = self.rset[last_cid]

        status =  "unsolvable" if  last_con.is_infeasible() else "solvable"

        if self.verbose:
            print("  Solution status:%s" % status)
            self.post_statistics(status, False)
        return status


    def show(self):
        self.conset.show()
    
    def show_state(self):
        print("  Processed:")
        self.sset.show()
        print("  Remaining:")
        self.rset.show()

    def show_remaining_state(self):
        self.rset.show()
            
    def pre_statistics(self):
        ccount = self.conset.constraint_count()
        vcount = self.N
        acount = len(self.var_used)
        tc = self.conset.term_count
        tmax = self.conset.term_max
        tavg = float(tc)/ccount
        print("  Problem: %d constraints, %d variables, %d nonzero coefficients.  %d total nonzeros (%.2f avg, %d max)" % (ccount, vcount, acount, tc, tavg, tmax))

    def post_statistics(self, status, maybe_solvable):
        # status: "solved", "unsolvable", "normal"
        expected = "solvable" if maybe_solvable else "unsolvable"
        print("  Solution status: %s (expected = %s)" % (status, expected))
        ccount = self.rset.constraint_count()
        tc = self.rset.term_count
        tmax = self.rset.term_max
        tavg = float(tc)/ccount
        print("    %d total constraints.  %d total nonzeros (%.2f avg, %d max)." % (ccount, tc, tavg, tmax))
        bcount = self.bdd_ops
        ncount = self.rset.bdd_node_count
        navg = self.rset.bdd_avg()
        nmax = self.rset.bdd_node_max
        print("    %d estimated BDD operations.  %d total BDD nodes (%.2f avg, %d max)" % (bcount, ncount, navg, nmax))
        
