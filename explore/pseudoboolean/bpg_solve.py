#!/usr/bin/python

import sys
import getopt
import random
import modsolve
import constraints

# Generate and solve equational or constraint representation of Bipartite perfect matching
def usage(name):
    print("Usage: %s [-h] [-v] [-c] [-p] [-m MOD] [-n LEFT] [-x EXTRA] ([-d DEN_PCT] [-e EDGES]) [-r SEEDS]" % name) 
    print("  -h         Print this message")
    print("  -v         Run in verbose mode")
    print("  -c         Use constraints rather than equations")
    print("  -p         Perform presumming")
    print("  -m MOD     Specify modulus")
    print("  -n LEFT    Specify number of nodes in left partition")
    print("  -x EXTRA   Specify number of additional nodes in right partition (default is 1)")
    print("  -d DEN_PCT Specify number of edges based on density (as percent).  Default is 100")
    print("  -e EDGES   Specify number of edges explicitly")
    print("  -r SEEDS   Set random seed.  Either single number S, or S1:S2 for graph generation and solving")

        
# Encoding of bipartite matching problem as linear equations or constraints
class Graph:
    # Number of nodes in left and right partitions
    lcount = 10
    rcount = 10
    ecount = 0
    # Map left vertex to its right neighbors (represented as dictionary mapping right Ids to variable number)
    l2r_map = {}
    # Map right vertex to its left neighbors (represented as dictionary mapping left Ids to variable number)
    r2l_map = {}

    # Create graph with specified number of edges
    # ecount should be between right and left*right
    def __init__(self, lcount, rcount, ecount):
        self.lcount = lcount
        self.rcount = rcount
        self.ecount = ecount
        if rcount < lcount:
            raise Exception("Must have no more nodes in left partition than in right. %d !<= %d" % (lcount, rcount))
        if ecount < lcount+rcount-1:
            raise Exception("Not enough edges to make graph connected.  Have %d.  Need at least %d" % (ecount, lcount+rcount-1))
        self.l2r_map = { i :  {} for i in range(lcount)  }
        self.r2l_map = { j :  {} for j in range(rcount) }
        self.ecount = 0
        self.add_edges(ecount)
        self.renumber_edges()

    def adjacent(self, l, r):
        if l not in self.l2r_map:
            raise Exception("ERROR.  Cannot have edge (%d,%d)" % (l, r))
            return False
        return r in self.l2r_map[l]

    def add_edge(self, l, r):
        if l < 0 or l >= self.lcount:
            raise Exception("ERROR.  Cannot have edge (%d,%d)" % (l, r))
        if r < 0 or r >= self.rcount:
            raise Exception("ERROR.  Cannot have edge (%d,%d)" % (l, r))
        if self.adjacent(l, r):
            raise Exception("Edge (%d,%d) already in graph" % (l, r))
        self.l2r_map[l][r] = self.ecount
        self.r2l_map[r][l] = self.ecount
        self.ecount += 1
        
    def add_edges(self, target):
        lcount = self.lcount
        rcount = self.rcount
        # Generate map of all possible edges
        possible = { (x//rcount, x%rcount) : True for x in range(lcount*rcount) }

        # Start by making graph connected
        lids = list(range(self.lcount))
        random.shuffle(lids)
        rids = list(range(self.rcount))
        random.shuffle(rids)
        li_max = 0
        ri_max = 0
        (l,r) = (lids[li_max], rids[ri_max])
        self.add_edge(l, r)
        del possible[(l, r)]
        while li_max < lcount-1:
            li_max += 1
            ri = random.randint(0, ri_max)
            (l,r) = (lids[li_max], rids[ri])
            self.add_edge(l, r)
            del possible[(l, r)]

            ri_max += 1
            li = random.randint(0, li_max)
            (l,r) = (lids[li], rids[ri_max])
            self.add_edge(l, r)
            del possible[(l, r)]

        ri_max += 1
        while ri_max < rcount:
            li = random.randint(0, lcount-1)
            (l,r) = (lids[li], rids[ri_max])
            self.add_edge(l, r)
            del possible[(l, r)]
            ri_max += 1

        choose = possible.keys()
        random.shuffle(choose)
        nchoose = target - self.ecount
        choose = choose[:nchoose]
            
        for (l,r) in choose:
            self.add_edge(l,r)

        
    def renumber_edges(self):
        l2r = self.l2r_map
        # Rebuild edges
        self.l2r_map = { i :  {} for i in range(self.lcount)  }
        self.r2l_map = { j :  {} for j in range(self.rcount) }
        self.ecount = 0
        for l in range(self.lcount):
            for r in sorted(l2r[l].keys()):
                self.add_edge(l, r)

    def show(self):
        for l in range(self.lcount):
            rmap = self.l2r_map[l]
            s = ['*' if r in rmap else '-' for r in range(self.rcount)]
            print "".join(s)

    def maybe_solvable(self):
        return self.lcount == self.rcount

    def equations(self, modulus, verbose, presum):
        ecount = self.ecount
        esys = modsolve.EquationSystem(ecount, modulus, verbose)
        left_equations = []
        right_equations = []
        for l in range(self.lcount):
            e = modsolve.Equation(ecount, modulus, 1, esys.mbox)
            rvars = self.l2r_map[l].values()
            for r in rvars:
                e[r] = 1
            eid = esys.add_equation(e)
            left_equations.append(eid)
        for r in range(self.rcount):
            e = modsolve.Equation(ecount, modulus, 1, esys.mbox)
            lvars = self.r2l_map[r].values()
            for l in lvars:
                e[l] = 1
            eid = esys.add_equation(e)
            right_equations.append(eid)
        if presum:
            esys.add_presum(left_equations)
            esys.add_presum(right_equations)
        return esys

    def constraints(self, verbose, presum):
        ecount = self.ecount
        csys = constraints.ConstraintSystem(ecount, verbose)
        left_constraints = []
        right_constraints = []
        con = constraints.Constraint(ecount, 0)
        for l in range(self.lcount):
            rvars = self.l2r_map[l].values()
            lcon = con.amo(rvars)
            cid = csys.add_constraint(lcon)
            left_constraints.append(cid)
        for r in range(self.rcount):
            lvars = self.r2l_map[r].values()
            rcon = con.alo(lvars)
            cid = csys.add_constraint(rcon)
            right_constraints.append(cid)
        if presum:
            csys.add_presum(left_constraints)
            csys.add_presum(right_constraints)
        return csys


def bpg_solve(verbose, constrain, presum, modulus, lcount, rcount, ecount, seed2):
    g = Graph(lcount, rcount, ecount)
    if constrain:
        print("Graph: %d X %d.  %d edges." % (lcount, rcount, ecount))        
    else:
        print("Graph: %d X %d.  %d edges.  Modulus = %d." % (lcount, rcount, ecount, modulus))
    xsys = g.constraints(verbose, presum) if constrain else g.equations(modulus, verbose, presum)
    if seed2 is not None:
        xsys.randomize = True
        random.seed(seed2)
    if not verbose:
        xsys.pre_statistics()
    status = xsys.solve()
    if not verbose:
        xsys.post_statistics(status, g.maybe_solvable())

def run(name, args):
    verbose = False
    presum = False
    modulus = 2
    constrain = False
    lcount = 10
    extra = 1
    den_pct = None
    ecount = None
    randomize = False
    seed2 = None
    optlist, args = getopt.getopt(args, "hvcpm:n:x:d:e:r:")
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
            lcount = int(val)
        elif opt == '-x':
            extra = int(val)
        elif opt == '-d':
            den_pct = int(val)
        elif opt == '-e':
            ecount = int(val)
        elif opt == '-r':
            randomize = True
            fields = val.split(':')
            seeds = [int(field) for field in fields]
            seed1 = seeds[0]
            random.seed(seed1)
            seed2 = seeds[1] if len(seeds) > 1 else seed1

    rcount = lcount+extra
    if ecount is None:
        density = 1.0 if den_pct is None else 0.01 * den_pct
        ecount = int(round(density * lcount * rcount))
    elif den_pct is not None:
        print("Can't specify both density and number of edges")
        usage(name)
        return

    bpg_solve(verbose, constrain, presum, modulus, lcount, rcount, ecount, seed2)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


                         
        

    


