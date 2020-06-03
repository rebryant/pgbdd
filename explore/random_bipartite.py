#!/usr/bin/python

# Generate random bipartite graph with 2N nodes, such that each node has degree K

import random
import sys

def usage(name):
    print("Usage: %s N [K [S]]" % name)
    print("  N = 1/2 the number of nodes")
    print("  K = degree of each node")
    print("  S = random seed")
    sys.exit(0)

# How many passes to attempt
max_pass = 100

# Do a swap of the given element with a randomly chosen element of a list
def random_swap(ls, i):
    N = len(ls)
    j = random.randrange(N)
    ls[i], ls[j] = ls[j], ls[i]
    

# Make a pass over the lists, trying to correct multi-edges
# Return number of swaps performed
# Assumes that identity permutation will be added later
def repair_pass(permlist):
    KM1 = len(permlist)
    N = len(permlist[0])
    ioffset = random.randrange(N)
    multiedges = 0
    for i in range(N):
        idx = (i + ioffset) % N
        othervals = []
        joffset = random.randrange(KM1)
        for j in range(KM1):
            jdx = (j + joffset) % KM1
            val = permlist[jdx][idx]
            if val == idx or val in othervals:
                random_swap(permlist[jdx], idx)
                multiedges += 1
            othervals.append(permlist[jdx][idx])
    return multiedges
                
def build(N, K):
    permlist = []
    for j in range(K-1):
        ls = list(range(N))
        random.shuffle(ls)
        permlist.append(ls)
    for p in range(max_pass):
        multiedges = repair_pass(permlist)
        print("# Pass %d.  Fixed %d multi-edges" % (p+1, multiedges))
        if multiedges == 0:
            permlist = [list(range(N))] + permlist
            return permlist
    print("# Failed to find valid graph after %d passes" % max_pass)
    # First permutation is identity
    permlist = [list(range(N))] + permlist
    return permlist
        
        
def run(name, args):
    if len(args) == 0 or len(args) > 3:
        usage(name)
    try:
        N = int(args[0])
    except:
        usage(name)
    if len(args) > 1:
        try:
            K = int(args[1])
        except:
            usage(name)
    else:
        K = 5
    if len(args) > 2:
        try:
            S = int(args[2])
            random.seed(S)
        except:
            usage(name)
    permlist = build(N, K)
    for i in range(N):
        slist = [str(permlist[j][i]) for j in range(K)]
        print("\t%d:\t" % i + "\t".join(slist))

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    

