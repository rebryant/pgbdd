#!/usr/bin/python3

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

import sys
import  getopt
import writer
import cnf_utilities

# Generate CNF file for pigeonhole problem
def usage(name):
    print("Usage: %s [-h] [-v] [-S] -r ROOT -n N [-p P]" % name) 
    print("  -h       Print this message")
    print("  -v       Run in verbose mode")
    print("  -L       Use Linear encoding of at-most-one constraints")
    print("  -r ROOT  Specify root name for files.  Will generate ROOT.cnf")
    print("  -n N     Specify number of holes")
    print("  -p P     Specify number of pigeons (default = N+1)")
    print("  -P       Generate permutation files ROOT.pigeon_major ROOT.hole_major")

verbose = False
holeCount = 8
pigeonCount = None
linear = False

# Get variable encoding whether pigeon j (numbered from 1) is
# in hole i (numbered from 1)

def pij(i, j):
    return (i-1)*pigeonCount + j

def permuter(froot, pigeonMajor):
    suffix = "pigeon_major" if pigeonMajor else "hole_major"
    pw = writer.PermutationWriter(holeCount, pigeonCount, froot, suffix)
    if pigeonMajor:
        pw.rowMajor()
    else:
        pw.columnMajor()
    pw.finish()

def generate(froot):
    cwriter = writer.LazyCnfWriter(froot, verbose)
    if verbose:
        cwriter.doComment("Encoding of pigeonhole problem for %d holes and %d pigeons" % (holeCount, pigeonCount))
        if linear:
            cwriter.doComment("Use linear encoding of at-most-one constraints")
        else:
            cwriter.doComment("Use direct encoding of at-most-one constraints")
    cwriter.newVariables(holeCount * pigeonCount)
    # Every pigeon must be in some hole
    for j in range(1, pigeonCount+1):
        pvars = [pij(i, j) for i in range(1, holeCount+1)]
        cnf_utilities.atLeastOne(cwriter, pvars, verbose)
    # Every hole can contain at most one pigeon
    for i in range(1, holeCount+1):
        hvars = [pij(i, j) for j in range(1, pigeonCount+1)]
        if linear:
            cnf_utilities.atMostOneLinear(cwriter, hvars, verbose)
        else:
            cnf_utilities.atMostOneDirect(cwriter, hvars, verbose)
    cwriter.finish()

def run(name, args):
    global verbose, holeCount, pigeonCount, linear
    froot = None
    holeCount = None
    pigeonCount = None
    permFiles = False
    optlist, args = getopt.getopt(args, "hvr:n:p:LP")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-r':
            froot = val
        elif opt == '-n':
            holeCount = int(val)
        elif opt == '-p':
            pigeonCount = int(val)
        elif opt == '-L':
            linear = True
        elif opt == '-P':
            permFiles = True
    if holeCount is None:
        print("Must have value for n")
        usage(name)
        return
    if froot is None:
        print("Must have root name")
        usage(name)
        return
    if pigeonCount is None:
        pigeonCount = holeCount+1
    if linear and permFiles:
        print("Cannot generate permutation files when using linear encoding")
        return
    generate(froot)
    if permFiles:
        permuter(froot, True)
        permuter(froot, False)
        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

        
