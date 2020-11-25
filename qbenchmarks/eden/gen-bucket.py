#!/usr/bin/python

## Generate permutation of variables to define bucket ordering for Garden of Eden problem
# Parses qcnf file to determine number of existential and universal variables
# Uses comment in header to determine number of rows and columns
# Arranges existential variables in column-major order, and universal variables afterwards

import sys

nrow = 0
ncol = 0
nuniversal = 0

def extractParameters(infile):
    global nrow, ncol, nuniversal
    found = False
    failed = False
    for line in infile:
        fields = line.split()
        if fields[0] == 'c' and fields[2] == 'X':
            try:
                nrow = int(fields[1])
                ncol = int(fields[3])
            except:
                continue
        elif fields[0] == 'a':
            nuniversal = len(fields)-2
            found = nrow > 0 and ncol > 0
            failed = nrow == 0 or ncol == 0
        else:
            try:
                lit = int(fields[0])
                failed = True
            except:
                pass
        if found or failed:
            break
    if failed:
        sys.stderr.write("Could not extract parameters from file\n")
        sys.exit(1)

def generate():
    vals = [str(u+1) for u in range(nuniversal)]
    print(" ".join(vals))

    erow = 2+nrow
    ecol = 2+ncol
    for c in range(ecol):
        vals = [str(c+r*ecol+nuniversal+1) for r in range(erow)]
        print(" ".join(vals))
            

def run(name, args):
    if len(args) == 0:
        infile = sys.stdin
    elif len(args) == 1:
        try:
            infile = open(args[0], 'r')
        except:
            sys.stderr.write("Couldn't open qcnf file '%s'\n" % args[0])
            sys.exit(1)
    else:
        sys.stderr.write("Usage: %s [FILE.qcnf]\n")
        sys.exit(0)
    extractParameters(infile)
    generate()


run(sys.argv[0], sys.argv[1:])
        
        
            
            
    
