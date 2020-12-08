#!/usr/bin/python

## Generate permutation of variables to define bucket ordering for Garden of Eden problem
# Parses qcnf file to determine number of existential and universal variables
# Uses comment in header to determine number of rows and columns
# Arranges existential variables in column-major order, and universal variables afterwards

import sys
import eextract

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
    eden = eextract.Eden(infile)
    eden.bucketOrder()

run(sys.argv[0], sys.argv[1:])
        
        
            
            
    
