#!/usr/bin/python
# Extract field(s) from file.  Turn into csv
# Fields numbered from 1

import sys

def trim(s):
    while s[-1] == '\n':
        s = s[:-1]
    return s

def usage(name):
    print("Usage %s: I1 I2 ... In")
    print("Each I is an index into the input fields, numbering from 1")

def extract(indices):
        for line in sys.stdin:
            line = trim(line)
            fields = line.split()
            slist = [(fields[i-1] if i > 0 and i < len(fields) else "") for i in indices]
            print(",".join(slist))
            
    
def run(name, arglist):
    ilist = []
    for arg in arglist:
        try:
            idx = int(arg)
        except:
            usage(name)
            sys.exit(0)
        ilist.append(idx)
    extract(ilist)

run(sys.argv[0], sys.argv[1:])

    
