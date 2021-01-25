#!/usr/bin/python

import sys
import re

# Generate csv of number specified on target line
# Extracts problem sizes N from file name containing substrings of form -N-

# Sample line
# #Seed:  1. true.  Bt:407409, Dec:2326631.  T: 267.872 s.

triggerPhrase = "T:"

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

dashOrDot = re.compile('[.-]')
def ddSplit(s):
    return dashOrDot.split(s)

colonOrSpace = re.compile('[\s:]+')
def lineSplit(s):
    return colonOrSpace.split(s)

def firstNumber(fields):
    for field in fields:
        try:
            val = int(field)
            return val
        except:
            continue
    return -1

def firstFloat(fields):
    for field in fields:
        try:
            val = float(field)
            return val
        except:
            continue
    return -1

# Extract clause data from log.  Turn into something usable for other tools
def extract(fname):
    # Try to find size from file name:
    fields = ddSplit(fname)
    n = firstNumber(fields)
    if n < 0:
        print("Couldn't extract problem size from file name '%s'" % fname)
        return None
    # Put n at beginning
    vlist = [n]

    try:
        f = open(fname, 'r')
    except:
        print("Couldn't open file '%s'" % fname)
        return None
    for line in f:
        line = trim(line)
        if triggerPhrase in line:
            fields = lineSplit(line)
            fields.reverse()
            val = firstFloat(fields)
            f.close()
            return vlist + [val]
    f.close()
    return None

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def run(name, args):
    vdict = {}
    if len(args) < 1:
        usage(name)
    for fname in args:
        vlist = extract(fname)
        if vlist is not None:
            vdict[vlist[0]] = vlist
    for k in sorted(vdict.keys()):
        vlist = vdict[k]
        slist = [str(v) for v in vlist]
        print(",".join(slist))

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
