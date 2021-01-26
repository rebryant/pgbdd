#!/usr/bin/python

import sys
import re

# For set of benchmarks, generate CSV file giving times for solver and for proof checker
# Extract value of size parameter from file name

triggerPhrases = ["Elapsed time for SAT", "Elapsed time for check"]

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

# Extract data from log.  Turn into something usable for other tools
def extract(fname):
    vals = [-2] * len(triggerPhrases)
    try:
        f = open(fname, 'r')
    except:
        print("Couldn't open file '%s'" % fname)
        return None

    for line in f:
        line = trim(line)
        for idx in range(len(triggerPhrases)):
            phrase  = triggerPhrases[idx]
            if phrase in line:
                fields = lineSplit(line)
                vals[idx] = firstFloat(fields)
    f.close()
    n = firstNumber(ddSplit(fname))
    vals = [n] + vals
    return vals

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def run(name, args):
    if len(args) < 1:
        usage(name)
    vdict = {}
    for fname in args:
        vlist = extract(fname)
        vdict[vlist[0]] = vlist
    for k in sorted(vdict.keys()):
        slist = [str(v) for v in vdict[k]]
        print(",".join(slist))


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
