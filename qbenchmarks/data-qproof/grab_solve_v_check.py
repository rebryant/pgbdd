#!/usr/bin/python

import sys
import re

# For set of benchmarks, generate CSV file giving times for solver and for proof checker

triggerPhrases = ["Elapsed time for SAT", "Elapsed time for check"]

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

colonOrSpace = re.compile('[\s:]+')
def lineSplit(s):
    return colonOrSpace.split(s)

def firstNumber(fields):
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
                vals[idx] = firstNumber(fields)
    f.close()
    return vals

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def run(name, args):
    if len(args) < 1:
        usage(name)
    for fname in args:
        vlist = extract(fname)
        slist = [str(v) for v in vlist]
        if min(vlist) > 0:
            print(",".join(slist))
        else:
            print("ERR: Got values [%s] from file %s" % (", ".join(slist), fname))



if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
