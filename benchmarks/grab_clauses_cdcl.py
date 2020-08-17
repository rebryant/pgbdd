#!/usr/bin/python

import sys
import re

# Generate csv of sum of numbers from different lines
# Extracts problem size from file name

triggerPhrases = [
    "c proof_added",
    "c parsed 'p cnf",
    ]

triggerPos = [
    1,
    2,
]

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

dashOrDot = re.compile('[.-]')
def ddSplit(s):
    return dashOrDot.split(s)

colonSpaceOrQuote = re.compile("[\s:']+")
def lineSplit(s):
    return colonSpaceOrQuote.split(s)

def nthNumber(fields, n):
    count  = 0
    for field in fields:
        try:
            val = int(field)
            count += 1
            if count == n:
                return val
        except:
            continue
    return 0


def findTrigger(line):
    idx = 0
    for phrase in triggerPhrases:
        if phrase in line:
            return idx
        idx += 1
    return -1

# Extract clause data from log.  Turn into something useable for other tools
def extract(fname):
    sum = 0
    # Try to find size from file name:
    fields = ddSplit(fname)
    n = nthNumber(fields, 1)
    if n < 0:
        print("Couldn't extract problem size from file name '%s'" % fname)
        return None
    try:
        f = open(fname, 'r')
    except:
        print("Couldn't open file '%s'" % fname)
        return None
    for line in f:
        line = trim(line)
        idx = findTrigger(line)
        if idx >= 0:
            fields = lineSplit(line)
            val = nthNumber(fields, triggerPos[idx])
            sum += val
    f.close()
    return None if sum == 0 else (n,sum)

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def run(name, args):
    if len(args) < 1:
        usage(name)
    for fname in args:
        pair = extract(fname)
        if pair is not None:
            print("%s,%s" % pair)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
