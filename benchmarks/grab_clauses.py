#!/usr/bin/python

import sys
import re

# Generate csv of number specified on target line
# Extracts problem size from file name

triggerPhrase = "Total Clauses"

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


# Extract clause data from log.  Turn into something useable for other tools
def extract(fname):
    # Try to find size from file name:
    fields = ddSplit(fname)
    n = firstNumber(fields)
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
        if triggerPhrase in line:
            fields = lineSplit(line)
            val = firstNumber(fields)
            f.close()
            return (n, val)
    f.close()
    return None

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

            
        
                
