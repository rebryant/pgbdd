#!/usr/bin/python

import sys
import re

# Generate csv of number specified on target line
# Extracts problem sizes N and M from file name containing substrings of form NxM.

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

def findXnum(s):
    vlist = None
    val = 0
    foundDigit = False
    while True:
        if len(s) == 0:
            if foundDigit:
                vlist = [val] if vlist is None else vlist + [val]
            return vlist
        if s[0] == 'x':
            if foundDigit:
                vlist = [val] if vlist is None else vlist + [val]
                rlist = findXnum(s[1:])
                return rlist if rlist is None else vlist + rlist
            else:
                return None
        if s[0] >= '0' and s[0] <= '9':
            foundDigit = True
            val = 10*val + (ord(s[0]) - ord('0'))
            s = s[1:]
        else:
            return None

def firstXNumber(fields):
    for field in fields:
        vlist = findXnum(field)
        if vlist is not None:
            return vlist
    return None

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
    vlist = firstXNumber(fields)
    if vlist is None:
        print("Couldn't extract problem size from file name '%s'" % fname)
        return None
    # Put product at beginning
    prod = 1
    for v in vlist:
        prod *= v
    vlist = [prod] + vlist

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
            return vlist + [val]
    f.close()
    return None

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def run(name, args):
    if len(args) < 1:
        usage(name)
    for fname in args:
        vlist = extract(fname)
        if vlist is not None:
            slist = [str(v) for v in vlist]
            print(",".join(slist))

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
