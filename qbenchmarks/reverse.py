#!/usr/bin/python

# Read list of numbers.
# Print them in reverse order

import sys

lineNumber = 0
listList = []

def error(message):
    global lineNumber
    sys.stderr.write("ERROR: Line #%d: %s" % (lineNumber, message))
    sys.exit(1)

def getList(line):
    global listList
    try:
        vals = [int(s) for s in line.split()]
    except:
        error("Only allow lists of numbers")
    vals.reverse()
    listList.append(vals)

for line in sys.stdin:
    lineNumber += 1
    getList(line)

listList.reverse()

for vals in listList:
    svals = [str(v) for v in vals]
    print(" ".join(svals))

    
    
