#!/usr/bin/python

# Enumerate list of numbers from 1 to N
import sys


if (len(sys.argv) > 1):
    t=int(sys.argv[1])
else:
    t=1

N=4*t+1

# Print in blocks of 10
BASE = 10
BCOUNT = N//BASE

for b in range(BCOUNT):
    vals = [b*BASE+i+1 for i in range(BASE)]
    svals = [str(v) for v in vals]
    print(" ".join(svals))

vals = list(range(BCOUNT*BASE+1,N+1))
svals = [str(v) for v in vals]
print(" ".join(svals))
