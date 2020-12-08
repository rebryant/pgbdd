#!/usr/bin/python

# Generate variable ordering for instance of KB formula
# Input: the index of the formula in the family

# translation table
# y0   1
# y1   2        y2   5  ...   yi   3*i-1      
# y1'  3        y2'  6  ...   yi'  3*i
# x1   4        x2   7  ...   xi   3*i+1
# yt+1 3*t+2    ...           yt+t 3*t+t+1

## REB Notes: 11/15/2020
# Comparing to notation in Kiesl, Heule, Seidl:
# t   --> n
# yi  --> ai  1 <= i <=n
# yi' --> bi  1 <= i <=n
# xi  --> xi  1 <= i <=n
# yt+1 ... yt+t --> c1 .. cn
# 
# Logical to interleave ai, bi, ci, xi
# Mostly done, except that all c's are at the end of the input ordering

# Variable ordering
# 1
# 2 3 4 3*t+2   (i = 1)
# 5 6 7 3*t+3   (i = 3)
# ....
# 3*t-1 3*t 3*t+1 3*t+t+1 (i = t)
#
# 3*i-1 3*i 3*i+1 3*t+i+1 (1 <= i <= t)

## End REB


import sys

if (len(sys.argv) > 1):
    t=int(sys.argv[1])
else:
    t=1

print "1"
for i in range(1,t+1):
    i3 = 3*i
    print "%d %d %d %d" % (i3-1, i3, i3+1, 3*t+i+1)
