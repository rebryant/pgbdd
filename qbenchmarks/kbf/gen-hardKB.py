#!/usr/bin/python

# Script to generate hard fomulas from the family given in Theorem 3.2 in
#   \cite{DBLP:journals/iandc/BuningKF95}
#
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
## End REB


import sys

if (len(sys.argv) > 1):
    t=int(sys.argv[1])
else:
    t=1

# compute number of variables
nvars=4*t+1
nclauses=4*t+2


cline = "c Formula " + str(t) + " in the family of Kleine Buening et al. (1995)"
pline = "p cnf " + str(nvars) + " " + str(nclauses)
print cline 
print pline

# output the quantifier lines
# first e/a block
print "e 1 2 3 0"
print "a 4 0"
for i in range(2, t+1):  
    print "e " + str(3*i-1) + " " + str(3*i) + " 0"
    print "a " + str(str(3*i+1)) + " 0"

# print last e block
sys.stdout.write("e")
for i in range(3*t+2, 4*t+2):   
    sys.stdout.write(" " + str(i))
print " 0"

# Now the matrix
# The first two clauses ...
print "-1 0"
print "1 -2 -3 0"

# ... then clauses with x literals, 
for i in range(1, t):  
    print str(3*i-1) + " " + "-" + str(3*i+1) + " " + "-" + str(3*i+2) + " " + \
"-" + str(3*i+3) + " 0"
    print str(3*i) + " " + " " + str(3*i+1) + " " + "-" + str(3*i+2) + " " + \
"-" + str(3*i+3) + " 0"

# ... the special t-th clauses
sys.stdout.write(str(3*t-1)) 
sys.stdout.write(" -") 
sys.stdout.write(str(3*t+1)) 
for i in range(3*t+2, 3*t+t+2):
    sys.stdout.write(" -") 
    sys.stdout.write(str(i))
print " 0"

sys.stdout.write(str(3*t)) 
sys.stdout.write("  ") 
sys.stdout.write(str(3*t+1)) 
for i in range(3*t+2, 3*t+t+2):
    sys.stdout.write(" -") 
    sys.stdout.write(str(i))
print " 0"

# ... and finally the binary clauses
for i in range(1, t+1):   
    print " " + str(3*i+1) + " " + str(3*t+1+i) + " 0"
    print "-" + str(3*i+1) + " " + str(3*t+1+i) + " 0"
