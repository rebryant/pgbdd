#!/usr/bin/python
import sys
import getopt
import math

# Input is CSV file with entries x,y.
# 12/02/2020 ... Allow entries of the form x,N,N,...,N,y
# where N is a number to be ignored.

# Perform trend analysis, fitting curves of the form y = x^C and y = C^x


def usage(name):
    print("Usage: %s [-h] [-e] < file.csv" % name)
    print("  -h     Print this message")
    print("  -e     Fit to exponential curve")

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

# Given values of x and y, find best linear fit
# Return pair (m,b)
def leastSquaresFit(pairList):
    # Formula taken from https://www.analyzemath.com/calculus/multivariable/linear-least-squares-fitting.html
    n = len(pairList)
    xsum = sum([x for x,y in pairList])
    ysum = sum([y for x,y in pairList])
    xysum = sum([x*y for x,y in pairList])
    xxsum = sum([x*x for x,y in pairList])
    mnum = n * xysum - xsum * ysum
    bnum = -xsum*xysum + xxsum*ysum
    denom = n * xxsum - xsum*xsum
    m = mnum/denom
    b = bnum/denom
    return (m,b)

def fitPolynomial(pairList):
    llpairs = [(math.log(x), math.log(y)) for x,y in pairList]
    m,b = leastSquaresFit(llpairs)
    print("%d values.  Polynomial fit.  m = %.3f, b = %.3f" % (len(llpairs), m, b))

def fitExponential(pairList):
    semipairs = [(x, math.log(y)) for x,y in pairList]
    m,b = leastSquaresFit(semipairs)
    print("%d values.  Exponential fit.  Exp(m) = %.3f, Exp(b) = %.3f" % (len(semipairs), math.exp(m), math.exp(b)))
    

# Generate list of form [(x1, y1), .., (xn,yn)]
def grab(infile):
    pairList = []
    for line in infile:
        line = trim(line)
        fields = line.split(",")
        if len(fields) >= 2:
            try:
                x = float(fields[0])
                y = float(fields[-1])
                pair = (x,y)
                pairList.append(pair)
            except:
                print("Line %s gives nothing" % (line))
                pass
    return pairList
        
def run(name, args):
    exponential = False
    optlist, args = getopt.getopt(args, "he")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-e':
            exponential = True
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    pairList = grab(sys.stdin)
    if exponential:
        fitExponential(pairList)
    else:
        fitPolynomial(pairList)
        


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
