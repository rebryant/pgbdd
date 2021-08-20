#!/usr/bin/python

# Generate shell scripts that enable testing of integer equations
# with modular arithmetic, by choosing prime modulus large enough to 
# encode integer equation without wraparound

import sys

def usage(name):
    sys.stderr.write("Usage: %s [-h] FSTRING N1:M1 N2:M2 ...\n")
    sys.stderr.write("  -h         Print this message\n")
    sys.stderr.write("  FSTRING  Format string for command.  Should contain '%n' for problem size and '%p' for chosen modulus\n")
    sys.stderr.write("  Nx:Mx    Pair giving problem size and minimum modulus\n")

    
sieve = []

primes = []

def fillSieve(n):
    global sieve, primes
    sieve = [False, False] + [True] * (n-1)
    primes = []
    for i  in range(n+1):
        if not sieve[i]:
            continue
        primes.append(i)
        j = 2*i
        while j <= n:
            sieve[j] = False
            j += i
    
def nextPrime(n):
    if len(primes) == 0 or primes[-1] < n:
        fillSieve(n+100)
    i = n
    while i < len(sieve):
        if sieve[i]:
            return i
        i += 1
    
def nextPrimeList(ls):
    mval = max(ls)
    p = nextPrime(mval)
    return [nextPrime(n) for n in ls]

        
def generate(fstring, nstring, m):
    p = nextPrime(m)
    ostring = ""
    rstring = fstring
    while len(rstring) > 0:
        c = rstring[0]
        rstring = rstring[1:]
        if c == '%':
            if len(rstring) == 0:
                sys.stderr.write("Can't have '%' as last character\n")
                return ""
            d = rstring[0]
            rstring = rstring[1:]
            if d == 'n':
                ostring += str(nstring)
            elif d == 'p':
                ostring += str(p)
            else:
                sys.stderr.write("Unknown format '%%%s'\n" % d)
                return ""
        else:
            ostring += c
    return ostring

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        usage(name)
        return
    fstring = args[0]
    for arg in args[1:]:
        fields = arg.split(':')
        if len(fields)  != 2:
            sys.stderr.write("Invalid specifier '%s' (Must have two parts)\n" % arg)
            usage(name)
            return
        nstring = fields[0]
        try:
            m = int(fields[1])
        except:
            sys.stderr.write("Invalid specifier '%s'\n (second part must be integer)" % arg)
            usage(name)
            return
        sys.stdout.write(generate(fstring, nstring, m) + '\n')

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
