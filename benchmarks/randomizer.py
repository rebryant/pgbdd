#!/usr/bin/python

# Given CNF file, read number of variables, and generate a random permutation of the variables

import sys
import random

def usage(name):
    print("Usage: %s FILE.cnf [SEED]" % name)

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

def doit(cname, seed):
    nvars = 0
    try:
        cfile = open(cname, 'r')
    except:
        print("Couldn't open CNF file '%s'" % cname)
        return
    for line in cfile:
        line = trim(line)
        fields = line.split()
        if len(fields) == 0:
            continue
        elif fields[0] == 'c':
            continue
        elif fields[0] == 'p':
            try:
                nvars = int(fields[2])
            except:
                print("Couldn't read line '%s'" % line)
                return
            break
        else:
            print("Unrecognized line before header: '%s'" % line)
            return
    cfile.close()
    if nvars == 0:
        print("Didn't determine number of variables")
        return
    if seed is not None:
        random.seed(seed)
    perm = list(range(1,nvars+1))
    random.shuffle(perm)
    slist = [str(p) for p in perm]
    cparts = cname.split('.')
    if len(cparts) > 1:
        cparts[-1] = "order"
    else:
        cparts.append("order")
    oname = ".".join(cparts)
    try:
        ofile = open(oname, "w")
    except:
        print("Couldn't open output file '%s'" % oname)
        return
    ofile.write(" ".join(slist))
    ofile.write("\n")
    ofile.close()
    
def run(name, args):
    seed = None
    if len(args) < 1 or len(args) > 2:
        usage(name)
        return
    cname = args[0]
    if len(args) == 2:
        try:
            seed = int(args[1])
        except:
            print("Invalid seed '%s'" % args[1])
            return
    doit(cname, seed)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


    
            
