#!/usr/bin/python

# Given (Q)CNF file, read number of variables, and list them in either forward or reverse order

import sys

def usage(name):
    sys.stderr.write("Usage: %s [-r] FILE.(q)cnf\n" % name)

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

def error(msg):
    sys.stderr.write("ERROR: %s\n" % msg)
    sys.exit(1)

def doit(cname, reverse):
    nvars = 0
    try:
        cfile = open(cname, 'r')
    except:
        error("Couldn't open (Q)CNF file '%s'" % cname)
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
                error("Couldn't read line '%s'" % line)
            break
        else:
            error("Unrecognized line before header: '%s'" % line)
            return
    cfile.close()
    if nvars == 0:
        error("Didn't determine number of variables")
    slist = [str(i) for i in range(1,nvars+1)]
    if reverse:
        slist.reverse()
    print(" ".join(slist))
    
def run(name, args):
    reverse = False
    index = 0
    if len(args) < 1 or len(args) > 2:
        usage(name)
        return
    if args[0][0] == '-':
        if args[0][1] == 'r':
            reverse = True
            index += 1
        else:
            error("Unrecognized option '%s'" % args[0])
    cname = args[index]
    doit(cname, reverse)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])


    
            
