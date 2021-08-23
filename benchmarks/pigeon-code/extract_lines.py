#!/usr/bin/python

# Extract tagged comment lines from CNF file
# Line of form 'c TAG REST'

import sys

def usage(name):
    print("Usage: %s [-h] TAG < infile > outfile" % name)

def process(tag):
    for line in sys.stdin:
        fields = line.split()
        if len(fields) >= 2 and fields[0] == 'c' and fields[1] == tag:
            rest = " ".join(fields[2:])
            sys.stdout.write(rest + '\n')

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        usage(name)
        return
    process(args[0])
    

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

                            
