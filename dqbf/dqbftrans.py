#!/usr/bin/python

# Long-term goal: Transform DQBF formula into a standard QBF formula
# Goal: Minimize number of clauses in resulting formula
# Added benefit: Generate clausal proof that resulting formula is logically equivalent to original

# Short term: Perform some of the steps in the process
# Generate statistics on performance

import sys
import getopt
import glob

import util
import partition

# CSV or tab separated?
#fieldSep = ','
fieldSep = '\t'
extension = "dqdimacs"

def formatList(ls):
    slist = [str(e) for e in ls]
    return fieldSep.join(slist)

def trimFile(fname):
    return fname.split('/')[-1]

def usage(prog):
    print("Usage: %s [-h] [-v] [-d DIR] [-i FILE]" % prog)
    print(" -h      Print this message")
    print(" -v      Provide more detailed information")
    print(" -d DIR  Process all dqdimacs files in specified directory")
    print(" -i FILE Process only specified file")

def processFile(fname, verbose):
    tfname = trimFile(fname)
    try:
        reader = util.DqcnfReader(fname)
    except util.CnfException as ex:
        print("File: %s. Read failed (%s)" % (tfname, str(ex)))
        return
    try:
        b = partition.Block(reader.dependencyMap)
    except partition.PartitionException as ex:
        print("File: %s.  Couldn't generate block partition (%s)" % (tfname, str(ex)))
        return
    if verbose:
        print("File: %s.  Blocks" % tfname)
        b.show()
        print(formatList(b.statFieldList()))
        print(formatList(b.statList()))
    else:
        print(formatList(b.statList() + [tfname]))
    
def run(name, args):
    dname = None
    fname = None
    verbose = False

    optlist, args = getopt.getopt(args, "hvd:f:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-d':
            dname = val
        elif opt == '-f':
            fname = val
    if not verbose:
        slist = partition.Block().statFieldList() + ["file"]
        print(formatList(slist))
    if fname is not None:
        processFile(fname, verbose)
    if dname is not None:
        flist = glob.glob(dname + "/*." + extension)
        for name in flist:
            processFile(name, verbose)    
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
    


