#!/usr/bin/python

# Long-term goal: Transform DQBF formula into a standard QBF formula
# Goal: Minimize number of clauses in resulting formula
# Added benefit: Generate clausal proof that resulting formula is logically equivalent to original

# Short term: Perform some of the steps in the process
# Generate statistics on performance

import sys
import getopt
import glob

import reader
import preprocess

def usage(prog):
    print("Usage: %s [-h] [-v] [-u] [-d DIR] [-p PFX] [-f FILE]" % prog)
    print(" -h      Print this message")
    print(" -v      Provide more detailed information")
    print(" -u      Treat universal variables as singleton partitions")
    print(" -d DIR  Process all matching files in specified directory")
    print(" -p PFX  Only process files with specified prefix")
    print(" -f FILE Process only specified file")


# CSV or tab separated?
#fieldSep = ','
fieldSep = '\t'
extension = "dqdimacs"

haveHeader = False

# Translation from labels by partitioner to labels relevant to DQBF
labelTransDict = { 'sele':'evar' , 'sblk':'eblk',  'dele':'uvar',  'dblk':'ublk' }

def formatList(ls):
    slist = [str(e) for e in ls]
    return fieldSep.join(slist)

def buildHeader(llist):
    return [ (labelTransDict[lab] if lab in labelTransDict else lab) for lab in llist]


# Get problem class and problem name
def trimFile(fname):
    tfname = fname.split('/')[-1]
    fields = tfname.split('_')
    if len(fields) > 1:
        return [fields[0], "_".join(fields[1:])]
    else:
        return ["", tfname]

# Build up library of formulas.  Store in form that can be cut & pasted into Python
def storeClauses(estimator, ifname):
    localName = ifname.split('/')[-1]
    root = ".".join(localName.split('.')[:-1])
    fname = root + ".clauses"
    clist = estimator.blocks.feasibilityFormula()
    try:
        outf = open(fname, 'w')
    except:
        print("Couldn't open file '%s'" % fname)
        return
    outf.write("[\n")
    for c in clist:
        slist = [str(v) for v in c]
        outf.write('  [' + ", ".join(slist) + '],\n')
    outf.write("]\n")
    outf.close()

def processFile(fname, verbose, singletons):
    global haveHeader
    info = trimFile(fname)
    tfname = info[1] if info[0] == "" else "_".join(info)
    try:
        estimator = preprocess.Estimator(fname, singletons)
        b = estimator.blocks
    except reader.CnfException as ex:
        print("File: %s. Read failed (%s)" % (tfname, str(ex)))
        return
    except preprocess.PartitionException as ex:
        print("File: %s.  Couldn't generate block partition (%s)" % (tfname, str(ex)))
        return
    if verbose:
        print("File: %s.  Blocks" % tfname)
        b.show()
    stats = b.statList()
    header = buildHeader(b.statFieldList())
    header += ['solns', 'icls', 'bcls', 'ratio', 'cat', 'prob']
    bcount = estimator.findSolutions(verbose = verbose)
    solns = len(estimator.totalCountList)
    icount = estimator.ccounter.inputCount
    ratio = "%.2f" % (float(bcount)/icount)
    stats += [solns, icount, bcount, ratio]
    if verbose:
        print(formatList(header))
        print(formatList(stats))
    else:
        if not haveHeader:
              haveHeader = True
              print(formatList(header))
        print(formatList(stats + info))
#    storeClauses(estimator, fname)
    
def run(name, args):
    dname = None
    fname = None
    verbose = False
    prefix = ""
    singletons = False

    optlist, args = getopt.getopt(args, "hvud:p:f:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-u':
            singletons = True
        elif opt == '-d':
            dname = val
        elif opt == '-p':
            prefix = val
        elif opt == '-f':
            fname = val
    if fname is not None:
        processFile(fname, verbose, singletons)
    if dname is not None:
        flist = sorted(glob.glob(dname + "/" + prefix + "*." + extension))
        for name in flist:
            processFile(name, verbose, singletons)    
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
    


