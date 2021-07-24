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
    print("Usage: %s [-h] [-v VERB] [-E] [-M MAXC] [-d DIR] [-p PFX] [-f FILE] [-L FILE]" % prog)
    print(" -h      Print this message")
    print(" -v VERB Set verbosity level (0 = None, 1 = Output comments, 2 = Debugging info)")
    print(" -E      Stop after estimation phase")
    print(" -M MAXC Don't generate expanded version if it would have more than MAXC clauses")
    print(" -f FILE Process specified file")
    print(" -d DIR  Process all matching files in specified directory")
    print(" -p PFX  Only process files with specified prefix")
    print(" -L FILE Write information as CSV to FILE")


# CSV or tab separated?
extension = "dqdimacs"
checkSolutions = False

# Global
haveHeader = False

# Translation from labels by partitioner to labels relevant to DQBF
labelTransDict = { 'sele':'evar' , 'sblk':'eblk',  'dele':'uvar',  'dblk':'ublk' }

# Benchmark categories
categories = ["misc", "bloem", "kullmann", "scholl", "tentrup"]

def formatList(ls, fieldSep = "\t"):
    slist = [str(e) for e in ls]
    return fieldSep.join(slist)

def buildHeader(llist):
    return [ (labelTransDict[lab] if lab in labelTransDict else lab) for lab in llist]


# Get problem class and problem name
def trimFile(fname):
    tfname = fname.split('/')[-1]
    fields = tfname.split('_')
    cat = categories[0]
    if fields[0] in categories:
        cat = fields[0]
    return [cat, tfname]

# Get root name from file name
def rootName(fname):
    fields = fname.split('.')
    root = ".".join(fields[:-1])
    return root

# Build up library of formulas.  Store in form that can be cut & pasted into Python
def storeClauses(estimator, ifname):
    localName = ifname.split('/')[-1]
    root = rootname(localName)
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

def processFile(fname, estimateOnly, maxClause, verbLevel, logFile):
    global haveHeader
    info = trimFile(fname)
    tfname = info[1] if info[0] == "" else "_".join(info)
    try:
        qreader = reader.DqcnfReader(fname)
    except reader.CnfException as ex:
        print("File: %s. Read failed (%s)" % (tfname, str(ex)))
        return
    try:
        estimator = preprocess.Estimator(qreader)
        b = estimator.blocks
    except preprocess.PartitionException as ex:
        print("File: %s.  Couldn't generate block partition (%s)" % (tfname, str(ex)))
        return
    if verbLevel > 1:
        print("File: %s.  Blocks" % tfname)
        b.show()
    stats = b.statList()
    bcount = estimator.findSolutions(verbose = verbLevel > 1, check = checkSolutions)
    solns = len(estimator.totalCountList)
    icount = estimator.ccounter.inputCount
    ratio = "%.2f" % (float(bcount)/icount)
    stats += [solns, icount, bcount, ratio]

    header = buildHeader(b.statFieldList())
    header += ['solns', 'icls', 'ecls', 'ratio']
    if not estimateOnly:
        header += ['eevar', 'euvar']
    header += ['cat', 'prob']
    if not haveHeader:
        haveHeader = True
        print(formatList(header))
        if logFile is not None:
            logFile.write(formatList(header, ',') + '\n')
    if not estimateOnly:
        if bcount <= maxClause:
            root = rootName(fname) + "_expanded"
            expander = preprocess.Expander(qreader)
            expander.expand(estimator.bestBlockList)
            euvar, eevar = expander.generate(root, verbLevel > 0)
            stats += [eevar, euvar]
        else:
            stats += ['', '']
    stats += info
    print(formatList(stats))
    if logFile is not None:
        logFile.write(formatList(stats, ',') + '\n')

    
def run(name, args):
    dname = None
    fname = None
    verbLevel = 0
    prefix = ""
    estimateOnly = False
    maxClause = 50000
    logFile = None

    optlist, args = getopt.getopt(args, "hv:EM:d:p:f:L:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-E':
            estimateOnly = True
        elif opt == '-M':
            maxClause = int(val)
        elif opt == '-d':
            dname = val
        elif opt == '-p':
            prefix = val
        elif opt == '-f':
            fname = val
        elif opt == '-L':
            try:
                logFile = open(val, 'w')
            except:
                print("Couldn't open log file '%s'" % val)
                return
    if fname is not None:
        processFile(fname, estimateOnly, maxClause, verbLevel, logFile)
    if dname is not None:
        flist = sorted(glob.glob(dname + "/" + prefix + "*." + extension))
        for name in flist:
            processFile(name, estimateOnly, maxClause, verbLevel, logFile)    
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
    


