#!/usr/bin/python

# Put quantifications in qcnf file into strict alternation
# Optionally stretch existential and/or universal levels to contain single variable
# Insert empty levels as necessary

import sys
import getopt

def usage(name):
    print("Usage: %s [-h] [-a] [-e] [-i IN.qcnf] [-o OUT.qncf]" % name)
    print("  -h          Print this message")
    print("  -a          Stretch universal levels")
    print("  -e          Stretch existential levels")
    print("  -e IN.qcnf  Input file name")
    print("  -e OUT.qcnf Output file name")


def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

class Level:
    isExistential = True
    # List of variables.  Kept as strings
    svlist = []

    def __init__(self, isExistential=True, svlist=[]):
        self.isExistential = isExistential
        self.svlist = svlist

    def parse(self, line):
        line = trim(line)
        fields = line.split()
        if len(fields) == 0 or (fields[0] != 'a' and fields[0] != 'e'):
            msg = "Invalid line '%s'" % line
            raise Exception(msg)
        isExistential = fields[0] == 'e'
        svlist = fields[1:]
        if len(svlist) > 0 and svlist[-1] == '0':
            svlist = svlist[:-1]
        return Level(isExistential, svlist)

    def emit(self, outfile):
        slist = ['e' if self.isExistential else 'a'] + self.svlist
        outfile.write(" ".join(slist) + ' 0\n')

    # Merge two levels.  Must have same quantification type
    def join(self, other):
        return Level(self.isExistential, self.svlist + other.svlist)

    def split(self):
        llist = [Level(self.isExistential, [sv]) for sv in self.svlist]
        return llist

# Given input list of quantifier declarations, convert into 
# target list of quantifier declarations
def reconstruct(levelList, stretchUniversal, stretchExistential):
    if len(levelList) == 0:
        return levelList
    # Pass one.  Merge lists of the same type
    mergeList = [levelList[0]]
    for level in levelList[1:]:
        if mergeList[-1].isExistential == level.isExistential:
            mergeList[-1] = mergeList[-1].join(level)
        else:
            mergeList.append(level)
    # Pass two.  Split lists that should be split
    splitList = []
    for level in mergeList:
        if (level.isExistential and stretchExistential) or (not level.isExistential and stretchUniversal):
            splitList = splitList + level.split()
        else:
            splitList.append(level)
    # Pass three.  Insert empty lists as needed
    outList = [splitList[0]]
    for level in splitList[1:]:
        if outList[-1].isExistential == level.isExistential:
            outList.append(Level(not level.isExistential, []))
        outList.append(level)
    return outList

# Read input, reformat quantifiers, generate output
def reformat(infile, outfile, stretchUniversal, stretchExistential):
    levelList = []
    preamble = True
    for line in infile:
#        print ("Reading '%s'" % trim(line))
        if not preamble:
            outfile.write(line)
            continue
        fields = line.split()
        if len(fields) == 0:
            outfile.write(line)
        elif fields[0] == 'c' or fields[0] == 'p':
            outfile.write(line)
        elif fields[0] == 'a' or fields[0] == 'e':
            level = Level().parse(line)
            levelList.append(level)
        else:
            preamble = False
            levelList = reconstruct(levelList, stretchUniversal, stretchExistential)
            for level in levelList:
                level.emit(outfile)
            outfile.write(line)

                
def run(name, args):
    infile = sys.stdin
    outfile = sys.stdout
    stretchExistential = False
    stretchUniversal = False
    optlist, args = getopt.getopt(args, "haei:o:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-a':
            stretchUniversal = True
        elif opt == '-e':
            stretchExistential = True    
        elif opt == '-i':
            try:
                infile = open(val, 'r')
            except:
                sys.stderr.write("Couldn't open input file '%s'\n" % val)
                return
        elif opt == '-o':
            try:
                outfile = open(val, 'w')
            except:
                sys.stderr.write("Couldn't open output file '%s'\n" % val)
                return
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    reformat(infile, outfile, stretchUniversal, stretchExistential)        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        
    

        
            
