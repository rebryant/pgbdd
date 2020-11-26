# Extract features from GoE qcnf file.
# File must have been generated to contain information similar to:

# c 6  X  6 Garden of Eden problem with ninety symmetry
# p cnf 73 6840
# a 1 2 3 4 5 6 7 8 9 0
# e 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 0

import sys

class Eden:
    nrow = 0
    ncol = 0
    ulist = []
    elist = []
    mode = None
    varCount = 0
    
    # If requested to find ordering of universal variables, must
    # find the lowest number existential variable with which it shares a clause
    uvarSuccessor = {}


    def __init__(self, infile, tagUvars = False):
        self.nrow = 0
        self.ncol = 0
        self.ulist = None
        self.elist = None
        self.varCount = 0
        for line in infile:
            fields = line.split()
            if len(fields) == 0:
                continue
            if fields[0] == 'c' and fields[2] == 'X':
                try:
                    self.nrow = int(fields[1])
                    self.ncol = int(fields[3])
                except:
                    continue
            elif fields[0] == 'a':
                sfields = fields[1:-1]
                try:
                    self.ulist = [int(s) for s in sfields]
                except:
                    sys.stderr.write("Couldn't get list of universal variables from line:" + line)
                    sys.exit(1)
                self.varCount += len(self.ulist)
            elif fields[0] == 'e':
                sfields = fields[1:-1]
                try:
                    self.elist = [int(s) for s in sfields]
                except:
                    sys.stderr.write("Couldn't get list of existential variables from line:" + line)
                    sys.exit(1)
                self.varCount += len(self.elist)
            else:
                try:
                    # Stop once hit first clause
                    lit = int(fields[0])
                    if tagUvars:
                        self.matchUvars(infile, line)
                except:
                    continue

        if self.nrow == 0 or self.ncol == 0 or self.ulist is None or self.elist is None:
            sys.stderr.write("Failed to extract metadata from QCNF file\n")
            sys.exit(1)

        
    def matchUvars(self, infile, firstLine):
        self.uvarSuccessor = { u : self.varCount+1 for u in self.ulist}
        self.matchLine(firstLine)
        for line in infile:
            self.matchLine(line)
            
        
    def matchLine(self, line):
        mine = self.varCount + 1
        uvars = []
        try:
            vlist = [abs(int(s)) for s in line.split()][:-1]
        except:
            sys.stderr.write("Warning.  Had trouble reading line: " + line)
            return
        for v in vlist:
            if v in self.uvarSuccessor:
                uvars.append(v)
            else:
                mine = min(mine, v)
        for u in uvars:
            self.uvarSuccessor[u] = min(mine, self.uvarSuccessor[u])
        


    def bucketOrder(self):
        # Universals first
        nuniversal = len(self.ulist)
        vals = [str(u+1) for u in range(nuniversal)]
        print(" ".join(vals))
        # Then existentials in column-major order
        erow = 2+self.nrow
        ecol = 2+self.ncol
        for c in range(ecol):
            vals = [str(c+r*ecol+nuniversal+1) for r in range(erow)]
            print(" ".join(vals))
            

    def variableOrder(self):
        for e in self.elist + [self.varCount + 1]:
            slist = []
            for u in self.ulist:
                if self.uvarSuccessor[u] == e:
                    slist.append(str(u))
            slist.append(str(e))
            print(" ".join(slist))

        
        
            
            
    
