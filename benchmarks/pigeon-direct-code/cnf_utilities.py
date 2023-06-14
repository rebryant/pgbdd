#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################

import writer

# Utilities for encoding problems into CNF

# Each of the following will add clauses to a CNF file (using the
# writer.LazyCnfWriter class) for a specified type of constraint
# If the verbose flag is set, then comments will be also added to the CNF file
# Argument lits is a list of literals (each given as a signed integer)

def atLeastOne(writer, lits, verbose = False):
    if verbose:
        writer.doComment("At-least-one constraint")
    writer.doClause(lits)

def atMostOneDirect(writer, lits, verbose = False):
    if verbose:
        slist = [str(lit) for lit in lits]
        writer.doComment("Direct encoding of at-most-one constraint for literals [%s]" % (", ".join(slist)))
    for i in range(len(lits)):
        for j in range(i+1, len(lits)):
            writer.doClause([-lits[i], -lits[j]])

# The following code can generate a linear representation of an at-most-one constraint.
# You need to supply the detailed code for functions lconEncode and rconEncode

# Your implementation of the left constraint LCON
def lconEncode(writer, x1, x2, z, verbose = False):
    if verbose:
        writer.doComment("Left constraint for variables [%d, %d, %d]" % (x1, x2, z))
    ## Make calls to writer.doClause
    # For example, calling writer.doClause([-x1, x2, z])
    # will generate the clause with these three literals
    ####### YOUR CODE HERE ####### 
    writer.doClause([-x1, z])      ## OMIT
    writer.doClause([-x2, z])      ## OMIT
    writer.doClause([-x1, -x2])    ## OMIT
    #######  END OF YOUR CODE ####### 

# Your implementation of the right constraint RCON
def rconEncode(writer, zp, xn, verbose = False):
    if verbose:
        writer.doComment("Right constraint for variables [%d, %d]" % (zp,xn))
    ## Make calls to writer.doClause
    ####### YOUR CODE HERE ####### 
    writer.doClause([-zp, -xn])     ## OMIT
    ####### END of your code ####### 


def atMostOneLinear(writer, lits, verbose = False):
    if verbose:
        slist = [str(lit) for lit in lits]
        writer.doComment("Linear encoding of at-most-one constraint for literals [%s]" % (", ".join(slist)))
    if len(lits) <= 3:
        atMostOneDirect(writer, lits, False)
    else:
        while len(lits) > 2:
            l1, l2 = lits[0], lits[1]
            z = writer.newVariable()
            lconEncode(writer, l1, l2, z, verbose)
            lits = [z] + lits[2:]
        zp, xn = lits[0], lits[1]
        rconEncode(writer, zp, xn, verbose)

# Determine parity of binary representation of integer w
def bitParity(w):
    value = 0
    while w != 0:
        value ^=  w & 0x1
        w = w >> 1
    return value

def getBit(word,pos):
    bit = (word>>pos) & 1
    return bit



def parityDirect(writer, lits, phase, verbose = False):
    if verbose:
        slist = [str(lit) for lit in lits]
        ptype = "odd" if phase == 1 else "even"
        writer.doComment("Direct encoding of %s parity for literals [%s]" % (ptype, ", ".join(slist)))
    n = len(lits)
    for i in range(1 << n):
        # Count number of 0's in i
        zparity = bitParity(~i & ((1 << n) - 1))
        if zparity == phase:
            continue
        nlits = []
        for j in range(n):
            weight = 1 if getBit(i,j) == 1 else -1
            nlits.append(lits[j] * weight)
        writer.doClause(nlits)
    
def parityTree(writer, lits, phase, group = 3, verbose = False, top = True):
    if verbose and top:
        slist = [str(lit) for lit in lits]
        ptype = "odd" if phase == 1 else "even"
        writer.doComment("Tree encoding (group size = %d) of %s parity for literals [%s]" % (group, ptype, ", ".join(slist)))
    if len(lits) <= group:
        parityDirect(writer, lits, phase, verbose = verbose)
    else:
        z = writer.newVariable()
        parityDirect(writer, lits[0:group-1] + [z], phase=0, verbose = verbose)
        parityTree(writer, lits[group-1:]  + [z], phase=phase, group = group, verbose = verbose, top = False)

def parityChain(writer, lits, phase, group = 3, verbose = False, top = True):
    if verbose and top:
        slist = [str(lit) for lit in lits]
        ptype = "odd" if phase == 1 else "even"
        writer.doComment("Chain encoding (group size = %d) of %s parity for literals [%s]" % (group, ptype, ", ".join(slist)))
    if len(lits) <= group:
        parityDirect(writer, lits, phase, verbose = verbose)
    else:
        z = writer.newVariable()
        parityDirect(writer, lits[0:group-1] + [z], phase=0, verbose = verbose)
        parityChain(writer, [z] + lits[group-1:], phase=phase, group = group, verbose = verbose, top = False)
        
