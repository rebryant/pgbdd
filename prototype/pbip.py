#!/usr/bin/python3

import bdd
import resolver
import pseudoboolean
import solver

# Return list of constraints from line of OBP
class ObpException(Exception):
    form = ""
    line = ""

    def __init__(self, line, msg):
        self.form = "OPB error"
        self.msg = "line = '%s', %s" % (line, msg)

    def __str__(self):
        m = self.form
        if self.msg != "":
            m += " (" + self.msg + ")"
        return m

# Read string representation of OPB constraint
# Return list of Constraint objects
# List contains one constraint for operations <, <=, >, >=
# and a pair of constraints for =
def parseObp(line):
    fields = line.split()
    # Get rid of trailing semicolon
    if len(fields) == 0:
        raise ObpException(line, "Empty")
    if fields[-1] == ';':
        fields = fields[:-1]
    elif fields[-1][-1] == ';':
        fields[-1] = fields[-1][:-1]
    if len(fields) < 2 or len(fields) % 2 != 0:
        raise ObpException(line, "Invalid number of fields")
    try:
        cval = int(fields[-1])
    except:
        raise ObpException(line, "Invalid constant %s" % fields[-1])
    rel = fields[-2]
    if rel not in ['<', '<=', '=', '>=', '>']:
        raise ObpException(line, "Invalid relation")
    cfields = fields[:-2]
    coeffs = []
    vars = []
    for i in len(cfields)//2:
        scoeff = cfields[2*i]
        try:
            coeff = int(scoeff)
        except:
            raise OpbException(line, "Invalid coefficient %s" % scoeff)
        svar = cfields[2*i+1]
        if svar[0] == 'x':
            try:
                var = int(svar[1:])
            except:
                raise OpbException(line, "Invalid term %s" % svar)
        else:
            raise OpbException(line, "Invalid term %s" % svar)
        coeffs.append(coeff)
        vars.append(var)
    # Normalize
    if rel == '<':
        rel = '<='
        cval -= 1
    if rel == '>':
        rel = '>='
        cval += 1
    if rel == '<=':
        rel = '>='
        cval -= sum(coeffs)
        coeffs = [-c for c in coeffs]
    nz = { v : c for v,c in zip(vars,coeffs) }
    con1 = pseudoboolean.Constraint(len(nz), cval)
    con1.setNz(nz)
    if rel == '>=':
        return [con1]
    else:
        cval -= sum(coeffs)
        coeffs = [-c for c in coeffs]
        nz = { v : c for v,c in zip(vars,coeffs) }
        con2 = pseudoboolean.Constraint(len(nz), cval)
        con2.setNz(nz)
        return [con1, con2]
    
    
        
    
