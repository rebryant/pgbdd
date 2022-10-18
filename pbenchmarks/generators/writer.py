# Code for generating CNF, order, and schedule files
class WriterException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Writer Exception: " + str(self.value)


# Generic writer
class Writer:
    outfile = None
    suffix = None
    verbLevel = 1
    variableCount = 0
    isNull = False

    def __init__(self, fname, verbLevel = 1, isNull = False):
        self.variableCount = 0
        self.verbLevel = verbLevel
        self.isNull = isNull
        if isNull:
            return
        try:
            self.outfile = open(fname, 'w')
        except:
            print("Couldn't open file '%s'. Aborting" % fname)
            sys.exit(1)

    def trim(self, line):
        while len(line) > 0 and line[-1] == '\n':
            line = line[:-1]
        return line

    def show(self, line):
        if self.isNull:
            return
        line = self.trim(line)
        if self.verbLevel >= 3:
            print(line)
        if self.outfile is not None:
            self.outfile.write(line + '\n')

    def finish(self):
        if self.isNull:
            return
        if self.outfile is None:
            return
        self.outfile.close()
        self.outfile = None


class ConstraintException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Constraint Exception: " + str(self.value)


class Constraint:
    vars = []
    coeffs = []
    cval = []
    rel = '>='

    def __init__(self, vars, coeffs, cval, rel = ">="):
        self.vars = vars
        self.coeffs = coeffs
        self.cval = cval
        self.rel = rel
        if rel not in ['=', '>=']:
            raise ConstraintException("Invalid relation '%s'" % rel)

    def add(self, other):
        if self.rel != other.rel:
            raise ConstraintException("Incompatible relations '%s' '%s'" % (self.rel, other.rel))
        vlist = []
        clist = []
        idx1 = 0
        idx2 = 0
        while idx1 < len(self.vars) and idx2 < len(other.vars):
            v1 = self.vars[idx1]
            v2 = other.vars[idx2]
            c1 = self.coeffs[idx1]
            c2 = other.coeffs[idx2]
            if v1 < v2:
                vlist.append(v1)
                clist.append(c1)
                idx1 += 1
            elif v2 < v1:
                vlist.append(v2)
                clist.append(c2)
                idx2 += 1
            else:
                c = c1+c2
                if c != 0:
                    vlist.append(v1)
                    clist.append(c)
                idx1 += 1
                idx2 += 1
        while idx1 < len(self.vars):
            v1 = self.vars[idx1]
            c1 = self.coeffs[idx1]
            vlist.append(v1)
            clist.append(c1)
            idx1 += 1
        while idx2 < len(other.vars):
            v2 = other.vars[idx2]
            c2 = other.coeffs[idx2]
            vlist.append(v2)
            clist.append(c2)
            idx2 += 1
        cval = self.cval + other.cval
        return Constraint(vlist, clist, cval, self.rel)
            
    def genOpb(self):
        slist = ["%d x%d " % (coeff, var) for coeff,var in zip(self.coeffs, self.vars)]
        return " ".join(slist) + self.rel + " " + str(self.cval)
                
def genCard(coeff, vars, cval, rel):
    coeffs = [coeff] * len(vars)
    return Constraint(vars, coeffs, cval, rel)


# Generators for different OPB constraints
def genAmo(varList):
    return genCard(-1, varList, -1, ">=")

def genAlo(varList):
    return genCard(1, varList, 1, ">=")

def genExactlyOne(varList):
    return genCard(1, varList, 1, "=")

# Creating PBIP
class PbipWriter(Writer):
    commandCount = 0
    
    def __init__(self, fname, verbLevel = False):
        Writer.__init__(self, fname, verbLevel=verbLevel)
        self.commandCount = 0

    def doComment(self, line):
        self.show("* " + line)

    def doCommand(self, cmd, opbstring, hints):
        shints = [str(hint) for hint in hints]
        self.show("%s %s ; %s" % (cmd, opbstring, " ".join(shints)))

    def doInput(self, opbstring, hints):
        self.doCommand('i', opbstring, hints)

    def doAssert(self, opbstring, hints):
        self.doCommand('a', opbstring, hints)
