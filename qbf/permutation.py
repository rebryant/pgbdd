import sys

class PermutationException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Permutation Exception: " + str(self.value)


class Permuter:
    forwardMap = {}
    reverseMap = {}
    
    def __init__(self, valueList = [], permutedList = []):
        self.forwardMap = {}
        self.reverseMap = {}
        identity = False
        if len(permutedList) == 0:
            permutedList = valueList
            identity = True
        if len(valueList) != len(permutedList):
            raise PermutationException("Unequal list lengths: %d, %d" % (len(valueList), len(permutedList)))
        for v, p in zip(valueList, permutedList):
            self.forwardMap[v] = p
            self.reverseMap[p] = v
        if identity:
            return
        # Check permutation
        for v in valueList:
            if v not in self.reverseMap:
                raise PermutationException("Not permutation: Nothing maps to %s" % str(v))
        for v in permutedList:
            if v not in self.forwardMap:
                raise PermutationException("Not permutation: %s does not map anything" % str(v))
            
            
    def forward(self, v):
        if v not in self.forwardMap:
            raise PermutationException("Value %s not in permutation" % (str(v)))
        return self.forwardMap[v]

    def permLess(self, v1, v2):
        pv1 = self.reverse(v1)
        pv2 = self.reverse(v2)
        return pv1 < pv2

    def sortList(self, ls):
        return sorted(ls, key = lambda x: self.reverse(x))


    def reverse(self, v):
        if v not in self.reverseMap:
            raise PermutationException("Value %s not in permutation range" % (str(v)))
        return self.reverseMap[v]
    
    def __len__(self):
        return len(self.forwardMap)

def readPermutation(fname, writer = None):
    valueList = []
    permutedList = []
    vcount = 0
    lineCount = 0
    if writer is None:
        writer = sys.stderr
    try:
        infile = open(fname, 'r')
    except:
        writer.write("Could not open permutation file '%s'\n" % fname)
        return None
    for line in infile:
        lineCount += 1
        fields = line.split()
        if len(fields) == 0:
            continue
        if fields[0][0] == '#':
            continue
        try:
            values = [int(v) for v in fields]
        except Exception:
                writer.write("Line #%d.  Invalid list of variables '%s'\n" % (lineCount, line))
                return None
        for v in values:
            vcount += 1
            valueList.append(vcount)
            permutedList.append(v)
    infile.close()
    try:
        permuter = Permuter(valueList, permutedList)
    except Exception as ex:
        writer.write("Invalid permutation: %s\n" % str(ex))
        return None
    return permuter
