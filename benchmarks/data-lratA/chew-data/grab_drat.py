#!/usr/bin/python

import sys

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

# Extract drat data from log.  Turn into something useable for other tools
def extract(fname):
    try:
        f = open(fname, 'r')
    except:
        sys.stderr.write("Couldn't open file '%s'\n" % fname)
        return None
    fieldList = []
    valueDict = {}
    for line in f:
        line = trim(line)
        fields = line.split()
        if len(fields) > 0 and fields[0] == 'n':
            for field in fields:
                if field[0] == '#':
                    field = field[1:]
                fieldList.append(field)
        elif len(fieldList) > 0:
            if len(fields) != len(fieldList):
                sys.stderr.write("File %s.  Mismatched lengths.  Field names = %d, fields = %d\n" % (fname, len(fieldList), len(fields)))
                f.close()
                return None
            for i in range(len(fields)):
                try:
                    val = int(fields[i])
                except:
                    sys.stderr.write("File %s.  Couldn't extract integer fields from line '%s'\n" % line)
                    f.close()
                    return None
                valueDict[fieldList[i]] = val
            f.close()
            return valueDict
        else:
            continue
    sys.stderr.write("File %s.  Didn't find expected data\n" % fname)
    f.close()
    return None

def usage(name):
    sys.stderr.write("Usage: %s file1 file2 ...\n" % name)
    sys.exit(0)

def run(name, args):
    if len(args) < 1:
        usage(name)
    for fname in args:
        valueDict = extract(fname)
        if valueDict is not None:
            print("%s,%s" % (valueDict['n'], valueDict['lines']))

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
