#!/usr/bin/python

# Given list of CSV files, generate new one, averaging each entry
import csv
import sys

def loadFile(fname):
    try:
        file = open(fname, 'r')
    except:
        raise Exception("Could not open file '%s'"  % fname)
    reader = csv.reader(file)
    vdict = {}
    for row in reader:
        if len(row) != 2:
            raise Exception("CSV file constains line with %d entries" % len(row))
        try:
            vals = [float(field) for field in row]
        except:
            raise Exception("Could not convert all fields in '%s' to floats" % str(row))
        k = int(vals[0])
        vdict[k] = vals[1]
    file.close()
    return vdict
        
def averageValues(dlist):
    countDict = {}
    sumDict = {}
    for vdict in dlist:
        for k in vdict.keys():
            val = vdict[k]
            countDict[k] = 1 if k not in countDict else countDict[k]+1
            sumDict[k] = val if k not in sumDict else sumDict[k]+val
    for k in sorted(countDict.keys()):
        val = sumDict[k]/countDict[k]
        print("%d,%.1f" % (k, val))
    
def run(name, args):
    if len(args) == 0 or len(args) == 1 and args[0] == '-h':
        print("Usage: %s csv1 csv2 ... csvk > outcsv" % name)
        return
    dlist = [loadFile(fname) for fname in args]
    averageValues(dlist)
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
