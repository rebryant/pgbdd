#!/usr/bin/python

import sys
# Merge files together.  Single byte of 0 as separator

sep = bytearray(b'\x00\x00\x00')

def run(outname, flist):
    try:
        outf = open(outname, 'wb')
    except:
        sys.stderr.write("Couldn't open output file '%s'\n" % outname)
        sys.exit(1);
    first = True
    for fname in flist:
        try:
            f = open(fname, 'rb')
        except:
            sys.stderr.write("Couldn't open file '%s'\n" % fname);
            sys.exit(1)
        if not first:
            outf.write(sep)
        first = False
        while True:
            bytes = f.read(1024)
            if len(bytes) == 0:
                break
            outf.write(bytes)
        f.close()
    outf.close()
    
            
if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.stderr.write("Usage: %s OFILE IFILE1 ...\n" % sys.argv[0])
        sys.exit(0)
    run(sys.argv[1], sys.argv[2:])
