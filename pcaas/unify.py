#!/usr/bin/python

import sys
# Merge files together.  Single byte of 0 as separator

sep = bytearray(b'\x00\x00\x00')

def nulltest(outf, name):
    zcount = 0
    for c in name:
        if c == 'z':
            zcount += 1
        else:
            return False
    zbuf = bytearray([0]*zcount)
    outf.write(zbuf)
    return True

def run(outname, flist):
    try:
        outf = open(outname, 'wb')
    except:
        sys.stderr.write("Couldn't open output file '%s'\n" % outname)
        sys.exit(1);
    for fname in flist:
        if nulltest(outf, fname):
            continue
        try:
            f = open(fname, 'rb')
        except:
            sys.stderr.write("Couldn't open file '%s'\n" % fname);
            sys.exit(1)
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
        sys.stderr.write("  If IFILE is 'z...z', then insert that many null bytes\n")
        sys.exit(0)
    run(sys.argv[1], sys.argv[2:])
