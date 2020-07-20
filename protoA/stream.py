# Support for binary representation of proofs
# and for communicating with proof server

import binascii
import sys

class Logger:
    outFile = None

    def __init__(self, outName = None):
        self.outFile = None
        if outName is not None:
            try:
                self.outFile = open(outName, 'a')
            except:
                sys.stderr.write("Couldn't open log file '%s'\n", outName)
                self.outFile = None

    def write(self, text):
        sys.stderr.write(text)
        if self.outFile is not None:
            self.outFile.write(text)

    def close(self):
        if self.outFile is not None:
            self.outFile.close()


class CompressArray:
    bytes = None

    def __init__(self, ilist = []):
        self.bytes = bytearray([])
        for x in ilist:
            self.append(x)

    def append(self, x):
        u = 2*x if x >= 0 else 2*(-x) + 1
        while u >= 128:
            b = u & 0x7F
            u = u >> 7
            self.bytes.append(b + 128)
        self.bytes.append(u)
        
    def toList(self):
        result = []
        weight = 0
        u = 0
        for b in self.bytes:
            ab = b & 0x7F;
            u += ab << weight
            if b < 128:
                x = u//2 if u & 0x1 == 0 else -u//2
                result.append(x)
                weight = 0
                u = 0
            else:
                weight += 7
        return result
        
    def hexify(self):
        return str(binascii.hexlify(self.bytes))

    def __str__(self):
        return self.hexify()

    def __len__(self):
        return len(self.bytes)

    
