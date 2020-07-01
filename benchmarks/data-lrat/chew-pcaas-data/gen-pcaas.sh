#!/bin/bash

make ro EXTENSION=lrat
make ro EXTENSION=lratb
make rop PMODE=t HOST=whaleshark.ics.cs.cmu.edu
make rop PMODE=b HOST=whaleshark.ics.cs.cmu.edu
make rop PMODE=t HOST=ghc32.ghc.andrew.cmu.edu
make rop PMODE=b HOST=ghc32.ghc.andrew.cmu.edu
make rop PMODE=t HOST=localhost
make rop PMODE=b HOST=localhost
