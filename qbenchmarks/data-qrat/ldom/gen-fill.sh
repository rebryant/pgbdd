#!/bin/bash
# Fill in gaps in QRAT checking

# Dual ref
make idra CAT=-FILLR N=16
make idra CAT=-FILLR N=18
make idra CAT=-FILLR N=19

make idra CAT=-FILLR N=24

# Dual sat
make  dsa CAT=-FILLS N=16
make  dsa CAT=-FILLS N=18
make  dsa CAT=-FILLS N=19
make idsa CAT=-FILLS N=21
make  dsa CAT=-FILLS N=23

# Ref
make  ira CAT=-FILLR N=16
make  ira CAT=-FILLR N=18
make  ira CAT=-FILLR N=19
make  ira CAT=-FILLR N=20
make   ra CAT=-FILLR N=21
make  ira CAT=-FILLR N=22
make  ira CAT=-FILLR N=23
make  ira CAT=-FILLR N=24
#make   ra CAT=-FILLR N=25
make  ira CAT=-FILLR N=26
#make  ira CAT=-FILLR N=27
make  ira CAT=-FILLR N=28

# Sat
make  sa CAT=-FILLS N=16
make  sa CAT=-FILLS N=18
make  sa CAT=-FILLS N=19
make isa CAT=-FILLS N=21
make  sa CAT=-FILLS N=23
make   sa CAT=-FILLS N=26
make   sa CAT=-FILLS N=27

# Stretch
make  dra CAT=-FILLR N=21
make idra CAT=-FILLR N=22
make idra CAT=-FILLR N=23
make  dsa CAT=-FILLS N=26

make   sa CAT=-FILLS N=28
