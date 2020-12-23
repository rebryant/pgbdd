INTERP=python3
# State encoding
#   u: Unary counter
#   o: Labeled objects
# Tseitin variable placement
#   e: End
#   a: After defining variables 
#   b: Before defining variables (when possible)

BDIR=../..
NDIR=$(BDIR)/nim
SDIR=$(BDIR)/../qbf

WRAP = $(BDIR)/wrap.py
DDIR = ../../../../depqbf
DEPQBF= $(DDIR)/depqbf
TLIM=1800

GEN=$(NDIR)/gen_nim.py
SOLVE=$(INTERP) $(WRAP) $(TLIM) $(DEPQBF)
PROFILE=4+3+2
CAT=

all: oa

oa: nimoa$(CAT)-$(PROFILE).data

nimoa$(CAT)-$(PROFILE).data:
	$(GEN) -e o -t a -p $(PROFILE) -r nimoa$(CAT)-$(PROFILE)
	$(SOLVE) nimoa$(CAT)-$(PROFILE).qcnf | tee nimoa$(CAT)-$(PROFILE).data

clean:
	rm -f *~ 

superclean: clean
	rm -f *.qcnf *.data
