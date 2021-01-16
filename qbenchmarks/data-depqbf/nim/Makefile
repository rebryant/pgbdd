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
TLIM=3600

TGRAB=../grab_plustime.py

GEN=$(NDIR)/gen_nim.py
SOLVE=$(INTERP) $(WRAP) $(TLIM) $(DEPQBF)
PROFILE=4+3+2
CAT=

all: oa

oa: nimoa$(CAT)-$(PROFILE).data
ua: nimua$(CAT)-$(PROFILE).data
ue: nimue$(CAT)-$(PROFILE).data

ualdr: nimua-ldr$(CAT)-$(PROFILE).data
ueldr: nimue-ldr$(CAT)-$(PROFILE).data

nimoa$(CAT)-$(PROFILE).data:
	$(GEN) -e o -t a -p $(PROFILE) -r nimoa$(CAT)-$(PROFILE)
	$(SOLVE) nimoa$(CAT)-$(PROFILE).qcnf | tee nimoa$(CAT)-$(PROFILE).data

nimua$(CAT)-$(PROFILE).data:
	$(GEN) -e u -t a -p $(PROFILE) -r nimua$(CAT)-$(PROFILE)
	$(SOLVE) nimua$(CAT)-$(PROFILE).qcnf | tee nimua$(CAT)-$(PROFILE).data

nimue$(CAT)-$(PROFILE).data:
	$(GEN) -e u -t e -p $(PROFILE) -r nimue$(CAT)-$(PROFILE)
	$(SOLVE) nimue$(CAT)-$(PROFILE).qcnf | tee nimue$(CAT)-$(PROFILE).data

nimua-ldr$(CAT)-$(PROFILE).data:
	$(GEN) -e u -t a -p $(PROFILE) -r nimua$(CAT)-$(PROFILE)
	$(SOLVE)  --long-dist-res --dep-man=simple nimua$(CAT)-$(PROFILE).qcnf | tee nimua-ldr$(CAT)-$(PROFILE).data

nimue-ldr$(CAT)-$(PROFILE).data:
	$(GEN) -e u -t e -p $(PROFILE) -r nimue$(CAT)-$(PROFILE)
	$(SOLVE)  --long-dist-res --dep-man=simple nimue$(CAT)-$(PROFILE).qcnf | tee nimue-ldr$(CAT)-$(PROFILE).data

data:
	$(TGRAB) nimua-b3*.data > nimu-depqbf-b3.csv
	$(TGRAB) nimua-t4*.data > nimu-depqbf-t4.csv
	$(TGRAB) nimua-f4*.data > nimu-depqbf-f4.csv

clean:
	rm -f *~ 

superclean: clean
	rm -f *.qcnf *.data
