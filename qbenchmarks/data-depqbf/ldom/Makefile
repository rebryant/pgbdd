INTERP=python3
# State encoding
#   u: Unary counter
#   o: Labeled objects
# Tseitin variable placement
#   e: End
#   a: After defining variables 
#   b: Before defining variables (when possible)

BDIR=../..
NDIR=$(BDIR)/ldominoes
SDIR=$(BDIR)/../qbf

WRAP = $(BDIR)/wrap.py
DDIR = ../../../../depqbf
DEPQBF= $(DDIR)/depqbf
TLIM=7200

TGRAB=../grab_plustime.py
WGRAB=../grab_wtime.py

GEN=$(NDIR)/gen_ldom.py
SOLVE=$(INTERP) $(WRAP) $(TLIM) $(DEPQBF)
N=5
CAT=

all: a

a: ldoma$(CAT)-$(N).data
ia: ildoma$(CAT)-$(N).data


ldoma$(CAT)-$(N).data:
	$(GEN) -t a -n $(N) -r ldoma$(CAT)-$(N)
	$(SOLVE) ldoma$(CAT)-$(N).qcnf | tee ldoma$(CAT)-$(N).data

ildoma$(CAT)-$(N).data:
	$(GEN) -i -t a -n $(N) -r ildoma$(CAT)-$(N)
	$(SOLVE) ildoma$(CAT)-$(N).qcnf | tee ildoma$(CAT)-$(N).data

data:
	$(WGRAB) *ldoma-TS-*.data > ldom-depqbf-allsat-seconds.csv
	$(WGRAB) *ldoma-TR-*.data > ldom-depqbf-allref-seconds.csv
	$(WGRAB) *BY5S*.data > ldom-depqbf-sat-seconds.csv
	$(WGRAB) *BY5R*.data > ldom-depqbf-ref-seconds.csv

clean:
	rm -f *~  *.order

superclean: clean
	rm -f *.qcnf *.data
