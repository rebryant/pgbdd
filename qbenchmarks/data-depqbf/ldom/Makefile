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
TLIM=3600

TGRAB=../grab_plustime.py

GEN=$(NDIR)/gen_ldom.py
SOLVE=$(INTERP) $(WRAP) $(TLIM) $(DEPQBF)
N=5


all: a

a: ldoma-$(N).data
ia: ildoma-$(N).data


ldoma-$(N).data:
	$(GEN) -t a -n $(N) -r ldoma-$(N)
	$(SOLVE) ldoma-$(N).qcnf | tee ldoma-$(N).data

ildoma-$(N).data:
	$(GEN) -i -t a -n $(N) -r ildoma-$(N)
	$(SOLVE) ildoma-$(N).qcnf | tee ildoma-$(N).data

data:
	$(TGRAB) ldoma-*.data > ldom-depqbf-a-seconds.csv
	$(TGRAB) ildoma-*.data > ildom-depqbf-a-seconds.csv

clean:
	rm -f *~  *.order

superclean: clean
	rm -f *.qcnf *.data
