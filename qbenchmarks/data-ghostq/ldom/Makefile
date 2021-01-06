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
GDIR = ../../../../ghostq/bin
CONV =  $(GDIR)/qcir-conv.py
GQBF= $(GDIR)/ghostq
TLIM=3600

TGRAB=../grab_plustime.py

GEN=$(NDIR)/gen_ldom.py
N=5

all: a

a: ldoma-$(N).data


ldoma-$(N).data:
	$(GEN)  -t a -n $(N) -r ldoma-$(N)
	$(CONV) ldoma-$(N).qcnf -write-gq -o ldoma-$(N).gq 2>&1 | tee ldoma-$(N).data
	$(GQBF) ldoma-$(N).gq -s-cnf -time-out $(TLIM) | tee -a ldoma-$(N).data

data:
	$(TGRAB) ldoma-*.data > ldom-ghostq-a-seconds.csv

clean:
	rm -f *~ *.order *.qcnf *.gq

superclean: clean
	rm -f  *.data
