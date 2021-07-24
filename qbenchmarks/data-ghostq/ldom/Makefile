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
TLIM=7200

TGRAB=../grab_time.py

GEN=$(NDIR)/gen_ldom.py
N=5
CAT=

all: a

a: ldoma$(CAT)-$(N).data
ia: ildoma$(CAT)-$(N).data


ldoma$(CAT)-$(N).data:
	$(GEN)  -t a -n $(N) -r ldoma$(CAT)-$(N)
	$(CONV) ldoma$(CAT)-$(N).qcnf -write-gq -o ldoma$(CAT)-$(N).gq 2>&1 | tee ldoma$(CAT)-$(N).data
	$(GQBF) ldoma$(CAT)-$(N).gq -s-cnf -time-out $(TLIM) | tee -a ldoma$(CAT)-$(N).data

ildoma$(CAT)-$(N).data:
	$(GEN)  -i -t a -n $(N) -r ildoma$(CAT)-$(N)
	$(CONV) ildoma$(CAT)-$(N).qcnf -write-gq -o ildoma$(CAT)-$(N).gq 2>&1 | tee ildoma$(CAT)-$(N).data
	$(GQBF) ildoma$(CAT)-$(N).gq -s-cnf -time-out $(TLIM) | tee -a ildoma$(CAT)-$(N).data


data:
	$(TGRAB) *ldoma-TS-*.data > ldom-ghostq-allsat-seconds.csv
	$(TGRAB) *ldoma-TR-*.data > ldom-ghostq-allref-seconds.csv
	$(TGRAB) *BY5S*.data > ldom-ghostq-sat-seconds.csv
	$(TGRAB) *BY5R*.data > ldom-ghostq-ref-seconds.csv


clean:
	rm -f *~ *.order *.qcnf *.gq

superclean: clean
	rm -f  *.data
