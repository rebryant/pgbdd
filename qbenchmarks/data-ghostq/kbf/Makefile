INTERP=python3
T=3

BDIR=../..
GENERATOR = $(BDIR)/kbf/gen-hardKB.py

GDIR = ../../../../ghostq/bin
CONV =  $(GDIR)/qcir-conv.py
GQBF= $(GDIR)/ghostq
TLIM=3600

TGRAB=../grab_plustime.py

all: ghostq

ghostq: kbf-$(T)-ghostq.data

kbf-$(T)-ghostq.data:
	$(GENERATOR) $(T) > kbf-$(T)-ghostq.qcnf 
	$(CONV) kbf-$(T)-ghostq.qcnf --quiet -write-gq | $(GQBF) - -s-cnf -q1 -cegar 0 | tee kbf-$(T)-ghostq.data

data:
	$(TGRAB) kbf-*-ghostq.data > kbf-ghostq-seconds.csv

clean:
	rm -f *~ 

superclean: clean
	rm -f *.qcnf *.data
