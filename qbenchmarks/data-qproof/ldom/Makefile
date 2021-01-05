INTERP=python3
# Abbreviations:
# Proof types
#   r: Refutation
#   s: Satisfaction
# Tseitin variable placement
#   e: End
#   a: After defining variables 
#   b: Before defining variables (when possible)

BDIR=../..
NDIR=$(BDIR)/ldominoes
SDIR=$(BDIR)/../qbf

GEN=$(NDIR)/gen_ldom.py
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) $(SDIR)/qchecker.py

CGRAB=../grab_plusclauses.py
TGRAB=../grab_plustime.py

VLEVEL=1
N=5
CAT=

all: sa

sa: ldom$(CAT)-$(N)-sa.data
ra: ldom$(CAT)-$(N)-ra.data


ldom$(CAT)-$(N)-sa.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ldom$(CAT)-$(N)-sa.qcnf \
		-o ldom$(CAT)-$(N)-sa.qproof \
		-p ldom$(CAT)-$(N)-sa.order \
		-L ldom$(CAT)-$(N)-sa.data
	$(CHECK) -m s -i ldom$(CAT)-$(N)-sa.qcnf -p ldom$(CAT)-$(N)-sa.qproof | tee -a ldom$(CAT)-$(N)-sa.data
	rm -f ldom$(CAT)-$(N)-sa.qproof

ldom$(CAT)-$(N)-ra.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-ra
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ldom$(CAT)-$(N)-ra.qcnf \
		-o ldom$(CAT)-$(N)-ra.qproof \
		-p ldom$(CAT)-$(N)-ra.order \
		-L ldom$(CAT)-$(N)-ra.data
	$(CHECK) -m r -i ldom$(CAT)-$(N)-ra.qcnf -p ldom$(CAT)-$(N)-ra.qproof | tee -a ldom$(CAT)-$(N)-ra.data
	rm -f ldom$(CAT)-$(N)-ra.qproof

data:

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *b.data *.qproof
