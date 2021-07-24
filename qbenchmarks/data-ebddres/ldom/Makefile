INTERP=python3
# Simulate operation of EBDDRES
# BDD Variables in reverse order of quantification
# Serialize quantifiers to order cause quantifiers to be eliminated
# in same order as variables

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

ORDER=$(INTERP) $(BDIR)/linear_order.py

CGRAB=../../data-qproof/grab_clauses.py
VGRAB=../../data-qproof/grab_solve_v_check.py

VLEVEL=1
N=5
CAT=

all: sa

sa: ldom$(CAT)-$(N)-sa.data
ra: ldom$(CAT)-$(N)-ra.data

isa: ildom$(CAT)-$(N)-sa.data
ira: ildom$(CAT)-$(N)-ra.data

ldom$(CAT)-$(N)-sa.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-sa
	$(ORDER) -r ldom$(CAT)-$(N)-sa.qcnf > ldom$(CAT)-$(N)-sa.vorder
	$(ORDER) ldom$(CAT)-$(N)-sa.qcnf > ldom$(CAT)-$(N)-sa.qorder
	$(SOLVE) -v $(VLEVEL) -m s -b -l eu \
		-i ldom$(CAT)-$(N)-sa.qcnf \
		-o ldom$(CAT)-$(N)-sa.qproof \
		-p ldom$(CAT)-$(N)-sa.vorder \
	        -B ldom$(CAT)-$(N)-sa.qorder \
		-L ldom$(CAT)-$(N)-sa.data
	$(CHECK) -m s -i ldom$(CAT)-$(N)-sa.qcnf -p ldom$(CAT)-$(N)-sa.qproof | tee -a ldom$(CAT)-$(N)-sa.data
	rm -f ldom$(CAT)-$(N)-sa.qproof

ldom$(CAT)-$(N)-ra.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-ra
	$(ORDER) -r ldom$(CAT)-$(N)-ra.qcnf > ldom$(CAT)-$(N)-ra.vorder
	$(ORDER) ldom$(CAT)-$(N)-ra.qcnf > ldom$(CAT)-$(N)-ra.qorder
	$(SOLVE) -v $(VLEVEL) -m r -b -l eu \
		-i ldom$(CAT)-$(N)-ra.qcnf \
		-o ldom$(CAT)-$(N)-ra.qproof \
		-p ldom$(CAT)-$(N)-ra.vorder \
	        -B ldom$(CAT)-$(N)-ra.qorder \
		-L ldom$(CAT)-$(N)-ra.data
	$(CHECK) -m r -i ldom$(CAT)-$(N)-ra.qcnf -p ldom$(CAT)-$(N)-ra.qproof | tee -a ldom$(CAT)-$(N)-ra.data
	rm -f ldom$(CAT)-$(N)-ra.qproof

ildom$(CAT)-$(N)-sa.data:
	$(GEN) -i -t a -n $(N) -r ildom$(CAT)-$(N)-sa
	$(ORDER) -r ildom$(CAT)-$(N)-sa.qcnf > ildom$(CAT)-$(N)-sa.vorder
	$(ORDER) ildom$(CAT)-$(N)-sa.qcnf > ildom$(CAT)-$(N)-sa.qorder
	$(SOLVE) -v $(VLEVEL) -m s -b -l eu \
		-i ildom$(CAT)-$(N)-sa.qcnf \
		-o ildom$(CAT)-$(N)-sa.qproof \
		-p ildom$(CAT)-$(N)-sa.vorder \
	        -B ildom$(CAT)-$(N)-sa.qorder \
		-L ildom$(CAT)-$(N)-sa.data
	$(CHECK) -m s -i ildom$(CAT)-$(N)-sa.qcnf -p ildom$(CAT)-$(N)-sa.qproof | tee -a ildom$(CAT)-$(N)-sa.data
	rm -f ildom$(CAT)-$(N)-sa.qproof

ildom$(CAT)-$(N)-ra.data:
	$(GEN) -i -t a -n $(N) -r ildom$(CAT)-$(N)-ra
	$(ORDER) -r ildom$(CAT)-$(N)-ra.qcnf > ildom$(CAT)-$(N)-ra.vorder
	$(ORDER) ildom$(CAT)-$(N)-ra.qcnf > ildom$(CAT)-$(N)-ra.qorder
	$(SOLVE) -v $(VLEVEL) -m r -b -l eu \
		-i ildom$(CAT)-$(N)-ra.qcnf \
		-o ildom$(CAT)-$(N)-ra.qproof \
		-p ildom$(CAT)-$(N)-ra.vorder \
	        -B ildom$(CAT)-$(N)-ra.qorder \
		-L ildom$(CAT)-$(N)-ra.data
	$(CHECK) -m r -i ildom$(CAT)-$(N)-ra.qcnf -p ildom$(CAT)-$(N)-ra.qproof | tee -a ildom$(CAT)-$(N)-ra.data
	rm -f ildom$(CAT)-$(N)-ra.qproof


data:
#	$(CGRAB) *ldom*-sa.data > ldom-ebddres-sat-clauses.csv
	$(CGRAB) *ldom*-ra.data > ldom-ebddres-ref-clauses.csv

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
