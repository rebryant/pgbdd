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

all: sa

sa: ldom-$(N)-sa.data
ra: ldom-$(N)-ra.data
na: ldom-$(N)-na.data

isa: ildom-$(N)-sa.data
ira: ildom-$(N)-ra.data
ina: ildom-$(N)-na.data

ldom-$(N)-sa.data:
	$(GEN) -t a -n $(N) -r ldom-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ldom-$(N)-sa.qcnf \
		-o ldom-$(N)-sa.qproof \
		-p ldom-$(N)-sa.order \
		-L ldom-$(N)-sa.data
	$(CHECK) -m s -i ldom-$(N)-sa.qcnf -p ldom-$(N)-sa.qproof | tee -a ldom-$(N)-sa.data
	rm -f ldom-$(N)-sa.qproof

ldom-$(N)-ra.data:
	$(GEN) -t a -n $(N) -r ldom-$(N)-ra
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ldom-$(N)-ra.qcnf \
		-o ldom-$(N)-ra.qproof \
		-p ldom-$(N)-ra.order \
		-L ldom-$(N)-ra.data
	$(CHECK) -m r -i ldom-$(N)-ra.qcnf -p ldom-$(N)-ra.qproof | tee -a ldom-$(N)-ra.data
	rm -f ldom-$(N)-ra.qproof

ldom-$(N)-na.data:
	$(GEN) -t a -n $(N) -r ldom-$(N)-na
	$(SOLVE) -v $(VLEVEL) -m n -b \
		-i ldom-$(N)-na.qcnf \
		-p ldom-$(N)-na.order \
		-L ldom-$(N)-na.data

ildom-$(N)-sa.data:
	$(GEN) -i -t a -n $(N) -r ildom-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ildom-$(N)-sa.qcnf \
		-o ildom-$(N)-sa.qproof \
		-p ildom-$(N)-sa.order \
		-L ildom-$(N)-sa.data
	$(CHECK) -m s -i ildom-$(N)-sa.qcnf -p ildom-$(N)-sa.qproof | tee -a ildom-$(N)-sa.data
	rm -f ildom-$(N)-sa.qproof

ildom-$(N)-ra.data:
	$(GEN) -i -t a -n $(N) -r ildom-$(N)-ra
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ildom-$(N)-ra.qcnf \
		-o ildom-$(N)-ra.qproof \
		-p ildom-$(N)-ra.order \
		-L ildom-$(N)-ra.data
	$(CHECK) -m r -i ildom-$(N)-ra.qcnf -p ildom-$(N)-ra.qproof | tee -a ildom-$(N)-ra.data
	rm -f ildom-$(N)-ra.qproof

ildom-$(N)-na.data:
	$(GEN) -i -t a -n $(N) -r ildom-$(N)-na
	$(SOLVE) -v $(VLEVEL) -m n -b \
		-i ildom-$(N)-na.qcnf \
		-p ildom-$(N)-na.order \
		-L ildom-$(N)-na.data

data:
	$(CGRAB) ldom*-sa.data > ldom-bdd-sa-clauses.csv
	$(CGRAB) ldom*-ra.data > ldom-bdd-ra-clauses.csv
	$(TGRAB) ldom*-sa.data > ldom-bdd-sa-seconds.csv
	$(TGRAB) ldom*-ra.data > ldom-bdd-ra-seconds.csv
	$(CGRAB) ildom*-sa.data > ildom-bdd-sa-clauses.csv
	$(CGRAB) ildom*-ra.data > ildom-bdd-ra-clauses.csv
	$(TGRAB) ildom*-sa.data > ildom-bdd-sa-seconds.csv
	$(TGRAB) ildom*-ra.data > ildom-bdd-ra-seconds.csv

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
