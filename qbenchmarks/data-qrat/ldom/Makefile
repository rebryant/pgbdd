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
QDIR=../../../../qrat-trim
TLIM=3600

GEN=$(NDIR)/gen_ldom.py
ALTERNATE=$(BDIR)/alternate.py
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) ../../wrap.py $(TLIM) $(QDIR)/qrat-trim 

CGRAB=../grab_plusclauses.py
TGRAB=../grab_plustime.py
AGRAB=../grab_plusapplies.py
VGRAB=../grab_solve_v_check.py

VLEVEL=1
N=5

all: sa

sa: ldom-$(N)-sa.data
ra: ldom-$(N)-ra.data

isa: ildom-$(N)-sa.data
ira: ildom-$(N)-ra.data

ldom-$(N)-sa.data:
	$(GEN) -t a -n $(N) -r ldom-$(N)-sa 
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ldom-$(N)-sa.qcnf \
		-o ldom-$(N)-sa.qrat \
		-p ldom-$(N)-sa.order \
		-L ldom-$(N)-sa.data
	$(CHECK) ldom-$(N)-sa.qcnf ldom-$(N)-sa.qrat -S -t $(TLIM) | tee -a ldom-$(N)-sa.data
#	rm -f ldom-$(N)-sa.qrat

ldom-$(N)-ra.data:
	$(GEN) -t a -n $(N) -r ldom-$(N)-ra
	$(ALTERNATE) -a -i ldom-$(N)-ra.qcnf -o ldom-$(N)-ra-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ldom-$(N)-ra.qcnf \
		-o ldom-$(N)-ra.qrat \
		-p ldom-$(N)-ra.order \
		-L ldom-$(N)-ra.data
	$(CHECK) ldom-$(N)-ra-expand.qcnf ldom-$(N)-ra.qrat -t $(TLIM) | tee -a ldom-$(N)-ra.data
#	rm -f ldom-$(N)-ra.qrat

ildom-$(N)-sa.data:
	$(GEN) -i -t a -n $(N) -r ildom-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ildom-$(N)-sa.qcnf \
		-o ildom-$(N)-sa.qrat \
		-p ildom-$(N)-sa.order \
		-L ildom-$(N)-sa.data
	$(CHECK) ildom-$(N)-sa.qcnf ildom-$(N)-sa.qrat -S -t $(TLIM) | tee -a ildom-$(N)-sa.data
#	rm -f ildom-$(N)-sa.qrat

ildom-$(N)-ra.data:
	$(GEN) -i -t a -n $(N) -r ildom-$(N)-ra
	$(ALTERNATE) -a -i ildom-$(N)-ra.qcnf -o ildom-$(N)-ra-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ildom-$(N)-ra.qcnf \
		-o ildom-$(N)-ra.qrat \
		-p ildom-$(N)-ra.order \
		-L ildom-$(N)-ra.data
	$(CHECK) ildom-$(N)-ra-expand.qcnf ildom-$(N)-ra.qrat -t $(TLIM) | tee -a ildom-$(N)-ra.data
#	rm -f ildom-$(N)-ra.qrat


data:
	$(CGRAB) ldom*-sa.data > ldom-bdd-sa-clauses.csv
	$(CGRAB) ldom*-ra.data > ldom-bdd-ra-clauses.csv
	$(TGRAB) ldom*-sa.data > ldom-bdd-sa-seconds.csv
	$(TGRAB) ldom*-ra.data > ldom-bdd-ra-seconds.csv
	$(CGRAB) ildom*-sa.data > ildom-bdd-sa-clauses.csv
	$(CGRAB) ildom*-ra.data > ildom-bdd-ra-clauses.csv
	$(TGRAB) ildom*-sa.data > ildom-bdd-sa-seconds.csv
	$(TGRAB) ildom*-ra.data > ildom-bdd-ra-seconds.csv
	$(AGRAB) ldom*-ra.data > ldom-bdd-ra-applies.csv
	$(AGRAB) ldom*-sa.data > ldom-bdd-sa-applies.csv
	$(AGRAB) ldom*-na.data > ldom-bdd-na-applies.csv
	$(AGRAB) ldom*-nae.data > ldom-bdd-nae-applies.csv
	$(AGRAB) ldom*-nau.data > ldom-bdd-nau-applies.csv
	$(AGRAB) ldom*-naeu.data > ldom-bdd-naeu-applies.csv
	$(VGRAB) *.data | grep -v ERR > ldom-solve-check.csv


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qrat
