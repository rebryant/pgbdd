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
TLIM=7200
CAT=

GEN=$(NDIR)/gen_ldom.py
ALTERNATE=$(BDIR)/alternate.py
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) ../../wrap.py $(TLIM) $(QDIR)/qrat-trim 
QCHECK = $(QDIR)/qrat-trim 


CGRAB=../grab_plusclauses.py
TGRAB=../grab_plustime.py
AGRAB=../grab_plusapplies.py
VGRAB=../grab_solve_v_check.py

VLEVEL=1
N=5

all: sa

sa: ldom$(CAT)-$(N)-sa.data
ra: ldom$(CAT)-$(N)-ra.data
qsa: ldom$(CAT)-$(N)-qsa.data
dsa: ldom$(CAT)-$(N)-dsa.data
dra: ldom$(CAT)-$(N)-dra.data

isa: ildom$(CAT)-$(N)-sa.data
ira: ildom$(CAT)-$(N)-ra.data
idsa: ildom$(CAT)-$(N)-dsa.data
idra: ildom$(CAT)-$(N)-dra.data

ldom$(CAT)-$(N)-sa.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-sa 
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ldom$(CAT)-$(N)-sa.qcnf \
		-o ldom$(CAT)-$(N)-sa.qrat \
		-p ldom$(CAT)-$(N)-sa.order \
		-L ldom$(CAT)-$(N)-sa.data
	$(CHECK) ldom$(CAT)-$(N)-sa.qcnf ldom$(CAT)-$(N)-sa.qrat -S -t $(TLIM) | tee -a ldom$(CAT)-$(N)-sa.data
	rm -f ldom$(CAT)-$(N)-sa.qrat

ldom$(CAT)-$(N)-qsa.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-qsa 
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ldom$(CAT)-$(N)-qsa.qcnf \
		-o ldom$(CAT)-$(N)-qsa.qrat \
		-p ldom$(CAT)-$(N)-qsa.order \
		-L ldom$(CAT)-$(N)-qsa.data
	$(QCHECK) ldom$(CAT)-$(N)-qsa.qcnf ldom$(CAT)-$(N)-qsa.qrat -S -t $(TLIM) 
	rm -f ldom$(CAT)-$(N)-qsa.qrat

ldom$(CAT)-$(N)-ra.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-ra
	$(ALTERNATE) -a -i ldom$(CAT)-$(N)-ra.qcnf -o ldom$(CAT)-$(N)-ra-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ldom$(CAT)-$(N)-ra.qcnf \
		-o ldom$(CAT)-$(N)-ra.qrat \
		-p ldom$(CAT)-$(N)-ra.order \
		-L ldom$(CAT)-$(N)-ra.data
	$(CHECK) ldom$(CAT)-$(N)-ra-expand.qcnf ldom$(CAT)-$(N)-ra.qrat -t $(TLIM) | tee -a ldom$(CAT)-$(N)-ra.data
#	$(CHECK) ldom$(CAT)-$(N)-ra.qcnf ldom$(CAT)-$(N)-ra.qrat -t $(TLIM) | tee -a ldom$(CAT)-$(N)-ra.data
#	rm -f ldom$(CAT)-$(N)-ra.qrat

ldom$(CAT)-$(N)-dsa.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-dsa 
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i ldom$(CAT)-$(N)-dsa.qcnf \
		-o ldom$(CAT)-$(N)-dsa.qrat \
		-p ldom$(CAT)-$(N)-dsa.order \
		-L ldom$(CAT)-$(N)-dsa.data
	$(CHECK) ldom$(CAT)-$(N)-dsa.qcnf ldom$(CAT)-$(N)-dsa.qrat -S -t $(TLIM) | tee -a ldom$(CAT)-$(N)-dsa.data
	rm -f ldom$(CAT)-$(N)-dsa.qrat

ldom$(CAT)-$(N)-dra.data:
	$(GEN) -t a -n $(N) -r ldom$(CAT)-$(N)-dra
	$(ALTERNATE) -a -i ldom$(CAT)-$(N)-dra.qcnf -o ldom$(CAT)-$(N)-dra-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i ldom$(CAT)-$(N)-dra.qcnf \
		-o ldom$(CAT)-$(N)-dra.qrat \
		-p ldom$(CAT)-$(N)-dra.order \
		-L ldom$(CAT)-$(N)-dra.data
	$(CHECK) ldom$(CAT)-$(N)-dra-expand.qcnf ldom$(CAT)-$(N)-dra.qrat -t $(TLIM) | tee -a ldom$(CAT)-$(N)-dra.data
	rm -f ldom$(CAT)-$(N)-dra.qrat


ildom$(CAT)-$(N)-sa.data:
	$(GEN) -i -t a -n $(N) -r ildom$(CAT)-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ildom$(CAT)-$(N)-sa.qcnf \
		-o ildom$(CAT)-$(N)-sa.qrat \
		-p ildom$(CAT)-$(N)-sa.order \
		-L ildom$(CAT)-$(N)-sa.data
	$(CHECK) ildom$(CAT)-$(N)-sa.qcnf ildom$(CAT)-$(N)-sa.qrat -S -t $(TLIM) | tee -a ildom$(CAT)-$(N)-sa.data
	rm -f ildom$(CAT)-$(N)-sa.qrat

ildom$(CAT)-$(N)-ra.data:
	$(GEN) -i -t a -n $(N) -r ildom$(CAT)-$(N)-ra
	$(ALTERNATE) -a -i ildom$(CAT)-$(N)-ra.qcnf -o ildom$(CAT)-$(N)-ra-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ildom$(CAT)-$(N)-ra.qcnf \
		-o ildom$(CAT)-$(N)-ra.qrat \
		-p ildom$(CAT)-$(N)-ra.order \
		-L ildom$(CAT)-$(N)-ra.data
	$(CHECK) ildom$(CAT)-$(N)-ra-expand.qcnf ildom$(CAT)-$(N)-ra.qrat -t $(TLIM) | tee -a ildom$(CAT)-$(N)-ra.data
	rm -f ildom$(CAT)-$(N)-ra.qrat

ildom$(CAT)-$(N)-dsa.data:
	$(GEN) -i -t a -n $(N) -r ildom$(CAT)-$(N)-dsa
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i ildom$(CAT)-$(N)-dsa.qcnf \
		-o ildom$(CAT)-$(N)-dsa.qrat \
		-p ildom$(CAT)-$(N)-dsa.order \
		-L ildom$(CAT)-$(N)-dsa.data
	$(CHECK) ildom$(CAT)-$(N)-dsa.qcnf ildom$(CAT)-$(N)-dsa.qrat -S -t $(TLIM) | tee -a ildom$(CAT)-$(N)-dsa.data
	rm -f ildom$(CAT)-$(N)-dsa.qrat

ildom$(CAT)-$(N)-dra.data:
	$(GEN) -i -t a -n $(N) -r ildom$(CAT)-$(N)-dra
	$(ALTERNATE) -a -i ildom$(CAT)-$(N)-dra.qcnf -o ildom$(CAT)-$(N)-dra-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i ildom$(CAT)-$(N)-dra.qcnf \
		-o ildom$(CAT)-$(N)-dra.qrat \
		-p ildom$(CAT)-$(N)-dra.order \
		-L ildom$(CAT)-$(N)-dra.data
	$(CHECK) ildom$(CAT)-$(N)-dra-expand.qcnf ildom$(CAT)-$(N)-dra.qrat -t $(TLIM) | tee -a ildom$(CAT)-$(N)-dra.data
	rm -f ildom$(CAT)-$(N)-dra.qrat


data:
#	$(CGRAB) ldom*-sa.data > ldom-bdd-sa-clauses.csv
#	$(CGRAB) ldom*-ra.data > ldom-bdd-ra-clauses.csv
#	$(TGRAB) ldom*-sa.data > ldom-bdd-sa-seconds.csv
#	$(TGRAB) ldom*-ra.data > ldom-bdd-ra-seconds.csv
#	$(CGRAB) ildom*-sa.data > ildom-bdd-sa-clauses.csv
#	$(CGRAB) ildom*-ra.data > ildom-bdd-ra-clauses.csv
#	$(TGRAB) ildom*-sa.data > ildom-bdd-sa-seconds.csv
#	$(TGRAB) ildom*-ra.data > ildom-bdd-ra-seconds.csv
#	$(AGRAB) ldom*-ra.data > ldom-bdd-ra-applies.csv
#	$(AGRAB) ldom*-sa.data > ldom-bdd-sa-applies.csv
#	$(AGRAB) ldom*-na.data > ldom-bdd-na-applies.csv
#	$(AGRAB) ldom*-nae.data > ldom-bdd-nae-applies.csv
#	$(AGRAB) ldom*-nau.data > ldom-bdd-nau-applies.csv
#	$(AGRAB) ldom*-naeu.data > ldom-bdd-naeu-applies.csv
#	$(VGRAB) *.data | grep -v ERR > ldom-solve-check.csv
	$(VGRAB) *BY5S*-sa.data > ldom-qrat-sat-seconds.csv
	$(VGRAB) *BY5R*-ra.data > ldom-qrat-ref-seconds.csv
	$(VGRAB) *BY5S*-dsa.data > ldom-qrat-dual-sat-seconds.csv
	$(VGRAB) *BY5R*-dra.data > ldom-qrat-dual-ref-seconds.csv
	$(VGRAB) *S*-sa.data > ldom-qrat-allsat-seconds.csv
	$(VGRAB) *R*-ra.data > ldom-qrat-allref-seconds.csv
	$(VGRAB) *S*-dsa.data > ldom-qrat-dual-allsat-seconds.csv
	$(VGRAB) *R*-dra.data > ldom-qrat-dual-allref-seconds.csv


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qrat
