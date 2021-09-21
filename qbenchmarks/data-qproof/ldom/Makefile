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

CGRAB=../grab_clauses.py
TGRAB=../grab_plustime.py
AGRAB=../grab_plusapplies.py
VGRAB=../grab_solve_v_check.py

VLEVEL=1
QVERB = -v
N=5
CAT=

all: sa

sa: ldom$(CAT)-$(N)-sa.data
ra: ldom$(CAT)-$(N)-ra.data
na: ldom$(CAT)-$(N)-na.data
da: ldom$(CAT)-$(N)-da.data
nae: ldom$(CAT)-$(N)-nae.data
nau: ldom$(CAT)-$(N)-nau.data
naeu: ldom$(CAT)-$(N)-naeu.data

isa: ildom$(CAT)-$(N)-sa.data
ira: ildom$(CAT)-$(N)-ra.data
ina: ildom$(CAT)-$(N)-na.data
ida: ildom$(CAT)-$(N)-da.data

ldom$(CAT)-$(N)-sa.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ldom$(CAT)-$(N)-sa.qcnf \
		-o ldom$(CAT)-$(N)-sa.qproof \
		-p ldom$(CAT)-$(N)-sa.order \
		-L ldom$(CAT)-$(N)-sa.data
	$(CHECK) -m s -i ldom$(CAT)-$(N)-sa.qcnf -p ldom$(CAT)-$(N)-sa.qproof | tee -a ldom$(CAT)-$(N)-sa.data
	rm -f ldom$(CAT)-$(N)-sa.qproof

ldom$(CAT)-$(N)-ra.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-ra
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ldom$(CAT)-$(N)-ra.qcnf \
		-o ldom$(CAT)-$(N)-ra.qproof \
		-p ldom$(CAT)-$(N)-ra.order \
		-L ldom$(CAT)-$(N)-ra.data
	$(CHECK) -m r -i ldom$(CAT)-$(N)-ra.qcnf -p ldom$(CAT)-$(N)-ra.qproof | tee -a ldom$(CAT)-$(N)-ra.data
	rm -f ldom$(CAT)-$(N)-ra.qproof

ldom$(CAT)-$(N)-na.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-na
	$(SOLVE) -v $(VLEVEL) -m n -b \
		-i ldom$(CAT)-$(N)-na.qcnf \
		-p ldom$(CAT)-$(N)-na.order \
		-L ldom$(CAT)-$(N)-na.data

ldom$(CAT)-$(N)-da.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-da
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i ldom$(CAT)-$(N)-da.qcnf \
		-o ldom$(CAT)-$(N)-da.qproof \
		-p ldom$(CAT)-$(N)-da.order \
		-L ldom$(CAT)-$(N)-da.data
	$(CHECK) -m d -i ldom$(CAT)-$(N)-da.qcnf -p ldom$(CAT)-$(N)-da.qproof | tee -a ldom$(CAT)-$(N)-da.data
	rm -f ldom$(CAT)-$(N)-da.qproof


ldom$(CAT)-$(N)-nae.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-nae
	$(SOLVE) -v $(VLEVEL) -m n -l e -b \
		-i ldom$(CAT)-$(N)-nae.qcnf \
		-p ldom$(CAT)-$(N)-nae.order \
		-L ldom$(CAT)-$(N)-nae.data

ldom$(CAT)-$(N)-nau.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-nau
	$(SOLVE) -v $(VLEVEL) -m n -l u -b \
		-i ldom$(CAT)-$(N)-nau.qcnf \
		-p ldom$(CAT)-$(N)-nau.order \
		-L ldom$(CAT)-$(N)-nau.data

ldom$(CAT)-$(N)-naeu.data:
	$(GEN) $(QVERB) -t a -n $(N) -r ldom$(CAT)-$(N)-naeu
	$(SOLVE) -v $(VLEVEL) -m n -l eu -b \
		-i ldom$(CAT)-$(N)-naeu.qcnf \
		-p ldom$(CAT)-$(N)-naeu.order \
		-L ldom$(CAT)-$(N)-naeu.data


ildom$(CAT)-$(N)-sa.data:
	$(GEN) $(QVERB) -i -t a -n $(N) -r ildom$(CAT)-$(N)-sa
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i ildom$(CAT)-$(N)-sa.qcnf \
		-o ildom$(CAT)-$(N)-sa.qproof \
		-p ildom$(CAT)-$(N)-sa.order \
		-L ildom$(CAT)-$(N)-sa.data
	$(CHECK) -m s -i ildom$(CAT)-$(N)-sa.qcnf -p ildom$(CAT)-$(N)-sa.qproof | tee -a ildom$(CAT)-$(N)-sa.data
	rm -f ildom$(CAT)-$(N)-sa.qproof

ildom$(CAT)-$(N)-ra.data:
	$(GEN) $(QVERB) -i -t a -n $(N) -r ildom$(CAT)-$(N)-ra
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i ildom$(CAT)-$(N)-ra.qcnf \
		-o ildom$(CAT)-$(N)-ra.qproof \
		-p ildom$(CAT)-$(N)-ra.order \
		-L ildom$(CAT)-$(N)-ra.data
	$(CHECK) -m r -i ildom$(CAT)-$(N)-ra.qcnf -p ildom$(CAT)-$(N)-ra.qproof | tee -a ildom$(CAT)-$(N)-ra.data
	rm -f ildom$(CAT)-$(N)-ra.qproof

ildom$(CAT)-$(N)-na.data:
	$(GEN) $(QVERB) -i -t a -n $(N) -r ildom$(CAT)-$(N)-na
	$(SOLVE) -v $(VLEVEL) -m n -b \
		-i ildom$(CAT)-$(N)-na.qcnf \
		-p ildom$(CAT)-$(N)-na.order \
		-L ildom$(CAT)-$(N)-na.data

ildom$(CAT)-$(N)-da.data:
	$(GEN) $(QVERB) -i -t a -n $(N) -r ildom$(CAT)-$(N)-da
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i ildom$(CAT)-$(N)-da.qcnf \
		-o ildom$(CAT)-$(N)-da.qproof \
		-p ildom$(CAT)-$(N)-da.order \
		-L ildom$(CAT)-$(N)-da.data
	$(CHECK) -m d -i ildom$(CAT)-$(N)-da.qcnf -p ildom$(CAT)-$(N)-da.qproof | tee -a ildom$(CAT)-$(N)-da.data
	rm -f ildom$(CAT)-$(N)-da.qproof


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
	$(CGRAB) *BY5S-*.data > ldom-qproof-sat-clauses.csv
	$(CGRAB) *BY5R-*.data > ldom-qproof-ref-clauses.csv
	$(VGRAB) *BY5S-*.data > ldom-qproof-sat-seconds.csv
	$(VGRAB) *BY5R-*.data > ldom-qproof-ref-seconds.csv
	$(CGRAB) *BY5DS-*.data > ldom-qproof-dual-sat-clauses.csv
	$(CGRAB) *BY5DR-*.data > ldom-qproof-dual-ref-clauses.csv
	$(VGRAB) *BY5DS-*.data > ldom-qproof-dual-sat-seconds.csv
	$(VGRAB) *BY5DR-*.data > ldom-qproof-dual-ref-seconds.csv

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
