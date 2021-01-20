INTERP=python3
# Abbreviations:
# Proof types
#   r: Refutation
#   s: Satisfaction
#   n: No proof
# Tseitin variable placement
#   e: End
#   a: After defining variables 
#   b: Before defining variables (when possible)
# Variable ordering
#   m: move-major
#   b: bucket-major
#   o: object-major

BDIR=../..
NDIR=$(BDIR)/nim
SDIR=$(BDIR)/../qbf

GEN=$(NDIR)/gen_nim.py
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) $(SDIR)/qchecker.py

CGRAB=../grab_plusclauses.py
TGRAB=../grab_plustime.py
VGRAB=../grab_solve_v_check.py

VLEVEL=1
PROFILE=4+3+2
CAT=

all: osab

usab: nimu$(CAT)-$(PROFILE)-sab.data
urab: nimu$(CAT)-$(PROFILE)-rab.data

usam: nimu$(CAT)-$(PROFILE)-sam.data
uram: nimu$(CAT)-$(PROFILE)-ram.data

usao: nimu$(CAT)-$(PROFILE)-sao.data
urao: nimu$(CAT)-$(PROFILE)-rao.data

useb: nimu$(CAT)-$(PROFILE)-seb.data
ureb: nimu$(CAT)-$(PROFILE)-reb.data

osab: nimo$(CAT)-$(PROFILE)-sab.data
orab: nimo$(CAT)-$(PROFILE)-rab.data

osao: nimo$(CAT)-$(PROFILE)-sao.data
orao: nimo$(CAT)-$(PROFILE)-rao.data

onao: nimo$(CAT)-$(PROFILE)-nao.data


nimu$(CAT)-$(PROFILE)-sab.data:
	$(GEN) -e u -t a -V b -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-sab
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu$(CAT)-$(PROFILE)-sab.qcnf \
		-o nimu$(CAT)-$(PROFILE)-sab.qproof \
		-p nimu$(CAT)-$(PROFILE)-sab.order \
		-L nimu$(CAT)-$(PROFILE)-sab.data
	$(CHECK) -m s -i nimu$(CAT)-$(PROFILE)-sab.qcnf -p nimu$(CAT)-$(PROFILE)-sab.qproof | tee -a nimu$(CAT)-$(PROFILE)-sab.data
	rm -f nimu$(CAT)-$(PROFILE)-sab.qproof

nimu$(CAT)-$(PROFILE)-rab.data:
	$(GEN) -e u -t a -V b -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-rab
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu$(CAT)-$(PROFILE)-rab.qcnf \
		-o nimu$(CAT)-$(PROFILE)-rab.qproof \
		-p nimu$(CAT)-$(PROFILE)-rab.order \
		-L nimu$(CAT)-$(PROFILE)-rab.data
	$(CHECK) -m r -i nimu$(CAT)-$(PROFILE)-rab.qcnf -p nimu$(CAT)-$(PROFILE)-rab.qproof | tee -a nimu$(CAT)-$(PROFILE)-rab.data
	rm -f nimu$(CAT)-$(PROFILE)-rab.qproof

nimu$(CAT)-$(PROFILE)-sam.data:
	$(GEN) -e u -t a -V m -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-sam
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu$(CAT)-$(PROFILE)-sam.qcnf \
		-o nimu$(CAT)-$(PROFILE)-sam.qproof \
		-p nimu$(CAT)-$(PROFILE)-sam.order \
		-L nimu$(CAT)-$(PROFILE)-sam.data
	$(CHECK) -m s -i nimu$(CAT)-$(PROFILE)-sam.qcnf -p nimu$(CAT)-$(PROFILE)-sam.qproof | tee -a nimu$(CAT)-$(PROFILE)-sam.data
	rm -f nimu$(CAT)-$(PROFILE)-sam.qproof

nimu$(CAT)-$(PROFILE)-ram.data:
	$(GEN) -e u -t a -V m -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-ram
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu$(CAT)-$(PROFILE)-ram.qcnf \
		-o nimu$(CAT)-$(PROFILE)-ram.qproof \
		-p nimu$(CAT)-$(PROFILE)-ram.order \
		-L nimu$(CAT)-$(PROFILE)-ram.data
	$(CHECK) -m r -i nimu$(CAT)-$(PROFILE)-ram.qcnf -p nimu$(CAT)-$(PROFILE)-ram.qproof | tee -a nimu$(CAT)-$(PROFILE)-ram.data
	rm -f nimu$(CAT)-$(PROFILE)-ram.qproof

nimu$(CAT)-$(PROFILE)-sao.data:
	$(GEN) -e u -t a -V o -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-sao
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu$(CAT)-$(PROFILE)-sao.qcnf \
		-o nimu$(CAT)-$(PROFILE)-sao.qproof \
		-p nimu$(CAT)-$(PROFILE)-sao.order \
		-L nimu$(CAT)-$(PROFILE)-sao.data
	$(CHECK) -m s -i nimu$(CAT)-$(PROFILE)-sao.qcnf -p nimu$(CAT)-$(PROFILE)-sao.qproof | tee -a nimu$(CAT)-$(PROFILE)-sao.data
	rm -f nimu$(CAT)-$(PROFILE)-sao.qproof

nimu$(CAT)-$(PROFILE)-rao.data:
	$(GEN) -e u -t a -V o -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-rao
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu$(CAT)-$(PROFILE)-rao.qcnf \
		-o nimu$(CAT)-$(PROFILE)-rao.qproof \
		-p nimu$(CAT)-$(PROFILE)-rao.order \
		-L nimu$(CAT)-$(PROFILE)-rao.data
	$(CHECK) -m r -i nimu$(CAT)-$(PROFILE)-rao.qcnf -p nimu$(CAT)-$(PROFILE)-rao.qproof | tee -a nimu$(CAT)-$(PROFILE)-rao.data
	rm -f nimu$(CAT)-$(PROFILE)-rao.qproof


nimu$(CAT)-$(PROFILE)-seb.data:
	$(GEN) -e u -t e -V b -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-seb
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu$(CAT)-$(PROFILE)-seb.qcnf \
		-o nimu$(CAT)-$(PROFILE)-seb.qproof \
		-p nimu$(CAT)-$(PROFILE)-seb.order \
		-L nimu$(CAT)-$(PROFILE)-seb.data
	$(CHECK) -m s -i nimu$(CAT)-$(PROFILE)-seb.qcnf -p nimu$(CAT)-$(PROFILE)-seb.qproof | tee -a nimu$(CAT)-$(PROFILE)-seb.data
	rm -f nimu$(CAT)-$(PROFILE)-seb.qproof

nimu$(CAT)-$(PROFILE)-reb.data:
	$(GEN) -e u -t e -V b -p $(PROFILE) -r nimu$(CAT)-$(PROFILE)-reb
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu$(CAT)-$(PROFILE)-reb.qcnf \
		-o nimu$(CAT)-$(PROFILE)-reb.qproof \
		-p nimu$(CAT)-$(PROFILE)-reb.order \
		-L nimu$(CAT)-$(PROFILE)-reb.data
	$(CHECK) -m r -i nimu$(CAT)-$(PROFILE)-reb.qcnf -p nimu$(CAT)-$(PROFILE)-reb.qproof | tee -a nimu$(CAT)-$(PROFILE)-reb.data
	rm -f nimu$(CAT)-$(PROFILE)-reb.qproof


nimo$(CAT)-$(PROFILE)-sab.data:
	$(GEN) -e o -t a -V b -p $(PROFILE) -r nimo$(CAT)-$(PROFILE)-sab
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimo$(CAT)-$(PROFILE)-sab.qcnf \
		-o nimo$(CAT)-$(PROFILE)-sab.qproof \
		-p nimo$(CAT)-$(PROFILE)-sab.order \
		-L nimo$(CAT)-$(PROFILE)-sab.data
	$(CHECK) -m s -i nimo$(CAT)-$(PROFILE)-sab.qcnf -p nimo$(CAT)-$(PROFILE)-sab.qproof | tee -a nimo$(CAT)-$(PROFILE)-sab.data
	rm -f nimo$(CAT)-$(PROFILE)-sab.qproof


nimo$(CAT)-$(PROFILE)-rab.data:
	$(GEN) -e o -t a -V b -p $(PROFILE) -r nimo$(CAT)-$(PROFILE)-rab
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimo$(CAT)-$(PROFILE)-rab.qcnf \
		-o nimo$(CAT)-$(PROFILE)-rab.qproof \
		-p nimo$(CAT)-$(PROFILE)-rab.order \
		-L nimo$(CAT)-$(PROFILE)-rab.data
	$(CHECK) -m r -i nimo$(CAT)-$(PROFILE)-rab.qcnf -p nimo$(CAT)-$(PROFILE)-rab.qproof | tee -a nimo$(CAT)-$(PROFILE)-rab.data
	rm -f nimo$(CAT)-$(PROFILE)-rab.qproof

nimo$(CAT)-$(PROFILE)-sao.data:
	$(GEN) -e o -t a -V o -p $(PROFILE) -r nimo$(CAT)-$(PROFILE)-sao
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimo$(CAT)-$(PROFILE)-sao.qcnf \
		-o nimo$(CAT)-$(PROFILE)-sao.qproof \
		-p nimo$(CAT)-$(PROFILE)-sao.order \
		-L nimo$(CAT)-$(PROFILE)-sao.data
	$(CHECK) -m s -i nimo$(CAT)-$(PROFILE)-sao.qcnf -p nimo$(CAT)-$(PROFILE)-sao.qproof | tee -a nimo$(CAT)-$(PROFILE)-sao.data
	rm -f nimo$(CAT)-$(PROFILE)-sao.qproof


nimo$(CAT)-$(PROFILE)-rao.data:
	$(GEN) -e o -t a -V o -p $(PROFILE) -r nimo$(CAT)-$(PROFILE)-rao
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimo$(CAT)-$(PROFILE)-rao.qcnf \
		-o nimo$(CAT)-$(PROFILE)-rao.qproof \
		-p nimo$(CAT)-$(PROFILE)-rao.order \
		-L nimo$(CAT)-$(PROFILE)-rao.data
	$(CHECK) -m r -i nimo$(CAT)-$(PROFILE)-rao.qcnf -p nimo$(CAT)-$(PROFILE)-rao.qproof | tee -a nimo$(CAT)-$(PROFILE)-rao.data
	rm -f nimo$(CAT)-$(PROFILE)-rao.qproof

nimo$(CAT)-$(PROFILE)-nao.data:
	$(GEN) -e o -t a -V o -p $(PROFILE) -r nimo$(CAT)-$(PROFILE)-nao
	$(SOLVE) -v $(VLEVEL) -m n -b \
		-i nimo$(CAT)-$(PROFILE)-nao.qcnf \
		-p nimo$(CAT)-$(PROFILE)-nao.order \
		-L nimo$(CAT)-$(PROFILE)-nao.data

data:
#	$(CGRAB) nimo-b2-*b.data > nimo-pgbddq-b2b-clauses.csv
	$(CGRAB) nimo-b3-*b.data > nimo-bdd-b3b-clauses.csv
	$(CGRAB) nimo-b3-*o.data > nimo-bdd-b3o-clauses.csv
#	$(CGRAB) nimo-b4-*b.data > nimo-bdd-b4b-clauses.csv
#	$(CGRAB) nimo-b5-*b.data > nimo-bdd-b5b-clauses.csv
#	$(CGRAB) nimo-s2-*b.data > nimo-bdd-s2b-clauses.csv
#	$(CGRAB) nimo-s3-*b.data > nimo-bdd-s3b-clauses.csv
#	$(CGRAB) nimo-s4-*b.data > nimo-bdd-s4b-clauses.csv
#	$(CGRAB) nimo-s5-*b.data > nimo-bdd-s5b-clauses.csv
#	$(CGRAB) nimo-m2-*b.data > nimo-bdd-m2b-clauses.csv
#	$(CGRAB) nimo-m3-*b.data > nimo-bdd-m3b-clauses.csv
#	$(CGRAB) nimo-m4-*b.data > nimo-bdd-m4b-clauses.csv
	$(CGRAB) nimu-b3-*b.data > nimu-bdd-b3b-clauses.csv
	$(CGRAB) nimu-b3-*o.data > nimu-bdd-b3o-clauses.csv
	$(CGRAB) nimo-f4-*-rao.data > nimo-bdd-f4o-clauses.csv
	$(CGRAB) nimo-t4-*-sao.data > nimo-bdd-t4o-clauses.csv
	$(TGRAB) nimo-f4-*-rao.data > nimo-bdd-f4o-seconds.csv
	$(TGRAB) nimo-t4-*-sao.data > nimo-bdd-t4o-seconds.csv
	$(VGRAB) *-{r,s}a*.data | grep -v ERR > nim-solve-check.csv

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
