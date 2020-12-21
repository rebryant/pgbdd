INTERP=python3
# Abbreviations:
# Proof types
#   r: Refutation
#   s: Satisfaction
# Tseitin variable placement
#   e: End
#   a: After defining variables 
#   b: Before defining variables (when possible)
# Variable ordering
#   m: move-major
#   b: bucket-major

BDIR=../..
NDIR=$(BDIR)/nim
SDIR=$(BDIR)/../qbf

GEN=$(NDIR)/gen_nim.py
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) $(SDIR)/qchecker.py

GRAB=./grab_plusclauses.py

VLEVEL=1
PROFILE=4+3+2
CAT=

all: osab

usab: nimu$(CAT)-$(PROFILE)-sab.data
urab: nimu$(CAT)-$(PROFILE)-rab.data

usam: nimu$(CAT)-$(PROFILE)-sam.data
uram: nimu$(CAT)-$(PROFILE)-ram.data

osab: nimo$(CAT)-$(PROFILE)-sab.data
orab: nimo$(CAT)-$(PROFILE)-rab.data



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

data:
	$(GRAB) nimo-b2-*.data > nim-b2.csv
	$(GRAB) nimo-b3-*.data > nim-b3.csv
	$(GRAB) nimo-b5-*.data > nim-b5.csv
	$(GRAB) nimo-s2-*.data > nim-s2.csv
	$(GRAB) nimo-s3-*.data > nim-s3.csv
	$(GRAB) nimo-m2-*.data > nim-m2.csv
	$(GRAB) nimo-m3-*.data > nim-m3.csv

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
