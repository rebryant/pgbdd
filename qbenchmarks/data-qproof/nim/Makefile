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
VLEVEL=2
PROFILE=4+3+2

all: osab

usab: nimu-$(PROFILE)-sab.data
urab: nimu-$(PROFILE)-rab.data

usam: nimu-$(PROFILE)-sam.data
uram: nimu-$(PROFILE)-ram.data

osab: nimo-$(PROFILE)-sab.data
orab: nimo-$(PROFILE)-rab.data



nimu-$(PROFILE)-sab.data:
	$(GEN) -e u -t a -V b -p $(PROFILE) -r nimu-$(PROFILE)-sab
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu-$(PROFILE)-sab.qcnf \
		-o nimu-$(PROFILE)-sab.qproof \
		-p nimu-$(PROFILE)-sab.order \
		-L nimu-$(PROFILE)-sab.data
	$(CHECK) -m s -i nimu-$(PROFILE)-sab.qcnf -p nimu-$(PROFILE)-sab.qproof | tee -a nimu-$(PROFILE)-sab.data
	rm -f nimu-$(PROFILE)-sab.qproof

nimu-$(PROFILE)-rab.data:
	$(GEN) -e u -t a -V b -p $(PROFILE) -r nimu-$(PROFILE)-rab
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu-$(PROFILE)-rab.qcnf \
		-o nimu-$(PROFILE)-rab.qproof \
		-p nimu-$(PROFILE)-rab.order \
		-L nimu-$(PROFILE)-rab.data
	$(CHECK) -m r -i nimu-$(PROFILE)-rab.qcnf -p nimu-$(PROFILE)-rab.qproof | tee -a nimu-$(PROFILE)-rab.data
	rm -f nimu-$(PROFILE)-rab.qproof

nimu-$(PROFILE)-sam.data:
	$(GEN) -e u -t a -V m -p $(PROFILE) -r nimu-$(PROFILE)-sam
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu-$(PROFILE)-sam.qcnf \
		-o nimu-$(PROFILE)-sam.qproof \
		-p nimu-$(PROFILE)-sam.order \
		-L nimu-$(PROFILE)-sam.data
	$(CHECK) -m s -i nimu-$(PROFILE)-sam.qcnf -p nimu-$(PROFILE)-sam.qproof | tee -a nimu-$(PROFILE)-sam.data
	rm -f nimu-$(PROFILE)-sam.qproof

nimu-$(PROFILE)-ram.data:
	$(GEN) -e u -t a -V m -p $(PROFILE) -r nimu-$(PROFILE)-ram
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu-$(PROFILE)-ram.qcnf \
		-o nimu-$(PROFILE)-ram.qproof \
		-p nimu-$(PROFILE)-ram.order \
		-L nimu-$(PROFILE)-ram.data
	$(CHECK) -m r -i nimu-$(PROFILE)-ram.qcnf -p nimu-$(PROFILE)-ram.qproof | tee -a nimu-$(PROFILE)-ram.data
	rm -f nimu-$(PROFILE)-ram.qproof

nimo-$(PROFILE)-sab.data:
	$(GEN) -e o -t a -V b -p $(PROFILE) -r nimo-$(PROFILE)-sab
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimo-$(PROFILE)-sab.qcnf \
		-o nimo-$(PROFILE)-sab.qproof \
		-p nimo-$(PROFILE)-sab.order \
		-L nimo-$(PROFILE)-sab.data
	$(CHECK) -m s -i nimo-$(PROFILE)-sab.qcnf -p nimo-$(PROFILE)-sab.qproof | tee -a nimo-$(PROFILE)-sab.data
	rm -f nimo-$(PROFILE)-sab.qproof


nimo-$(PROFILE)-rab.data:
	$(GEN) -e o -t a -V b -p $(PROFILE) -r nimo-$(PROFILE)-rab
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimo-$(PROFILE)-rab.qcnf \
		-o nimo-$(PROFILE)-rab.qproof \
		-p nimo-$(PROFILE)-rab.order \
		-L nimo-$(PROFILE)-rab.data
	$(CHECK) -m r -i nimo-$(PROFILE)-rab.qcnf -p nimo-$(PROFILE)-rab.qproof | tee -a nimo-$(PROFILE)-rab.data
	rm -f nimo-$(PROFILE)-rab.qproof


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
