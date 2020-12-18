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
#   p: ply-major
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

usap: nimu-$(PROFILE)-sap.data
urap: nimu-$(PROFILE)-rap.data

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

nimu-$(PROFILE)-rab.data:
	$(GEN) -e u -t a -V b -p $(PROFILE) -r nimu-$(PROFILE)-rab
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu-$(PROFILE)-rab.qcnf \
		-o nimu-$(PROFILE)-rab.qproof \
		-p nimu-$(PROFILE)-rab.order \
		-L nimu-$(PROFILE)-rab.data
	$(CHECK) -m r -i nimu-$(PROFILE)-rab.qcnf -p nimu-$(PROFILE)-rab.qproof | tee -a nimu-$(PROFILE)-rab.data

nimu-$(PROFILE)-sap.data:
	$(GEN) -e u -t a -V p -p $(PROFILE) -r nimu-$(PROFILE)-sap
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimu-$(PROFILE)-sap.qcnf \
		-o nimu-$(PROFILE)-sap.qproof \
		-p nimu-$(PROFILE)-sap.order \
		-L nimu-$(PROFILE)-sap.data
	$(CHECK) -m s -i nimu-$(PROFILE)-sap.qcnf -p nimu-$(PROFILE)-sap.qproof | tee -a nimu-$(PROFILE)-sap.data

nimu-$(PROFILE)-rap.data:
	$(GEN) -e u -t a -V p -p $(PROFILE) -r nimu-$(PROFILE)-rap
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimu-$(PROFILE)-rap.qcnf \
		-o nimu-$(PROFILE)-rap.qproof \
		-p nimu-$(PROFILE)-rap.order \
		-L nimu-$(PROFILE)-rap.data
	$(CHECK) -m r -i nimu-$(PROFILE)-rap.qcnf -p nimu-$(PROFILE)-rap.qproof | tee -a nimu-$(PROFILE)-rap.data

nimo-$(PROFILE)-sab.data:
	$(GEN) -e o -t a -V b -p $(PROFILE) -r nimo-$(PROFILE)-sab
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i nimo-$(PROFILE)-sab.qcnf \
		-o nimo-$(PROFILE)-sab.qproof \
		-p nimo-$(PROFILE)-sab.order \
		-L nimo-$(PROFILE)-sab.data
	$(CHECK) -m s -i nimo-$(PROFILE)-sab.qcnf -p nimo-$(PROFILE)-sab.qproof | tee -a nimo-$(PROFILE)-sab.data

nimo-$(PROFILE)-rab.data:
	$(GEN) -e o -t a -V b -p $(PROFILE) -r nimo-$(PROFILE)-rab
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i nimo-$(PROFILE)-rab.qcnf \
		-o nimo-$(PROFILE)-rab.qproof \
		-p nimo-$(PROFILE)-rab.order \
		-L nimo-$(PROFILE)-rab.data
	$(CHECK) -m r -i nimo-$(PROFILE)-rab.qcnf -p nimo-$(PROFILE)-rab.qproof | tee -a nimo-$(PROFILE)-rab.data


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
