INTERP=python3
# Abbreviations:
# V/v: Reorder/don't reorder variables
# B/b: Reorder/don't reorder buckets
# C/c: Use/don't use clustering of input clauses
MODE=plain
GDIR=../../eden
SDIR=../../../qbf

BUCKET=$(INTERP) $(GDIR)/gen-bucket.py
VARIABLE=$(INTERP) $(GDIR)/gen-variable.py
CLUSTER=$(INTERP) $(GDIR)/gen-cluster.py
GEN=$(GDIR)/gen-goe-$(MODE)
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) $(SDIR)/qchecker.py
VLEVEL=2
R=4
C=4

all: VBC

VBC: goe-$(MODE)-$(R)x$(C)-VBC.data
VBc: goe-$(MODE)-$(R)x$(C)-VBc.data
vBC: goe-$(MODE)-$(R)x$(C)-vBC.data

goe-$(MODE)-$(R)x$(C).qcnf:
	- $(GEN) $(R) $(C) > goe-$(MODE)-$(R)x$(C).qcnf
	$(BUCKET) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).border
	$(VARIABLE) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).vorder
	$(CLUSTER) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).cluster


goe-$(MODE)-$(R)x$(C)-VBC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-VBC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-VBC.data

goe-$(MODE)-$(R)x$(C)-VBc.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-VBc.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-VBc.data


goe-$(MODE)-$(R)x$(C)-vBC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-vBC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-vBC.data


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.border *.data *.qproof
