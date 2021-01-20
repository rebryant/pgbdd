INTERP=python3
# Abbreviations:
# V/v: Reorder/don't reorder variables
# B/b: Reorder/don't reorder buckets
# C/c: Use/don't use clustering of input clauses
# np: Don't generate proof
MODE=plain
BDIR=../..
GDIR=$(BDIR)/eden
SDIR=$(BDIR)/../qbf

BUCKET=$(INTERP) $(GDIR)/gen-bucket.py
VARIABLE=$(INTERP) $(GDIR)/gen-variable.py
UVARIABLE=$(INTERP) $(GDIR)/gen-uvariable.py
REVERSE=$(INTERP) $(BDIR)/reverse.py
CLUSTER=$(INTERP) $(GDIR)/gen-cluster.py
GRABBER = $(INTERP) ./grab_xclauses.py
VGRAB=../grab_solve_v_check.py
GEN=$(GDIR)/gen-goe-$(MODE)
SOLVE=$(INTERP) $(SDIR)/qsolver.py
CHECK=$(INTERP) $(SDIR)/qchecker.py
VLEVEL=1
R=4
C=4

all: VBC

VBC: goe-$(MODE)-$(R)x$(C)-VBC.data
VBc: goe-$(MODE)-$(R)x$(C)-VBc.data
vBC: goe-$(MODE)-$(R)x$(C)-vBC.data
VbC: goe-$(MODE)-$(R)x$(C)-VbC.data

UBC: goe-$(MODE)-$(R)x$(C)-UBC.data
RRC: goe-$(MODE)-$(R)x$(C)-RRC.data

np: goe-$(MODE)-$(R)x$(C)-np.data

goe-$(MODE)-$(R)x$(C).qcnf:
	$(GEN) $(R) $(C) > goe-$(MODE)-$(R)x$(C).qcnf
	$(BUCKET) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).border
	$(VARIABLE) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).vorder
	$(CLUSTER) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).cluster
	$(UVARIABLE) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).uorder
	$(REVERSE) < goe-$(MODE)-$(R)x$(C).uorder > goe-$(MODE)-$(R)x$(C).rorder

goe-$(MODE)-$(R)x$(C)-VBC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-VBC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-VBC.data
	rm -f goe-$(MODE)-$(R)x$(C).qproof

goe-$(MODE)-$(R)x$(C)-VBc.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-VBc.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-VBc.data
	rm -f goe-$(MODE)-$(R)x$(C).qproof

goe-$(MODE)-$(R)x$(C)-vBC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-vBC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-vBC.data
	rm -f goe-$(MODE)-$(R)x$(C).qproof

goe-$(MODE)-$(R)x$(C)-VbC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-VbC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-VbC.data
	rm -f goe-$(MODE)-$(R)x$(C).qproof

goe-$(MODE)-$(R)x$(C)-RRC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
		-B goe-$(MODE)-$(R)x$(C).rorder \
	        -p goe-$(MODE)-$(R)x$(C).uorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-RRC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-RRC.data
	rm -f goe-$(MODE)-$(R)x$(C).qproof

goe-$(MODE)-$(R)x$(C)-UBC.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b \
		-B goe-$(MODE)-$(R)x$(C).border \
	        -p goe-$(MODE)-$(R)x$(C).uorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C)-UBC.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C)-UBC.data
	rm -f goe-$(MODE)-$(R)x$(C).qproof

goe-$(MODE)-$(R)x$(C)-np.data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m n -v $(VLEVEL) -b \
	        -p goe-$(MODE)-$(R)x$(C).vorder \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf  | tee goe-$(MODE)-$(R)x$(C)-np.data

demo:
	$(GEN) $(R) $(C) > goe-$(MODE)-$(R)x$(C)-demo.qcnf
	$(CLUSTER) goe-$(MODE)-$(R)x$(C)-demo.qcnf > goe-$(MODE)-$(R)x$(C).cluster
	$(SOLVE) -m s -b -v 2 \
	        -c goe-$(MODE)-$(R)x$(C).cluster \
	 	-i goe-$(MODE)-$(R)x$(C)-demo.qcnf -o goe-$(MODE)-$(R)x$(C)-demo.qproof | tee goe-$(MODE)-$(R)x$(C)-demo.data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C)-demo.qcnf -p goe-$(MODE)-$(R)x$(C)-demo.qproof | tee -a goe-$(MODE)-$(R)x$(C)-demo.data

data:
#	$(GRABBER) goe-plain-*-VBC.data > goe-plain-VBC.csv
#	$(GRABBER) goe-oneeighty-*-VBC.data > goe-oneeighty-VBC.csv
#	$(GRABBER) goe-ninety-*-VBC.data > goe-ninety-VBC.csv
#	$(GRABBER) goe-plain-*-vBC.data > goe-plain-vBC.csv
#	$(GRABBER) goe-plain-*-VbC.data > goe-plain-VbC.csv
#	$(GRABBER) goe-plain-*-VBc.data > goe-plain-VBc.csv
#
#	$(GRABBER) goe-plain-01x*-VBC.data > goe-plain-01x-VBC.csv
#	$(GRABBER) goe-plain-*x01-VBC.data > goe-plain-x01-VBC.csv
#	$(GRABBER) goe-plain-02x*-VBC.data > goe-plain-02x-VBC.csv
#	$(GRABBER) goe-plain-*x02-VBC.data > goe-plain-x02-VBC.csv
#	$(GRABBER) goe-plain-03x*-VBC.data > goe-plain-03x-VBC.csv
#	$(GRABBER) goe-plain-*x03-VBC.data > goe-plain-x03-VBC.csv
	$(GRABBER) goe-plain-01x*-UBC.data > goe-plain-bdd-01x-UBC-clauses.csv
#	$(GRABBER) goe-plain-*x01-UBC.data > goe-plain-x01-UBC.csv
	$(GRABBER) goe-plain-02x*-UBC.data > goe-plain-bdd-02x-UBC-clauses.csv
#	$(GRABBER) goe-plain-*x02-UBC.data > goe-plain-x02-UBC.csv
	$(GRABBER) goe-plain-03x*-UBC.data > goe-plain-bdd-03x-UBC-clauses.csv
#	$(GRABBER) goe-plain-*x03-UBC.data > goe-plain-x03-UBC.csv
	$(GRABBER) goe-plain-04x*-UBC.data > goe-plain-bdd-04x-UBC-clauses.csv
	$(VGRAB) *.data | grep -v ERR > eden-solve-check.csv

clean:
	rm -f *~


superclean: clean
	rm -f *.qcnf *.border *.vorder *.cluster *.data *.qproof
