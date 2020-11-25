MODE=plain
GDIR=../../eden
SDIR=../../../qbf

BUCKET=$(GDIR)/gen-bucket.py
GEN=$(GDIR)/gen-goe-$(MODE)
SOLVE=$(SDIR)/qsolver.py
CHECK=$(SDIR)/qchecker.py
VLEVEL=2
R=4
C=4

all: goe-$(MODE)-$(R)x$(C).data

goe-$(MODE)-$(R)x$(C).qcnf: $(GEN)
	$(GEN) $(R) $(C) > goe-$(MODE)-$(R)x$(C).qcnf
	$(BUCKET) goe-$(MODE)-$(R)x$(C).qcnf > goe-$(MODE)-$(R)x$(C).border

goe-$(MODE)-$(R)x$(C).data: goe-$(MODE)-$(R)x$(C).qcnf
	$(SOLVE) -m s -v $(VLEVEL) -b -B goe-$(MODE)-$(R)x$(C).border \
	 	-i goe-$(MODE)-$(R)x$(C).qcnf -o goe-$(MODE)-$(R)x$(C).qproof | tee goe-$(MODE)-$(R)x$(C).data
	$(CHECK) -S -i goe-$(MODE)-$(R)x$(C).qcnf -p goe-$(MODE)-$(R)x$(C).qproof | tee -a goe-$(MODE)-$(R)x$(C).data

clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.border *.data *.qproof
