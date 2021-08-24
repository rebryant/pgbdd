INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../pigeon-sinz.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = ../../grab_clauses.py
VGRABBER = ../../grab_verification.py
EXTENSION = lrat

c: pigeon-tseitin-$(N)-column.data
b: pigeon-tseitin-$(N)-bucket.data
pb: pigeon-tseitin-$(N)-bucket-pm.data
l: pigeon-tseitin-$(N)-linear.data
con: pigeon-tseitin-$(N)-constraint.data

pigeon-tseitin-$(N)-column.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf -s pigeon-tseitin-$(N).schedule \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-column.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).$(EXTENSION) | tee -a pigeon-tseitin-$(N)-column.data
	rm -f pigeon-tseitin-$(N).$(EXTENSION)

pigeon-tseitin-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-bucket.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).$(EXTENSION) | tee -a pigeon-tseitin-$(N)-bucket.data
	rm -f pigeon-tseitin-$(N).$(EXTENSION)

pigeon-tseitin-$(N)-bucket-pm.data:
	$(GENERATOR) -n $(N) -p -r pigeon-tseitin-$(N)-bucket-pm | tee pigeon-tseitin-$(N)-bucket-pm.data
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-tseitin-$(N)-bucket-pm.cnf \
		-p pigeon-tseitin-$(N)-bucket-pm.order -o pigeon-tseitin-$(N)-bucket-pm.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-bucket-pm.data
	$(CHECKER) pigeon-tseitin-$(N)-bucket-pm.cnf pigeon-tseitin-$(N)-bucket-pm.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-bucket-pm.data
	rm -f pigeon-tseitin-$(N)-bucket-pm.$(EXTENSION)


pigeon-tseitin-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-linear.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).$(EXTENSION) | tee -a pigeon-tseitin-$(N)-linear.data
	rm -f pigeon-tseitin-$(N).$(EXTENSION)

pigeon-tseitin-$(N)-constraint.data:
	$(GENERATOR) -c -n $(N) -r pigeon-tseitin-$(N)-constraint | tee pigeon-tseitin-$(N)-constraint.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N)-constraint.cnf -s pigeon-tseitin-$(N)-constraint.schedule \
		-p pigeon-tseitin-$(N)-constraint.order -o pigeon-tseitin-$(N)-constraint.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-constraint.data
	$(CHECKER) pigeon-tseitin-$(N)-constraint.cnf pigeon-tseitin-$(N)-constraint.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-constraint.data
	rm -f pigeon-tseitin-$(N)-constraint.$(EXTENSION)


data:
	$(GRABBER) pigeon-*-bucket.data > pigeon-tseitin-bucket.csv
	$(GRABBER) pigeon-*-bucket-pm.data > pigeon-tseitin-bucket-pm.csv
	$(GRABBER) pigeon-*-column.data > pigeon-tseitin-column.csv
	$(GRABBER) pigeon-*-linear.data > pigeon-tseitin-linear.csv
	$(GRABBER) pigeon-*-constraint.data > pigeon-tseitin-constraint.csv

vdata:
	$(VGRABBER) pigeon-*-bucket.data > pigeon-tseitin-bucket-verification.csv
	$(VGRABBER) pigeon-*-bucket-pm.data > pigeon-tseitin-bucket-verification-pm.csv
	$(VGRABBER) pigeon-*-column.data > pigeon-tseitin-column-verification.csv
	$(VGRABBER) pigeon-*-linear.data > pigeon-tseitin-linear-verification.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
