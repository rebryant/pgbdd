INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = $(INTERP) ../../pigeon-sinz.py
RANDOMIZER = $(INTERP) ../../randomizer.py
EXDIR = ../../../extractor
EXTRACTOR = $(INTERP) $(EXDIR)/constraint_extractor.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = $(INTERP) ../../grab_clauses.py
VGRABBER = $(INTERP) ../../grab_verification.py
AVERAGE = $(INTERP) ../../average_csv.py

EXTENSION = lrat

c: pigeon-tseitin-$(N)-column.data
rc: pigeon-tseitin-$(N)-column-randomorder.data
b: pigeon-tseitin-$(N)-bucket.data
pb: pigeon-tseitin-$(N)-bucket-pm.data
l: pigeon-tseitin-$(N)-linear.data
con: pigeon-tseitin-$(N)-constraint.data
rcon: pigeon-tseitin-$(N)-constraint-randomorder.data
e: pigeon-tseitin-$(N)-equation.data
re: pigeon-tseitin-$(N)-equation-randomorder.data

pigeon-tseitin-$(N)-column.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf -s pigeon-tseitin-$(N).schedule \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-column.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).$(EXTENSION) | tee -a pigeon-tseitin-$(N)-column.data
	rm -f pigeon-tseitin-$(N).$(EXTENSION)

pigeon-tseitin-$(N)-column-randomorder.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N)-column-randomorder | tee pigeon-tseitin-$(N)-column-randomorder.data
	$(RANDOMIZER) pigeon-tseitin-$(N)-column-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N)-column-randomorder.cnf -s pigeon-tseitin-$(N)-column-randomorder.schedule \
		-p pigeon-tseitin-$(N)-column-randomorder.order -o pigeon-tseitin-$(N)-column-randomorder.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-column-randomorder.data
	$(CHECKER) pigeon-tseitin-$(N)-column-randomorder.cnf pigeon-tseitin-$(N)-column-randomorder.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-column-randomorder.data
	rm -f pigeon-tseitin-$(N)-column-randomorder.$(EXTENSION)


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
	$(GENERATOR) -C -c -n $(N) -r pigeon-tseitin-$(N)-constraint | tee pigeon-tseitin-$(N)-constraint.data
	$(EXTRACTOR) < pigeon-tseitin-$(N)-constraint.cnf > pigeon-tseitin-$(N)-constraint.schedule
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N)-constraint.cnf -s pigeon-tseitin-$(N)-constraint.schedule \
		-o pigeon-tseitin-$(N)-constraint.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-constraint.data
	$(CHECKER) pigeon-tseitin-$(N)-constraint.cnf pigeon-tseitin-$(N)-constraint.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-constraint.data
	rm -f pigeon-tseitin-$(N)-constraint.$(EXTENSION)

pigeon-tseitin-$(N)-constraint-randomorder.data:
	$(GENERATOR) -C -c -n $(N) -r pigeon-tseitin-$(N)-constraint-randomorder | tee pigeon-tseitin-$(N)-constraint-randomorder.data
	$(EXTRACTOR) < pigeon-tseitin-$(N)-constraint-randomorder.cnf > pigeon-tseitin-$(N)-constraint-randomorder.schedule
	$(RANDOMIZER) pigeon-tseitin-$(N)-constraint-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N)-constraint-randomorder.cnf -s pigeon-tseitin-$(N)-constraint-randomorder.schedule \
		-p pigeon-tseitin-$(N)-constraint-randomorder.order -o pigeon-tseitin-$(N)-constraint-randomorder.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-constraint-randomorder.data
	$(CHECKER) pigeon-tseitin-$(N)-constraint-randomorder.cnf pigeon-tseitin-$(N)-constraint-randomorder.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-constraint-randomorder.data
	rm -f pigeon-tseitin-$(N)-constraint-randomorder.$(EXTENSION)

pigeon-tseitin-$(N)-equation.data:
	$(GENERATOR) -E -C -c -n $(N) -r pigeon-tseitin-$(N)-equation | tee pigeon-tseitin-$(N)-equation.data
	$(EXTRACTOR) < pigeon-tseitin-$(N)-equation.cnf > pigeon-tseitin-$(N)-equation.schedule
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N)-equation.cnf -s pigeon-tseitin-$(N)-equation.schedule \
		-o pigeon-tseitin-$(N)-equation.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-equation.data
	$(CHECKER) pigeon-tseitin-$(N)-equation.cnf pigeon-tseitin-$(N)-equation.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-equation.data
	rm -f pigeon-tseitin-$(N)-equation.$(EXTENSION)

pigeon-tseitin-$(N)-equation-randomorder.data:
	$(GENERATOR) -E -C -c -n $(N) -r pigeon-tseitin-$(N)-equation-randomorder | tee pigeon-tseitin-$(N)-equation-randomorder.data
	$(EXTRACTOR) < pigeon-tseitin-$(N)-equation-randomorder.cnf > pigeon-tseitin-$(N)-equation-randomorder.schedule
	$(RANDOMIZER) pigeon-tseitin-$(N)-equation-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N)-equation-randomorder.cnf -s pigeon-tseitin-$(N)-equation-randomorder.schedule \
		-p pigeon-tseitin-$(N)-equation-randomorder.order -o pigeon-tseitin-$(N)-equation-randomorder.$(EXTENSION) 2>&1 | tee -a pigeon-tseitin-$(N)-equation-randomorder.data
	$(CHECKER) pigeon-tseitin-$(N)-equation-randomorder.cnf pigeon-tseitin-$(N)-equation-randomorder.$(EXTENSION) | tee -a pigeon-tseitin-$(N)-equation-randomorder.data
	rm -f pigeon-tseitin-$(N)-equation-randomorder.$(EXTENSION)

data:
	$(GRABBER) pigeon-*-bucket.data > pigeon-tseitin-bucket.csv
	$(GRABBER) pigeon-*-bucket-pm.data > pigeon-tseitin-bucket-pm.csv
	$(GRABBER) pigeon-*-column.data > pigeon-tseitin-column.csv
	$(GRABBER) pigeon-*-column-randomorder.data > pigeon-tseitin-column-randomorder.csv
	$(GRABBER) pigeon-*-linear.data > pigeon-tseitin-linear.csv
	$(GRABBER) pigeon-*-constraint.data > pigeon-tseitin-constraint.csv
	$(GRABBER) pigeon-*-constraint-randomorder.data > pigeon-tseitin-constraint-randomorder.csv
	$(GRABBER) pigeon-*-equation.data > pigeon-tseitin-equation.csv
	$(GRABBER) pigeon-*-equation-randomorder.data > pigeon-tseitin-equation-randomorder.csv
	$(AVERAGE) pigeon-tseitin-equation.csv pigeon-tseitin-equation-randomorder.csv > pigeon-tseitin-equation-average.csv

vdata:
	$(VGRABBER) pigeon-*-bucket.data > pigeon-tseitin-bucket-verification.csv
	$(VGRABBER) pigeon-*-bucket-pm.data > pigeon-tseitin-bucket-verification-pm.csv
	$(VGRABBER) pigeon-*-column.data > pigeon-tseitin-column-verification.csv
	$(VGRABBER) pigeon-*-linear.data > pigeon-tseitin-linear-verification.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
