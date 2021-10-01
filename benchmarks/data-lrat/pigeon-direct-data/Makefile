INTERP = python3
N = 4
VLEVEL = 2
SEED=123456

GDIR=../../pigeon-code

AGENERATOR = $(GDIR)/pigeon-augmented
GENERATOR = $(GDIR)/pigeonhole
EGENERATOR = $(GDIR)/pigeon-equations
RANDOMIZER = $(INTERP) ../../randomizer.py
EXDIR = ../../../extractor
EXTRACTOR = $(INTERP) $(EXDIR)/constraint_extractor.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = $(INTERP) ../../grab_clauses.py
EXTENSION = lrat

hml: pigeon-direct-$(N)-hm-linear.data
pml: pigeon-direct-$(N)-pm-linear.data
hmb: pigeon-direct-$(N)-hm-bucket.data
pmb: pigeon-direct-$(N)-pm-bucket.data
pc: pigeon-direct-$(N)-constraint.data
rpc: pigeon-direct-$(N)-constraint-randomorder.data
re: pigeon-direct-$(N)-equation-randomorder.data

pigeon-direct-$(N)-hm-bucket.data:
	$(AGENERATOR) -$(N) > pigeon-direct-$(N)-hm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-direct-$(N)-hm.cnf -o pigeon-direct-$(N)-hm.$(EXTENSION) 2>&1 | tee pigeon-direct-$(N)-hm-bucket.data
	$(CHECKER) pigeon-direct-$(N)-hm.cnf pigeon-direct-$(N)-hm.$(EXTENSION) | tee -a pigeon-direct-$(N)-hm-bucket.data
	rm -f pigeon-direct-$(N)-hm.$(EXTENSION)

pigeon-direct-$(N)-pm-bucket.data:
	$(AGENERATOR) $(N) > pigeon-direct-$(N)-pm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-direct-$(N)-pm.cnf -o pigeon-direct-$(N)-pm.$(EXTENSION) 2>&1 | tee pigeon-direct-$(N)-pm-bucket.data
	$(CHECKER) pigeon-direct-$(N)-pm.cnf pigeon-direct-$(N)-pm.$(EXTENSION) | tee -a pigeon-direct-$(N)-pm-bucket.data
	rm -f pigeon-direct-$(N)-pm.$(EXTENSION)

pigeon-direct-$(N)-hm-linear.data:
	$(AGENERATOR) -$(N) > pigeon-direct-$(N)-hm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-hm.cnf -o pigeon-direct-$(N)-hm.$(EXTENSION) 2>&1 | tee pigeon-direct-$(N)-hm-linear.data
	$(CHECKER) pigeon-direct-$(N)-hm.cnf pigeon-direct-$(N)-hm.$(EXTENSION) | tee -a pigeon-direct-$(N)-hm-linear.data
	rm -f pigeon-direct-$(N)-hm.$(EXTENSION)

pigeon-direct-$(N)-pm-linear.data:
	$(AGENERATOR) $(N) > pigeon-direct-$(N)-pm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-pm.cnf -o pigeon-direct-$(N)-pm.$(EXTENSION) 2>&1 | tee pigeon-direct-$(N)-pm-linear.data
	$(CHECKER) pigeon-direct-$(N)-pm.cnf pigeon-direct-$(N)-pm.$(EXTENSION) | tee -a pigeon-direct-$(N)-pm-linear.data
	rm -f pigeon-direct-$(N)-pm.$(EXTENSION)

pigeon-direct-$(N)-constraint.data:
	$(GENERATOR) $(N) > pigeon-direct-$(N)-constraint.cnf
	$(EXTRACTOR) < pigeon-direct-$(N)-constraint.cnf > pigeon-direct-$(N)-constraint.schedule
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-constraint.cnf -o pigeon-direct-$(N)-constraint.$(EXTENSION) -s pigeon-direct-$(N)-constraint.schedule 2>&1 | tee pigeon-direct-$(N)-constraint.data
	$(CHECKER) pigeon-direct-$(N)-constraint.cnf pigeon-direct-$(N)-constraint.$(EXTENSION) | tee -a pigeon-direct-$(N)-constraint.data
	rm -f pigeon-direct-$(N)-constraint.$(EXTENSION)

pigeon-direct-$(N)-constraint-randomorder.data:
	$(GENERATOR) $(N) > pigeon-direct-$(N)-constraint-randomorder.cnf
	$(RANDOMIZER) pigeon-direct-$(N)-constraint-randomorder.cnf $(SEED)
	$(EXTRACTOR) < pigeon-direct-$(N)-constraint-randomorder.cnf > pigeon-direct-$(N)-constraint-randomorder.schedule
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-constraint-randomorder.cnf -o pigeon-direct-$(N)-constraint-randomorder.$(EXTENSION) \
		-p pigeon-direct-$(N)-constraint-randomorder.order \
		-s pigeon-direct-$(N)-constraint-randomorder.schedule 2>&1 | tee pigeon-direct-$(N)-constraint-randomorder.data
	$(CHECKER) pigeon-direct-$(N)-constraint-randomorder.cnf pigeon-direct-$(N)-constraint-randomorder.$(EXTENSION) | tee -a pigeon-direct-$(N)-constraint-randomorder.data
	rm -f pigeon-direct-$(N)-constraint-randomorder.$(EXTENSION)

pigeon-direct-$(N)-equation-randomorder.data:
	$(EGENERATOR) $(N) > pigeon-direct-$(N)-equation-randomorder.cnf
	$(RANDOMIZER) pigeon-direct-$(N)-equation-randomorder.cnf $(SEED)
	$(EXTRACTOR) < pigeon-direct-$(N)-equation-randomorder.cnf > pigeon-direct-$(N)-equation-randomorder.schedule
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-equation-randomorder.cnf -o pigeon-direct-$(N)-equation-randomorder.$(EXTENSION) \
		-p pigeon-direct-$(N)-equation-randomorder.order \
		-s pigeon-direct-$(N)-equation-randomorder.schedule 2>&1 | tee pigeon-direct-$(N)-equation-randomorder.data
	$(CHECKER) pigeon-direct-$(N)-equation-randomorder.cnf pigeon-direct-$(N)-equation-randomorder.$(EXTENSION) | tee -a pigeon-direct-$(N)-equation-randomorder.data
	rm -f pigeon-direct-$(N)-equation-randomorder.$(EXTENSION)


data:
	$(GRABBER) pigeon-*-hm-bucket.data > pigeon-direct-hm-bucket.csv
	$(GRABBER) pigeon-*-pm-bucket.data > pigeon-direct-pm-bucket.csv
	$(GRABBER) pigeon-*-hm-linear.data > pigeon-direct-hm-linear.csv
	$(GRABBER) pigeon-*-pm-linear.data > pigeon-direct-pm-linear.csv
	$(GRABBER) pigeon-*-constraint.data > pigeon-direct-constraint.csv
	$(GRABBER) pigeon-*-constraint-randomorder.data > pigeon-direct-constraint-randomorder.csv
	$(GRABBER) pigeon-*-equation-randomorder.data > pigeon-direct-equation-randomorder.csv



clean:
	rm -f *.lrat *.lratb *.cnf

superclean: clean
	rm -f *.data
