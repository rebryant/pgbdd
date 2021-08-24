INTERP = python3
N = 4
VLEVEL = 1

GENERATOR = ../../pigeon-code/pigeonhole
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py

hml: pigeon-direct-$(N)-hm-linear.data
pml: pigeon-direct-$(N)-pm-linear.data

hmb: pigeon-direct-$(N)-hm-bucket.data
pmb: pigeon-direct-$(N)-pm-bucket.data

pigeon-direct-$(N)-hm-bucket.data:
	$(GENERATOR) -$(N) > pigeon-direct-$(N)-hm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-direct-$(N)-hm.cnf -O pigeon-direct-$(N)-hm.lrat | tee pigeon-direct-$(N)-hm-bucket.data
	$(CHECKER) pigeon-direct-$(N)-hm.cnf pigeon-direct-$(N)-hm.lrat | tee -a pigeon-direct-$(N)-hm-bucket.data
	rm -f pigeon-direct-$(N)-hm.lrat

pigeon-direct-$(N)-pm-bucket.data:
	$(GENERATOR) $(N) > pigeon-direct-$(N)-pm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-direct-$(N)-pm.cnf -O pigeon-direct-$(N)-pm.lrat | tee pigeon-direct-$(N)-pm-bucket.data
	$(CHECKER) pigeon-direct-$(N)-pm.cnf pigeon-direct-$(N)-pm.lrat | tee -a pigeon-direct-$(N)-pm-bucket.data
	rm -f pigeon-direct-$(N)-pm.lrat

pigeon-direct-$(N)-hm-linear.data:
	$(GENERATOR) -$(N) > pigeon-direct-$(N)-hm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-hm.cnf -O pigeon-direct-$(N)-hm.lrat | tee pigeon-direct-$(N)-hm-linear.data
	$(CHECKER) pigeon-direct-$(N)-hm.cnf pigeon-direct-$(N)-hm.lrat | tee -a pigeon-direct-$(N)-hm-linear.data
	rm -f pigeon-direct-$(N)-hm.lrat

pigeon-direct-$(N)-pm-linear.data:
	$(GENERATOR) $(N) > pigeon-direct-$(N)-pm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-pm.cnf -O pigeon-direct-$(N)-pm.lrat | tee pigeon-direct-$(N)-pm-linear.data
	$(CHECKER) pigeon-direct-$(N)-pm.cnf pigeon-direct-$(N)-pm.lrat | tee -a pigeon-direct-$(N)-pm-linear.data
	rm -f pigeon-direct-$(N)-pm.lrat

data:
	$(GRABBER) pigeon-*-hm-bucket.data > pigeon-direct-hm-bucket.csv
	$(GRABBER) pigeon-*-pm-bucket.data > pigeon-direct-pm-bucket.csv
	$(GRABBER) pigeon-*-hm-linear.data > pigeon-direct-hm-linear.csv
	$(GRABBER) pigeon-*-pm-linear.data > pigeon-direct-pm-linear.csv



clean:
	rm -f *.lrat *.cnf

superclean: clean
	rm -f *.data
