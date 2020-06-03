N = 4
VLEVEL = 1

GENERATOR = ../pigeon-code/pigeonhole
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

hml: pigeon-direct-$(N)-hm-linear.data
pml: pigeon-direct-$(N)-pm-linear.data

hmb: pigeon-direct-$(N)-hm-bucket.data
pmb: pigeon-direct-$(N)-pm-bucket.data

pigeon-direct-$(N)-hm-bucket.data:
	$(GENERATOR) -$(N) > pigeon-direct-$(N)-hm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-direct-$(N)-hm.cnf -o pigeon-direct-$(N)-hm.proof | tee pigeon-direct-$(N)-hm-bucket.data
	$(CHECKER) -v pigeon-direct-$(N)-hm.proof | tee -a pigeon-direct-$(N)-hm-bucket.data
	rm -rv pigeon-direct-$(N)-hm.proof

pigeon-direct-$(N)-pm-bucket.data:
	$(GENERATOR) $(N) > pigeon-direct-$(N)-pm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-direct-$(N)-pm.cnf -o pigeon-direct-$(N)-pm.proof | tee pigeon-direct-$(N)-pm-bucket.data
	$(CHECKER) -v pigeon-direct-$(N)-pm.proof | tee -a pigeon-direct-$(N)-pm-bucket.data
	rm -rv pigeon-direct-$(N)-pm.proof

pigeon-direct-$(N)-hm-linear.data:
	$(GENERATOR) -$(N) > pigeon-direct-$(N)-hm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-hm.cnf -o pigeon-direct-$(N)-hm.proof | tee pigeon-direct-$(N)-hm-linear.data
	$(CHECKER) -v pigeon-direct-$(N)-hm.proof | tee -a pigeon-direct-$(N)-hm-linear.data
	rm -rv pigeon-direct-$(N)-hm.proof

pigeon-direct-$(N)-pm-linear.data:
	$(GENERATOR) $(N) > pigeon-direct-$(N)-pm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-direct-$(N)-pm.cnf -o pigeon-direct-$(N)-pm.proof | tee pigeon-direct-$(N)-pm-linear.data
	$(CHECKER) -v pigeon-direct-$(N)-pm.proof | tee -a pigeon-direct-$(N)-pm-linear.data
	rm -rv pigeon-direct-$(N)-pm.proof


clean:
	rm -f *.proof *.cnf

superclean: clean
	rm -f *.data
