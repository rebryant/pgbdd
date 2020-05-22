N = 4
VLEVEL = 1

GENERATOR = ../pigeon-code/pigeonhole
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

hml: pigeon-$(N)-hm-linear.data
pml: pigeon-$(N)-pm-linear.data

hmb: pigeon-$(N)-hm-bucket.data
pmb: pigeon-$(N)-pm-bucket.data

pigeon-$(N)-hm-bucket.data:
	$(GENERATOR) -$(N) > pigeon-$(N)-hm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-$(N)-hm.cnf -o pigeon-$(N)-hm.proof | tee pigeon-$(N)-hm-bucket.data
	$(CHECKER) -v pigeon-$(N)-hm.proof | tee -a pigeon-$(N)-hm-bucket.data
	rm -rv pigeon-$(N)-hm.proof

pigeon-$(N)-pm-bucket.data:
	$(GENERATOR) $(N) > pigeon-$(N)-pm.cnf
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-$(N)-pm.cnf -o pigeon-$(N)-pm.proof | tee pigeon-$(N)-pm-bucket.data
	$(CHECKER) -v pigeon-$(N)-pm.proof | tee -a pigeon-$(N)-pm-bucket.data
	rm -rv pigeon-$(N)-pm.proof

pigeon-$(N)-hm-linear.data:
	$(GENERATOR) -$(N) > pigeon-$(N)-hm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-$(N)-hm.cnf -o pigeon-$(N)-hm.proof | tee pigeon-$(N)-hm-linear.data
	$(CHECKER) -v pigeon-$(N)-hm.proof | tee -a pigeon-$(N)-hm-linear.data
	rm -rv pigeon-$(N)-hm.proof

pigeon-$(N)-pm-linear.data:
	$(GENERATOR) $(N) > pigeon-$(N)-pm.cnf
	$(SOLVER) -v $(VLEVEL) -i pigeon-$(N)-pm.cnf -o pigeon-$(N)-pm.proof | tee pigeon-$(N)-pm-linear.data
	$(CHECKER) -v pigeon-$(N)-pm.proof | tee -a pigeon-$(N)-pm-linear.data
	rm -rv pigeon-$(N)-pm.proof


clean:
	rm -f *.proof *.cnf

superclean: clean
	rm -f *.data
