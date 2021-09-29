INTERP = python3
N = 4
VLEVEL = 1

GENERATOR = $(INTERP) ../../pigeon-cook.py
CHECKER = ../../../lrat/lrat-check
GRABBER = $(INTERP) ../../grab_clauses.py

p: pigeon-direct-$(N)-cook.data


pigeon-direct-$(N)-cook.data:
	$(GENERATOR) -n $(N) -r pigeon-direct-$(N)-cook | tee pigeon-direct-$(N)-cook.data
	$(CHECKER) pigeon-direct-$(N)-cook.cnf pigeon-direct-$(N)-cook.lrat | tee -a pigeon-direct-$(N)-cook.data
	rm -f pigeon-direct-$(N)-cook.lrat
data:
	$(GRABBER) pigeon-direct-*-cook.data > pigeon-direct-cook.csv

clean:
	rm -f *.lrat *.cnf

superclean: clean
	rm -f *.data
