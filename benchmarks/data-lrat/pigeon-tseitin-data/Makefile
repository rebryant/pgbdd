INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../pigeon-sinz.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py

c: pigeon-tseitin-$(N)-column.data
b: pigeon-tseitin-$(N)-bucket.data
l: pigeon-tseitin-$(N)-linear.data

pigeon-tseitin-$(N)-column.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf -s pigeon-tseitin-$(N).schedule \
		-p pigeon-tseitin-$(N).order -O pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-column.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-column.data
	rm -f pigeon-tseitin-$(N).lrat

pigeon-tseitin-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -O pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-bucket.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-bucket.data
	rm -f pigeon-tseitin-$(N).lrat

pigeon-tseitin-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -O pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-linear.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-linear.data
	rm -f pigeon-tseitin-$(N).lrat

data:
	$(GRABBER) pigeon-*-bucket.data > pigeon-tseitin-bucket.csv
	$(GRABBER) pigeon-*-column.data > pigeon-tseitin-column.csv
	$(GRABBER) pigeon-*-linear.data > pigeon-tseitin-linear.csv
