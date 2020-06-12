INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../pigeon-sinz2.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py

c: pigeon-tseitin2-$(N)-column.data
b: pigeon-tseitin2-$(N)-bucket.data
l: pigeon-tseitin2-$(N)-linear.data

pigeon-tseitin2-$(N)-column.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin2-$(N) | tee pigeon-tseitin2-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin2-$(N).cnf -s pigeon-tseitin2-$(N).schedule \
		-p pigeon-tseitin2-$(N).order -O pigeon-tseitin2-$(N).lrat | tee -a pigeon-tseitin2-$(N)-column.data
	$(CHECKER) pigeon-tseitin2-$(N).cnf pigeon-tseitin2-$(N).lrat | tee -a pigeon-tseitin2-$(N)-column.data
	rm -f pigeon-tseitin2-$(N).lrat

pigeon-tseitin2-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin2-$(N) | tee pigeon-tseitin2-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-tseitin2-$(N).cnf \
		-p pigeon-tseitin2-$(N).order -O pigeon-tseitin2-$(N).lrat | tee -a pigeon-tseitin2-$(N)-bucket.data
	$(CHECKER) pigeon-tseitin2-$(N).cnf pigeon-tseitin2-$(N).lrat | tee -a pigeon-tseitin2-$(N)-bucket.data
	rm -f pigeon-tseitin2-$(N).lrat

pigeon-tseitin2-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin2-$(N) | tee pigeon-tseitin2-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin2-$(N).cnf \
		-p pigeon-tseitin2-$(N).order -O pigeon-tseitin2-$(N).lrat | tee -a pigeon-tseitin2-$(N)-linear.data
	$(CHECKER) pigeon-tseitin2-$(N).cnf pigeon-tseitin2-$(N).lrat | tee -a pigeon-tseitin2-$(N)-linear.data
	rm -f pigeon-tseitin2-$(N).lrat

data:
	$(GRABBER) pigeon-*-bucket.data > pigeon-tseitin2-bucket.csv
	$(GRABBER) pigeon-*-column.data > pigeon-tseitin2-column.csv
	$(GRABBER) pigeon-*-linear.data > pigeon-tseitin2-linear.csv
