INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../pigeon-direct-code/gen_pigeon.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = $(INTERP) ../../grab_clauses.py
VGRABBER = $(INTERP) ../../grab_verification.py

EXTENSION = lrat

ph: pigeon-bucket-$(N)-ph.data
hp: pigeon-bucket-$(N)-hp.data
pp: pigeon-bucket-$(N)-pp.data
hh: pigeon-bucket-$(N)-hh.data

pigeon-bucket-$(N)-ph.data:
	$(GENERATOR) -n $(N) -r pigeon-bucket-$(N) -P | tee pigeon-bucket-$(N)-ph.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-bucket-$(N).cnf -B pigeon-bucket-$(N).pigeon_major -p pigeon-bucket-$(N).hole_major \
		-o pigeon-bucket-$(N)-ph.$(EXTENSION) 2>&1 | tee -a pigeon-bucket-$(N)-ph.data
	$(CHECKER) pigeon-bucket-$(N).cnf pigeon-bucket-$(N)-ph.$(EXTENSION) | tee -a pigeon-bucket-$(N)-ph.data
	rm -f pigeon-bucket-$(N)-ph.$(EXTENSION)

pigeon-bucket-$(N)-hp.data:
	$(GENERATOR) -n $(N) -r pigeon-bucket-$(N) -P | tee pigeon-bucket-$(N)-hp.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-bucket-$(N).cnf -B pigeon-bucket-$(N).hole_major -p pigeon-bucket-$(N).pigeon_major \
		-o pigeon-bucket-$(N)-hp.$(EXTENSION) 2>&1 | tee -a pigeon-bucket-$(N)-hp.data
	$(CHECKER) pigeon-bucket-$(N).cnf pigeon-bucket-$(N)-hp.$(EXTENSION) | tee -a pigeon-bucket-$(N)-hp.data
	rm -f pigeon-bucket-$(N)-hp.$(EXTENSION)


data:
	$(GRABBER) pigeon-bucket-*-ph.data > pigeon-bucket-ph.csv
	$(GRABBER) pigeon-bucket-*-hp.data > pigeon-bucket-hp.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *major
