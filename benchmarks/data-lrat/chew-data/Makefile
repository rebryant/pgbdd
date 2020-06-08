INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

FULLGENERATOR = ../../chew-code/parity
GENERATOR = ../../chew-code/parity-cnf
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
DGRABBER = ./grab_drat.py

io: chew-$(N)-inputorder.data
ro: chew-$(N)-randomorder.data
nq: chew-$(N)-noquant.data
cd: chew-$(N)-drat.data

chew-$(N)-drat.data:
	$(FULLGENERATOR) $(N) $(SEED) | tee chew-$(N)-drat.data
	rm -f formula.*

chew-$(N)-inputorder.data:
	$(FULLGENERATOR) $(N) $(SEED) | tee chew-$(N)-inputorder.data
	mv formula.cnf chew-$(N)-inputorder.cnf
	rm -f formula.drat
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-inputorder.cnf -b \
		-O chew-$(N)-inputorder.lrat | tee -a chew-$(N)-inputorder.data
	$(CHECKER) chew-$(N)-inputorder.cnf chew-$(N)-inputorder.lrat | tee -a chew-$(N)-inputorder.data
	rm -f chew-$(N)-inputorder.lrat

chew-$(N)-randomorder.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-randomorder.data
	mv formula.cnf chew-$(N)-randomorder.cnf
	$(RANDOMIZER) chew-$(N)-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-randomorder.cnf -b -p chew-$(N)-randomorder.order \
		-O chew-$(N)-randomorder.lrat | tee -a chew-$(N)-randomorder.data
	$(CHECKER) chew-$(N)-randomorder.cnf chew-$(N)-randomorder.lrat | tee -a chew-$(N)-randomorder.data
	rm -f chew-$(N)-randomorder.lrat

chew-$(N)-noquant.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-noquant.data
	mv formula.cnf chew-$(N)-noquant.cnf
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-noquant.cnf \
		-O chew-$(N)-noquant.lrat | tee -a chew-$(N)-noquant.data
	$(CHECKER) chew-$(N)-noquant.cnf chew-$(N)-noquant.lrat | tee -a chew-$(N)-noquant.data
	rm -f chew-$(N)-noquant.lrat


data:
	$(GRABBER) chew*-randomorder.data > chew-randomorder.csv
	$(GRABBER) chew*-inputorder.data > chew-inputorder.csv
	$(DGRABBER) chew*-inputorder.data chew*-drat.data > chew-drat.csv
	$(GRABBER) chew*-noquant.data > chew-noquant.csv
clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
