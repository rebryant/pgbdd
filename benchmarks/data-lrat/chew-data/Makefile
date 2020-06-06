INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

FULLGENERATOR = ../../chew-code/parity
GENERATOR = ../../chew-code/parity-cnf
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check

io: chew-$(N)-inputorder.data
ro: chew-$(N)-randomorder.data


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

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
