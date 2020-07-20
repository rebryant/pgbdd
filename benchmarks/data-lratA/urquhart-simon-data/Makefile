INTERP = python3
M = 3
VLEVEL = 1
SEED=1

# ./genurq 3 5 | more

GENERATOR = ../../urquhart-simon-code/genurq
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lratb

io: urquhart-simon-$(M)-$(SEED)-inputorder.data
ro: urquhart-simon-$(M)-$(SEED)-randomorder.data
l: urquhart-simon-$(M)-$(SEED)-linear.data

urquhart-simon-$(M)-$(SEED)-inputorder.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-inputorder.cnf | tee urquhart-simon-$(M)-$(SEED)-inputorder.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-inputorder.cnf -b \
		-o urquhart-simon-$(M)-$(SEED)-inputorder.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-inputorder.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-inputorder.cnf urquhart-simon-$(M)-$(SEED)-inputorder.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-inputorder.data
	rm -f urquhart-simon-$(M)-$(SEED)-inputorder.$(EXTENSION)

urquhart-simon-$(M)-$(SEED)-randomorder.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-randomorder.cnf | tee urquhart-simon-$(M)-$(SEED)-randomorder.data
	$(RANDOMIZER) urquhart-simon-$(M)-$(SEED)-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-randomorder.cnf -b -p urquhart-simon-$(M)-$(SEED)-randomorder.order \
		-o urquhart-simon-$(M)-$(SEED)-randomorder.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-randomorder.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-randomorder.cnf urquhart-simon-$(M)-$(SEED)-randomorder.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-randomorder.data
	rm -f urquhart-simon-$(M)-$(SEED)-randomorder.$(EXTENSION)

urquhart-simon-$(M)-$(SEED)-linear.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-linear.cnf | tee urquhart-simon-$(M)-$(SEED)-linear.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-linear.cnf \
		-o urquhart-simon-$(M)-$(SEED)-linear.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-linear.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-linear.cnf urquhart-simon-$(M)-$(SEED)-linear.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-linear.data
	rm -f urquhart-simon-$(M)-$(SEED)-linear.$(EXTENSION)


data:
	$(GRABBER) urquhart-simon-*-randomorder.data > urquhart-simon-randomorder.csv
	$(GRABBER) urquhart-simon-*-linear.data > urquhart-simon-linear.csv
clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
