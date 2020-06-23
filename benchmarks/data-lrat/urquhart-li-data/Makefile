INTERP = python3
M = 3
VLEVEL = 1
PCT=50
SEED=123456

GENERATOR = ../../urquhart-li-code/generate
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lratb

io: urquhart-li-$(M)-inputorder.data
ro: urquhart-li-$(M)-randomorder.data
l: urquhart-li-$(M)-linear.data

urquhart-li-$(M)-inputorder.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-inputorder.cnf | tee urquhart-li-$(M)-inputorder.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-inputorder.cnf -b \
		-o urquhart-li-$(M)-inputorder.$(EXTENSION) | tee -a urquhart-li-$(M)-inputorder.data
	$(CHECKER) urquhart-li-$(M)-inputorder.cnf urquhart-li-$(M)-inputorder.$(EXTENSION) | tee -a urquhart-li-$(M)-inputorder.data
	rm -f urquhart-li-$(M)-inputorder.$(EXTENSION)

urquhart-li-$(M)-randomorder.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)_randomorder.cnf | tee urquhart-li-$(M)-randomorder.data
	$(RANDOMIZER) urquhart-li-$(M)_randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)_randomorder.cnf -b -p urquhart-li-$(M)_randomorder.order \
		-o urquhart-li-$(M)-randomorder.$(EXTENSION) | tee -a urquhart-li-$(M)-randomorder.data
	$(CHECKER) urquhart-li-$(M)_randomorder.cnf urquhart-li-$(M)-randomorder.$(EXTENSION) | tee -a urquhart-li-$(M)-randomorder.data
#	rm -f urquhart-li-$(M)-randomorder.$(EXTENSION)

urquhart-li-$(M)-linear.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-linear.cnf | tee urquhart-li-$(M)-linear.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-linear.cnf \
		-o urquhart-li-$(M)-linear.$(EXTENSION) | tee -a urquhart-li-$(M)-linear.data
	$(CHECKER) urquhart-li-$(M)-linear.cnf urquhart-li-$(M)-linear.$(EXTENSION) | tee -a urquhart-li-$(M)-linear.data
	rm -f urquhart-li-$(M)-linear.$(EXTENSION)


data:
	$(GRABBER) urquhart-li-*-randomorder.data > urquhart-li-randomorder.csv
	$(GRABBER) urquhart-li-*-inputorder.data > urquhart-li-inputorder.csv
	$(GRABBER) urquhart-li-*-linear.data > urquhart-li-linear.csv
clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
