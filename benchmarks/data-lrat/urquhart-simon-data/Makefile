INTERP = python3
M = 3
VLEVEL = 1
SEED=1

# ./genurq 3 5 | more

GENERATOR = ../../urquhart-simon-code/genurq
RANDOMIZER = ../../randomizer.py
EXTRACTOR = ../../xor_extractor.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = ../../grab_clauses.py
VGRABBER = ../../grab_verification.py
EXTENSION = lratb

io: urquhart-simon-$(M)-$(SEED)-inputorder.data
ro: urquhart-simon-$(M)-$(SEED)-randomorder.data
l: urquhart-simon-$(M)-$(SEED)-linear.data

re: urquhart-simon-$(M)-$(SEED)-ro-equation.data

urquhart-simon-$(M)-$(SEED)-inputorder.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-inputorder.cnf | tee urquhart-simon-$(M)-$(SEED)-inputorder.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-inputorder.cnf -b \
		-o urquhart-simon-$(M)-$(SEED)-inputorder.$(EXTENSION) 2>&1 | tee -a urquhart-simon-$(M)-$(SEED)-inputorder.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-inputorder.cnf urquhart-simon-$(M)-$(SEED)-inputorder.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-inputorder.data
	rm -f urquhart-simon-$(M)-$(SEED)-inputorder.$(EXTENSION)

urquhart-simon-$(M)-$(SEED)-randomorder.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-randomorder.cnf | tee urquhart-simon-$(M)-$(SEED)-randomorder.data
	$(RANDOMIZER) urquhart-simon-$(M)-$(SEED)-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-randomorder.cnf -b -p urquhart-simon-$(M)-$(SEED)-randomorder.order \
		-o urquhart-simon-$(M)-$(SEED)-randomorder.$(EXTENSION) 2>&1 | tee -a urquhart-simon-$(M)-$(SEED)-randomorder.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-randomorder.cnf urquhart-simon-$(M)-$(SEED)-randomorder.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-randomorder.data
	rm -f urquhart-simon-$(M)-$(SEED)-randomorder.$(EXTENSION)

urquhart-simon-$(M)-$(SEED)-ro-equation.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-ro-equation.cnf | tee urquhart-simon-$(M)-$(SEED)-ro-equation.data
	$(EXTRACTOR) -i urquhart-simon-$(M)-$(SEED)-ro-equation.cnf -o urquhart-simon-$(M)-$(SEED)-ro-equation.schedule
	$(RANDOMIZER) urquhart-simon-$(M)-$(SEED)-ro-equation.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-ro-equation.cnf -s  urquhart-simon-$(M)-$(SEED)-ro-equation.schedule \
		-p urquhart-simon-$(M)-$(SEED)-ro-equation.order \
		-o urquhart-simon-$(M)-$(SEED)-ro-equation.$(EXTENSION) 2>&1 | tee -a urquhart-simon-$(M)-$(SEED)-ro-equation.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-ro-equation.cnf urquhart-simon-$(M)-$(SEED)-ro-equation.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-ro-equation.data
	rm -f urquhart-simon-$(M)-$(SEED)-ro-equation.$(EXTENSION)

urquhart-simon-$(M)-$(SEED)-linear.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-linear.cnf | tee urquhart-simon-$(M)-$(SEED)-linear.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-$(SEED)-linear.cnf \
		-o urquhart-simon-$(M)-$(SEED)-linear.$(EXTENSION) 2>&1 | tee -a urquhart-simon-$(M)-$(SEED)-linear.data
	$(CHECKER) urquhart-simon-$(M)-$(SEED)-linear.cnf urquhart-simon-$(M)-$(SEED)-linear.$(EXTENSION) | tee -a urquhart-simon-$(M)-$(SEED)-linear.data
	rm -f urquhart-simon-$(M)-$(SEED)-linear.$(EXTENSION)


data:
	$(GRABBER) urquhart-simon-*-randomorder.data > urquhart-simon-randomorder.csv
	$(GRABBER) urquhart-simon-*-linear.data > urquhart-simon-linear.csv
	$(GRABBER) urquhart-simon-*-ro-equation.data > urquhart-simon-ro-equation.csv

vdata:
	$(VGRABBER) urquhart-simon-*-randomorder.data > urquhart-simon-randomorder-verification.csv
	$(VGRABBER) urquhart-simon-*-linear.data > urquhart-simon-linear-verification.csv


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
