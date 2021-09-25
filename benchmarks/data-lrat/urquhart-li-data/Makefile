INTERP = python3
M = 3
VLEVEL = 1
PCT=50
SEED=123456

GENERATOR = ../../urquhart-li-code/generate
RANDOMIZER = ../../randomizer.py
EXTRACTOR = ../../xor_extractor.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = ../../grab_clauses.py
VGRABBER = ../../grab_verification.py
#EXTENSION = lratb
EXTENSION = lrat

io: urquhart-li-$(M)-inputorder.data
ro: urquhart-li-$(M)-randomorder.data
l: urquhart-li-$(M)-linear.data
ie: urquhart-li-$(M)-io-equation.data
re: urquhart-li-$(M)-ro-equation.data

urquhart-li-$(M)-inputorder.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-inputorder.cnf | tee urquhart-li-$(M)-inputorder.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-inputorder.cnf -b \
		-o urquhart-li-$(M)-inputorder.$(EXTENSION) 2>&1 | tee -a urquhart-li-$(M)-inputorder.data
	$(CHECKER) urquhart-li-$(M)-inputorder.cnf urquhart-li-$(M)-inputorder.$(EXTENSION) | tee -a urquhart-li-$(M)-inputorder.data
	rm -f urquhart-li-$(M)-inputorder.$(EXTENSION)

urquhart-li-$(M)-randomorder.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)_randomorder.cnf | tee urquhart-li-$(M)-randomorder.data
	$(RANDOMIZER) urquhart-li-$(M)_randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)_randomorder.cnf -b -p urquhart-li-$(M)_randomorder.order \
		-o urquhart-li-$(M)-randomorder.$(EXTENSION) 2>&1 | tee -a urquhart-li-$(M)-randomorder.data
	$(CHECKER) urquhart-li-$(M)_randomorder.cnf urquhart-li-$(M)-randomorder.$(EXTENSION) | tee -a urquhart-li-$(M)-randomorder.data
	rm -f urquhart-li-$(M)-randomorder.$(EXTENSION)

urquhart-li-$(M)-io-equation.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-io-equation.cnf | tee urquhart-li-$(M)-io-equation.data
	$(EXTRACTOR) -i urquhart-li-$(M)-io-equation.cnf -o urquhart-li-$(M)-io-equation.schedule
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-io-equation.cnf -s urquhart-li-$(M)-io-equation.schedule \
		-o urquhart-li-$(M)-io-equation.$(EXTENSION) 2>&1 | tee -a urquhart-li-$(M)-io-equation.data
	$(CHECKER) urquhart-li-$(M)-io-equation.cnf urquhart-li-$(M)-io-equation.$(EXTENSION) | tee -a urquhart-li-$(M)-io-equation.data
	rm -f urquhart-li-$(M)-io-equation.$(EXTENSION)

urquhart-li-$(M)-ro-equation.data:
	$(GENERATOR) -m$(M) -p$(PCT) -ft.cnf | tee urquhart-li-$(M)-ro-equation.data
	mv t.cnf urquhart-li-$(M)-ro-equation.cnf
	$(RANDOMIZER) urquhart-li-$(M)-ro-equation.cnf $(SEED)
	$(EXTRACTOR) -i urquhart-li-$(M)-ro-equation.cnf -o urquhart-li-$(M)-ro-equation.schedule
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-ro-equation.cnf -s urquhart-li-$(M)-ro-equation.schedule \
	        -p urquhart-li-$(M)-ro-equation.order \
		-o urquhart-li-$(M)-ro-equation.$(EXTENSION) 2>&1 | tee -a urquhart-li-$(M)-ro-equation.data
	$(CHECKER) urquhart-li-$(M)-ro-equation.cnf urquhart-li-$(M)-ro-equation.$(EXTENSION) | tee -a urquhart-li-$(M)-ro-equation.data
	rm -f urquhart-li-$(M)-ro-equation.$(EXTENSION)


urquhart-li-$(M)-linear.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-linear.cnf | tee urquhart-li-$(M)-linear.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-linear.cnf \
		-o urquhart-li-$(M)-linear.$(EXTENSION) 2>&1 | tee -a urquhart-li-$(M)-linear.data
	$(CHECKER) urquhart-li-$(M)-linear.cnf urquhart-li-$(M)-linear.$(EXTENSION) | tee -a urquhart-li-$(M)-linear.data
	rm -f urquhart-li-$(M)-linear.$(EXTENSION)


data:
	$(GRABBER) urquhart-li-*-randomorder.data > urquhart-li-randomorder.csv
	$(GRABBER) urquhart-li-*-io-equation.data > urquhart-li-io-equation.csv
	$(GRABBER) urquhart-li-*-ro-equation.data > urquhart-li-ro-equation.csv
#	$(GRABBER) urquhart-li-*-inputorder.data > urquhart-li-inputorder.csv
#	$(GRABBER) urquhart-li-*-linear.data > urquhart-li-linear.csv

vdata:
	$(VGRABBER) urquhart-li-*-randomorder.data > urquhart-li-randomorder-verification.csv


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
