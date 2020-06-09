INTERP = python3
M = 3
VLEVEL = 1
SEED=1

# ./genurq 3 5 | more

GENERATOR = ../../urquhart-simon-code/genurq
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py

io: urquhart-simon-$(M)-inputorder.data
ro: urquhart-simon-$(M)-randomorder.data
l: urquhart-simon-$(M)-noquant.data

urquhart-simon-$(M)-inputorder.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-inputorder.cnf | tee urquhart-simon-$(M)-inputorder.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-inputorder.cnf -b \
		-O urquhart-simon-$(M)-inputorder.lrat | tee -a urquhart-simon-$(M)-inputorder.data
	$(CHECKER) urquhart-simon-$(M)-inputorder.cnf urquhart-simon-$(M)-inputorder.lrat | tee -a urquhart-simon-$(M)-inputorder.data
	rm -f urquhart-simon-$(M)-inputorder.lrat

urquhart-simon-$(M)-randomorder.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-randomorder.cnf | tee urquhart-simon-$(M)-randomorder.data
	$(RANDOMIZER) urquhart-simon-$(M)-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-randomorder.cnf -b -p urquhart-simon-$(M)-randomorder.order \
		-O urquhart-simon-$(M)-randomorder.lrat | tee -a urquhart-simon-$(M)-randomorder.data
	$(CHECKER) urquhart-simon-$(M)-randomorder.cnf urquhart-simon-$(M)-randomorder.lrat | tee -a urquhart-simon-$(M)-randomorder.data
	rm -f urquhart-simon-$(M)-randomorder.lrat

urquhart-simon-$(M)-linear.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-linear.cnf | tee urquhart-simon-$(M)-linear.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-simon-$(M)-linear.cnf \
		-O urquhart-simon-$(M)-linear.lrat | tee -a urquhart-simon-$(M)-linear.data
	$(CHECKER) urquhart-simon-$(M)-linear.cnf urquhart-simon-$(M)-linear.lrat | tee -a urquhart-simon-$(M)-linear.data
	rm -f urquhart-simon-$(M)-linear.lrat


data:
	$(GRABBER) urquhart-d*-randomorder.data > urquhart-simon-randomorder.csv
	$(GRABBER) urquhart-d*-inputorder.data > urquhart-simon-inputorder.csv
	$(GRABBER) urquhart-d*-linear.data > urquhart-simon-linear.csv
clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
