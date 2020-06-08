INTERP = python3
M = 3
VLEVEL = 1
PCT=50
SEED=123456

GENERATOR = ../../urquhart-li-code/generate
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py

io: urquhart-li-$(M)-inputorder.data
ro: urquhart-li-$(M)-randomorder.data
nq: urquhart-li-$(M)-noquant.data

urquhart-li-$(M)-inputorder.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-inputorder.cnf | tee urquhart-li-$(M)-inputorder.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-inputorder.cnf -b \
		-O urquhart-li-$(M)-inputorder.lrat | tee -a urquhart-li-$(M)-inputorder.data
	$(CHECKER) urquhart-li-$(M)-inputorder.cnf urquhart-li-$(M)-inputorder.lrat | tee -a urquhart-li-$(M)-inputorder.data
	rm -f urquhart-li-$(M)-inputorder.lrat

urquhart-li-$(M)-randomorder.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)_randomorder.cnf | tee urquhart-li-$(M)-randomorder.data
	$(RANDOMIZER) urquhart-li-$(M)_randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)_randomorder.cnf -b -p urquhart-li-$(M)_randomorder.order \
		-O urquhart-li-$(M)-randomorder.lrat | tee -a urquhart-li-$(M)-randomorder.data
	$(CHECKER) urquhart-li-$(M)_randomorder.cnf urquhart-li-$(M)-randomorder.lrat | tee -a urquhart-li-$(M)-randomorder.data
	rm -f urquhart-li-$(M)-randomorder.lrat

urquhart-li-$(M)-noquant.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-noquant.cnf | tee urquhart-li-$(M)-noquant.data
	$(SOLVER) -v $(VLEVEL) -i urquhart-li-$(M)-noquant.cnf \
		-O urquhart-li-$(M)-noquant.lrat | tee -a urquhart-li-$(M)-noquant.data
	$(CHECKER) urquhart-li-$(M)-noquant.cnf urquhart-li-$(M)-noquant.lrat | tee -a urquhart-li-$(M)-noquant.data
	rm -f urquhart-li-$(M)-noquant.lrat


data:
	$(GRABBER) urquhart-d*-randomorder.data > urquhart-li-randomorder.csv
	$(GRABBER) urquhart-d*-inputorder.data > urquhart-li-inputorder.csv
	$(GRABBER) urquhart-d*-noquant.data > urquhart-li-noquant.csv
clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
