INTERP = python3
N = 10
VLEVEL = 2

GENERATOR = $(INTERP) ../../chess.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

q: chess-$(N)-column.data

nq: chess-$(N)-noquant.data

ns: chess-$(N)-noschedule.data

b: chess-$(N)-bucket.data

gb: chess-$(N)-gbucket.data

chess-$(N)-column.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-column | tee chess-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-column.cnf -s chess-$(N)-column.schedule \
		-p chess-$(N)-column.order -o chess-$(N)-column.$(EXTENSION) 2>&1 | tee -a chess-$(N)-column.data
	$(CHECKER) chess-$(N)-column.cnf chess-$(N)-column.$(EXTENSION) | tee -a chess-$(N)-column.data
	rm -f chess-$(N)-column.$(EXTENSION)


chess-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noquant | tee chess-$(N)-noquant.data
	grep -v "q" chess-$(N)-noquant.schedule > chess-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noquant.cnf -s chess-$(N)-noquant-stripped.schedule \
		-p chess-$(N)-noquant.order -o chess-$(N)-noquant.$(EXTENSION) 2>&1 | tee -a chess-$(N)-noquant.data
	$(CHECKER) chess-$(N)-noquant.cnf chess-$(N)-noquant.$(EXTENSION) | tee -a chess-$(N)-noquant.data
	rm -f chess-$(N)-noquant.$(EXTENSION)

chess-$(N)-noschedule.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noschedule | tee chess-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noschedule.cnf \
		-p chess-$(N)-noschedule.order -o chess-$(N)-noschedule.$(EXTENSION) 2>&1 | tee -a chess-$(N)-noschedule.data
	$(CHECKER) chess-$(N)-noschedule.cnf chess-$(N)-noschedule.$(EXTENSION) | tee -a chess-$(N)-noschedule.data
	rm -f chess-$(N)-noschedule.$(EXTENSION)

chess-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-bucket | tee chess-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-$(N)-bucket.cnf \
		-p chess-$(N)-bucket.order -o chess-$(N)-bucket.$(EXTENSION) 2>&1 | tee -a chess-$(N)-bucket.data
	$(CHECKER) chess-$(N)-bucket.cnf chess-$(N)-bucket.$(EXTENSION) | tee -a chess-$(N)-bucket.data
	rm -f chess-$(N)-bucket.$(EXTENSION)

chess-$(N)-gbucket.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-gbucket | tee chess-$(N)-gbucket.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-gbucket.cnf -B chess-$(N)-gbucket.buckets \
		-p chess-$(N)-gbucket.order -o chess-$(N)-gbucket.$(EXTENSION) 2>&1 | tee -a chess-$(N)-gbucket.data
	$(CHECKER) chess-$(N)-gbucket.cnf chess-$(N)-gbucket.$(EXTENSION) | tee -a chess-$(N)-gbucket.data
	rm -f chess-$(N)-gbucket.$(EXTENSION)


data:
	$(GRABBER) chess-*-column.data > chess-column.csv
	$(GRABBER) chess-*-bucket.data > chess-bucket.csv
	$(GRABBER) chess-*-gbucket.data > chess-gbucket.csv
	$(GRABBER) chess-*-noquant.data > chess-noquant.csv
	$(GRABBER) chess-*-noschedule.data > chess-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
