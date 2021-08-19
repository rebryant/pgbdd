INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = $(INTERP) ../../chess.py
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

q: chess-$(N)-column.data

rq: chess-$(N)-column-randomorder.data

nq: chess-$(N)-noquant.data

e: chess-$(N)-equation.data

re: chess-$(N)-equation-randomorder.data

ns: chess-$(N)-noschedule.data

b: chess-$(N)-bucket.data

gb: chess-$(N)-gbucket.data

chess-$(N)-column.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-column | tee chess-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-column.cnf -s chess-$(N)-column.schedule \
		-p chess-$(N)-column.order -o chess-$(N)-column.$(EXTENSION) 2>&1 | tee -a chess-$(N)-column.data
	$(CHECKER) chess-$(N)-column.cnf chess-$(N)-column.$(EXTENSION) | tee -a chess-$(N)-column.data
	rm -f chess-$(N)-column.$(EXTENSION)

chess-$(N)-column-randomorder.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-column-randomorder | tee chess-$(N)-column-randomorder.data
	$(RANDOMIZER) chess-$(N)-column-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-column-randomorder.cnf -s chess-$(N)-column-randomorder.schedule \
		-p chess-$(N)-column-randomorder.order -o chess-$(N)-column-randomorder.$(EXTENSION) 2>&1 | tee -a chess-$(N)-column-randomorder.data
	$(CHECKER) chess-$(N)-column-randomorder.cnf chess-$(N)-column-randomorder.$(EXTENSION) | tee -a chess-$(N)-column-randomorder.data
	rm -f chess-$(N)-column-randomorder.$(EXTENSION)

chess-$(N)-equation.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-equation -p e | tee chess-$(N)-equation.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation.cnf -s chess-$(N)-equation.schedule -m 3 \
		-p chess-$(N)-equation.order -o chess-$(N)-equation.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation.data
	$(CHECKER) chess-$(N)-equation.cnf chess-$(N)-equation.$(EXTENSION) | tee -a chess-$(N)-equation.data
	rm -f chess-$(N)-equation.$(EXTENSION)

chess-$(N)-equation-randomorder.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-equation-randomorder -p e | tee chess-$(N)-equation-randomorder.data
	$(RANDOMIZER) chess-$(N)-equation-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-randomorder.cnf -s chess-$(N)-equation-randomorder.schedule -m 3 \
		-p chess-$(N)-equation-randomorder.order -o chess-$(N)-equation-randomorder.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-randomorder.data
	$(CHECKER) chess-$(N)-equation-randomorder.cnf chess-$(N)-equation-randomorder.$(EXTENSION) | tee -a chess-$(N)-equation-randomorder.data
	rm -f chess-$(N)-equation-randomorder.$(EXTENSION)

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
	$(GRABBER) chess-*-column-randomorder.data > chess-column-randomorder.csv
	$(GRABBER) chess-*-equation.data > chess-equation.csv
	$(GRABBER) chess-*-equation-randomorder.data > chess-equation-randomorder.csv
	$(GRABBER) chess-*-bucket.data > chess-bucket.csv
	$(GRABBER) chess-*-gbucket.data > chess-gbucket.csv
	$(GRABBER) chess-*-noquant.data > chess-noquant.csv
	$(GRABBER) chess-*-noschedule.data > chess-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
