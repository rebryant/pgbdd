INTERP = python3
N = 10
VLEVEL = 2

GENERATOR = $(INTERP) ../../chess.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

q: chess-torus-$(N)-column.data

nq: chess-torus-$(N)-noquant.data

e: chess-torus-$(N)-equation.data

ns: chess-torus-$(N)-noschedule.data

b: chess-torus-$(N)-bucket.data

gb: chess-torus-$(N)-gbucket.data

chess-torus-$(N)-column.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-column | tee chess-torus-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-column.cnf -s chess-torus-$(N)-column.schedule \
		-p chess-torus-$(N)-column.order -o chess-torus-$(N)-column.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-column.data
	$(CHECKER) chess-torus-$(N)-column.cnf chess-torus-$(N)-column.$(EXTENSION) | tee -a chess-torus-$(N)-column.data
	rm -f chess-torus-$(N)-column.$(EXTENSION)

chess-torus-$(N)-equation.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-equation -p e | tee chess-torus-$(N)-equation.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-equation.cnf -s chess-torus-$(N)-equation.schedule -m 3 \
		-p chess-torus-$(N)-equation.order -o chess-torus-$(N)-equation.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-equation.data
	$(CHECKER) chess-torus-$(N)-equation.cnf chess-torus-$(N)-equation.$(EXTENSION) | tee -a chess-torus-$(N)-equation.data
	rm -f chess-torus-$(N)-equation.$(EXTENSION)


chess-torus-$(N)-noquant.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-noquant | tee chess-torus-$(N)-noquant.data
	grep -v "q" chess-torus-$(N)-noquant.schedule > chess-torus-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-noquant.cnf -s chess-torus-$(N)-noquant-stripped.schedule \
		-p chess-torus-$(N)-noquant.order -o chess-torus-$(N)-noquant.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-noquant.data
	$(CHECKER) chess-torus-$(N)-noquant.cnf chess-torus-$(N)-noquant.$(EXTENSION) | tee -a chess-torus-$(N)-noquant.data
	rm -f chess-torus-$(N)-noquant.$(EXTENSION)

chess-torus-$(N)-noschedule.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-noschedule | tee chess-torus-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-noschedule.cnf \
		-p chess-torus-$(N)-noschedule.order -o chess-torus-$(N)-noschedule.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-noschedule.data
	$(CHECKER) chess-torus-$(N)-noschedule.cnf chess-torus-$(N)-noschedule.$(EXTENSION) | tee -a chess-torus-$(N)-noschedule.data
	rm -f chess-torus-$(N)-noschedule.$(EXTENSION)

chess-torus-$(N)-bucket.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-bucket | tee chess-torus-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-torus-$(N)-bucket.cnf \
		-p chess-torus-$(N)-bucket.order -o chess-torus-$(N)-bucket.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-bucket.data
	$(CHECKER) chess-torus-$(N)-bucket.cnf chess-torus-$(N)-bucket.$(EXTENSION) | tee -a chess-torus-$(N)-bucket.data
	rm -f chess-torus-$(N)-bucket.$(EXTENSION)

chess-torus-$(N)-gbucket.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-gbucket | tee chess-torus-$(N)-gbucket.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-gbucket.cnf -B chess-torus-$(N)-gbucket.buckets \
		-p chess-torus-$(N)-gbucket.order -o chess-torus-$(N)-gbucket.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-gbucket.data
	$(CHECKER) chess-torus-$(N)-gbucket.cnf chess-torus-$(N)-gbucket.$(EXTENSION) | tee -a chess-torus-$(N)-gbucket.data
	rm -f chess-torus-$(N)-gbucket.$(EXTENSION)


data:
	$(GRABBER) chess-torus-*-column.data > chess-torus-column.csv
	$(GRABBER) chess-torus-*-equation.data > chess-torus-equation.csv
#	$(GRABBER) chess-torus-*-bucket.data > chess-torus-bucket.csv
#	$(GRABBER) chess-torus-*-gbucket.data > chess-torus-gbucket.csv
#	$(GRABBER) chess-torus-*-noquant.data > chess-torus-noquant.csv
#	$(GRABBER) chess-torus-*-noschedule.data > chess-torus-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
