INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = $(INTERP) ../../chess.py
RANDOMIZER = $(INTERP) ../../randomizer.py
EXDIR = ../../../extractor
EXTRACTOR = $(INTERP) $(EXDIR)/constraint_extractor.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = $(INTERP) ../../grab_clauses.py
AVERAGE = $(INTERP) ../../average_csv.py

EXTENSION = lrat

q: chess-torus-$(N)-column.data

nq: chess-torus-$(N)-noquant.data

ea: chess-torus-$(N)-equation-auto.data

rea: chess-torus-$(N)-equation-auto-randomorder.data

c: chess-torus-$(N)-constraint.data

dc: chess-torus-$(N)-constraint-dual.data

ns: chess-torus-$(N)-noschedule.data

b: chess-torus-$(N)-bucket.data

gb: chess-torus-$(N)-gbucket.data

chess-torus-$(N)-column.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-column | tee chess-torus-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-column.cnf -s chess-torus-$(N)-column.schedule \
		-p chess-torus-$(N)-column.order -o chess-torus-$(N)-column.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-column.data
	$(CHECKER) chess-torus-$(N)-column.cnf chess-torus-$(N)-column.$(EXTENSION) | tee -a chess-torus-$(N)-column.data
	rm -f chess-torus-$(N)-column.$(EXTENSION)

chess-torus-$(N)-equation-auto.data:
	$(GENERATOR) -C -w b -n $(N) -r chess-torus-$(N)-equation-auto -p e | tee chess-torus-$(N)-equation-auto.data
	$(EXTRACTOR) -i chess-torus-$(N)-equation-auto.cnf -o chess-torus-$(N)-equation-auto.schedule -v 2 | tee -a chess-torus-$(N)-equation-auto.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-equation-auto.cnf -s chess-torus-$(N)-equation-auto.schedule -m a \
		-o chess-torus-$(N)-equation-auto.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-equation-auto.data
	$(CHECKER) chess-torus-$(N)-equation-auto.cnf chess-torus-$(N)-equation-auto.$(EXTENSION) | tee -a chess-torus-$(N)-equation-auto.data
	rm -f chess-torus-$(N)-equation-auto.$(EXTENSION)

chess-torus-$(N)-equation-auto-randomorder.data:
	$(GENERATOR) -C -w b -n $(N) -r chess-torus-$(N)-equation-auto-randomorder -p e | tee chess-torus-$(N)-equation-auto-randomorder.data
	$(RANDOMIZER) chess-torus-$(N)-equation-auto-randomorder.cnf $(SEED)
	$(EXTRACTOR) -i chess-torus-$(N)-equation-auto-randomorder.cnf -o chess-torus-$(N)-equation-auto-randomorder.schedule -v 2 | tee -a chess-torus-$(N)-equation-auto-randomorder.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-equation-auto-randomorder.cnf -s chess-torus-$(N)-equation-auto-randomorder.schedule -m a \
		-p chess-torus-$(N)-equation-auto-randomorder.order \
		-o chess-torus-$(N)-equation-auto-randomorder.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-equation-auto-randomorder.data
	$(CHECKER) chess-torus-$(N)-equation-auto-randomorder.cnf chess-torus-$(N)-equation-auto-randomorder.$(EXTENSION) | tee -a chess-torus-$(N)-equation-auto-randomorder.data
	rm -f chess-torus-$(N)-equation-auto-randomorder.$(EXTENSION)

chess-torus-$(N)-constraint.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-constraint -p c | tee chess-torus-$(N)-constraint.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-constraint.cnf -s chess-torus-$(N)-constraint.schedule -m 3 \
		-p chess-torus-$(N)-constraint.order -o chess-torus-$(N)-constraint.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-constraint.data
	$(CHECKER) chess-torus-$(N)-constraint.cnf chess-torus-$(N)-constraint.$(EXTENSION) | tee -a chess-torus-$(N)-constraint.data
	rm -f chess-torus-$(N)-constraint.$(EXTENSION)

chess-torus-$(N)-constraint-dual.data:
	$(GENERATOR) -w b -n $(N) -r chess-torus-$(N)-constraint-dual -p d | tee chess-torus-$(N)-constraint-dual.data
	$(SOLVER) -v $(VLEVEL) -i chess-torus-$(N)-constraint-dual.cnf -s chess-torus-$(N)-constraint-dual.schedule -m 3 \
		-p chess-torus-$(N)-constraint-dual.order -o chess-torus-$(N)-constraint-dual.$(EXTENSION) 2>&1 | tee -a chess-torus-$(N)-constraint-dual.data
	$(CHECKER) chess-torus-$(N)-constraint-dual.cnf chess-torus-$(N)-constraint-dual.$(EXTENSION) | tee -a chess-torus-$(N)-constraint-dual.data
	rm -f chess-torus-$(N)-constraint-dual.$(EXTENSION)


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
	$(GRABBER) chess-torus-*-equation-auto.data > chess-torus-equation-auto.csv
	$(GRABBER) chess-torus-*-equation-auto-randomorder.data > chess-torus-equation-auto-randomorder.csv
	$(AVERAGE) chess-torus-equation-auto.csv chess-torus-equation-auto-randomorder.csv > chess-torus-equation-auto-average.csv
#	$(GRABBER) chess-torus-*-gbucket.data > chess-torus-gbucket.csv
#	$(GRABBER) chess-torus-*-noquant.data > chess-torus-noquant.csv
#	$(GRABBER) chess-torus-*-noschedule.data > chess-torus-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
