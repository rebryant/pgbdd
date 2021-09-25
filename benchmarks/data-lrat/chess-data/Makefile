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

q: chess-$(N)-column.data

rq: chess-$(N)-column-randomorder.data

nq: chess-$(N)-noquant.data

e3: chess-$(N)-equation-mod3.data

ea: chess-$(N)-equation-auto.data

ei: chess-$(N)-equation-integer.data

re3: chess-$(N)-equation-mod3-randomorder.data

rea: chess-$(N)-equation-auto-randomorder.data

rei: chess-$(N)-equation-integer-randomorder.data

c: chess-$(N)-constraint.data

dc: chess-$(N)-constraint-dual.data

dcr:  chess-$(N)-constraint-dual-randomorder.data

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

chess-$(N)-equation-mod3.data:
	$(GENERATOR) -C -n $(N) -r chess-$(N)-equation-mod3 -p e | tee chess-$(N)-equation-mod3.data
	$(EXTRACTOR) -i chess-$(N)-equation-mod3.cnf -o chess-$(N)-equation-mod3.schedule -v 2 | tee -a chess-$(N)-equation-mod3.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-mod3.cnf -s chess-$(N)-equation-mod3.schedule -m 3 \
		-o chess-$(N)-equation-mod3.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-mod3.data
	$(CHECKER) chess-$(N)-equation-mod3.cnf chess-$(N)-equation-mod3.$(EXTENSION) | tee -a chess-$(N)-equation-mod3.data
	rm -f chess-$(N)-equation-mod3.$(EXTENSION)

chess-$(N)-equation-auto.data:
	$(GENERATOR) -C -n $(N) -r chess-$(N)-equation-auto -p e | tee chess-$(N)-equation-auto.data
	$(EXTRACTOR) -i chess-$(N)-equation-auto.cnf -o chess-$(N)-equation-auto.schedule -v 2 | tee -a chess-$(N)-equation-auto.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-auto.cnf -s chess-$(N)-equation-auto.schedule -m a \
		-o chess-$(N)-equation-auto.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-auto.data
	$(CHECKER) chess-$(N)-equation-auto.cnf chess-$(N)-equation-auto.$(EXTENSION) | tee -a chess-$(N)-equation-auto.data
	rm -f chess-$(N)-equation-auto.$(EXTENSION)

chess-$(N)-equation-integer.data:
	$(GENERATOR) -C -n $(N) -r chess-$(N)-equation-integer -p e | tee chess-$(N)-equation-integer.data
	$(EXTRACTOR) -i chess-$(N)-equation-integer.cnf -o chess-$(N)-equation-integer.schedule -v 2 | tee -a chess-$(N)-equation-integer.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-integer.cnf -s chess-$(N)-equation-integer.schedule  -m i \
		-o chess-$(N)-equation-integer.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-integer.data
	$(CHECKER) chess-$(N)-equation-integer.cnf chess-$(N)-equation-integer.$(EXTENSION) | tee -a chess-$(N)-equation-integer.data
	rm -f chess-$(N)-equation-integer.$(EXTENSION)

chess-$(N)-equation-mod3-randomorder.data:
	$(GENERATOR) -C -n $(N) -r chess-$(N)-equation-mod3-randomorder -p e | tee chess-$(N)-equation-mod3-randomorder.data
	$(RANDOMIZER) chess-$(N)-equation-mod3-randomorder.cnf $(SEED)
	$(EXTRACTOR) -i chess-$(N)-equation-mod3-randomorder.cnf -o chess-$(N)-equation-mod3-randomorder.schedule -v 2 | tee -a chess-$(N)-equation-mod3-randomorder.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-mod3-randomorder.cnf -s chess-$(N)-equation-mod3-randomorder.schedule -m 3 \
		-p chess-$(N)-equation-mod3-randomorder.order -o chess-$(N)-equation-mod3-randomorder.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-mod3-randomorder.data
	$(CHECKER) chess-$(N)-equation-mod3-randomorder.cnf chess-$(N)-equation-mod3-randomorder.$(EXTENSION) | tee -a chess-$(N)-equation-mod3-randomorder.data
	rm -f chess-$(N)-equation-mod3-randomorder.$(EXTENSION)

chess-$(N)-equation-auto-randomorder.data:
	$(GENERATOR) -C -n $(N) -r chess-$(N)-equation-auto-randomorder -p e | tee chess-$(N)-equation-auto-randomorder.data
	$(RANDOMIZER) chess-$(N)-equation-auto-randomorder.cnf $(SEED)
	$(EXTRACTOR) -i chess-$(N)-equation-auto-randomorder.cnf -o chess-$(N)-equation-auto-randomorder.schedule -v 2 | tee -a chess-$(N)-equation-auto-randomorder.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-auto-randomorder.cnf -s chess-$(N)-equation-auto-randomorder.schedule -m a \
		-p chess-$(N)-equation-auto-randomorder.order -o chess-$(N)-equation-auto-randomorder.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-auto-randomorder.data
	$(CHECKER) chess-$(N)-equation-auto-randomorder.cnf chess-$(N)-equation-auto-randomorder.$(EXTENSION) | tee -a chess-$(N)-equation-auto-randomorder.data
	rm -f chess-$(N)-equation-mod3-randomorder.$(EXTENSION)

chess-$(N)-equation-integer-randomorder.data:
	$(GENERATOR) -C -n $(N) -r chess-$(N)-equation-integer-randomorder -p e | tee chess-$(N)-equation-integer-randomorder.data
	$(RANDOMIZER) chess-$(N)-equation-integer-randomorder.cnf $(SEED)
	$(EXTRACTOR) -i chess-$(N)-equation-integer-randomorder.cnf -o chess-$(N)-equation-integer-randomorder.schedule -v 2 | tee -a chess-$(N)-equation-integer-randomorder.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-equation-integer-randomorder.cnf -s chess-$(N)-equation-integer-randomorder.schedule -m i \
		-p chess-$(N)-equation-integer-randomorder.order -o chess-$(N)-equation-integer-randomorder.$(EXTENSION) 2>&1 | tee -a chess-$(N)-equation-integer-randomorder.data
	$(CHECKER) chess-$(N)-equation-integer-randomorder.cnf chess-$(N)-equation-integer-randomorder.$(EXTENSION) | tee -a chess-$(N)-equation-integer-randomorder.data
	rm -f chess-$(N)-equation-integer-randomorder.$(EXTENSION)


chess-$(N)-constraint.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-constraint -p c | tee chess-$(N)-constraint.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-constraint.cnf -s chess-$(N)-constraint.schedule \
		-p chess-$(N)-constraint.order -o chess-$(N)-constraint.$(EXTENSION) 2>&1 | tee -a chess-$(N)-constraint.data
	$(CHECKER) chess-$(N)-constraint.cnf chess-$(N)-constraint.$(EXTENSION) | tee -a chess-$(N)-constraint.data
	rm -f chess-$(N)-constraint.$(EXTENSION)

chess-$(N)-constraint-dual.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-constraint-dual -p d | tee chess-$(N)-constraint-dual.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-constraint-dual.cnf -s chess-$(N)-constraint-dual.schedule \
		-p chess-$(N)-constraint-dual.order -o chess-$(N)-constraint-dual.$(EXTENSION) 2>&1 | tee -a chess-$(N)-constraint-dual.data
	$(CHECKER) chess-$(N)-constraint-dual.cnf chess-$(N)-constraint-dual.$(EXTENSION) | tee -a chess-$(N)-constraint-dual.data
	rm -f chess-$(N)-constraint-dual.$(EXTENSION)


chess-$(N)-constraint-dual-randomorder.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-constraint-dual-randomorder -p d | tee chess-$(N)-constraint-dual-randomorder.data
	$(RANDOMIZER) chess-$(N)-constraint-dual-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-constraint-dual-randomorder.cnf -s chess-$(N)-constraint-dual-randomorder.schedule \
		-p chess-$(N)-constraint-dual-randomorder.order -o chess-$(N)-constraint-dual-randomorder.$(EXTENSION) 2>&1 | tee -a chess-$(N)-constraint-dual-randomorder.data
	$(CHECKER) chess-$(N)-constraint-dual-randomorder.cnf chess-$(N)-constraint-dual-randomorder.$(EXTENSION) | tee -a chess-$(N)-constraint-dual-randomorder.data
	rm -f chess-$(N)-constraint-dual-randomorder.$(EXTENSION)


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
	$(GRABBER) chess-*-equation-mod3.data > chess-equation-mod3.csv
	$(GRABBER) chess-*-equation-integer.data > chess-equation-integer.csv
	$(GRABBER) chess-*-equation-auto.data > chess-equation-auto.csv
	$(GRABBER) chess-*-equation-auto-randomorder.data > chess-equation-auto-randomorder.csv
	$(AVERAGE) chess-equation-auto.csv chess-equation-auto-randomorder.csv > chess-equation-auto-average.csv
	$(GRABBER) chess-*-bucket.data > chess-bucket.csv
	$(GRABBER) chess-*-noquant.data > chess-noquant.csv
	$(GRABBER) chess-*-noschedule.data > chess-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
