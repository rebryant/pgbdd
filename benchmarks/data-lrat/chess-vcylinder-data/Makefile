INTERP = python3
N = 10
VLEVEL = 2

GENERATOR = $(INTERP) ../../chess.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

q: chess-vcylinder-$(N)-column.data

nq: chess-vcylinder-$(N)-noquant.data

ns: chess-vcylinder-$(N)-noschedule.data

b: chess-vcylinder-$(N)-bucket.data

gb: chess-vcylinder-$(N)-gbucket.data

chess-vcylinder-$(N)-column.data:
	$(GENERATOR) -w v -n $(N) -r chess-vcylinder-$(N)-column | tee chess-vcylinder-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-vcylinder-$(N)-column.cnf -s chess-vcylinder-$(N)-column.schedule \
		-p chess-vcylinder-$(N)-column.order -o chess-vcylinder-$(N)-column.$(EXTENSION) 2>&1 | tee -a chess-vcylinder-$(N)-column.data
	$(CHECKER) chess-vcylinder-$(N)-column.cnf chess-vcylinder-$(N)-column.$(EXTENSION) | tee -a chess-vcylinder-$(N)-column.data
	rm -f chess-vcylinder-$(N)-column.$(EXTENSION)


chess-vcylinder-$(N)-noquant.data:
	$(GENERATOR) -w v -n $(N) -r chess-vcylinder-$(N)-noquant | tee chess-vcylinder-$(N)-noquant.data
	grep -v "q" chess-vcylinder-$(N)-noquant.schedule > chess-vcylinder-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-vcylinder-$(N)-noquant.cnf -s chess-vcylinder-$(N)-noquant-stripped.schedule \
		-p chess-vcylinder-$(N)-noquant.order -o chess-vcylinder-$(N)-noquant.$(EXTENSION) 2>&1 | tee -a chess-vcylinder-$(N)-noquant.data
	$(CHECKER) chess-vcylinder-$(N)-noquant.cnf chess-vcylinder-$(N)-noquant.$(EXTENSION) | tee -a chess-vcylinder-$(N)-noquant.data
	rm -f chess-vcylinder-$(N)-noquant.$(EXTENSION)

chess-vcylinder-$(N)-noschedule.data:
	$(GENERATOR) -w v -n $(N) -r chess-vcylinder-$(N)-noschedule | tee chess-vcylinder-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i chess-vcylinder-$(N)-noschedule.cnf \
		-p chess-vcylinder-$(N)-noschedule.order -o chess-vcylinder-$(N)-noschedule.$(EXTENSION) 2>&1 | tee -a chess-vcylinder-$(N)-noschedule.data
	$(CHECKER) chess-vcylinder-$(N)-noschedule.cnf chess-vcylinder-$(N)-noschedule.$(EXTENSION) | tee -a chess-vcylinder-$(N)-noschedule.data
	rm -f chess-vcylinder-$(N)-noschedule.$(EXTENSION)

chess-vcylinder-$(N)-bucket.data:
	$(GENERATOR) -w v -n $(N) -r chess-vcylinder-$(N)-bucket | tee chess-vcylinder-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-vcylinder-$(N)-bucket.cnf \
		-p chess-vcylinder-$(N)-bucket.order -o chess-vcylinder-$(N)-bucket.$(EXTENSION) 2>&1 | tee -a chess-vcylinder-$(N)-bucket.data
	$(CHECKER) chess-vcylinder-$(N)-bucket.cnf chess-vcylinder-$(N)-bucket.$(EXTENSION) | tee -a chess-vcylinder-$(N)-bucket.data
	rm -f chess-vcylinder-$(N)-bucket.$(EXTENSION)

chess-vcylinder-$(N)-gbucket.data:
	$(GENERATOR) -w v -n $(N) -r chess-vcylinder-$(N)-gbucket | tee chess-vcylinder-$(N)-gbucket.data
	$(SOLVER) -v $(VLEVEL) -i chess-vcylinder-$(N)-gbucket.cnf -B chess-vcylinder-$(N)-gbucket.buckets \
		-p chess-vcylinder-$(N)-gbucket.order -o chess-vcylinder-$(N)-gbucket.$(EXTENSION) 2>&1 | tee -a chess-vcylinder-$(N)-gbucket.data
	$(CHECKER) chess-vcylinder-$(N)-gbucket.cnf chess-vcylinder-$(N)-gbucket.$(EXTENSION) | tee -a chess-vcylinder-$(N)-gbucket.data
	rm -f chess-vcylinder-$(N)-gbucket.$(EXTENSION)


data:
	$(GRABBER) chess-vcylinder-*-column.data > chess-vcylinder-column.csv
#	$(GRABBER) chess-vcylinder-*-bucket.data > chess-vcylinder-bucket.csv
#	$(GRABBER) chess-vcylinder-*-gbucket.data > chess-vcylinder-gbucket.csv
#	$(GRABBER) chess-vcylinder-*-noquant.data > chess-vcylinder-noquant.csv
#	$(GRABBER) chess-vcylinder-*-noschedule.data > chess-vcylinder-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
