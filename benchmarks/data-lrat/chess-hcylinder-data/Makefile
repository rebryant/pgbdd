INTERP = python3
N = 10
VLEVEL = 2

GENERATOR = $(INTERP) ../../chess.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

q: chess-hcylinder-$(N)-column.data

nq: chess-hcylinder-$(N)-noquant.data

ns: chess-hcylinder-$(N)-noschedule.data

b: chess-hcylinder-$(N)-bucket.data

gb: chess-hcylinder-$(N)-gbucket.data

chess-hcylinder-$(N)-column.data:
	$(GENERATOR) -w h -n $(N) -r chess-hcylinder-$(N)-column | tee chess-hcylinder-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-hcylinder-$(N)-column.cnf -s chess-hcylinder-$(N)-column.schedule \
		-p chess-hcylinder-$(N)-column.order -o chess-hcylinder-$(N)-column.$(EXTENSION) 2>&1 | tee -a chess-hcylinder-$(N)-column.data
	$(CHECKER) chess-hcylinder-$(N)-column.cnf chess-hcylinder-$(N)-column.$(EXTENSION) | tee -a chess-hcylinder-$(N)-column.data
	rm -f chess-hcylinder-$(N)-column.$(EXTENSION)


chess-hcylinder-$(N)-noquant.data:
	$(GENERATOR) -w h -n $(N) -r chess-hcylinder-$(N)-noquant | tee chess-hcylinder-$(N)-noquant.data
	grep -v "q" chess-hcylinder-$(N)-noquant.schedule > chess-hcylinder-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-hcylinder-$(N)-noquant.cnf -s chess-hcylinder-$(N)-noquant-stripped.schedule \
		-p chess-hcylinder-$(N)-noquant.order -o chess-hcylinder-$(N)-noquant.$(EXTENSION) 2>&1 | tee -a chess-hcylinder-$(N)-noquant.data
	$(CHECKER) chess-hcylinder-$(N)-noquant.cnf chess-hcylinder-$(N)-noquant.$(EXTENSION) | tee -a chess-hcylinder-$(N)-noquant.data
	rm -f chess-hcylinder-$(N)-noquant.$(EXTENSION)

chess-hcylinder-$(N)-noschedule.data:
	$(GENERATOR) -w h -n $(N) -r chess-hcylinder-$(N)-noschedule | tee chess-hcylinder-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i chess-hcylinder-$(N)-noschedule.cnf \
		-p chess-hcylinder-$(N)-noschedule.order -o chess-hcylinder-$(N)-noschedule.$(EXTENSION) 2>&1 | tee -a chess-hcylinder-$(N)-noschedule.data
	$(CHECKER) chess-hcylinder-$(N)-noschedule.cnf chess-hcylinder-$(N)-noschedule.$(EXTENSION) | tee -a chess-hcylinder-$(N)-noschedule.data
	rm -f chess-hcylinder-$(N)-noschedule.$(EXTENSION)

chess-hcylinder-$(N)-bucket.data:
	$(GENERATOR) -w h -n $(N) -r chess-hcylinder-$(N)-bucket | tee chess-hcylinder-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-hcylinder-$(N)-bucket.cnf \
		-p chess-hcylinder-$(N)-bucket.order -o chess-hcylinder-$(N)-bucket.$(EXTENSION) 2>&1 | tee -a chess-hcylinder-$(N)-bucket.data
	$(CHECKER) chess-hcylinder-$(N)-bucket.cnf chess-hcylinder-$(N)-bucket.$(EXTENSION) | tee -a chess-hcylinder-$(N)-bucket.data
	rm -f chess-hcylinder-$(N)-bucket.$(EXTENSION)

chess-hcylinder-$(N)-gbucket.data:
	$(GENERATOR) -w h -n $(N) -r chess-hcylinder-$(N)-gbucket | tee chess-hcylinder-$(N)-gbucket.data
	$(SOLVER) -v $(VLEVEL) -i chess-hcylinder-$(N)-gbucket.cnf -B chess-hcylinder-$(N)-gbucket.buckets \
		-p chess-hcylinder-$(N)-gbucket.order -o chess-hcylinder-$(N)-gbucket.$(EXTENSION) 2>&1 | tee -a chess-hcylinder-$(N)-gbucket.data
	$(CHECKER) chess-hcylinder-$(N)-gbucket.cnf chess-hcylinder-$(N)-gbucket.$(EXTENSION) | tee -a chess-hcylinder-$(N)-gbucket.data
	rm -f chess-hcylinder-$(N)-gbucket.$(EXTENSION)


data:
	$(GRABBER) chess-hcylinder-*-column.data > chess-hcylinder-column.csv
#	$(GRABBER) chess-hcylinder-*-bucket.data > chess-hcylinder-bucket.csv
#	$(GRABBER) chess-hcylinder-*-gbucket.data > chess-hcylinder-gbucket.csv
#	$(GRABBER) chess-hcylinder-*-noquant.data > chess-hcylinder-noquant.csv
#	$(GRABBER) chess-hcylinder-*-noschedule.data > chess-hcylinder-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
