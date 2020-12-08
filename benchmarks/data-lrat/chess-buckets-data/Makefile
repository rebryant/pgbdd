INTERP = python3
N = 10
VLEVEL = 2
BMODE=1

GENERATOR = $(INTERP) ../../chess_bucket.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

gb: chess-$(N)-gbucket-$(BMODE).data

chess-$(N)-gbucket-$(BMODE).data:
	$(GENERATOR) -n $(N) -r chess-$(N)-gbucket-$(BMODE) -m $(BMODE) | tee chess-$(N)-gbucket-$(BMODE).data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-gbucket-$(BMODE).cnf -B chess-$(N)-gbucket-$(BMODE).buckets \
		-p chess-$(N)-gbucket-$(BMODE).order -o chess-$(N)-gbucket-$(BMODE).$(EXTENSION) 2>&1 | tee -a chess-$(N)-gbucket-$(BMODE).data
	$(CHECKER) chess-$(N)-gbucket-$(BMODE).cnf chess-$(N)-gbucket-$(BMODE).$(EXTENSION) | tee -a chess-$(N)-gbucket-$(BMODE).data
	rm -f chess-$(N)-gbucket-$(BMODE).$(EXTENSION)


data:
	$(GRABBER) chess-*-gbucket-1.data > chess-gbucket-1.csv
	$(GRABBER) chess-*-gbucket-2.data > chess-gbucket-2.csv
	$(GRABBER) chess-*-gbucket-3.data > chess-gbucket-3.csv
	$(GRABBER) chess-*-gbucket-4.data > chess-gbucket-4.csv
	$(GRABBER) chess-*-gbucket-5.data > chess-gbucket-5.csv
	$(GRABBER) chess-*-gbucket-6.data > chess-gbucket-6.csv


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.buckets
