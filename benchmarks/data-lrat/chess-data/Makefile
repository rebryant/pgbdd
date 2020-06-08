INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../chess.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check
GRABBER = ../../grab_clauses.py

q: chess-$(N).data

nq: chess-$(N)-noquant.data

ns: chess-$(N)-noschedule.data

b: chess-$(N)-bucket.data

chess-$(N).data:
	$(GENERATOR) -n $(N) -r chess-$(N) | tee chess-$(N).data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N).cnf -s chess-$(N).schedule \
		-p chess-$(N).order -O chess-$(N).lrat | tee -a chess-$(N).data
	$(CHECKER) chess-$(N).cnf chess-$(N).lrat | tee -a chess-$(N).data
	rm -f chess-$(N).lrat

chess-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noquant | tee chess-$(N)-noquant.data
	grep -v "q" chess-$(N)-noquant.schedule > chess-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noquant.cnf -s chess-$(N)-noquant-stripped.schedule \
		-p chess-$(N)-noquant.order -O chess-$(N)-noquant.lrat | tee -a chess-$(N)-noquant.data
	$(CHECKER) chess-$(N)-noquant.cnf chess-$(N)-noquant.lrat | tee -a chess-$(N)-noquant.data
	rm -f chess-$(N)-noquant.lrat

chess-$(N)-noschedule.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noschedule | tee chess-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noschedule.cnf \
		-p chess-$(N)-noschedule.order -O chess-$(N)-noschedule.lrat | tee -a chess-$(N)-noschedule.data
	$(CHECKER) chess-$(N)-noschedule.cnf chess-$(N)-noschedule.lrat | tee -a chess-$(N)-noschedule.data
	rm -f chess-$(N)-noschedule.lrat

chess-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-bucket | tee chess-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-$(N)-bucket.cnf \
		-p chess-$(N)-bucket.order -O chess-$(N)-bucket.lrat | tee -a chess-$(N)-bucket.data
	$(CHECKER) chess-$(N)-bucket.cnf chess-$(N)-bucket.lrat | tee -a chess-$(N)-bucket.data
	rm -f chess-$(N)-bucket.lrat

data:
	$(GRABBER) chess-???.data > chess-columnscan.csv
	$(GRABBER) chess-*-bucket.data > chess-bucket.csv
	$(GRABBER) chess-*-noquant.data > chess-noquant.csv
	$(GRABBER) chess-*-noschedule.data > chess-noschedule.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
