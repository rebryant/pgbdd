INTERP = python3
N = 10
VLEVEL = 2

GENERATOR = $(INTERP) ../../chess.py
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
DRAT=../../../../drat-trim/drat-trim


c: chess-$(N)-cdcl.data
t: chess-$(N)-cdcl-time.data

chess-$(N)-cdcl.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-cdcl | tee chess-$(N)-cdcl.data
	$(CDCL) --unsat --no-binary chess-$(N)-cdcl.cnf chess-$(N)-cdcl.drat | tee -a chess-$(N)-cdcl.data
	$(DRAT) chess-$(N)-cdcl.cnf chess-$(N)-cdcl.drat | tee -a chess-$(N)-cdcl.data
	rm -f chess-$(N)-cdcl.drat

chess-$(N)-cdcl-time.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-cdcl | tee chess-$(N)-cdcl-time.data
	$(CDCL) --unsat --no-binary chess-$(N)-cdcl.cnf chess-$(N)-cdcl.drat | tee -a chess-$(N)-cdcl-time.data
	rm -f chess-$(N)-cdcl.drat


data:
	$(GRABBER) chess-*-cdcl.data > chess-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.drat *.data *.order *.schedule
