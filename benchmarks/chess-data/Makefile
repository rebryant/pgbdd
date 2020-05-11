INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../chess.py
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

nq: chess-$(N).proof

q: chess-$(N)-DQ.proof

chess-$(N).proof:
	$(GENERATOR) -n $(N) -r chess-$(N) | tee chess-$(N).data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N).cnf -s chess-$(N).schedule \
		-p chess-$(N).order -o chess-$(N).proof | tee -a chess-$(N).data
	$(CHECKER) -v chess-$(N).proof | tee -a chess-$(N).data

chess-$(N)-DQ.proof:
	$(GENERATOR) -Q -n $(N) -r chess-$(N)-DQ | tee chess-$(N)-DQ.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-DQ.cnf -s chess-$(N)-DQ.schedule \
		-p chess-$(N)-DQ.order -o chess-$(N)-DQ.proof | tee -a chess-$(N)-DQ.data
	$(CHECKER) -v chess-$(N)-DQ.proof | tee -a chess-$(N)-DQ.data

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.proof *.data *.order *.schedule
