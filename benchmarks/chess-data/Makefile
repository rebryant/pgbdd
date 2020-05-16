INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../chess.py
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

q: chess-$(N).data

chess-$(N).data:
	$(GENERATOR) -n $(N) -r chess-$(N) | tee chess-$(N).data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N).cnf -s chess-$(N).schedule \
		-p chess-$(N).order -o chess-$(N).proof | tee -a chess-$(N).data
	$(CHECKER) -v chess-$(N).proof | tee -a chess-$(N).data
	rm -f chess-$(N).proof

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.proof *.data *.order *.schedule
