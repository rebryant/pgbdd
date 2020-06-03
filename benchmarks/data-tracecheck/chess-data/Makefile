INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../chess.py
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

q: chess-$(N).data

nq: chess-$(N)-noquant.data

ns: chess-$(N)-noschedule.data

l: chess-$(N)-linear.data

b: chess-$(N)-bucket.data

chess-$(N).data:
	$(GENERATOR) -n $(N) -r chess-$(N) | tee chess-$(N).data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N).cnf -s chess-$(N).schedule \
		-p chess-$(N).order -o chess-$(N).proof | tee -a chess-$(N).data
	$(CHECKER) -v chess-$(N).proof | tee -a chess-$(N).data
	rm -f chess-$(N).proof

chess-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noquant | tee chess-$(N)-noquant.data
	grep -v "q" chess-$(N)-noquant.schedule > chess-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noquant.cnf -s chess-$(N)-noquant-stripped.schedule \
		-p chess-$(N)-noquant.order -o chess-$(N)-noquant.proof | tee -a chess-$(N)-noquant.data
	$(CHECKER) -v chess-$(N)-noquant.proof | tee -a chess-$(N)-noquant.data
	rm -f chess-$(N)-noquant.proof

chess-$(N)-noschedule.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noschedule | tee chess-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noschedule.cnf \
		-p chess-$(N)-noschedule.order -o chess-$(N)-noschedule.proof | tee -a chess-$(N)-noschedule.data
	$(CHECKER) -v chess-$(N)-noschedule.proof | tee -a chess-$(N)-noschedule.data
	rm -f chess-$(N)-noschedule.proof

chess-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-linear | tee chess-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-linear.cnf -s chess-$(N)-linear.schedule \
		-p chess-$(N)-linear.order -o chess-$(N)-linear.proof | tee -a chess-$(N)-linear.data
	$(CHECKER) -v chess-$(N)-linear.proof | tee -a chess-$(N)-linear.data
	rm -f chess-$(N)-linear.proof

chess-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-bucket | tee chess-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-$(N)-bucket.cnf \
		-p chess-$(N)-bucket.order -o chess-$(N)-bucket.proof | tee -a chess-$(N)-bucket.data
	$(CHECKER) -v chess-$(N)-bucket.proof | tee -a chess-$(N)-bucket.data
	rm -f chess-$(N)-bucket.proof



clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.proof *.data *.order *.schedule
