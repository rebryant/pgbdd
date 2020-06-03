N = 4
VLEVEL = 1
SEED = 1
GENERATOR = ../urquhart-code/urquhart
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

l: urquhart-$(N)-$(SEED)-linear.data
b: urquhart-$(N)-$(SEED)-bucket.data

urquhart-$(N)-$(SEED)-bucket.data:
	$(GENERATOR) $(N) $(SEED) > urquhart-$(N)-$(SEED).cnf
	$(SOLVER) -b -v $(VLEVEL) -i urquhart-$(N)-$(SEED).cnf -o urquhart-$(N)-$(SEED).proof | tee urquhart-$(N)-$(SEED)-bucket.data
	$(CHECKER) -v urquhart-$(N)-$(SEED).proof | tee -a urquhart-$(N)-$(SEED)-bucket.data
	rm -rv urquhart-$(N)-$(SEED).proof

urquhart-$(N)-$(SEED)-linear.data:
	$(GENERATOR) $(N) $(SEED) > urquhart-$(N)-$(SEED).cnf
	$(SOLVER) -v $(VLEVEL) -i urquhart-$(N)-$(SEED).cnf -o urquhart-$(N)-$(SEED).proof | tee urquhart-$(N)-$(SEED)-linear.data
	$(CHECKER) -v urquhart-$(N)-$(SEED).proof | tee -a urquhart-$(N)-$(SEED)-linear.data
	rm -rv urquhart-$(N)-$(SEED).proof

clean:
	rm -f *.proof *.cnf

superclean: clean
	rm -f *.data
