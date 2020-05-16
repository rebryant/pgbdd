INTERP = python3
MODES = LP
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../xortree.py
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

xor-$(N)-$(MODES).data:
	$(GENERATOR) -n $(N) -r xor-$(N)-$(MODES) -m $(MODES) | tee xor-$(N)-$(MODES).data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-$(MODES).cnf -s xor-$(N)-$(MODES).schedule \
		-p xor-$(N)-$(MODES).order -o xor-$(N)-$(MODES).proof | tee -a xor-$(N)-$(MODES).data
	$(CHECKER) -v xor-$(N)-$(MODES).proof | tee -a xor-$(N)-$(MODES).data
	rm -f xor-$(N)-$(MODES).proof

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.proof *.data *.order *.schedule
