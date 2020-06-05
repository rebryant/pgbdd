INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = ../../chew-code/parity
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check

io: chew-$(N)-inputorder.data


chew-$(N)-inputorder.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-inputorder.data
	mv formula.cnf chew-$(N)-inputorder.cnf
	rm -f formula.drat
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-inputorder.cnf -b \
		-O chew-$(N)-inputorder.lrat | tee -a chew-$(N)-inputorder.data
	$(CHECKER) chew-$(N)-inputorder.cnf chew-$(N)-inputorder.lrat | tee -a chew-$(N)-inputorder.data
	rm -f chew-$(N)-inputorder.lrat

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
