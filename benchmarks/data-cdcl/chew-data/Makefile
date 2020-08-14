INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = ../../chew-code/parity-cnf
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
DRAT=../../../../drat-trim/drat-trim

c: chew-$(N)-cdcl.data

chew-$(N)-cdcl.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-cdcl.data
	mv formula.cnf chew-$(N)-cdcl.cnf
	$(CDCL) --unsat --no-binary chew-$(N)-cdcl.cnf chew-$(N)-cdcl.drat | tee -a chew-$(N)-cdcl.data
	$(DRAT) chew-$(N)-cdcl.cnf chew-$(N)-cdcl.drat | tee -a chew-$(N)-cdcl.data
	rm -f chew-$(N)-cdcl.drat

data:
	$(GRABBER) chew*-cdcl.data > chew-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.drat *.data *.order *.schedule
