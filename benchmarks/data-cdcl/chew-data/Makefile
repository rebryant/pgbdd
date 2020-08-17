INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = ../../chew-code/parity-cnf
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
DRAT=../../../../drat-trim/drat-trim

c: chew-$(N)-$(SEED)-cdcl.data

chew-$(N)-$(SEED)-cdcl.data:
	$(GENERATOR) $(N)-$(SEED) $(SEED) | tee chew-$(N)-$(SEED)-cdcl.data
	mv formula.cnf chew-$(N)-$(SEED)-cdcl.cnf
	$(CDCL) --unsat --no-binary chew-$(N)-$(SEED)-cdcl.cnf chew-$(N)-$(SEED)-cdcl.drat | tee -a chew-$(N)-$(SEED)-cdcl.data
	$(DRAT) chew-$(N)-$(SEED)-cdcl.cnf chew-$(N)-$(SEED)-cdcl.drat | tee -a chew-$(N)-$(SEED)-cdcl.data
	rm -f chew-$(N)-$(SEED)-cdcl.drat

data:
	$(GRABBER) chew*-cdcl.data > chew-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.drat *.data *.order *.schedule
