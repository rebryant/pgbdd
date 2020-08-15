INTERP = python3
M = 3
VLEVEL = 1
SEED=1

# ./genurq 3 5 | more

GENERATOR = ../../urquhart-simon-code/genurq
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
DRAT=../../../../drat-trim/drat-trim


c: urquhart-simon-$(M)-$(SEED)-cdcl.data

urquhart-simon-$(M)-$(SEED)-cdcl.data:
	$(GENERATOR) $(M) $(SEED) > urquhart-simon-$(M)-$(SEED)-cdcl.cnf | tee urquhart-simon-$(M)-$(SEED)-cdcl.data
	$(CDCL) --unsat --no-binary urquhart-simon-$(M)-$(SEED)-cdcl.cnf urquhart-simon-$(M)-$(SEED)-cdcl.drat | tee -a urquhart-simon-$(M)-$(SEED)-cdcl.data
	$(DRAT) urquhart-simon-$(M)-$(SEED)-cdcl.cnf urquhart-simon-$(M)-$(SEED)-cdcl.drat | tee -a urquhart-simon-$(M)-$(SEED)-cdcl.data
	rm -f urquhart-simon-$(M)-$(SEED)-cdcl.drat

data:
	$(GRABBER) urquhart-simon-*-cdcl.data > urquhart-simon-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.drat
