INTERP = python3
M = 3
VLEVEL = 1
PCT=50
SEED=123456

GENERATOR = ../../urquhart-li-code/generate
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
DRAT=../../../../drat-trim/drat-trim


c: urquhart-li-$(M)-cdcl.data


urquhart-li-$(M)-cdcl.data:
	$(GENERATOR) -m$(M) -p$(PCT) -furquhart-li-$(M)-cdcl.cnf | tee urquhart-li-$(M)-cdcl.data
	$(CDCL) --unsat --no-binary urquhart-li-$(M)-cdcl.cnf urquhart-li-$(M)-cdcl.drat | tee -a urquhart-li-$(M)-cdcl.data
	$(DRAT) urquhart-li-$(M)-cdcl.cnf urquhart-li-$(M)-cdcl.drat | tee -a urquhart-li-$(M)-cdcl.data
	rm -f urquhart-li-$(M)-cdcl.drat

data:
	$(GRABBER) urquhart-li-*-cdcl.data > urquhart-li-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.drat
