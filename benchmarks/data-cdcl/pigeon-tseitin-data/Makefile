INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../pigeon-sinz.py
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
DRAT=../../../../drat-trim/drat-trim

c: pigeon-tseitin-$(N)-cdcl.data

t: pigeon-tseitin-$(N)-cdcl-time.data

pigeon-tseitin-$(N)-cdcl.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N)-cdcl | tee pigeon-tseitin-$(N)-cdcl.data
	$(CDCL) --unsat --no-binary pigeon-tseitin-$(N)-cdcl.cnf pigeon-tseitin-$(N)-cdcl.drat | tee -a pigeon-tseitin-$(N)-cdcl.data
	$(DRAT) pigeon-tseitin-$(N)-cdcl.cnf pigeon-tseitin-$(N)-cdcl.drat | tee -a pigeon-tseitin-$(N)-cdcl.data
	rm -f pigeon-tseitin-$(N)-cdcl.drat

pigeon-tseitin-$(N)-cdcl-time.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N)-cdcl | tee pigeon-tseitin-$(N)-cdcl-time.data
	$(CDCL) --unsat --no-binary pigeon-tseitin-$(N)-cdcl.cnf pigeon-tseitin-$(N)-cdcl.drat | tee -a pigeon-tseitin-$(N)-cdcl-time.data
	rm -f pigeon-tseitin-$(N)-cdcl.drat


data:
	$(GRABBER) pigeon-*-cdcl.data > pigeon-tseitin-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule *.drat
