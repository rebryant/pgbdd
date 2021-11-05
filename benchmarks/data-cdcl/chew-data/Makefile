INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

GENERATOR = ../../chew-code/parity-cnf
GRABBER = ../../grab_clauses_cdcl.py
CDCL=../../../../kissat/build/kissat
CMS = /Users/bryant/repos/cryptominisat/cryptominisat5
DRAT=../../../../drat-trim/drat-trim

c: chew-$(N)-$(SEED)-cdcl.data
cms: chew-$(N)-$(SEED)-cms.data
cmsx: chew-$(N)-$(SEED)-cmsx.data

chew-$(N)-$(SEED)-cdcl.data:
	$(GENERATOR) $(N)-$(SEED) $(SEED) | tee chew-$(N)-$(SEED)-cdcl.data
	mv formula.cnf chew-$(N)-$(SEED)-cdcl.cnf
	$(CDCL) --unsat --no-binary chew-$(N)-$(SEED)-cdcl.cnf chew-$(N)-$(SEED)-cdcl.drat | tee -a chew-$(N)-$(SEED)-cdcl.data
	$(DRAT) chew-$(N)-$(SEED)-cdcl.cnf chew-$(N)-$(SEED)-cdcl.drat | tee -a chew-$(N)-$(SEED)-cdcl.data
	rm -f chew-$(N)-$(SEED)-cdcl.drat

chew-$(N)-$(SEED)-cms.data:
	$(GENERATOR) $(N)-$(SEED) $(SEED) | tee chew-$(N)-$(SEED)-cms.data
	mv formula.cnf chew-$(N)-$(SEED)-cms.cnf
	$(CMS) chew-$(N)-$(SEED)-cms.cnf chew-$(N)-$(SEED)-cms.drat | tee -a chew-$(N)-$(SEED)-cms.data
	$(DRAT) chew-$(N)-$(SEED)-cms.cnf chew-$(N)-$(SEED)-cms.drat | tee -a chew-$(N)-$(SEED)-cms.data
	rm -f chew-$(N)-$(SEED)-cms.drat

chew-$(N)-$(SEED)-cmsx.data:
	$(GENERATOR) $(N)-$(SEED) $(SEED) | tee chew-$(N)-$(SEED)-cmsx.data
	mv formula.cnf chew-$(N)-$(SEED)-cmsx.cnf
	$(CMS) chew-$(N)-$(SEED)-cmsx.cnf | tee -a chew-$(N)-$(SEED)-cmsx.data


data:
	$(GRABBER) chew*-cdcl.data > chew-cdcl.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.drat *.data *.order *.schedule
