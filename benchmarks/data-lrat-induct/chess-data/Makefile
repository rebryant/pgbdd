INTERP = python3
N = 8
M = 6
VLEVEL = 1

GENERATOR = $(INTERP) ../../chess-induct.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
GRABBER = ../../grab_clauses.py
EXTENSION = lrat

q: chessi-$(N)-$(M)-column.data

chessi-$(N)-$(M)-column.data:
	$(GENERATOR) -f -n $(N) -m $(M) -r chessi-$(N)-$(M)-column | tee chessi-$(N)-$(M)-column.data
	$(SOLVER) -v $(VLEVEL) -i chessi-$(N)-$(M)-column.cnf -s chessi-$(N)-$(M)-column.schedule \
		-p chessi-$(N)-$(M)-column.order -o chessi-$(N)-$(M)-column.$(EXTENSION) 2>&1 | tee -a chessi-$(N)-$(M)-column.data
	$(CHECKER) chessi-$(N)-$(M)-column.cnf chessi-$(N)-$(M)-column.$(EXTENSION) | tee -a chessi-$(N)-$(M)-column.data
	rm -f chessi-$(N)-$(M)-column.$(EXTENSION)

data:
	$(GRABBER) chess-???.data > chess-columnscan.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
