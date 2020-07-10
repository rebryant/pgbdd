INTERP = python3
N = 10
VLEVEL = 1
SEED=123456

FULLGENERATOR = ../../chew-code/parity
GENERATOR = ../../chew-code/parity-cnf
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../protoB/solver.py
CHECKER = ../../../pcaas/lrat-check
UPLOADER = ../../../pcaas/upload
GRABBER = ../../grab_clauses.py
DGRABBER = ./grab_drat.py
EXTENSION = lrat
HOST = whaleshark.ics.cs.cmu.edu
PMODE = t

io: chew-$(N)-inputorder.data
ro: chew-$(N)-randomorder.data
nq: chew-$(N)-noquant.data
cd: chew-$(N)-drat.data

iop: chew-$(N)-inputorder-pipe.data
rop: chew-$(N)-randomorder-pipe.data
nqp: chew-$(N)-noquant-pipe.data

chew-$(N)-drat.data:
	$(FULLGENERATOR) $(N) $(SEED) | tee chew-$(N)-drat.data
	rm -f formula.*

chew-$(N)-inputorder.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-inputorder.data
	mv formula.cnf chew-$(N)-inputorder.cnf
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-inputorder.cnf -b \
		-o chew-$(N)-inputorder.$(EXTENSION) 2>&1 | tee -a chew-$(N)-inputorder.data
	$(CHECKER) chew-$(N)-inputorder.cnf chew-$(N)-inputorder.$(EXTENSION) | tee -a chew-$(N)-inputorder.data
	rm -f chew-$(N)-inputorder.$(EXTENSION)

chew-$(N)-inputorder-pipe.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-inputorder-pipe.data
	mv formula.cnf chew-$(N)-inputorder-pipe.cnf
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-inputorder-pipe.cnf -b -m $(PMODE) -L chew-$(N)-inputorder-pipe.data \
		 | $(UPLOADER) -m $(PMODE) -H $(HOST) -c chew-$(N)-inputorder-pipe.cnf | tee -a chew-$(N)-inputorder-pipe.data

chew-$(N)-randomorder.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-randomorder.data
	mv formula.cnf chew-$(N)-randomorder.cnf
	$(RANDOMIZER) chew-$(N)-randomorder.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-randomorder.cnf -b -p chew-$(N)-randomorder.order \
		-o chew-$(N)-randomorder.$(EXTENSION) 2>&1 | tee -a chew-$(N)-randomorder.data
	$(CHECKER) chew-$(N)-randomorder.cnf chew-$(N)-randomorder.$(EXTENSION) | tee -a chew-$(N)-randomorder.data
	rm -f chew-$(N)-randomorder.$(EXTENSION)

chew-$(N)-randomorder-pipe.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-randomorder-pipe.data
	mv formula.cnf chew-$(N)-randomorder-pipe.cnf
	$(RANDOMIZER) chew-$(N)-randomorder-pipe.cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-randomorder-pipe.cnf -b -p chew-$(N)-randomorder-pipe.order \
		   -m $(PMODE) -L chew-$(N)-randomorder-pipe.data \
		 | $(UPLOADER) -m $(PMODE) -H $(HOST) -c chew-$(N)-randomorder-pipe.cnf | tee -a chew-$(N)-randomorder-pipe.data

chew-$(N)-noquant.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-noquant.data
	mv formula.cnf chew-$(N)-noquant.cnf
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-noquant.cnf \
		-o chew-$(N)-noquant.$(EXTENSION) 2>&1 | tee -a chew-$(N)-noquant.data
	$(CHECKER) chew-$(N)-noquant.cnf chew-$(N)-noquant.$(EXTENSION) | tee -a chew-$(N)-noquant.data
	rm -f chew-$(N)-noquant.$(EXTENSION)

chew-$(N)-noquant-pipe.data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-noquant.data
	mv formula.cnf chew-$(N)-noquant.cnf
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-noquant.cnf \
		   -m $(PMODE) -L chew-$(N)-noquant-pipe.data \
		 | $(UPLOADER) -m $(PMODE) -H $(HOST) -c chew-$(N)-noquant-pipe.cnf | tee -a chew-$(N)-noquant-pipe.data

data:
	$(GRABBER) chew*-randomorder.data > chew-randomorder.csv
	$(GRABBER) chew*-inputorder.data > chew-inputorder.csv
	$(DGRABBER) chew*-inputorder.data chew*-drat.data > chew-drat.csv
	$(GRABBER) chew*-noquant.data > chew-noquant.csv
clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
