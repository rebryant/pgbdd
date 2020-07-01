INTERP = python3
N = 02000
VLEVEL = 1
SEED=123456

FULLGENERATOR = ../../chew-code/parity
GENERATOR = ../../chew-code/parity-cnf
RANDOMIZER = ../../randomizer.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
UPLOADER = ../../../pcaas/upload
GRABBER = ../../grab_clauses.py
DGRABBER = ./grab_drat.py
EXTENSION = lrat
HOST = whaleshark.ics.cs.cmu.edu
PORT = 6616
PMODE = t

ro: chew-$(N)-randomorder-file-$(EXTENSION).data
rop: chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).data

chew-$(N)-randomorder-file-$(EXTENSION).data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-randomorder-file-$(EXTENSION).data
	mv formula.cnf chew-$(N)-randomorder-file-$(EXTENSION).cnf
	$(RANDOMIZER) chew-$(N)-randomorder-file-$(EXTENSION).cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-randomorder-file-$(EXTENSION).cnf -b -p chew-$(N)-randomorder-file-$(EXTENSION).order \
		-o chew-$(N)-randomorder-file.$(EXTENSION) 2>&1 | tee -a chew-$(N)-randomorder-file-$(EXTENSION).data
	$(CHECKER) chew-$(N)-randomorder-file-$(EXTENSION).cnf chew-$(N)-randomorder-file.$(EXTENSION) \
		| tee -a chew-$(N)-randomorder-file-$(EXTENSION).data
	rm -f chew-$(N)-randomorder-file.$(EXTENSION)

chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).data:
	$(GENERATOR) $(N) $(SEED) | tee chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).data
	mv formula.cnf chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).cnf
	$(RANDOMIZER) chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).cnf $(SEED)
	$(SOLVER) -v $(VLEVEL) -i chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).cnf -b -p chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).order \
		   -m $(PMODE) -L chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).data \
		 | $(UPLOADER) -m $(PMODE) -H $(HOST) -P $(PORT) -c chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).cnf \
		 | tee -a chew-$(N)-randomorder-pipe-$(PMODE)-$(HOST).data


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
