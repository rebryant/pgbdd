INTERP = python3
MODES = LP
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../xortree.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../pcaas/lrat-check
EXTENSION = lratb

$(MODES): xor-$(N)-$(MODES).data

nq: xor-$(N)-noquant.data
ns: xor-$(N)-noschedule.data
no: xor-$(N)-noorder.data
tr: xor-$(N)-toproots.data
ti: xor-$(N)-topinputs.data
tf: xor-$(N)-topflip.data
tR: xor-$(N)-toprandom.data

xor-$(N)-$(MODES).data:
	$(GENERATOR) -n $(N) -r xor-$(N)-$(MODES) -m $(MODES) | tee xor-$(N)-$(MODES).data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-$(MODES).cnf -s xor-$(N)-$(MODES).schedule \
		-p xor-$(N)-$(MODES).order -o xor-$(N)-$(MODES).$(EXTENSION) | tee -a xor-$(N)-$(MODES).data
	$(CHECKER) xor-$(N)-$(MODES).cnf xor-$(N)-$(MODES).$(EXTENSION) | tee -a xor-$(N)-$(MODES).data
	rm -f xor-$(N)-$(MODES).$(EXTENSION)

xor-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noquant -m $(MODES) | tee xor-$(N)-noquant.data
	grep -v "q" xor-$(N)-noquant.schedule > xor-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noquant.cnf -s xor-$(N)-noquant-stripped.schedule \
		-p xor-$(N)-noquant.order -o xor-$(N)-noquant.$(EXTENSION) | tee -a xor-$(N)-noquant.data
	$(CHECKER) xor-$(N)-noquant.cnf xor-$(N)-noquant.$(EXTENSION) | tee -a xor-$(N)-noquant.data
	rm -f xor-$(N)-noquant.$(EXTENSION)

xor-$(N)-noschedule.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noschedule -m $(MODES) | tee xor-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noschedule.cnf \
		-p xor-$(N)-noschedule.order -o xor-$(N)-noschedule.$(EXTENSION) | tee -a xor-$(N)-noschedule.data
	$(CHECKER) xor-$(N)-noschedule.cnf xor-$(N)-noschedule.$(EXTENSION) | tee -a xor-$(N)-noschedule.data
	rm -f xor-$(N)-noschedule.$(EXTENSION)

xor-$(N)-noorder.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noorder -m $(MODES) | tee xor-$(N)-noorder.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noorder.cnf -s xor-$(N)-noorder.schedule \
		-o xor-$(N)-noorder.$(EXTENSION) | tee -a xor-$(N)-noorder.data
	$(CHECKER) xor-$(N)-noorder.cnf xor-$(N)-noorder.$(EXTENSION) | tee -a xor-$(N)-noorder.data
	rm -f xor-$(N)-noorder.$(EXTENSION)

xor-$(N)-toproots.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-toproots -m $(MODES) | tee xor-$(N)-toproots.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-toproots.cnf -b \
		-p xor-$(N)-toproots.order -o xor-$(N)-toproots.$(EXTENSION) | tee -a xor-$(N)-toproots.data
	$(CHECKER) xor-$(N)-toproots.cnf xor-$(N)-toproots.$(EXTENSION) | tee -a xor-$(N)-toproots.data
	rm -f xor-$(N)-toproots.$(EXTENSION)

xor-$(N)-topflip.data:
	$(GENERATOR) -o f -n $(N) -r xor-$(N)-topflip -m $(MODES) | tee xor-$(N)-topflip.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-topflip.cnf -b \
		-p xor-$(N)-topflip.order -o xor-$(N)-topflip.$(EXTENSION) | tee -a xor-$(N)-topflip.data
	$(CHECKER) xor-$(N)-topflip.cnf xor-$(N)-topflip.$(EXTENSION) | tee -a xor-$(N)-topflip.data
	rm -f xor-$(N)-topflip.$(EXTENSION)


xor-$(N)-topinputs.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-topinputs -m $(MODES) | tee xor-$(N)-topinputs.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-topinputs.cnf -b \
		-o xor-$(N)-topinputs.$(EXTENSION) | tee -a xor-$(N)-topinputs.data
	$(CHECKER) xor-$(N)-topinputs.cnf xor-$(N)-topinputs.$(EXTENSION) | tee -a xor-$(N)-topinputs.data
	rm -f xor-$(N)-topinputs.$(EXTENSION)


xor-$(N)-toprandom.data:
	$(GENERATOR) -o r -n $(N) -r xor-$(N)-toprandom -m $(MODES) | tee xor-$(N)-toprandom.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-toprandom.cnf -b \
		-p xor-$(N)-toprandom.order -o xor-$(N)-toprandom.$(EXTENSION) | tee -a xor-$(N)-toprandom.data
	$(CHECKER) xor-$(N)-toprandom.cnf xor-$(N)-toprandom.$(EXTENSION) | tee -a xor-$(N)-toprandom.data
#	rm -f xor-$(N)-toprandom.$(EXTENSION)


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule
