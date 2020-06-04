INTERP = python3
MODES = LP
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../xortree.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../booleforce-1.3/tracecheck

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
		-p xor-$(N)-$(MODES).order -o xor-$(N)-$(MODES).proof | tee -a xor-$(N)-$(MODES).data
	$(CHECKER) -v xor-$(N)-$(MODES).proof | tee -a xor-$(N)-$(MODES).data
	rm -f xor-$(N)-$(MODES).proof

xor-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noquant -m $(MODES) | tee xor-$(N)-noquant.data
	grep -v "q" xor-$(N)-noquant.schedule > xor-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noquant.cnf -s xor-$(N)-noquant-stripped.schedule \
		-p xor-$(N)-noquant.order -o xor-$(N)-noquant.proof | tee -a xor-$(N)-noquant.data
	$(CHECKER) -v xor-$(N)-noquant.proof | tee -a xor-$(N)-noquant.data
	rm -f xor-$(N)-noquant.proof

xor-$(N)-noschedule.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noschedule -m $(MODES) | tee xor-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noschedule.cnf \
		-p xor-$(N)-noschedule.order -o xor-$(N)-noschedule.proof | tee -a xor-$(N)-noschedule.data
	$(CHECKER) -v xor-$(N)-noschedule.proof | tee -a xor-$(N)-noschedule.data
	rm -f xor-$(N)-noschedule.proof

xor-$(N)-noorder.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noorder -m $(MODES) | tee xor-$(N)-noorder.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noorder.cnf -s xor-$(N)-noorder.schedule \
		-o xor-$(N)-noorder.proof | tee -a xor-$(N)-noorder.data
	$(CHECKER) -v xor-$(N)-noorder.proof | tee -a xor-$(N)-noorder.data
	rm -f xor-$(N)-noorder.proof

xor-$(N)-toproots.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-toproots -m $(MODES) | tee xor-$(N)-toproots.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-toproots.cnf -b \
		-p xor-$(N)-toproots.order -o xor-$(N)-toproots.proof | tee -a xor-$(N)-toproots.data
	$(CHECKER) -v xor-$(N)-toproots.proof | tee -a xor-$(N)-toproots.data
	rm -f xor-$(N)-toproots.proof

xor-$(N)-topflip.data:
	$(GENERATOR) -O f -n $(N) -r xor-$(N)-topflip -m $(MODES) | tee xor-$(N)-topflip.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-topflip.cnf -b \
		-p xor-$(N)-topflip.order -o xor-$(N)-topflip.proof | tee -a xor-$(N)-topflip.data
	$(CHECKER) -v xor-$(N)-topflip.proof | tee -a xor-$(N)-topflip.data
	rm -f xor-$(N)-topflip.proof


xor-$(N)-topinputs.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-topinputs -m $(MODES) | tee xor-$(N)-topinputs.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-topinputs.cnf -b \
		-o xor-$(N)-topinputs.proof | tee -a xor-$(N)-topinputs.data
	$(CHECKER) -v xor-$(N)-topinputs.proof | tee -a xor-$(N)-topinputs.data
	rm -f xor-$(N)-topinputs.proof


xor-$(N)-toprandom.data:
	$(GENERATOR) -O r -n $(N) -r xor-$(N)-toprandom -m $(MODES) | tee xor-$(N)-toprandom.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-toprandom.cnf -b \
		-p xor-$(N)-toprandom.order -o xor-$(N)-toprandom.proof | tee -a xor-$(N)-toprandom.data
	$(CHECKER) -v xor-$(N)-toprandom.proof | tee -a xor-$(N)-toprandom.data
	rm -f xor-$(N)-toprandom.proof


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.proof *.data *.order *.schedule
