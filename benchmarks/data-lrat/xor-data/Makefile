INTERP = python3
MODES = LP
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../../xortree.py
SOLVER = $(INTERP) ../../../prototype/solver.py
CHECKER = ../../../lrat/lrat-check

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
		-p xor-$(N)-$(MODES).order -O xor-$(N)-$(MODES).lrat | tee -a xor-$(N)-$(MODES).data
	$(CHECKER) xor-$(N)-$(MODES).cnf xor-$(N)-$(MODES).lrat | tee -a xor-$(N)-$(MODES).data
	rm -f xor-$(N)-$(MODES).lrat

xor-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noquant -m $(MODES) | tee xor-$(N)-noquant.data
	grep -v "q" xor-$(N)-noquant.schedule > xor-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noquant.cnf -s xor-$(N)-noquant-stripped.schedule \
		-p xor-$(N)-noquant.order -O xor-$(N)-noquant.lrat | tee -a xor-$(N)-noquant.data
	$(CHECKER) xor-$(N)-noquant.cnf xor-$(N)-noquant.lrat | tee -a xor-$(N)-noquant.data
	rm -f xor-$(N)-noquant.lrat

xor-$(N)-noschedule.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noschedule -m $(MODES) | tee xor-$(N)-noschedule.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noschedule.cnf \
		-p xor-$(N)-noschedule.order -O xor-$(N)-noschedule.lrat | tee -a xor-$(N)-noschedule.data
	$(CHECKER) xor-$(N)-noschedule.cnf xor-$(N)-noschedule.lrat | tee -a xor-$(N)-noschedule.data
	rm -f xor-$(N)-noschedule.lrat

xor-$(N)-noorder.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-noorder -m $(MODES) | tee xor-$(N)-noorder.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-noorder.cnf -s xor-$(N)-noorder.schedule \
		-O xor-$(N)-noorder.lrat | tee -a xor-$(N)-noorder.data
	$(CHECKER) xor-$(N)-noorder.cnf xor-$(N)-noorder.lrat | tee -a xor-$(N)-noorder.data
	rm -f xor-$(N)-noorder.lrat

xor-$(N)-toproots.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-toproots -m $(MODES) | tee xor-$(N)-toproots.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-toproots.cnf -b \
		-p xor-$(N)-toproots.order -O xor-$(N)-toproots.lrat | tee -a xor-$(N)-toproots.data
	$(CHECKER) xor-$(N)-toproots.cnf xor-$(N)-toproots.lrat | tee -a xor-$(N)-toproots.data
	rm -f xor-$(N)-toproots.lrat

xor-$(N)-topflip.data:
	$(GENERATOR) -O f -n $(N) -r xor-$(N)-topflip -m $(MODES) | tee xor-$(N)-topflip.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-topflip.cnf -b \
		-p xor-$(N)-topflip.order -O xor-$(N)-topflip.lrat | tee -a xor-$(N)-topflip.data
	$(CHECKER) xor-$(N)-topflip.cnf xor-$(N)-topflip.lrat | tee -a xor-$(N)-topflip.data
	rm -f xor-$(N)-topflip.lrat


xor-$(N)-topinputs.data:
	$(GENERATOR) -n $(N) -r xor-$(N)-topinputs -m $(MODES) | tee xor-$(N)-topinputs.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-topinputs.cnf -b \
		-O xor-$(N)-topinputs.lrat | tee -a xor-$(N)-topinputs.data
	$(CHECKER) xor-$(N)-topinputs.cnf xor-$(N)-topinputs.lrat | tee -a xor-$(N)-topinputs.data
	rm -f xor-$(N)-topinputs.lrat


xor-$(N)-toprandom.data:
	$(GENERATOR) -O r -n $(N) -r xor-$(N)-toprandom -m $(MODES) | tee xor-$(N)-toprandom.data
	$(SOLVER) -v $(VLEVEL) -i xor-$(N)-toprandom.cnf -b \
		-p xor-$(N)-toprandom.order -O xor-$(N)-toprandom.lrat | tee -a xor-$(N)-toprandom.data
	$(CHECKER) xor-$(N)-toprandom.cnf xor-$(N)-toprandom.lrat | tee -a xor-$(N)-toprandom.data
	rm -f xor-$(N)-toprandom.lrat


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule
