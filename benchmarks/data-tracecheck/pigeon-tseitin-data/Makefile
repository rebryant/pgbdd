INTERP = python3
N = 10
VLEVEL = 1

GENERATOR = $(INTERP) ../pigeon-tseitin.py
SOLVER = $(INTERP) ../../prototype/solver.py
CHECKER = ../../booleforce-1.3/tracecheck

q: pigeon-tseitin-$(N)-quant.data
b: pigeon-tseitin-$(N)-bucket.data
l: pigeon-tseitin-$(N)-linear.data

pigeon-tseitin-$(N)-quant.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-quant.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf -s pigeon-tseitin-$(N).schedule \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).proof | tee -a pigeon-tseitin-$(N)-quant.data
	$(CHECKER) -v pigeon-tseitin-$(N).proof | tee -a pigeon-tseitin-$(N)-quant.data
	rm -f pigeon-tseitin-$(N).proof

pigeon-tseitin-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).proof | tee -a pigeon-tseitin-$(N)-bucket.data
	$(CHECKER) -v pigeon-tseitin-$(N).proof | tee -a pigeon-tseitin-$(N)-bucket.data
	rm -f pigeon-tseitin-$(N).proof

pigeon-tseitin-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).proof | tee -a pigeon-tseitin-$(N)-linear.data
	$(CHECKER) -v pigeon-tseitin-$(N).proof | tee -a pigeon-tseitin-$(N)-linear.data
	rm -f pigeon-tseitin-$(N).proof
