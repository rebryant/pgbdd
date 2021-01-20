INTERP = python3
T = 3
VLEVEL = 2
SEED = 1

GENERATOR = ../../kbf/gen-hardKB.py
VGENERATOR = ../../kbf/gen-hardKB-vorder.py
QGENERATOR = ../../kbf/gen-hardKB-qorder.py
REVERSER = ../../reverse.py
RANDOMIZER = ../../../benchmarks/randomizer.py
SOLVER = $(INTERP) ../../../qbf/qsolver.py
CHECKER = $(INTERP) ../../../qbf/qchecker.py
GRABBER = $(INTERP) ../../../benchmarks/grab_clauses.py
VGRAB=../grab_solve_v_check.py

EXTENSION = qproof

vo: kbf-$(T)-vo.data
rvo: kbf-$(T)-rvo.data
qo: kbf-$(T)-qo.data
rqo: kbf-$(T)-rqo.data
ran: kbf-$(T)-ran-$(SEED).data

kbf-$(T)-vo.data:
	$(GENERATOR) $(T) > kbf-$(T).qcnf 
	$(VGENERATOR) $(T) > kbf-$(T)-v.order 
	$(SOLVER) -m r -v $(VLEVEL) -i kbf-$(T).qcnf -p kbf-$(T)-v.order -b \
		-o kbf-$(T)-vo.$(EXTENSION) | tee kbf-$(T)-vo.data
	$(CHECKER) -i kbf-$(T).qcnf -p kbf-$(T)-vo.$(EXTENSION) | tee -a kbf-$(T)-vo.data
#	rm -f kbf-$(T)-vo.$(EXTENSION)

kbf-$(T)-rvo.data:
	$(GENERATOR) $(T) > kbf-$(T).qcnf 
	$(VGENERATOR) $(T) | $(REVERSER) > kbf-$(T)-rv.order 
	$(SOLVER) -m r -v $(VLEVEL) -i kbf-$(T).qcnf -p kbf-$(T)-rv.order -b \
		-o kbf-$(T)-rvo.$(EXTENSION) | tee kbf-$(T)-rvo.data
	$(CHECKER) -i kbf-$(T).qcnf -p kbf-$(T)-rvo.$(EXTENSION) | tee -a kbf-$(T)-rvo.data
	rm -f kbf-$(T)-rvo.$(EXTENSION)

kbf-$(T)-qo.data:
	$(GENERATOR) $(T) > kbf-$(T).qcnf 
	$(QGENERATOR) $(T) > kbf-$(T)-q.order 
	$(SOLVER) -m r -v $(VLEVEL) -i kbf-$(T).qcnf -p kbf-$(T)-q.order -b \
		-o kbf-$(T)-qo.$(EXTENSION) | tee kbf-$(T)-qo.data
	$(CHECKER) -i kbf-$(T).qcnf -p kbf-$(T)-qo.$(EXTENSION) | tee -a kbf-$(T)-qo.data
	rm -f kbf-$(T)-qo.$(EXTENSION)

kbf-$(T)-rqo.data:
	$(GENERATOR) $(T) > kbf-$(T).qcnf 
	$(QGENERATOR) $(T) | $(REVERSER) > kbf-$(T)-rq.order 
	$(SOLVER) -m r -v $(VLEVEL) -i kbf-$(T).qcnf -p kbf-$(T)-rq.order -b \
		-o kbf-$(T)-rqo.$(EXTENSION) | tee kbf-$(T)-rqo.data
	$(CHECKER) -i kbf-$(T).qcnf -p kbf-$(T)-rqo.$(EXTENSION) | tee -a kbf-$(T)-rqo.data
	rm -f kbf-$(T)-rqo.$(EXTENSION)

kbf-$(T)-ran-$(SEED).data:
	$(GENERATOR) $(T) > kbf-$(T)-ran-$(SEED).qcnf 
	$(RANDOMIZER) kbf-$(T)-ran-$(SEED).qcnf $(SEED)
	$(SOLVER) -m r -v $(VLEVEL) -i kbf-$(T)-ran-$(SEED).qcnf -p kbf-$(T)-ran-$(SEED).order -b \
		-o kbf-$(T)-ran-$(SEED).$(EXTENSION) | tee kbf-$(T)-ran-$(SEED).data
	$(CHECKER) -i kbf-$(T)-ran-$(SEED).qcnf -p kbf-$(T)-ran-$(SEED).$(EXTENSION) | tee -a kbf-$(T)-ran-$(SEED).data
	rm -f kbf-$(T)-ran-$(SEED).$(EXTENSION)

data:
#	$(GRABBER) kbf-*-vo.data > kbf-vo.csv
	$(GRABBER) kbf-*-rvo.data > kbf-bdd-rvo-clauses.csv
#	$(GRABBER) kbf-*-qo.data > kbf-qo.csv
	$(GRABBER) kbf-*-rqo.data > kbf-bdd-rqo-clauses.csv
	$(GRABBER) kbf-*-ran-*.data > kbf-bdd-ran-clauses.csv
	$(VGRAB) *.data | grep -v ERR > kbf-solve-check.csv


clean:
	rm -f *~

superclean: clean
	rm -f *.qcnf *.qrat *.qproof *.data *.order
