N=8
INTERP = python3
PBIPDIR = ../../prototype
PGEN = ../generators/pigeon.py
CNFGEN = $(PBIPDIR)/pbip_cnf.py
PROOFGEN = $(PBIPDIR)/pbip_check.py
LRATDIR = ~/repos/drat-trim
LRAT = $(LRATDIR)/lrat-check
VLEVEL=1

php: php-$(N).ipbip

php-all: php-$(N).ipbip php-$(N).pbip php-$(N).lrat php-$(N).ldata
	cat php-$(N).{pdata,cnfdata,checkdata} > php-$(N).data

php-$(N).ipbip: $(PGEN)
	$(INTERP) $(PGEN) -n $(N) -v $(VLEVEL) -o php-$(N).ipbip | tee $*.pdata

.SUFFIXES: .ipbip .pbip .lrat .ldata

.ipbip.pbip:
	$(INTERP) $(CNFGEN) -v $(VLEVEL) -i $< -o $@ -c $*.cnf | tee $*.cnfdata

.pbip.lrat:
	$(INTERP) $(PROOFGEN) -v $(VLEVEL) -i $*.cnf -p $< -o $@ | tee $*.checkdata

.lrat.ldata:
	$(LRAT) $*.cnf $< | tee $@
