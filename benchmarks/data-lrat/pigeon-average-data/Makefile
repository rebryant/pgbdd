INTERP = python3

AVERAGE = $(INTERP) ../../average_csv.py
DDIR = ../pigeon-direct-data
TDIR = ../pigeon-tseitin-data


data:
	$(AVERAGE) $(DDIR)/pigeon-direct-constraint.csv $(TDIR)/pigeon-tseitin-constraint.csv > piegon-average-constraint.csv
	$(AVERAGE) $(DDIR)/pigeon-direct-constraint-randomorder.csv $(TDIR)/pigeon-tseitin-constraint-randomorder.csv > piegon-average-constraint-randomorder.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.csv
