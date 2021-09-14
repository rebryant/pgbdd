INTERP = python3

AVERAGE = $(INTERP) ../../average_csv.py
DDIR = ../pigeon-direct-data
TDIR = ../pigeon-tseitin-data


data:
	$(AVERAGE) $(DDIR)/pigeon-direct-constraint.csv $(TDIR)/pigeon-tseitin-constraint.csv > pigeon-average-constraint.csv
	$(AVERAGE) $(DDIR)/pigeon-direct-constraint-randomorder.csv $(TDIR)/pigeon-tseitin-constraint-randomorder.csv > pigeon-average-constraint-randomorder.csv
	$(AVERAGE) pigeon-average-constraint.csv pigeon-average-constraint-randomorder.csv > pigeon-average-constraint-average.csv

clean:
	rm -f *~

superclean: clean
	rm -f *.csv
