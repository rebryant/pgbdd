# Author: Tjark Weber
# (c) 2007

pigeonhole: pigeonhole.c
	gcc -Wall -O3 pigeonhole.c -o pigeonhole

pigeon-1.cnf: pigeonhole
	./pigeonhole 1 > pigeon-1.cnf

pigeon-2.cnf: pigeonhole
	./pigeonhole 2 > pigeon-2.cnf

pigeon-3.cnf: pigeonhole
	./pigeonhole 3 > pigeon-3.cnf

pigeon-4.cnf: pigeonhole
	./pigeonhole 4 > pigeon-4.cnf

pigeon-5.cnf: pigeonhole
	./pigeonhole 5 > pigeon-5.cnf

pigeon-6.cnf: pigeonhole
	./pigeonhole 6 > pigeon-6.cnf

pigeon-7.cnf: pigeonhole
	./pigeonhole 7 > pigeon-7.cnf

pigeon-8.cnf: pigeonhole
	./pigeonhole 8 > pigeon-8.cnf

pigeon-9.cnf: pigeonhole
	./pigeonhole 9 > pigeon-9.cnf

pigeon-10.cnf: pigeonhole
	./pigeonhole 10 > pigeon-10.cnf

pigeon-11.cnf: pigeonhole
	./pigeonhole 11 > pigeon-11.cnf

pigeon-12.cnf: pigeonhole
	./pigeonhole 12 > pigeon-12.cnf

pigeon-13.cnf: pigeonhole
	./pigeonhole 13 > pigeon-13.cnf

pigeon-14.cnf: pigeonhole
	./pigeonhole 14 > pigeon-14.cnf

pigeon-15.cnf: pigeonhole
	./pigeonhole 15 > pigeon-15.cnf

pigeon-16.cnf: pigeonhole
	./pigeonhole 16 > pigeon-16.cnf

pigeon-17.cnf: pigeonhole
	./pigeonhole 17 > pigeon-17.cnf

pigeon-18.cnf: pigeonhole
	./pigeonhole 18 > pigeon-18.cnf

pigeon-19.cnf: pigeonhole
	./pigeonhole 19 > pigeon-19.cnf

pigeon-20.cnf: pigeonhole
	./pigeonhole 20 > pigeon-20.cnf

.PHONY: cnf

cnf: pigeon-1.cnf \
     pigeon-2.cnf \
     pigeon-3.cnf \
     pigeon-4.cnf \
     pigeon-5.cnf \
     pigeon-6.cnf \
     pigeon-7.cnf \
     pigeon-8.cnf \
     pigeon-9.cnf \
     pigeon-10.cnf \
     pigeon-11.cnf \
     pigeon-12.cnf \
     pigeon-13.cnf \
     pigeon-14.cnf \
     pigeon-15.cnf \
     pigeon-16.cnf \
     pigeon-17.cnf \
     pigeon-18.cnf \
     pigeon-19.cnf \
     pigeon-20.cnf

.PHONY: clean

clean:
	rm -f pigeonhole pigeon-*.cnf *~
