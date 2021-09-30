# Author: Tjark Weber
# (c) 2007

FILES= pigeonhole pigeon-augmented pigeon-equations

all: $(FILES)

pigeonhole: pigeonhole.c
	gcc -Wall -O3 pigeonhole.c -o pigeonhole

pigeon-augmented: pigeon-augmented.c
	gcc -Wall -O3 pigeon-augmented.c -o pigeon-augmented

pigeon-equations: pigeon-equations.c
	gcc -Wall -O3 pigeon-equations.c -o pigeon-equations

clean:
	rm -f pigeonhole pigeon-augmented pigeon-equations *.cnf *~

