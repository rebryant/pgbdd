CC=gcc
CFLAGS = -O0 -g

all: lrat-check

csapp-subset.o: csapp-subset.c csapp-subset.h
	$(CC) $(CFLAGS) -c csapp-subset.c

stream.o: stream.c stream.h csapp-subset.h
	$(CC) $(CFLAGS) -c stream.c

translator: translator.c csapp-subset.o stream.o
	$(CC) $(CFLAGS) -o translator translator.c csapp-subset.o stream.o

lrat-check: lrat-check.c
	gcc -g lrat-check.c -O2 -o lrat-check

clean:
	rm -f lrat-check

