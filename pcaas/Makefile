CC=gcc
CFLAGS = -O0 -g

all: lrat-check

stream.o: stream.c stream.h
	$(CC) $(CFLAGS) -c stream.c

translator: translator.c stream.o
	$(CC) $(CFLAGS) -o translator translator.c stream.o

lrat-check: lrat-check.c
	gcc -g lrat-check.c -O2 -o lrat-check

clean:
	rm -f lrat-check

