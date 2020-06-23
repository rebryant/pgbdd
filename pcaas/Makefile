CC=gcc
CFLAGS = -O0 -g

all: lrat-check translator

stream.o: stream.c stream.h
	$(CC) $(CFLAGS) -c stream.c

lrat.o: lrat.c stream.h
	$(CC) $(CFLAGS) -c lrat.c

translator: translator.c stream.o
	$(CC) $(CFLAGS) -o translator translator.c stream.o

lrat-check: lrat-main.c stream.o lrat.o
	$(CC) $(CFLAGS) lrat-main.c stream.o lrat.o -o lrat-check

clean:
	rm -f lrat-check translator *.o *~


