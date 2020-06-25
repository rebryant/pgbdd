CC=gcc
CFLAGS = -O0 -g -Wall

all: lrat-check translator lrat-server upload

stream.o: stream.c stream.h
	$(CC) $(CFLAGS) -c stream.c

lrat.o: lrat.c stream.h
	$(CC) $(CFLAGS) -c lrat.c

translator: translator.c stream.o
	$(CC) $(CFLAGS) -o translator translator.c stream.o

lrat-check: lrat-main.c stream.o lrat.o
	$(CC) $(CFLAGS) lrat-main.c stream.o lrat.o -o lrat-check

lrat-server: lrat-server.c stream.o lrat.o
	$(CC) $(CFLAGS) lrat-server.c stream.o lrat.o -o lrat-server

upload: upload.c stream.o
	$(CC) $(CFLAGS) upload.c stream.o -o upload

clean:
	rm -f lrat-check lrat-server translator upload *.o *~


