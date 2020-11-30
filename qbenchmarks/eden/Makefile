CC = gcc
CFLAGS = -O1 -g

all: gen-goe-plain gen-goe-doublediag gen-goe-ninety gen-goe-oneeighty

gen-goe-plain: GoE-QBF.c
	$(CC) $(CFLAGS) -DPLAIN  -o gen-goe-plain GoE-QBF.c

gen-goe-doublediag: GoE-QBF.c
	$(CC) $(CFLAGS) -DDOUBLEDIAG  -o gen-goe-doublediag GoE-QBF.c

gen-goe-ninety: GoE-QBF.c
	$(CC) $(CFLAGS) -DNINETY  -o gen-goe-ninety GoE-QBF.c

gen-goe-oneeighty: GoE-QBF.c
	$(CC) $(CFLAGS) -DONEEIGHTY  -o gen-goe-oneeighty GoE-QBF.c


clean:
	rm -rf *.dSYM
	rm -f *~ gen-goe-*

