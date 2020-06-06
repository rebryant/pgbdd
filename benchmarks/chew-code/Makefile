all: parity parity-cnf

parity: Source.cpp
	g++ Source.cpp -std=c++11 -g -O2 -o parity

parity-cnf: Source.cpp
	g++ Source.cpp -std=c++11 -g -O2 -DCNF_ONLY -o parity-cnf


clean:
	rm -f parity parity-cnf
