# pgbdd
Proof-generated, BDD-based SAT solver

The program(s) here implement a SAT solver based on BDDs.  The key
feature is that, for unsatisfiable formulas, they also generate proofs
of unsatisfiable in Extended Resolution.

Some inspirations for this work include:

C. Sinz and A. Biere, "Extended resolution proofs for conjoining
BDDs," CSR, 2006.

T. Jussila, C. Sinz and A. Biere, "Extended resolution proofs for
symbolic SAT solving with quantification," SAT, 2006

J. Franco, M. Kouril, J. Schlipf, J. Ward, S. Weaver, M. Dransfeld,
and W. Fleet "SBSAT: a state-based, BDD-based satisfiability solver,"
SAT 2003

That is, the overall program operation is similar to that of SBSAT,
but it generates proofs using generalizations of the ideas found in
EBDDRES (Jussila, Sinz, Biere).

