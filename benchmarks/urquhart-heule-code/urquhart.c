#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int getEdge (int a, int b) {
  assert (a != b);
  assert (a >  0);
  assert (b >  0);
  int min = a, max = b;
  if (min > max) { min = b; max = a; }

  int res = min + (max - 2) * (max - 1) / 2;

  return res;
}

void printXOR (int* array, int size, int polarity) {
  int i, j, on;

  //  printf ("c XOR %i %i:\n", size, polarity);
  for (i = 0; i <  (1 << size); i++) {
    on = size + 1;
    for (j = 0; j < size; j++)
      if (i & (1 << j)) on++;
    if (on % 2 == polarity) {
      for (j = 0; j < size; j++) {
        if ((i & (1 << j)) == 0) printf ("-");
        printf("%i ", array[j]);
      }
      printf ("0\n");
    }
  }
}

int main (int argc, char** argv) {
  int i, j;

  if (argc <= 2) {
    printf ("use: ./urquhart [size] [seed]\n"); exit(0);
  }

  int m = atoi (argv[1]);
  int n = m * m;
  int nVertices = 2 * n;
  int seed = atoi (argv[2]);
  srand (seed);

  // allocate the graph
  int **matrix, *degree, *polarity;
  polarity = (int*) malloc (sizeof(int) * nVertices);
  degree   = (int*) malloc (sizeof(int) * nVertices);
  matrix   = (int**) malloc (sizeof(int*) * nVertices);
  for (i = 0; i < nVertices; i++) {
    polarity[i] = rand() % 2;
    degree[i]   = 0;
    matrix[i]   = (int *) malloc (sizeof(int) * nVertices);
    for (j = 0; j < nVertices; j++) matrix[i][j] = 0;
  }

  int count = 0;
  for (i = 0; i < nVertices; i++)
    count += polarity[i];

  if ((count % 2) == 0) polarity[0] ^= 1;

  // construct the bipartite graph (vertex degree at most 5)
  while (1) {
    int l = rand() % n;
    int r = (rand() % n) + n;
    if ((degree[l] == 5) || (degree[r] == 5)) {
      int flag = 1;
      for (i = 0; i < nVertices; i++)
        if (degree[i] == 0) flag = 0;
      if (flag) break;
    }
    else if (matrix[l][r] == 0) {
      matrix[l][r] = matrix[r][l] = 1;
      degree[l]++; degree[r]++;
    }
  }

  // add side edges
  for (i = 0; i < n - 1; i++) {
    matrix[i][i+1] = matrix[i+1][i] = 1;
    degree[i]++; degree[i+1]++;
    matrix[i+n][i+n+1] = matrix[i+n+1][i+n] = 1;
    degree[i+n]++; degree[i+n+1]++;
  }

  int nVar = nVertices * (nVertices - 1) / 2;
  int nCls = 0;
  for (i = 0; i < nVertices; i++)
    nCls += 1 << (degree[i] - 1);

  printf ("p cnf %i %i\n", nVar, nCls);

  // print CNF;
  int size, xor[7];
  for (i = 0; i < nVertices; i++) {
    size = 0;
    for (j = 0; j < nVertices; j++)
      if (matrix[i][j]) xor[size++] = getEdge (i+1, j+1);

    printXOR (xor, size, polarity[i]);
  }

}
