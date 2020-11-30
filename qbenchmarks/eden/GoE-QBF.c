#include <stdio.h>
#include <stdlib.h>

// REB Notations as explanations.
// REB: Allow different aspect ratios

//#define PLAIN
//#define DOUBLEDIAG
//#define NINETY
//#define ONEEIGHTY
//#define BIGTEN

#ifdef PLAIN
const char *modename = "plain";
#endif    

#ifdef DOUBLEDIAG
const char *modename = "double-diag";
#endif    

#ifdef NINETY
const char *modename = "ninety";
#endif    

#ifdef ONEEIGHTY
const char *modename = "one-eighty";
#endif    

// REB: Generate constraint for specified cell.  Rotation is the
// new value at this position
void printInternal (int row, int column, int vsize, int hsize, int universals, int rotation) {
	int i,j,k,l;
	int cell[8];
	int center = row * (hsize + 2) + column + 1 + universals;

	cell[ 0 ] = center -1 - (hsize+2);
	cell[ 1 ] = cell[ 0 ] + 1;
	cell[ 2 ] = cell[ 1 ] + 1;
	cell[ 3 ] = center - 1;
	cell[ 4 ] = center + 1;
	cell[ 5 ] = center -1 + (hsize+2);
	cell[ 6 ] = cell[ 5 ] + 1;
	cell[ 7 ] = cell[ 6 ] + 1;

	// REB: If Count = 0 or 1, then new value = 0
	// Enumerate 8 combinations of 7 zeros
	// 8
	for( i = 0; i < 8; i++ ) {
	    for( j = 0;j < 8; j++ )
		if( j != i ) printf("%i ", cell[j] );
	    printf("-%i 0\n", rotation );
	}

	// REB: If Count = 2 then new value = old value
	// For all pairs (i, j), let positions i and j be 1 and all others be zero
	// 2 * 8 * 7 / 2 = 56
	for( i = 0; i < 8; i++ )
	  for( j = i+1; j < 8; j++ ) {
	      for( l= 0; l < 8; l++ )
	      {  if( (l==i) || (l==j) ) printf("-"); printf("%i ", cell[l] ); }
	      printf("-%i %i 0\n", center, rotation );

	      for( l= 0; l < 8; l++ )
	      {  if( (l==i) || (l==j) ) printf("-"); printf("%i ", cell[l] ); }
	      printf("%i -%i 0\n", center, rotation );
	  }

	// REB: If Count = 3, then new value = 1
	// For all triples (i, j, k), let positions i, j, and k be 1 and all others be zero
	// 8 * 7 * 6 / (3 * 2) = 56
	for( i = 0; i < 8; i++ )
	  for( j = i+1; j < 8; j++ )
	    for( k = j+1; k < 8; k++ ) {
	      for( l= 0; l < 8; l++ ) {
		if( (l==i) || (l==j) || (l==k) ) printf("-");
		printf("%i ", cell[l] );
	      }
	      printf("%i 0\n", rotation );
	    }

	// REB: If Count >= 4, then new value = 0
	// For all quadruples (i, j, k, l), let positions i, j, k, and l be 1
	// 8 * 7 * 6 * 5 / (2 * 3 * 4) = 70
	for (i = 0; i < 8; i++)
	  for (j = i + 1; j < 8; j++)
	    for (k = j + 1; k < 8; k++)
	      for (l = k + 1; l < 8; l++)
		printf("-%i -%i -%i -%i -%i 0\n", cell[i], cell[j], cell[k], cell[l], rotation );

	// Total clauses = 8 + 56 + 56 + 70 = 190
}


int main (int argc, char **argv )
{
    int i, j, hsize, vsize, existentials, universals;

	if( argc < 2 || argc > 3) {
	    printf("run: ./eden #size [#hsize]\n");
	    exit(0); }

	vsize = atoi(argv[1]);
	if (argc == 3) {
	    hsize = atoi(argv[2]);
	    if (hsize == 0)
		hsize  = vsize;
	}
	else
	    hsize = vsize;

	printf("c %d  X  %d Garden of Eden problem with %s symmetry\n", vsize, hsize, modename);

	// REB: Allow indexing from 1 to {v,h}size
	int map[ vsize+1 ][ hsize+1 ];

        for (i = 1; i <= vsize; ++i)
          for (j = 1; j <= hsize; ++j)
             map [i][j] = 0;

	// REB: Next index of existential variable
 	int tmp = 1;

#ifdef NINETY
	if (hsize != vsize) {
	    fprintf(stderr, "Can only do rotation symmetry for square grids\n");
	    exit(1);
	}
        // 90 degrees mapping
	// REB: Reflect single quadrant to all 4 rotations
        for (i = 1; i <= (vsize + 0) / 2; ++i)
          for (j = 1; j <= (hsize + 1) / 2; ++j) {
             map [i][j] = tmp;
             map [vsize - i + 1][ hsize - j + 1] = tmp;
             map [j][ hsize - i + 1] = tmp;
             map [vsize - j + 1][i] = tmp;
             tmp++;
          }
#endif
        // double reflection mapping
/*
        // REB: Reflect single quandrant to mirror in X and Y
        for (i = 1; i <= vsize / 2; ++i)
          for (j = 1; j <= (hsize + 1) / 2; ++j) {
             map [i][j] = tmp;
             map [vsize - i + 1][ j ] = tmp;
             map [i][hsize - j + 1] = tmp;
             map [vsize - i + 1][ hsize - j + 1] = tmp;
             tmp++;
          }
*/

#ifdef DOUBLEDIAG
	if (hsize != vsize) {
	    fprintf(stderr, "Can only do diagonal symmetry for square grids\n");
	    exit(1);
	}
        // double diagonal mapping
	// REB: Reflect triangle that is size high and size/2 wide
	// by mirroring to right and rotating this pair by 90
        for (i = 1; i <= vsize; ++i)
          for (j = i; j <= hsize + 1 - i; ++j) {
             map [i][j] = tmp;
             map [j][i] = tmp;
             map [vsize + 1 - i][hsize + 1 - j] = tmp;
             map [vsize + 1 - j][hsize + 1 - i] = tmp;
             tmp++;
          }
#endif

#ifdef ONEEIGHTY
	// REB: Reflect left half by rotating by 180 degrees
        for (i = 1; i <= vsize; ++i)
          for (j = 1; j <= hsize; ++j) {
             if (map[i][j]) continue;
             map [i][j] = tmp;
             map [vsize + 1 - i][hsize + 1 - j] = tmp;
             tmp++;
          }
#endif

#ifdef PLAIN
	// REB: Every cell has separate value
	// Row major ordering
        for (i = 1; i <= vsize; ++i)
          for (j = 1; j <= hsize; ++j) {
             map [i][j] = tmp++;
          }
#endif

#ifdef DOUBLEDIAG
        // REB: Double diag with odd size requires additional value at center
        if (vsize % 2) map [(vsize / 2) + 1][ (hsize / 2) + 1] = tmp++;
#endif
	// REB: One universal for each unique square
        universals   = tmp - 1;
	// REB: One existential for each square + square, expanded to include boundary values
	existentials = (vsize + 2) * (hsize + 2);

        tmp = 0;
	for (i = 1; i <= vsize; ++i)
	  for (j = 1; j <= hsize; ++j)
	      tmp++;

	printf ("p cnf %i %i\n", existentials + universals, tmp * 190);

	printf ("a ");
        for (i = 1; i <= universals; i++)
	    printf ("%i ", i); printf ("0\n");
	printf ("e "); for (i = 1; i <= existentials;  i++) printf ("%i ", universals + i); printf ("0\n");

	for (i = 1; i <= vsize; ++i)
	    for (j = 1; j <= hsize; ++j)
		printInternal (i, j, vsize, hsize, universals, map [i][j]);
	return 0;
}
