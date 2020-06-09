/**CFile***********************************************************************

  FileName    [genurq.c]

  Synopsis    [Benchmark generator of the Urquhart's problem.]

  Description [Benchmark generator of the Urquhart's problem. It generate
               a DIMACS format file (under cnf) which has been
               demonstrate to be hard for resolution. The sizes are
               greater than 3.]

  Author      [Laurent Simon (simon@lri.fr)]

  Date        [May 1999]

  Copyright   [This file was created at the University of Paris XI.
  We makes no warranty about the suitability of this software for any purpose.
  It is presented on an AS IS basis.]

******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <time.h>


/*  #define DBG */
/*  #define DBG2  */

/* Uncomment this line to generate a dot file
   that contains the graph description of the
   generated expansion graph */
/* #define DUMPDOT */

#define DMAX 5 // Degré max initial des noeuds.

int myrand(int r) {
  return (rand()%r);
}

typedef struct {
  int link[DMAX + 2];
  int linktoens[DMAX + 2];
  int numlink[DMAX + 2];
  int degre;
  int charge;
} noeud;

noeud *noeuds[2];  // noeuds[0] et noeuds[1] représente les deux côtés
                 // du graphe bipartie

int *apiocher;
int *tabvars;

void affiche_noeud(noeud * n) {
  int i;
  fprintf(stderr, "C=%d, d=%d, vars=[",n->charge, n->degre);
  for(i=0;i<(n->degre - 1);i++)
    fprintf(stderr, "%d,",tabvars[n->numlink[i]]);
  fprintf(stderr, "%d]\n",tabvars[n->numlink[i]]);
}

int estdans(int src, int deg, int * tab) {
  int i;

  for(i=0;i<deg;i++) {
    if(tab[i]==src) return (-1);
  }
  return(0);
}

int getdegre() {
  return(myrand(DMAX));
    }

void achoisi(int * affect, int nb) {
  int i;
  for(i=0;i<nb;i++)
    fprintf(stdout, "%d ", affect[i]);
  fprintf(stdout, "0\n");
}

/* Si parite vrai, en choisir un nombre paire */
int choisirparmis(int* affect, int* t, int indice, int nb, int parite, int nbtot) {
  int nbc;
  if (nb==1) {
    if (parite)
      affect[indice] = t[indice] + 1;
    else
      affect[indice] = -t[indice] - 1;
    achoisi(affect,nbtot);
    return(1);
  }

  affect[indice] = t[indice] + 1;
  nbc = choisirparmis(affect, t, indice + 1, nb-1, parite, nbtot);
  affect[indice] = -t[indice] - 1;
  nbc += choisirparmis(affect, t, indice + 1, nb-1, (parite==0?1:0),nbtot);
  affect[indice] = 0;
  return(nbc);
}

/* renvois le nb de clause créées. */
int creerBaseNoeud(noeud * n) {
  int nbc = 0;
  int* choisir;
  int i;
  int * tabaffect;

  choisir = (int*)malloc(sizeof(int)* (n->degre));
  tabaffect = (int*)malloc(sizeof(int)* (n->degre));
  for(i=0;i<(n->degre);i++) {
    choisir[i] = tabvars[n->numlink[i]];
    tabaffect[i] = 0;
  }
  
  nbc = choisirparmis(tabaffect, choisir, 0, n->degre, n->charge, n->degre);

  free(choisir);
  return(nbc);
}


void dumpDOT(char * nom, int m, int n) {
  FILE * fout;
  int i,j;

  fout = fopen(nom, "w");

  fprintf(fout, "graph Urquhart%d {\n",n);

  fprintf(fout, "  size=\"7.5,10\";\n\n");

  fprintf(fout, "  subgraph a {\n");
  fprintf(fout, "    node [style=filled, color=white];\n");
  fprintf(fout, "    style=filled;\n");
  fprintf(fout, "    color=lightgrey;\n");
  for(i=0;i<m;i++) {
    for(j=0;j<(noeuds[0][i].degre);j++)
      if (noeuds[0][i].linktoens[j] == 0)
  	if (noeuds[0][i].link[j] > i)
	  fprintf(fout, "    a%d -- a%d [label=\"v%d\"];\n",i,noeuds[0][i].link[j], tabvars[ noeuds[0][i].numlink[j]]);
    fprintf(fout,"    a%d [label=\"A%d (%d)\"];\n",i,i,noeuds[0][i].charge);
  }
  fprintf(fout, "    shape=ellipse;\n");
  fprintf(fout, "    label=\"A\";\n");
  fprintf(fout, "    }\n\n");

  fprintf(fout, "  subgraph b {\n");
  fprintf(fout, "    node [style=filled];\n");
  fprintf(fout, "    style=filled;\n");
  for(i=0;i<m;i++) {
    for(j=0;j<(noeuds[1][i].degre);j++)
      if (noeuds[1][i].linktoens[j] == 1)
  	if (noeuds[1][i].link[j] > i)
	  fprintf(fout, "    b%d -- b%d [label=\"v%d\"];\n",i,noeuds[1][i].link[j], tabvars[ noeuds[1][i].numlink[j]]);
    fprintf(fout,"    b%d [label=\"B%d (%d)\"];\n",i,i,noeuds[1][i].charge);
  }
  fprintf(fout, "    shape=ellipse;\n");
  fprintf(fout, "    label=\"B\";\n");
  fprintf(fout, "    }\n\n");

  for(i=0;i<m;i++)
    for(j=0;j<noeuds[0][i].degre;j++)
      if (noeuds[0][i].linktoens[j] == 1)
  	if (noeuds[0][i].link[j] >= i)
 	  fprintf(fout, "    a%d -- b%d [label=\"v%d\"];\n",i,noeuds[0][i].link[j], tabvars[ noeuds[0][i].numlink[j]]);

  fprintf(fout,"\n");

  for(i=0;i<m;i++)
    for(j=0;j<noeuds[1][i].degre;j++)
      if (noeuds[1][i].linktoens[j] == 0)
  	if (noeuds[1][i].link[j] > i)
 	  fprintf(fout, "    b%d -- a%d [label=\"v%d\"];\n",i,noeuds[1][i].link[j], tabvars[ noeuds[1][i].numlink[j]]);

  fprintf(fout,"\n");


  fprintf(fout, "}\n");
  fclose(fout);
}

int main(int argc, char ** argv) {
FILE * fout;
int graine, taille;
int m, ouDansPioche, decalage;
int i,j,k;
int d,lie,dlie;
int tmp,totalcharge;
int cptlink = 0;
int nbc;

  if (argc < 2) {
    printf("Usage : genurq n [g]\nGenerate a DIMACS file format (cnf) corresponding to an instance of\the problem proposed by Urquhart: Hard Examples For Resolution.\n - The output is on the standard output.\n - g allow to noise the random generation.\n      (time initialized instead).\n             Laurent Simon, Mai 1999.\n");
    exit(1);
  }

  taille = atoi(argv[1]);
  if (taille < 3) {
    printf("instance size too small (min=3).\n");
    exit(1);
  }

  if (argc>2) 
    graine = atoi(argv[2]);
  else
    graine = ((int)(time((time_t*)NULL))) + ((int)clock());

  //  graine += ((int)(time((time_t*)NULL))) + ((int)clock());

  srand(graine);

#ifdef DBG
  fprintf(stderr,"Initializing Random-seed to :%d\n",graine);
#endif
  m = taille * taille;

#ifdef DBG
  fprintf(stderr,"Allocating %d bytes for bipartite graph H.\n",
	  (sizeof(noeud) * m * 2));
#endif
  noeuds[0] = (noeud*)malloc(sizeof(noeud) * m);
  noeuds[1] = (noeud*)malloc(sizeof(noeud) * m );

  totalcharge = 0;

  for(i=0;i<2;i++)
  for(j=0;j<m;j++) {
    for(k=0;k<(DMAX+2);k++) {
      noeuds[i][j].link[k] = -1;
      noeuds[i][j].numlink[k] = -1;
      noeuds[i][j].linktoens[k] = -1;
    }
    noeuds[i][j].degre = 1;
    tmp = myrand(2);
    noeuds[i][j].charge = tmp;
    totalcharge += tmp;
  }
  

#ifdef DBG
  fprintf(stderr, "Charge totale %d ",totalcharge);
#endif

  if (!(totalcharge &0x1)) { // Etiquettage aléatoire paire
    j = myrand(m); // inverser une charge au hasard.
    i = myrand(2);
    if (noeuds[i][j].charge) { 
      noeuds[i][j].charge = 0;
      totalcharge --;
    } else {
      noeuds[i][j].charge = 1;
      totalcharge ++;
    }
  }

#ifdef DBG
  fprintf(stderr, "amenée à %d\n", totalcharge);
#endif

  // Génération du graphe bipartie initial

  apiocher = (int*) malloc(sizeof(int) * m);
  for(i=0;i<m;i++) apiocher[i] = 0;

  ouDansPioche = 0;
  for(i=0;i<m;i++) { // lie chaque noeud de H1 avec un (et un seul de H2)
    decalage = myrand(m<<1)+1;
    for(j=0;j<decalage;j++) {
      if (ouDansPioche<(m-1)) 
	ouDansPioche++; 
      else 
	ouDansPioche=0; 
      while(apiocher[ouDansPioche]) {
	if (ouDansPioche<(m-1)) 
	  ouDansPioche++; 
	else 
	  ouDansPioche=0;
      }
    }
    apiocher[ouDansPioche] = 1;
#ifdef DBG2
    fprintf(stderr,"Linking(%d) A%d to B%d.\n",cptlink, i,ouDansPioche);
#endif
    noeuds[0][i].link[0] = ouDansPioche;
    noeuds[0][i].linktoens[0] = 1;
    noeuds[1][ouDansPioche].link[0] = i;
    noeuds[1][ouDansPioche].linktoens[0] = 0;
    noeuds[0][i].numlink[0] = cptlink;
    noeuds[1][ouDansPioche].numlink[0] = cptlink++;
  }


#ifdef DBG2
  fprintf(stderr, "Deuxième partie.\n");
#endif
  for(i=0;i<m;i++) { // remplir jusqu'à degré DMAX
    d = getdegre(); // on a déjà une arrête arrivant sur chaque noeud...
    for(j=0;j<d;j++) {
      lie = myrand(m);
      /* Il faut trouver le premier noeud de B non plein à partir de lie */
      /* ET ne contenant pas déjà un lien avec i */
      while ( (noeuds[1][lie].degre == DMAX) ||
	      (estdans(i,noeuds[1][lie].degre, noeuds[1][lie].link)) ) {
	if (lie < (m - 1)) 
	  lie++;
	else
	  lie = 0;
      }
#ifdef DBG2
      fprintf(stderr,"Linking(%d) A%d to B%d.\n",cptlink, i,lie);
#endif
      noeuds[0][i].degre++;
      noeuds[1][lie].degre++;
      noeuds[0][i].link[noeuds[0][i].degre - 1] = lie;
      noeuds[0][i].linktoens[noeuds[0][i].degre - 1] = 1;
      noeuds[1][lie].link[noeuds[1][lie].degre - 1] = i;
      noeuds[1][lie].linktoens[noeuds[1][lie].degre - 1] = 0;
      noeuds[0][i].numlink[noeuds[0][i].degre - 1] = cptlink;
      noeuds[1][lie].numlink[noeuds[1][lie].degre - 1] = cptlink++;
    }


  }
	
#ifdef DBG2
    fprintf(stderr,"Troisième partie. Création des side edges\n");
#endif

    free(apiocher);

    for(i=0;i<2;i++)
      for(j=0;j<(m-1);j++) {
#ifdef DBG
	  fprintf(stderr,(i==0?"Linking(%d) A%d to A%d.\n":"Linking(%d) B%d to B%d.\n"),
		 cptlink, j, j+1);
#endif
	noeuds[i][j].link[noeuds[i][j].degre] = j + 1;
	noeuds[i][j].linktoens[noeuds[i][j].degre] = i;
	noeuds[i][j+1].link[noeuds[i][j+1].degre] = j;
	noeuds[i][j+1].linktoens[noeuds[i][j+1].degre] = i;
	noeuds[i][j].numlink[noeuds[i][j].degre] = cptlink;
	noeuds[i][j+1].numlink[noeuds[i][j+1].degre] = cptlink++;
	noeuds[i][j].degre++;
	noeuds[i][j+1].degre++;
      }
      

    nbc = 0;
    for(i=0;i<2;i++)
      for(j=0;j<m;j++) 
	nbc += (1<<(noeuds[i][j].degre - 1));

    fprintf(stderr, "Instance with %d variables and %d clauses.\n",cptlink, nbc);
    
    /* Affectation des variables aux liens. */
    tabvars = (int*)malloc(sizeof(int)*cptlink);
    apiocher = (int*)malloc(sizeof(int)*cptlink);
    for(i=0;i<cptlink;i++) {
      apiocher[i] = 0;
      tabvars[i] = -1;
    }
    ouDansPioche = 0;

    for(i=0;i<cptlink;i++) {
      decalage = myrand(cptlink<<1)+1;
      for(j=0;j<decalage;j++) {
	if (ouDansPioche<(cptlink-1)) 
	  ouDansPioche++; 
	else 
	  ouDansPioche=0; 
	while(apiocher[ouDansPioche]) {
	  if (ouDansPioche<(cptlink-1)) 
	    ouDansPioche++; 
	  else 
	    ouDansPioche=0;
	}
      }
      apiocher[ouDansPioche] = 1;
#ifdef DBG2
      fprintf(stderr,"Link%d is Var%d.\n", ouDansPioche,i);
#endif

      tabvars[ouDansPioche] = i;
    }
	
    free(apiocher);

    fprintf(stdout, "c Random Instance of Urquhart's Problem for SAT (size=%d randomSeed=%d).\n", taille,graine);
    fprintf(stdout, "c Like Hole, this problem as been proved to be exponential for resolution.\n");
    fprintf(stdout, "c N.B. : instance is unsatisfiable by construction.\n");
    fprintf(stdout, "c \nc Come from the paper 'Hard Examples for Resolution'.\n");
    fprintf(stdout, "c        Source : Laurent Simon, simon@lri.fr. May 1999.\n");
    fprintf(stdout, "c \n");
    fprintf(stdout, "c n=%d, so there is m^2=%d vertices in each part of the bipartite graph. \n",taille, taille*taille);
    fprintf(stdout, "c Bases creations : \n");
    fprintf(stdout, "c   - a '1' charge is 'there must be an even number of negated vars'\n");
    fprintf(stdout, "c   - edges contains variables from which all subbases are constructed.\n");
    for(i=0;i<2;i++)
      for(j=0;j<m;j++) {
	fprintf(stdout, (i==0?"c vertex A%d :":"c vertex B%d :"),j);
	fprintf(stdout, "(charge=%d), (edges=[", noeuds[i][j].charge);
	for(k=0;k<noeuds[i][j].degre - 1;k++)
	  fprintf(stdout, "%d,", tabvars[noeuds[i][j].numlink[k]] + 1);
	fprintf(stdout, "%d])\n", tabvars[noeuds[i][j].numlink[k]] + 1);
      }

    fprintf(stdout, "c \n");

    fprintf(stdout, "p cnf %d %d\n", cptlink, nbc);

    nbc = 0;
    for(i=0;i<2;i++)
      for(j=0;j<m;j++) {
#ifdef DBG2
	fprintf(stderr, (i==0?"Creating base for A%d :":
			 "Creating base for B%d"),j);
	affiche_noeud(&noeuds[i][j]);
#endif
	nbc += creerBaseNoeud(&(noeuds[i][j]));
      }
#ifdef DBG
    fprintf(stderr, "%d Clauses created.\n",nbc);
#endif

#ifdef DUMPDOT
    dumpDOT("urq.dot",m,taille);
    fprintf(stderr, "The file urq.dot contain the dot description of the corresponding expansion graph.\n");
#endif
    free(tabvars);
    free(noeuds[0]);
    free(noeuds[1]);
}





