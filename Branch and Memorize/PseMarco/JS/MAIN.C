/********************************************************************/
/* MODULO					: MAIN.C																					*/
/* PROGRAMMA			: JOBSHOP.EXE																			*/
/* VERSIONE				: Vedi fine main.c																*/
/* PROGRAMMATORE  : Ghirardi Marco																	*/
/* ALTRI MODULI   : BeB.C, Bounds.C, Branch.C, Utils.C							*/
/********************************************************************/
 
#include "beb.h"

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>

/*****************************/
/* FLOW-JOB SHOP SOLVER MAIN */
/*****************************/

void main(int argc, char *argv[])
{
  int c1,c2;
  double t;
  FILE *FFF;

  /* PROFILING

  BeB("testpetit.dat", 10, 10000);
  exit(1);


	/* Normally this should be off */
  Debug = OFF;

  printf("FLOW(JOB) SHOP - 2 MACHINES SOLVER V0.7\n");
  printf("---------------------------------------\n");

  if (argc != 4) {

    printf("Programmed by Ghirardi Marco\n");
		printf("\nUsage : JOBSHOP <Data File>\n\n");
    exit(0);
  }

  c1 = clock();

  BeB(argv[1], atoi(argv[2]), atoi(argv[3]));

  c2 = clock();
  t = (double)(c2 - c1) / (double)(CLOCKS_PER_SEC);
  printf("CPU Time : %f\n\n",t);

  FFF = fopen("js.txt", "w");

  fprintf(FFF, "%d\n", (int)t);
  fprintf(FFF, "%ld\n",Nbnodes);
  fprintf(FFF, "%ld\n",CutActive);
  fprintf(FFF, "%ld\n",CutDone);

  fclose(FFF);

  printf("Number of ActiveCuts=%ld\n",CutActive);
  printf("Number of DoneCuts=%ld\n",CutDone);
  printf("Number of nodes branched=%ld\n",Nbnodes);

  exit(1);
}


/* 

	Versione 0.7 gamma(overrided ini) :

		FS funzionante:
		Modello di memoria: nodi allocati a blocchi, hash table, cache.
		Tabelle LA ottimizzate.
		
		MultiObiettivo implementato (debuggato Ahmadi/Bachi).

		Database per il criterio di dominanza 4 implementato (brutto ma funge)

  Da fare :
			
	In futuro (molto futuro):

		Job Shop

*/