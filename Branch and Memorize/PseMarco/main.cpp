/********************************************************************/
/* MODULO					: MAIN.C																					*/
/* PROGRAMMA			: JOBSHOP.EXE																			*/
/* VERSIONE				: Vedi fine main.c																*/
/* PROGRAMMATORE  : Ghirardi Marco																	*/
/* ALTRI MODULI   : BeB.C, Bounds.C, Branch.C, Utils.C							*/
/********************************************************************/

#include "beb.h"
#include "DATABASE.H"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <limits.h>
#include "Stat.h"
/*****************************/
/* FLOW-JOB SHOP SOLVER MAIN */
/*****************************/
int CleanStrategy = 0; //!
//! K perm dominance: look at the last k scheduled jobs, permutate to find dominant sol
//! The last four bits stands for (left to right): Whether add dominant sol to db; whether enable k perm; whether enumerate all k perm or just stop when finding the first; whether enable dom conditon based on unscheduled job (not used for this pb)
int DomStrategy = 0; //!
long long NbAddKPerm = 0;
extern int TimesClean;
extern long long NbCleanMin, NbCleanAvg, NbCleanMax;
void main(int argc, char *argv[])
{
	setvbuf(stdout, NULL, _IONBF, 0);
	//argc = 6;	char * argv2[] = { "", "../../Output/data/30/2.txt", "6", "1000000", "3", "0" };	argv = argv2;//6000000
	//10.7 should = 2832

  int c1,c2;
  double t;
  FILE *FFF;
  
  /* PROFILING

  BeB("testpetit.dat", 10, 10000);
  exit(1);


	/* Normally this should be off */
  Debug = OFF;
  printf("*****\nc_type defined as long for pmax=1000.\n*****");
  printf("FLOW(JOB) SHOP - 2 MACHINES SOLVER V0.7\n");
  printf("---------------------------------------\n");

  if (argc != 6) {

    printf("Programmed by Ghirardi Marco\n");
	printf("\nUsage : JOBSHOP <Data File> stra dbdim cleanstra domstra!\n\n");
	printf("\nGiven %d: %s\t%s\t%s\t%s \n\n", argc, argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
    exit(0);
  }
  Stat<> cputime, maxram;
  c1 = clock();
  cputime.getCpuDuration();
  CleanStrategy = atoi(argv[4]);
  DomStrategy = atoi(argv[5]);
  BeB(argv[1], atoi(argv[2]), atoi(argv[3]));//! set dbdim to 0 to disable db.
  //BeB("../../Output/data/30/1.txt", 6, 6000000);//! set dbdim to 0 to disable db.
  //! version 2, bigger maxdim
  //BeB(argv[1], atoi(argv[2]), 6000000);

  c2 = clock();
  double t_cpu = cputime.getCpuDuration();
  maxram.updateMaxRam();
  t = (double)(c2 - c1) / (double)(CLOCKS_PER_SEC);
  printf("CPU Time(clock) : %f\n\n",t);

  FFF = fopen("js.txt", "w");

  fprintf(FFF, "%d\n", (int)t);
  fprintf(FFF, "%ld\n",Nbnodes);
  fprintf(FFF, "%ld\n",CutActive);
  fprintf(FFF, "%ld\n", CutDone);
  fprintf(FFF, "%d\n", (int)t_cpu);
  fprintf(FFF, "%lld\n", maxram.maxRam);
  fprintf(FFF, "%lld\n", NbAddKPerm);
  fprintf(FFF, "%d\n", BestSolValue);

  fclose(FFF);

  fprintf(stdout, "t=%d\n", (int)t);
  fprintf(stdout, "nbNodes=%ld\n", Nbnodes);
  fprintf(stdout, "cutAct=%ld\n", CutActive);
  fprintf(stdout, "cutDone=%ld\n", CutDone);
  fprintf(stdout, "tcpu=%d\n", (int)t_cpu);
  fprintf(stdout, "ram=%lld\n", maxram.maxRam);
  fprintf(stdout, "nbAddKperm=%lld\n", NbAddKPerm);
  fprintf(stdout, "sol=%d\n", BestSolValue);
  if (TimesClean > 0){
	  printf("TimesClean:%lld\n", TimesClean);
	  printf("NbCleanMinAvgMAx : %lld, %lld, %lld\n", NbCleanMin, NbCleanAvg, NbCleanMax);
  }

  if (t - t_cpu > 100) printf("Warning: time diff = %d.\n", int(t - t_cpu));
  //printf("Number of ActiveCuts=%ld\n",CutActive);
  //printf("Number of DoneCuts=%ld\n",CutDone);
  //printf("Number of nodes branched=%ld\n",Nbnodes);
  //if (DBMaximumDimension > 0)PrintDB();
  printf("==================================\n");
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