/********************************************************************/
/* MODULO					: Bounds.C																				*/
/* FUNZIONALITA'	: Implementa tutti i lower bounds e gli upper     */
/*								bounds utilizzati per il flow o il job shop.      */
/********************************************************************/ 

#include "beb.h"
#include "bounds.h"
#include "utils.h"
#include "branch.h"

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>

/* Numero di lower bounds implementati */
#define NUMLB 10

/* Utilita' */
#define FUNC int (*)(const void *, const void *)
#define ZERO 0.0000001
#define APPROX (1.0-ZERO)
#define max(a,b)    (((a) > (b)) ? (a) : (b))
/***********************************/
/* GLOBAL VARIABLES AND STRUCTURES */
/***********************************/

/* Strutture d'ordine usate per il qsort (interi - double) */

#define FUNC int (*)(const void *, const void *)
struct O {
  int Order;
  int Val;
};

struct Of {
  int Order;
  double Val;
};

/* Ultimo UpperBound Calcolato */
int LastUBValue;
c_type LastUB1[MAXJOBS];
c_type LastUB2[MAXJOBS];

/* Strutture d'ordine per SPT1 - STP2 - JOHNSON */
struct O P1[MAXJOBS];
struct O P2[MAXJOBS];
struct O JH[MAXJOBS];

/* Sequenze e Lambda per il LB di VanDeVelde */
double Lambda[21][MAXJOBS];
c_type Seq[21][MAXJOBS];

/* Struttura d'ordine per il C2SRPT */
struct O C2SRPT[MAXJOBS];

/* Variabili per implementare la funzione OnlyBest */
int BestLambdaatRootVDVC, BestLambdaatRootLINDO, BestLambdaatRootLA;

/* Raccolta di statistiche sui diversi LB */
int LBStats[NUMLB];
int LA2NA, LA2EQ, LA2BE, LA2WO;
int LAComplex;

/**************/
/* PROTOTYPES */
/**************/

/* Utility Functions */
int O_Inc_Comp(struct O *i, struct O *j);
int O_Dec_Comp(struct O *i, struct O *j);
int Of_Comp(struct Of *i, struct Of *j);

int DoSRPT(Node *N);
int SeqCompare(c_type *A, c_type *B, Node *N);

/* Flow Shop procedures */
int FSBoundsInit(void);
int FS_LB_AB(Node *N);
int FS_LB_IS1(Node *N);
int FS_LB_IS2(Node *N);
int FS_LB_HV(Node *N);
int FS_LB_VDV(Node *N, int *Best);
int FS_LB_VDV2(Node *N);
int FS_LB_DNT1(Node *N);
int FS_LB_DNT2(Node *N);
int FS_LB_LINDO(Node *N);
int FS_LB_LA(Node *N, int BestVDV);

int FSUB_AtRoot(void);
int FSUB_AtRoot_MO(void);
int FSUB_PLNUB(void);
int FSUB(Node *N);

/*******************************/
/* LA : Structures and globals */
/*******************************/

#define LOWER 1
#define UPPER 2

typedef struct L2 {
  int lim_id;
  double k,m;
} mod_lim;

typedef struct L1 {
  double curr_value;
  int type;
  mod_lim Mod[2*MAXJOBS];
  int mod_size;
  int dirty;
} limit;

c_type LSeq[MAXJOBS];
limit LIMITSUB[2*MAXJOBS];
limit LIMITSVDV[21][2*MAXJOBS];
c_type UBSeq[MAXJOBS];

int LAInit(void);
int lim_add(limit *L, int a,int b,double k, double m);
int Create_Limits(limit *L, int KeepL);
int LB_LIMITS(limit *L, Node *N, int KeepL);
int EveryLSeq(limit *L, int Pos, int Max, Node *N);

/* Job Shop procedures */

/*********************/
/* UTILITY FUNCTIONS */
/*********************/

/********************************************************************/
/* FUNZIONE : O_Inc_Comp																						*/
/* EFFETTO  : Da utilizzare con QSORT() per l'ordinamento crescente */
/*					di un array di strutture d'ordine di interi							*/
/********************************************************************/
int O_Inc_Comp(struct O *i, struct O *j)
{
  if (i->Val > j->Val) return(1);
  if (j->Val > i->Val) return(-1);
  return(0);
}

/********************************************************************/
/* FUNZIONE : O_Dec_Comp																						*/
/* EFFETTO  : Da utilizzare con QSORT() per l'ordinamento decresc.	*/
/*					di un array di strutture d'ordine di interi							*/
/********************************************************************/
int O_Dec_Comp(struct O *i, struct O *j)
{
  if (i->Val > j->Val) return(-1);
  if (j->Val > i->Val) return(1);
  return(0);
}

/********************************************************************/
/* FUNZIONE : Of_Comp																								*/
/* EFFETTO  : Da utilizzare con QSORT() per l'ordinamento crescente */
/*					di un array di strutture d'ordine di double							*/
/********************************************************************/
int Of_Comp(struct Of *i, struct Of *j)
{
  double A = i->Val - j->Val;

  if (A < ZERO && A > -ZERO) return(0);

  if (A > 0) return(1);
	
	return(-1);
}

/********************************************************************/
/* FUNZIONE : DoSRPT																								*/
/* INPUT		: Puntatore al nodo sul quale implementare l'SRPT				*/
/* EFFETTO  : Caricamento in C2SRPT dei tempi di comletamento sulla	*/
/*					2' macchina secondo la medodologia SRPT + prehemption		*/
/* OUTPUT		: 0																											*/
/********************************************************************/

int DoSRPT(Node *N)
{
  int i, MinRPT, Min;
  int Time, Pos, C;
  int RPT[MAXJOBS];
  int True = 1;
  struct O R[MAXJOBS];
  
	/* Init */

	for (i=0; i<Jobs; i++) C2SRPT[i].Order = i;

  /* Calcolo Release Times */

  C = 0;
  for (i=0;i<Jobs;i++) RPT[i] = JOB[i].p2;

  for (i=0;i<Jobs;i++) 
		if (N->NextWork[i] != 0) {
			R[i].Val = Imax(N->C2, N->C1 + JOB[i].p1);
			R[i].Order = i;
    }
    else {
			C2SRPT[i].Val = INT_MAX;
			R[i].Order = i;
      R[i].Val = -1;
		}
  qsort((void *)R, (size_t)Jobs, sizeof(struct O), (FUNC) O_Inc_Comp);
  
  Pos = N->Pos1;
  Time = R[Pos].Val;
  
  while(True) {
  
    /* Prossimo Job */

		Min    = 0;
    MinRPT = INT_MAX;
		for (i=Pos;i<Jobs;i++) {
			if (R[i].Val > Time) break;
			if (RPT[R[i].Order] < MinRPT) {
				MinRPT = RPT[R[i].Order];
				Min = i;
			}
		}
	
		if (MinRPT == INT_MAX) break;
	
		/* Avanzamento */

		if (i == Jobs) {
			Time += RPT[R[Min].Order];
			RPT[R[Min].Order] = INT_MAX;
			C += Time;
			C2SRPT[R[Min].Order].Val = Time;
			continue;
		}		
	
		if ( RPT[R[Min].Order] <= R[i].Val - Time ) {
			Time += RPT[R[Min].Order];
			RPT[R[Min].Order] = INT_MAX;
			C += Time;
			C2SRPT[R[Min].Order].Val = Time;
		}
		else {
			RPT[R[Min].Order] -= R[i].Val - Time;
			Time = R[i].Val;
		}
  }
  
	return(0);
}

/********************************************************************/
/* FUNZIONE : SeqCompare																						*/
/* INPUT		: Due sequenze ed un nodo																*/
/* EFFETTO  : Verifica dell'uguaglianza delle due sequenze una vol-	*/
/*					ta eliminati da entrambe i job gia allocati nel nodo		*/
/* OUTPUT		: 0 (Seq. diverse)																			*/
/*						1 (Seq. uguali)																				*/
/********************************************************************/
int SeqCompare(c_type A[], c_type B[], Node *N)
{
  int a = 0, b = 0;

  while (a != Jobs && b != Jobs) {
  
	  while (N->NextWork[A[a]] == 0) {
		  a++;
		  if (a == Jobs) break;
	  }
	  while (N->NextWork[B[b]] == 0) {
		  b++;
		  if (b == Jobs) break;
	  }
	  if (a == Jobs && b == Jobs) break;
	  if (A[a] == B[b]) { a++; b++; } else return(0);
  }

  return(1);
}

/*******************************/
/* FLOW SHOP BOUNDS PROCEDURES */
/*******************************/

/********************************************************************/
/* FUNZIONE : FSBoundsInit																					*/
/* INPUT		: void																									*/
/* EFFETTO  : Init generale, creazione strutture d'ordine, pre-cal-	*/
/*					coli per i lower-bounds che li necessitano							*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int FSBoundsInit(void)
{
  int i;

  int   j,k,q,jjj,fcomp,scomp;
  double Akj,Ajk,P1k,P2k,A,P,Djk;
  double deljplus, deljminus;
  struct Of Lf[MAXJOBS];
  
	/* Init varie */

	if (LA == ON && UseEuristic == ON) OldEuristic = ON;
	if (LA == ON && GetBestVDV == ON && OnlyBest == ON) VDV_ORIGINAL = ON;

	/* Init statistiche */

	for (i=0; i<NUMLB; i++)
		LBStats[i] = 0;

	LA2NA = 0;
	LA2EQ = 0;
	LA2BE = 0;
	LA2WO = 0;
	LAComplex = 0;

  /* Creazione strutture di ordine SPT1, SPT2, JH */

  for (i=0;i<Jobs;i++) {
    P1[i].Val = JOB[i].p1;
    P1[i].Order = i;
    P2[i].Val = JOB[i].p2;
    P2[i].Order = i;
		
		if (JOB[i].p1 <= JOB[i].p2) 
			JH[i].Val = JOB[i].p1; 
		else 
			JH[i].Val = INT_MAX - JOB[i].p2;
		
		JH[i].Order = i;
	}

  qsort((void *)P1, (size_t)Jobs, sizeof(struct O), (FUNC) O_Inc_Comp);
  qsort((void *)P2, (size_t)Jobs, sizeof(struct O), (FUNC) O_Inc_Comp);
	qsort((void *)JH, (size_t)Jobs, sizeof(struct O), (FUNC) O_Inc_Comp);

	for (i=0;i<Jobs;i++) JHSequence[i] = JH[i].Order;
	i = 0; JH_C2 = 0;
	SeqEval(JHSequence, Jobs, &i, &JH_C2);
	if (MO_C2Limit == 0) MO_C2Limit = JH_C2;

  /* Creazione Lambda per perturbazione */

  for (i=0; i < 21; i++)
    for (j=0; j<Jobs;j++)
      Lambda[i][j] = (double)i * 0.05;

  /* Creazione sequenze per VDV */

  for(k=0; k < 21; k++) {

    for(i=0; i< Jobs; i++) {

      Lf[i].Val = Lambda[k][0] * (double)JOB[i].p1 +
						(1.0-Lambda[k][0]) * (double)JOB[i].p2;
      Lf[i].Order = i;
    }

    qsort((void *)Lf, (size_t)Jobs, sizeof(struct Of), (FUNC)Of_Comp);

    for(i=0; i < Jobs; i++) Seq[k][i] = Lf[i].Order;
  }

  /*
     Seq[i][j] = POSIZIONE del job in j-esima posizione
     secondo il lambda i-esimo

     Lambda[i][j] = Valore dell' i-esimo lambda. Dopo la
     perturbazione e' il valore del lambda del job in j-
     esima posizione di joblist[] perturbato partendo dalla
     sequenza i-esima.

  */

	if (LA == ON) LAInit();

  if (VDV_ORIGINAL == OFF) return(0);
  if (Perturb == OFF) return(0);

  /* Perturbazione dei LAMBDA per VDV_ORIGINAL */

  for(i=0; i<21; i++) {
		fcomp = 0;
		scomp = P1[0].Val;
    for(j=0; j<Jobs; j++) {
			jjj=Seq[i][j];
			deljminus = -999999.0;
			deljplus = 999999.0;
			for(q=0; q<Jobs; q++) {
				k = Seq[i][q];
				if((k != jjj) && (JOB[k].p1 != JOB[k].p2)) {
					Akj = Lambda[i][k]*(double)JOB[jjj].p1
							+(1.0-Lambda[i][k])*(double)JOB[jjj].p2;
					Ajk = Lambda[i][jjj]*(double)JOB[k].p1
							+(1.0-Lambda[i][jjj])*(double)JOB[k].p2;

					A = Akj - Ajk;
		
					P1k = (double)(JOB[k].p1);
					P2k = (double)(JOB[k].p2);

					/* Copertura UNDERFLOW ERRORS */
					if (A < ZERO && A > -ZERO) A = 0.0;

					if (A == 0.0) {
						if (q < j) {
							if (P1k > P2k) deljplus = 0.0;
							if (P1k < P2k) deljminus = 0.0;
						}
						else {
							if (P1k < P2k) deljplus = 0.0;
							if (P1k > P2k) deljminus = 0.0;
						}
						continue;
					}

					P = P1k - P2k;

					Djk = (double)A / (double)P;

					if(Djk > 0.0)
						deljplus = Fmin(deljplus,Djk);
					if(Djk < 0.0)
						deljminus = Fmax(deljminus,Djk);
				}
			}
			fcomp += JOB[jjj].p1;
			scomp += JOB[jjj].p2;

      if (fcomp + JOB[jjj].p2 > scomp)
	      Lambda[i][jjj] += deljplus;
      if (fcomp + JOB[jjj].p2 < scomp)
	      Lambda[i][jjj] += deljminus;
      if (Lambda[i][jjj] < 0.0) Lambda[i][jjj] = 0.0;
      if (Lambda[i][jjj] > 1.0) Lambda[i][jjj] = 1.0;
    }
  }

  return(0);
}

/********************************************************************/
/* FUNZIONE : FS_LB_AB	   																					*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcola il lower bound di Ahmadi-Bagchi per il nodo N	*/
/* OUTPUT		: Il lower bound calcolato															*/
/********************************************************************/
int FS_LB_AB(Node *N)
{
	int C,i;

  DoSRPT(N);
  
  C = N->CSUM;
  for (i=0;i<Jobs;i++)
	  if (N->NextWork[i] != 0) C += C2SRPT[i].Val;

	return(C);
}
/********************************************************************/
/* FUNZIONE : FS_LB_IS1	   																					*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcola il lower bound IS1 per il nodo N							*/
/* OUTPUT		: Il lower bound calcolato															*/
/********************************************************************/
int FS_LB_IS1(Node *N)
{
	int i, C1, Sum;

	Sum = N->CSUM;
	C1 = N->C1;
	for (i=0; i<Jobs;	i++)
		if (N->NextWork[P1[i].Order] != 0) {
			C1 += P1[i].Val;
			Sum += C1 + JOB[P1[i].Order].p2;
		}

	return(Sum);
}

/********************************************************************/
/* FUNZIONE : FS_LB_IS2	   																					*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcola il lower bound IS2 per il nodo N							*/
/* OUTPUT		: Il lower bound calcolato															*/
/********************************************************************/
int FS_LB_IS2(Node *N)
{
	int i, C2, Sum;

	for (i=0;i<Jobs;i++)
		if (N->NextWork[P1[i].Order] != 0) break;

	C2 = Imax(N->C2, N->C1 + P1[i].Val);

	Sum = N->CSUM;
	for (i=0; i<Jobs;	i++)
		if (N->NextWork[P2[i].Order] != 0) {
			C2 += P2[i].Val;
			Sum += C2;
		}

	return(Sum);
}

/********************************************************************/
/* FUNZIONE : FS_LB_HV	   																					*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcola il lower bound HV per il nodo N								*/
/* OUTPUT		: Il lower bound calcolato															*/
/********************************************************************/
int FS_LB_HV(Node *N)
{
	int i,j,k,fcomp, scomp, flag, Newscomp;
  double t, total, maxtotal=0.0, slack;
	int T1[MAXJOBS], T2[MAXJOBS];

	/* Slack optimization */

	k=0;
	for (j=0; j<Jobs;j++)
		if (N->NextWork[P1[j].Order] != 0) {
			T1[k] = P1[j].Val;
			k++;
		}
	T1[k] = INT_MAX;

	k=0; flag = 0;
	for (j=0;j<Jobs;j++)
		if (N->NextWork[P2[j].Order] != 0)
			if (N->C2 - N->C1 > P2[j].Val || flag) {
				T2[k] = P2[j].Val;
				k++;
			}
			else {
				T2[k] = N->C2 - N->C1;
				T2[k+1] = P2[j].Val;
				k+=2;
				flag = 1;
			}

	slack = 0.0;
	for (j=0; j<k; j++) slack += Imax(0, T2[j] - T1[j]);

	/* Van de Velde */

  i=0;
  maxtotal=0.0;

	fcomp = N->C1;
	Newscomp = N->C2;

	for (j=0;j<Jobs;j++)
    if (N->NextWork[P1[j].Order] != 0) {
			if (fcomp + P1[j].Val > Newscomp)
	      Newscomp = fcomp + P1[j].Val;
			break;
    }

  for(i=0; i<21; i++) {

	/* if (i != 0 && SeqCompare(Seq[i-1], Seq[i], N)) continue; */ 
    
	/* Aggiungere la linea sopra se si vogliono esaminare tutte le sequenze	*/
	/* Sostituire la linea sopra con la seguente se si vogliono esaminare		*/
	/* solo le sequenze diverse al nodo radice : */
	/* if (i != 0 && Istrcmp(Seq[i-1], Seq[i])) continue; */

		fcomp = N->C1;
		scomp = Newscomp;

		total = 0;
		for(j=0; j<Jobs; j++) {
			k = Seq[i][j];

			if(N->NextWork[k] != 0) {
				fcomp += JOB[k].p1;
				scomp += JOB[k].p2;

				t = (double)i * 0.05;

				total += t * (double)fcomp + (1.0 - t) * (double)scomp+
							   t * (double)JOB[k].p2;
					
			}
		}

		total += slack * (double)i * 0.05;

		if (total > maxtotal) maxtotal = total;
	}

	maxtotal = maxtotal + (double)(N->CSUM);
	
	return((int)(maxtotal+APPROX));
}

/********************************************************************/
/* FUNZIONE : FS_LB_VDV   																					*/
/* INPUT		: Puntatore ad un nodo e uno ad un intero								*/
/* EFFETTO  : Calcola il lower bound di Van de Velde per il nodo N	*/
/*						L'indice della miglior sequenza e' restituito in Best */
/* OUTPUT		: Il lower bound calcolato															*/
/********************************************************************/
int FS_LB_VDV(Node *N, int *Best)
{
  int i,j,k,fcomp, scomp, Newscomp;
  double t, total, maxtotal=0.0;

  i=0;
  maxtotal=0.0;

	fcomp = N->C1;
	Newscomp = N->C2;

	for (j=0;j<Jobs;j++)
    if (N->NextWork[P1[j].Order] != 0) {
			if (fcomp + P1[j].Val > Newscomp)
	      Newscomp = fcomp + P1[j].Val;
			break;
    }

  for(i=0; i<21; i++) {

	/* if (i != 0 && SeqCompare(Seq[i-1], Seq[i], N)) continue; */ 
    
	/* Aggiungere la linea sopra se si vogliono esaminare tutte le sequenze	*/
	/* Sostituire la linea sopra con la seguente se si vogliono esaminare		*/
	/* solo le sequenze diverse al nodo radice : */
	/* if (i != 0 && Istrcmp(Seq[i-1], Seq[i])) continue; */

		fcomp = N->C1;
		scomp = Newscomp;

		total = 0;
		for(j=0; j<Jobs; j++) {
			k = Seq[i][j];

			if(N->NextWork[k] != 0) {
				fcomp += JOB[k].p1;
				scomp += JOB[k].p2;

				t = Lambda[i][k];

				total += t * (double)fcomp + (1.0 - t) * (double)scomp+
							   t * (double)JOB[k].p2;
					
			}
		}

		if (total > maxtotal) {
			maxtotal = total;
			*Best = i;
		}
	}

	maxtotal = maxtotal + (double)(N->CSUM);
	
	return((int)(maxtotal+APPROX));
}

/********************************************************************/
/* FUNZIONE : FS_LB_VDV2																						*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcola il lower bound VDV-C per il nodo N           	*/
/* OUTPUT		: Il lower bound calcolato															*/
/********************************************************************/
int FS_LB_VDV2(Node *N)
{
  int i, j, jjj, q, k, fcomp, scomp;
  double total, maxtotal;
  double Akj, Ajk, A, P, Djk, deljplus, deljminus;
  double NewLambda[MAXJOBS];

  struct O PertOrder[MAXJOBS];
  int FCOMP[MAXJOBS], SCOMP[MAXJOBS];

  /* Init */

  maxtotal=0.0;
  fcomp = N->C1;
  scomp = N->C2;

  for (j=0; j<Jobs; j++)
    if (N->NextWork[P1[j].Order] != 0) {
      if (fcomp + P1[j].Val > scomp)
        scomp = fcomp + P1[j].Val;
      break;
    }

  for(i=0; i<21; i++) {

	if (AtRoot || OnlyBest == OFF)
		if (i != 0 && SeqCompare(Seq[i-1], Seq[i], N)) continue;
	
	/* Eliminare la linea sopra se si vogliono esaminare tutte le sequenze */
	/* Sostituire la linea sopra con la seguente se si vogliono esaminare */
	/* solo le sequenze diverse al nodo radice : */
	/* if (i != 0 && Istrcmp(Seq[i-1], Seq[i])) continue; */

	/* Nodo radice? Opzione onlybestlambda attiva? */

  if (!AtRoot && OnlyBest == ON) {
		if (i < BestLambdaatRootVDVC) i = BestLambdaatRootVDVC;
		if (i > BestLambdaatRootVDVC) break;
	}

  /* Copia dei lambda in NewLambda */

	for (j=0; j<Jobs; j++) NewLambda[j] = Lambda[i][j];

  /* calcolo di FCOMP, SCOMP, PERTORDER */

  total = 0.0;
    
	k = fcomp; q = scomp;
	for (j=0; j<Jobs; j++) {
	  jjj = Seq[i][j];
    PertOrder[jjj].Val = 0;
	  PertOrder[jjj].Order = jjj;
	  if (N->NextWork[jjj] != 0) {
	    k += JOB[jjj].p1; FCOMP[jjj] = k;
	    q += JOB[jjj].p2; SCOMP[jjj] = q;
	    PertOrder[jjj].Val = k + JOB[jjj].p2 - q;
			if (PertOrder[jjj].Val < 0) PertOrder[jjj].Val = -PertOrder[jjj].Val;
	  }
	}

  if (PertOrderbyDelta == ON) 
		qsort((void *)PertOrder, (size_t)Jobs, sizeof(struct O), (FUNC) O_Dec_Comp);
  
  /* START */

  for(j=0; j<Jobs; j++) {
		jjj = PertOrder[j].Order;
    if(N->NextWork[jjj] != 0) {

  	/* PERTURBO IL LAMBDA DI J--JJJ */

	  deljminus = -999999.0;
	  deljplus = 999999.0;

	  for(q=0; q<Jobs; q++) {
	    if (PertOrder[j].Val == 0) break;
		  k = Seq[i][q];
	    if(N->NextWork[k] != 0) {

	    /* VINCOLO CON Q--K */

			  if((k != jjj) && (JOB[k].p1 != JOB[k].p2)) {
	          Akj = NewLambda[k]*(double)JOB[jjj].p1
	  					+(1.0-NewLambda[k])*(double)JOB[jjj].p2;
	  	      Ajk = NewLambda[jjj]*(double)JOB[k].p1
							+(1.0-NewLambda[jjj])*(double)JOB[k].p2;

						A = Akj - Ajk;

						/* Copertura UNDERFLOW ERRORS */
						if (A < ZERO && A > -ZERO) A = 0.0;

						if (A == 0.0) {
							if (FCOMP[k] < FCOMP[jjj]) {
								if (JOB[k].p1 > JOB[k].p2) deljplus = 0.0;
								if (JOB[k].p1 < JOB[k].p2) deljminus = 0.0;
							}
							else {
								if (JOB[k].p1 < JOB[k].p2) deljplus = 0.0;
								if (JOB[k].p1 > JOB[k].p2) deljminus = 0.0;
							}
							continue;
						}

						P = (double)(JOB[k].p1 - JOB[k].p2);

						Djk = (double)A / (double)P;

						if(Djk > 0.0)
							deljplus = Fmin(deljplus,Djk);
						if(Djk < 0.0)
							deljminus = Fmax(deljminus,Djk);
	        }

				}
			}

	    /* Tutti i vincoli considerati! */

	    if (FCOMP[jjj] + JOB[jjj].p2 > SCOMP[jjj]) NewLambda[jjj] += deljplus;
			if (FCOMP[jjj] + JOB[jjj].p2 < SCOMP[jjj]) NewLambda[jjj] += deljminus;
			if (NewLambda[jjj] < 0.0) NewLambda[jjj] = 0.0;
			if (NewLambda[jjj] > 1.0) NewLambda[jjj] = 1.0;

			/* Lambda perturbato!! */

			A = NewLambda[jjj];

			total += A * (double)FCOMP[jjj] +
	       (1.0 - A) * (double)SCOMP[jjj]+
	       A * (double)JOB[jjj].p2;
      }
		}

    if (total > maxtotal) {
      maxtotal = total;
      if (AtRoot) BestLambdaatRootVDVC = i;
    }

  }

  maxtotal = maxtotal + (double)(N->CSUM);

  return((int)(maxtotal+APPROX));
}

/********************************************************************/
/* FUNZIONE : FS_LB_DNT1																						*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcolo del lower bound DNT1													*/
/* OUTPUT		: Il lower bound																				*/
/*																																	*/
/* ALTRE FUNZIONI UTILIZZATE	: hung() per risolvere il problema di */
/*															assegnamento.												*/
/********************************************************************/

/* Prototipo */
int hung(int RemJobs, int proc1[], int proc2[], int secproc, int firstproc);

/* Funzione hung */
int hung(int RemJobs, int proc1[], int proc2[], int secproc, int firstproc)
{
	int True = 1;
	int I, J, L = 0, M, R, K, LJ, LM;
	int KC, KR, N;
	int S, Q, H, T;
	int C[MAXJOBS+1], U[MAXJOBS+1], LZ[MAXJOBS+1], NZ[MAXJOBS+1];
	int RH[MAXJOBS+1], CH[MAXJOBS+1], LR[MAXJOBS+1], LC[MAXJOBS+1];
	int SLR[MAXJOBS+1], SLC[MAXJOBS+1];
	int FLAG_A = 0, FLAG_B = 0, FLAG_C = 0;
	int A[MAXJOBS+1][MAXJOBS+1];

	N = RemJobs;
	for (I = 0; I < N; I++) { 
		 for (J = 0; J < N; J++) { 
			 if ((I != 0 && J != 0 ) && (I!=J)) 
				 A[I][J] = ( max(0,proc2[I]-proc1[J]) + max(proc1[I]-proc1[J],0)+1);
			 else if ((I == J)&&(I)&&(J))
				 A[I][J] = 10000;
			 else 
				 A[I][J] = 0;
		}
	}	
 
	for(I=0; I<N; I++)
		if(I)
			A[I][N] = 1;
 
	A[N][N] = 10000;

	for(J=0; J<N; J++)
		if(J)
			A[N][J] = (max(0,secproc-firstproc-proc1[J])+1);
	    /*A[N][J] = -1*(N+1);*/

	for (I = 0;I <= N;I++) { 
		C[I] = 0;
		U[I] = 0;
    LZ[I] = 0;
    NZ[I] = 0;
	}

	T = 0;

	for(J = 1;J <= N;J++) { 
		S = A[1][J];
		for(I = 1;I <= N;I++) if(A[I][J] < S) S = A[I][J];
		T += S;
		for(I = 1;I <= N;I++) A[I][J] -= S;
	}

	for(I = 1;I <= N;I++) { 
		Q = A[I][1];
		for(J = 1;J <= N;J++) if(A[I][J] < Q) Q = A[I][J];
		T += Q;
		L = 0;
		for(J = 1;J <= N;J++) { 
			A[I][J] -= Q;
			if(A[I][J] == 0) { 
				A[I][L] = -1*J;
				L = J;
			}
		}
	}

	K = 0;

	for(I= 1;I <= N;I++) { 
		LJ = 0;
		J = -1*A[I][0];
	  
		do { 
			if(C[J] == 0) { 
				C[J] = I;
				A[I][LJ] = A[I][J];
				NZ[I] = -1*A[I][J];
				LZ[I] = LJ;
				A[I][J] = 0;
				FLAG_A = FALSE;
				break;
			}
			LJ =J;
			J = -1*A[I][J];
			if(J != 0) FLAG_A = TRUE;
			else { 
				LJ = 0;
				J = -1*A[I][0];
				do { 
					R = C[J];
					LM =LZ[R];
					M = NZ[R];
					do { 
						if(M == 0) { 
							LJ = J;
							J = -1*A[I][J];
							if(J == 0) { 
								U[K] = I;
								K = I;
								FLAG_A = FALSE;
								FLAG_B = FALSE;
								break;
							}
							else { 
								FLAG_B = TRUE;
								break;
							}
						}
						else { 
							if( C[M] == 0) { 
								NZ[R] = -1*A[R][M];
								LZ[R] = J;
								A[R][LM] = -1*J;
								A[R][J] = A[R][M];
								A[R][M] = 0;
								C[M] = R;
								C[J] = I;
								A[I][LJ] = A[I][J];
								NZ[I] = -1*A[I][J];
								LZ[I] = LJ;
								A[I][J] = 0;
								FLAG_A = FALSE;
								FLAG_B = FALSE;
								break;
							}
							else { 
								LM = M;
								M = -1*A[R][M];
							}
						}
					}
					while( True );
				}
				while( FLAG_B );
			}
	  }
	  while( FLAG_A );
	}

	while( U[0] != 0) { 
		for (K = 0;K <= N;K++) {
			CH[K] = 0;
			RH[K] = 0;
			LC[K] = 0;
			SLC[K] = 0;
			LR[K] = 0;
			SLR[K] = 0;
		}
		RH[0] = -1;
		R = U[0];
		LR[R] = -1;
		KC = 0;
		KR = 0;
		SLR[++KR] = R;
		if( A[R][0] != 0) FLAG_A= TRUE;
		else { 
			FLAG_A = FALSE;
			FLAG_B = FALSE;
			FLAG_C = TRUE;
		}
   
		do { 
			if( FLAG_A ) { 
				FLAG_B = TRUE;
				L = -1*A[R][0];
				if(  A[R][L] != 0) { 
					if( RH[R] == 0) { 
						RH[R] = RH[0];
						RH[0] = R;
						CH[R] = -1*A[R][L];
					}
				}
			}
	    
			if( FLAG_B ) { 
				if(LC[L] == 0) { 
					LC[L] = R;
					if(C[L] == 0) break;
					else { 
						R = C[L];
						LR[R] = L;
						SLC[++KC] = L;
						SLR[++KR] = R;
						if( A[R][0] != 0 ) { 
							FLAG_A = TRUE;
							continue;
						}
						else FLAG_C = TRUE;
					}
				}
				else { 
					if(RH[R] == 0 ) FLAG_C = TRUE; else FLAG_C = FALSE;
				}
			}
	    
			if ( FLAG_C ) { 
				if(RH[0] <= 0) { 
					H = 1000000;
					for(J = 1;J <= N;J++) { 
						if(LC[J] == 0) { 
							for(K = 1;K <= KR;K++) { 
								I = SLR[K];
								if(A[I][J] < H)  H = A[I][J];
							}
						}
					}
					T += H;
					for(J = 1;J <= N;J++) { 
						if(LC[J] == 0) { 
							for(K = 1;K <= KR;K++) { 
								I = SLR[K];
								A[I][J] -= H;
								if(A[I][J] == 0) { 
									if(RH[I] == 0) { 
										RH[I] = RH[0];
										CH[I] = J;
										RH[0] = I;
									}
									LJ = 0;
									L = -1*A[I][0];
									while( L != 0) { 
										LJ = L;
										L = -1*A[I][L];
									}
									A[I][LJ] = -1*J;
								}
							}
						}
					}
					if(KC != 0) { 
						for(I = 1;I <= N;I++) { 
							if(LR[I] == 0) { 
								for(K = 1;K <= KC; K++) { 
									J = SLC[K];
									if(A[I][J] <= 0) { 
										LJ = 0;
										L = -1*A[I][0];
										while(L != J) { 
											LJ = L;
											L = -1*A[I][L];
										}
										A[I][LJ] = A[I][J];
										A[I][J] = H;
									}
									else A[I][J] += H;
								}
							}
						}
					}
				}
				R = RH[0];
			}
	    
			L = CH[R];
			CH[R] = -1*A[R][L];
			if( A[R][L] == 0) { 
				RH[0] = RH[R];
				RH[R] = 0;
			}
			FLAG_A = FALSE;
			FLAG_B = TRUE;
		}
		while( True );
	
		do { 
			C[L] = R;
			LM = 0;
			M = -1*A[R][0];
			while( M != L) { 
				LM = M;
				M = -1*A[R][M];
			}
			A[R][LM] = A[R][M];
			A[R][L] = 0;
			if(LR[R] <= 0) { 
				U[0] = U[R];
				U[R] = 0;
				break;
			}
			else { 
				L = LR[R];
				A[R][L] = A[R][0];
				A[R][0] = -1*L;
				R = LC[L];
			}
	  }
	  while( True );
	}

	T -= RemJobs;

	return(T);
}

/* Funzione principale */
int FS_LB_DNT1(Node *N)
{
	int count, total, remain, JobsToDo;
	int temp_1[MAXJOBS+2], temp_2[MAXJOBS+2];
	
	JobsToDo = Jobs - N->Pos1;
	remain = JobsToDo;

	/* Lower Bound IS1	*/
	/* Creazione strutture temp_1 e temp_2 */

	if (N->Pos1 == 0) temp_1[0] = 0;
	else temp_1[0] = JOB[N->Order1[N->Pos1 - 1]].p1;
	temp_2[0] = (N->C2) - (N->C1);

	total = JobsToDo*(N->C1);
	for(count = 0; count < Jobs; count++)
		if(N->NextWork[P1[count].Order] != 0) {

			total += (JobsToDo)*(P1[count].Val) + JOB[P1[count].Order].p2;
			temp_1[remain - JobsToDo + 1] = P1[count].Val;
			temp_2[remain - JobsToDo + 1] = JOB[P1[count].Order].p2;
			JobsToDo--;
		}

	for(count = remain+1; count < Jobs+2; count++) {
		temp_2[count] = 9999;
		temp_1[count] = 9999;
  }
	
	total += hung(remain+1, temp_1, temp_2, N->C1, N->C2);
  
	total += N->CSUM;

	return(total);
}

/********************************************************************/
/* FUNZIONE : FS_LB_DNT2																						*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcolo del Lower Bound DNT2													*/		
/* OUTPUT		: Il Lower Bound																				*/
/********************************************************************/
int FS_LB_DNT2(Node *N)
{
	int i, j;
  int K, C;

	int C1SPT[MAXJOBS];
	struct O P2New[MAXJOBS];

  /* A.B. LOWER BOUND */

  DoSRPT(N);
  
  C = 0;
  for (i=0;i<Jobs;i++)
	  if (N->NextWork[i] != 0) C += C2SRPT[i].Val;

	/* Ordinamento C2SRPT */

	qsort((void *)C2SRPT, (size_t)Jobs, sizeof(struct O), (FUNC) O_Inc_Comp);
  
	/* Calcolo C1SPT */

	K = N->Pos1; j = 0;
	for (i=0; i<Jobs; i++)
		if (N->NextWork[P1[i].Order]) {
			K += P1[i].Val;
			C1SPT[j] = K;
			j++;
		}
	
	/* Calcolo C2SRPT - C1SPT */

	for (i=0; i< (Jobs - N->Pos1); i++) 
			C2SRPT[i].Val = C2SRPT[i].Val - C1SPT[i];
		
	/* Ordino il risultato */

	qsort((void *)C2SRPT, (size_t)(Jobs - N->Pos1), sizeof(struct O), (FUNC) O_Inc_Comp);

  /* Calcolo P2New */

	for (i=0; i<Jobs; i++) {
		if (N->NextWork[i]) P2New[i].Val = JOB[i].p2;
		else P2New[i].Val = INT_MAX;
	}
	qsort((void *)P2New, (size_t)Jobs, sizeof(struct O), (FUNC) O_Inc_Comp);
  
	/* Calcolo LB */

	for (i=0; i<(Jobs - N->Pos1); i++) 
		C += Imax(0, P2New[i].Val - C2SRPT[i].Val);
	
  C += N->CSUM;
	
	return(C);
}

/********************************************************************/
/* FUNZIONE : FS_LB_LINDO																						*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcolo del Lower Bound LINDO													*/		
/* OUTPUT		: Il Lower Bound																				*/
/********************************************************************/
int FS_LB_LINDO(Node *N)
{
  int f,s,K, K1, K2, FCOMP[MAXJOBS], SCOMP[MAXJOBS];
  int MaxValue = 0, Res;
  int i,j,k,q,w;
  char string[128];
  float Result;

  FILE *F;
  
  for (i=0; i<21; i++) {
    
	/* Eliminazione sequenze uguali */
		  
	if (AtRoot || OnlyBest == OFF)
		if (i != 0 && SeqCompare(Seq[i-1], Seq[i], N))
			continue;

	/* Nodo radice? Opzione onlybestlambda attiva? */

    if (!AtRoot && OnlyBest == ON) {
      if (i < BestLambdaatRootLINDO) i = BestLambdaatRootLINDO;
	  if (i > BestLambdaatRootLINDO) break;
	}	
	
	/* Calcolo di FCOMP e SCOMP */
    
	f = N->C1; s = N->C2;
	for (j=0; j<Jobs; j++) {
      if (N->NextWork[P1[j].Order] == 0) continue;
	  if (f + P1[j].Val > s) 
	    s = f + P1[j].Val;
	  break;
	}

	for (j=0;j<Jobs;j++) {
	  if (N->NextWork[Seq[i][j]] == 0) continue;
	  f += JOB[Seq[i][j]].p1;
	  s += JOB[Seq[i][j]].p2;
	  FCOMP[Seq[i][j]] = f;
	  SCOMP[Seq[i][j]] = s;
	}

	/* Scrittura F.O. */

	F = fopen("model.dat","w");
	fprintf(F,"MAX ");
    w = 0;

	for (j=0;j<Jobs;j++) {
	  if (N->NextWork[Seq[i][j]] == 0) continue;
	  if ((j%10) == 0) fprintf(F,"\n");
	  K = FCOMP[Seq[i][j]] + JOB[Seq[i][j]].p2 - SCOMP[Seq[i][j]];
	  if (j && K >= 0) fprintf(F, "+");
	  fprintf(F,"%dL%d", K, Seq[i][j]);
	  w += SCOMP[Seq[i][j]];
	}

	SCOMP[0] = w; 

	fprintf(F,"\nSUBJECT TO\n");

	/* Scrittura Vincoli */
	f = 1;
	for (j=0;j<Jobs;j++) {
	  q = Seq[i][j];
	  if (N->NextWork[q] == 0) continue;

	  fprintf(F, "     %d) ",f);
	  f++;
	  fprintf(F,"L%d <= 1\n",q);
	  fprintf(F, "     %d) ",f);
	  f++;
	  fprintf(F,"-1 L%d <= 0\n",q);
	  
	  for (k=j+1;k<Jobs;k++) {
	    w = Seq[i][k];
		if (N->NextWork[w] == 0) continue;

		/* w precede q */

		fprintf(F, "     %d) ", f);
		
		K1 = JOB[q].p1 - JOB[q].p2;
		
		if (K1>0) fprintf(F,"%d L%d ",K1,w);
		if (K1<0) fprintf(F,"-%d L%d ",-K1,w);
		
		K2 = JOB[w].p2 - JOB[w].p1;
		
		if (K2>0) fprintf(F,"+ %d L%d ", K2, q);
		if (K2<0) fprintf(F,"- %d L%d ", -K2, q);
		
		if (K1 == 0 && K2 == 0) fprintf(F, "0 ");

		fprintf(F,"<= %d\n", JOB[w].p2 - JOB[q].p2);
	  
	    f++;
	  }
	}
	fprintf(F,"END");
	fclose(F);

	/* LANCIO DI LINDO */

	system("LINDO < dummy.txt > dummyres.txt");
	
	/* ESTRAZIONE RISULTATO */

	F = fopen("result.txt", "r");
	if (F == NULL) {
	  printf("LINDOWarning: Missing Output File. ");
	  continue;
	}
	fgets(string,128,F);
	fgets(string,128,F);
	
	if (string[4] != 79 && string[21] != 83) {
		printf("LINDOWarning: No Solution. ");
		fclose(F);
		continue;
	}
	
	fgets(string,128,F);
	fgets(string,128,F);
	fscanf(F, "%s", &string);
	if (string[1] != 41) {
		printf("LINDOWarning: Boh! ");
		fclose(F);
		continue;
	}
	fscanf(F, "%s", &string);
	sscanf(string, "%f\n", &Result);

  Result += (float)SCOMP[0];
	Res = (int)(Result + APPROX);

	fclose(F);

    if (Res > MaxValue) {
		MaxValue = Res;
		if (AtRoot) BestLambdaatRootLINDO = i;
	}
  }

  MaxValue += N->CSUM;

  return(MaxValue);
}

/********************************************************************/
/* FUNZIONE : FS_LB_LA																							*/
/* INPUT		: Puntatore ad un nodo e indice miglior seq. VDV				*/
/* EFFETTO  : Calcolo del lower bound LA														*/
/* OUTPUT		: Il lower bound																				*/
/*																																	*/
/* STRUTTURE UTILIZZATE : L1 e L2 per il calcolo dei limiti superio */
/*											re ed inferiore dei lambda del duale				*/
/*																																	*/
/* ALTRE FUNZIONI UTILIZZATE	: lim_add(), Create_Limits(),					*/
/*														LB_LIMITS(), EveryLSeq()							*/
/********************************************************************/

int LAInit(void)
{
	int i;
	
	for (i=0;i<21;i++) {
		Istrcpy(LSeq, Seq[i]);
		Create_Limits(LIMITSVDV[i],0);	
	}
	
	return(0);
}

int lim_add(limit *L, int a,int b,double k, double m) 
{
  /* il LIMITS[a] influenza il LIMITS[b] con k e m */

  L[a].Mod[L[a].mod_size].lim_id = b;
  L[a].Mod[L[a].mod_size].k = k;
  L[a].Mod[L[a].mod_size].m = m;
  
  L[a].mod_size = L[a].mod_size + 1;
 
  return(0);
}

int Create_Limits(limit *L, int KeepL)
{
  /* Init */
	
  int i,k,ii,kk,a,b,c;
  double ab,cb,ba,ca;
  
  /* Ottimizzazione tabelle */
	if (KeepL) { 
    for (i=0;i<Jobs;i++) {
      L[2*i].curr_value   = 0.0;
			L[2*i+1].curr_value = 1.0;
		}
		return(0);
  }

  for (i=0;i<Jobs;i++) {
    L[2*i].type   = LOWER;
		L[2*i+1].type = UPPER;
    L[2*i].mod_size   = 0;
		L[2*i+1].mod_size = 0;
    L[2*i].curr_value = (double)0.0;
		L[2*i+1].curr_value = (double)1.0;
    L[2*i].dirty = 0;
		L[2*i+1].dirty = 0;
	}

  /* Inserisco nella tabella tutti i vincoli */
  /* LIMITS[2i] e LIMITS[2i+1] si riferiscono ai limiti dei lambda */
  /* che riguardano i job puntati da JOB[i] */
  /* La sequenza usata e' LSeq[] */

  for (i=0;i<Jobs;i++) {
		ii = LSeq[i];
	  
		for (k=i+1;k<Jobs;k++) {
			kk = LSeq[k];
  
			/* ii precede kk */

			a = JOB[kk].p1 - JOB[kk].p2;
			b = JOB[ii].p1 - JOB[ii].p2;
			c = JOB[ii].p2 - JOB[kk].p2;

			ab = (double)a / (double)b;
			cb = (double)c / (double)b;
			ca = (double)c / (double)a;
			ba = (double)b / (double)a;

			/* Modifica limiti */  

			if (a>0 && b<0) {
				lim_add(L, 2*kk+1, 2*ii, ba, ca);
        lim_add(L, 2*ii+1, 2*kk, ab, -cb);
				continue;
			}
	  
			if (a<0 && b>0) {
				lim_add(L, 2*kk, 2*ii+1, ba, ca);
				lim_add(L, 2*ii, 2*kk+1, ab, -cb);
				continue;
			}

			if (a>0 && b>0) {
				lim_add(L, 2*kk  , 2*ii  , ba, ca);
				lim_add(L, 2*ii+1, 2*kk+1, ab, -cb);
				continue;
			}

			if (a<0 && b<0) {
				lim_add(L, 2*kk+1, 2*ii+1, ba, ca);
				lim_add(L, 2*ii  , 2*kk  , ab, -cb);
	  		continue;
			}

			if (a==0 && b>0)
				lim_add(L, 2*ii, 2*kk+1, 0, -cb);
	  
			if (a==0 && b<0)
				lim_add(L, 2*ii, 2*kk, 0, -cb);
	  
			if (b==0 && a<0)
				lim_add(L, 2*kk, 2*ii+1, 0, ca);
	  
			if (b==0 && a>0)
				lim_add(L, 2*kk, 2*ii, 0, ca);

			if (a==0 && b==0 && c > 0) {
				lim_add(L, 2*kk, 2*ii+1, 0, -100.0);
			  lim_add(L, 2*ii, 2*kk+1, 0, -100.0);
			}
		}
  }

  return(0);
}

int LB_LIMITS(limit *L, Node *N, int KeepL)
{
  int fcomp,scomp;
  int i,ii,j,P,Q;
  double newlim;
  double C2SUM;
  int K[MAXJOBS];
  int NDirty, DirtyList[2*MAXJOBS];
  double bestL,f;
  int best;
  int FirstPassC=0;

  Create_Limits(L, KeepL);

	if (AtRoot) FirstPassC = 0;

  /* Init fcomp,scomp */
  
  NDirty = 0;
  C2SUM  = N->CSUM;
  fcomp  = N->C1;
  scomp  = N->C2;

  for (j=0;j<Jobs;j++)
    if (N->NextWork[P1[j].Order] != 0) {
			if (fcomp + P1[j].Val > scomp)
	      scomp = fcomp + P1[j].Val;
			break;
    }

  /* settaggio dirty bit (solo quelli non ancora fissati) */
  
  for (i=0;i<Jobs;i++) {
	  ii = LSeq[i];
	  if (N->NextWork[ii] != 0) {
	    L[2*ii].dirty = 1;
			L[2*ii+1].dirty = 1;
			DirtyList[NDirty] = 2*ii;
			DirtyList[NDirty + 1] = 2*ii+1;
			NDirty += 2;
	  }
	  else {
	    
			/* Limiti da non considerare */
		  
			L[2*ii].dirty = -1;
			L[2*ii+1].dirty = -1;
	    continue;
	  }
  
		/* Init C2SUM e K */

    fcomp += JOB[ii].p1;
    scomp += JOB[ii].p2;
  
    C2SUM += (double)scomp;
    K[ii] = fcomp + JOB[ii].p2 - scomp;
  }

  P = DirtyList[NDirty - 1];

  while (P != -1) {
		/* Ciclo principale di calcolo dei limiti */

    while (NDirty != 0) {
      if (L[P].dirty == 1) {

				if (AtRoot) FirstPassC++;
				NDirty--;
				L[P].dirty = 0;
	    
				for (j=0;j<L[P].mod_size;j++) {
	    
					Q = L[P].Mod[j].lim_id;
					if (L[Q].dirty == -1) continue;
		
  				/* LIMITS[P] modifica LIMITS[Q] */

					newlim = L[P].Mod[j].k * L[P].curr_value + L[P].Mod[j].m;
		  
					f = newlim - L[Q].curr_value;
					if (f < ZERO && f > -ZERO) f = (double)0.0;

					if (L[Q].type == UPPER)
						if (f < 0.0) {
							L[Q].curr_value = newlim;
							if (newlim - L[Q-1].curr_value < -ZERO)
								return(ERROR);
							if (L[Q].dirty == 0) { 
								L[Q].dirty = 1;
								DirtyList[NDirty] = Q;
								NDirty ++; 
							}
						}
        
					if (L[Q].type == LOWER)
						if (f > 0.0) {
							L[Q].curr_value = newlim;
							if (L[Q+1].curr_value - newlim < -ZERO) 
								return(ERROR);
							if (L[Q].dirty == 0) { 
								L[Q].dirty = 1;
								DirtyList[NDirty] = Q;
								NDirty ++; 
							}
						}
				}
			}
      
			P = DirtyList[NDirty -1];
		}

    /* Quale Lambda fisso ? */

    best = 0; bestL = (double)0.0;

    for (i=0;i<Jobs;i++) {
      if (L[2*i].dirty == -1) continue;
      f = L[2*i].curr_value - L[2*i+1].curr_value;
      f = f * K[i];
			if (f < 0) f = -f;

			if (f > bestL) { best = i; bestL = f; }
    }
		
    /* Condizione di uscita, nessun miglioramento possibile */

    if (bestL < ZERO) break;

    /* Fisso il lambda best */
  
    if (K[best] > 0) {
			L[2*best].curr_value = L[2*best+1].curr_value;
			L[2*best].dirty = 1;
			NDirty = 1;
			P = 2*best;
    }

    if (K[best] < 0) {
      L[2*best+1].curr_value = L[2*best].curr_value;
			L[2*best+1].dirty = 1;
			NDirty = 1;
			P = 2*best+1;
    }
  } 

  /* CALCOLO DEL L.B. */

	if (AtRoot && FirstPassC > LAComplex) LAComplex = FirstPassC;

  for (i=0;i<Jobs;i++)
		if (L[2*i].dirty != -1) 
			C2SUM += K[i] * L[2*i].curr_value;

  i = (int)(C2SUM + APPROX);
	
	return(i);
}

int EveryLSeq(limit *L, int Pos, int Max, Node *N)
{
  int i, j, l, flag;

	if (Pos == Jobs) {
    l = LB_LIMITS(L, N, 0);
    if (l == ERROR) 
			return(Max);
		if (AtRoot) {
			for (j=0; j<Jobs; j++) printf("%d ", JOB[LSeq[j]].ID);
			printf(" ) LA = %d\n", l);
		}
		if (l > Max) Max = l; 
	
		return(Max);
	}

	if (Pos == 0)
		for (i=0;i<Jobs;i++)
		if (N->NextWork[i] == 0) {
			LSeq[Pos] = i;
			Pos++;
		}

  for (i=0;i<Jobs;i++) {

    flag = 0;
    for (j=0; j<Pos; j++)
			if (i == LSeq[j]) flag = 1;
		if (flag) continue;

		LSeq[j] = i;

		Max = EveryLSeq(L, Pos+1, Max, N);
  }

  return(Max);
}

/* Funzione principale */
int FS_LB_LA(Node *N, int BestSeqVDV)
{
  int i,l,Max = 0, UBLA = 0;

  if (AllSeqExam == ON) {
		if (AtRoot) printf("L.A. Root Examination :\n");
		Max = EveryLSeq(LIMITSUB, 0, 0, N);
		return(Max);
	}
  
	/* Use Euristic ? */

	if (UseEuristic) {
		if (AtRoot) {
			Istrcpy(UBSeq, LastUB1);
			Istrcpy(LSeq, LastUB1);
			UBLA = LB_LIMITS(LIMITSUB, N, 0);
		}
		else {
			Istrcpy(LSeq, UBSeq);
			UBLA = LB_LIMITS(LIMITSUB, N, 1);
		}
	  if (UBLA == ERROR) LA2NA++;
	}
	
	/* LA on VDV Sequences */

	for (i=0;i<21;i++) {
			
		/* Eliminazione sequenze uguali */
		  
		if (AtRoot || OnlyBest == OFF)
			if (GetBestVDV == OFF && i != 0 && SeqCompare(Seq[i-1], Seq[i], N))
				continue;
				
		/* Opzione OnlyBest attiva? */

		if (!AtRoot && OnlyBest == ON) {
			
			if (GetBestVDV == OFF) {
				Istrcpy(LSeq, Seq[BestLambdaatRootLA]);
				l = LB_LIMITS(LIMITSVDV[BestLambdaatRootLA], N, 1);
			}
			else {
				Istrcpy(LSeq, Seq[BestSeqVDV]);
				l = LB_LIMITS(LIMITSVDV[BestSeqVDV], N, 1);
			}
			if (l == ERROR) printf("LA : Unexpected sequence not allowed");
			if (l > Max) Max = l; 
			break;
		}		
	
		/* i-esima sequenza di Van de Velde */

		Istrcpy(LSeq, Seq[i]);
	
		/*if (AtRoot) 
			l = LB_LIMITS(LIMITSVDV[i], N, 0);
		else*/ 
			l = LB_LIMITS(LIMITSVDV[i], N, 1);

		if (l == ERROR) printf("LA : Unexpected sequence not allowed");
  	
		if (l > Max) {
			if (AtRoot) BestLambdaatRootLA = i;
			Max = l;
		}
	}
  
	/* Statistics for LA2 */

	if (UseEuristic && UBLA != -1) {
		if (UBLA == Max) LA2EQ++;
		if (UBLA > Max) LA2BE++;
		if (UBLA < Max) LA2WO++;
	}
	if (UBLA > Max) Max = UBLA;

  return(Max);
}

/********************************************************************/
/* FUNZIONE : FS_UB_AtRoot																					*/
/* INPUT		: void																									*/
/* EFFETTO  : Calcolo dell' Upper Bound al nodo radice							*/		
/* OUTPUT		: L'Upper Bound																					*/
/********************************************************************/
int FSUB_AtRoot(void)
{
  int t,tt,ttt,tst,tstt;
  c_type seq[MAXJOBS];
  c_type basta=0;
  int local1 = 0,local2 = 0, oldsol,z;
  int i,jj;
	int C2New, C1New;

  oldsol=INT_MAX;  
  z=INT_MAX;

  for (i=0;i<Jobs;i++)              /* inserisce SPT1 in seq */
    seq[i] = P1[i].Order;

  t=0;
  tt=1;
  ttt=0;
  do {
    ttt-=1;
    tt-=1;
    for (tstt=0;tstt<3;tstt++) {
      ttt+=1;
      if (ttt>=3) ttt=0;
      for (tst=1;tst<Jobs;tst++) {
				tt+=1;
				if (tt>=Jobs) tt=1;
				for (t=0;t<tt;t++) {

					if((ttt>0) && (oldsol<INT_MAX) && (tt==t+1)) {
						basta=0;
						break;
					}
					basta=0;
					if((ttt==0) && (oldsol<INT_MAX)) {
						local1=seq[tt];
						local2=seq[t];
						seq[tt]=local2;
						seq[t]=local1;
					}
					if ((ttt==1) && (tt!=t+1)) {
						local1=seq[tt];
						local2=seq[t];
						for (jj=t;jj<tt;jj++) {
							seq[jj]=seq[jj+1];
						}
						seq[tt]=local2;
					}
					if ((ttt==2) && (tt!=t+1)) {
						local1=seq[tt];
						local2=seq[t];
						for (jj=tt;jj>t;jj--) {
							seq[jj]=seq[jj-1];
						}
						seq[t]=local1;
					}
					
					C1New = 0; C2New = 0;
					z = SeqEval(seq, Jobs, &C1New, &C2New);
										
					if ((z>=oldsol)&& (ttt==0) && (oldsol<INT_MAX)) {
						seq[t]=local2;
						seq[tt]=local1;
					}

					if ((z>=oldsol)&& (ttt==1) && (tt!=t+1) && (oldsol<INT_MAX)) {
						for (jj=tt-1;jj>t;jj--) {
							seq[jj]=seq[jj-1];
						}
						seq[t]=local2;
						seq[tt]=local1;
					}

					if ((z>=oldsol)&& (ttt==2) && (tt!=t+1) && (oldsol<INT_MAX)) {
						for (jj=t+1;jj<tt;jj++) {
							seq[jj]=seq[jj+1];
						}
						seq[t]=local2;
						seq[tt]=local1;
					}
					if (z<oldsol) {
	       
						for (i=0;i<Jobs;i++) {
							LastUB1[i] = seq[i];
							LastUB2[i] = seq[i];
						}
		  
						oldsol=z;						/* considera la nuova se_ */
						basta=1;						/* quenza solo se viene   */
																/* migliorato il valore di*/
																/* somma(Cj)              */
						break;
					}
				}											/* end FOR t    */
				if (basta==1) break;
			}												/* end FOR tst  */
			if (basta==1) break;
		}													/* end FOR tstt */
	}
	while (basta==1);

  LastUBValue = oldsol;
	return(oldsol);
}

/********************************************************************/
/* FUNZIONE : FS_UB_AtRoot_MO																				*/
/* INPUT		: void																									*/
/* EFFETTO  : Calcolo dell' Upper Bound al nodo radice (MULTIOB.)		*/		
/* OUTPUT		: L'Upper Bound																					*/
/********************************************************************/
int FSUB_AtRoot_MO(void)
{

  int t,tt,ttt,tst,tstt;
  c_type seq[MAXJOBS];
  int basta=0;
  int local1 = 0,local2 = 0, oldsol,z;
  int i,jj;
	int C2New, C1New;

  oldsol=INT_MAX;  
  z=INT_MAX;       

  for (i=0;i<Jobs;i++)              /* inserisce JH in seq */
    seq[i] = JHSequence[i];

  t=0;
  tt=1;
  ttt=0;
  do {
    ttt-=1;
    tt-=1;
    for (tstt=0;tstt<3;tstt++) {
      ttt+=1;
      if (ttt>=3) ttt=0;
      for (tst=1;tst<Jobs;tst++) {
				tt+=1;
				if (tt>=Jobs) tt=1;
				for (t=0;t<tt;t++) {

					if((ttt>0) && (oldsol<INT_MAX) && (tt==t+1)) {
						basta=0;
						break;
					}
					basta=0;
					if((ttt==0) && (oldsol<INT_MAX)) {
						local1=seq[tt];
						local2=seq[t];
						seq[tt]=local2;
						seq[t]=local1;
					}
					if ((ttt==1) && (tt!=t+1)) {
						local1=seq[tt];
						local2=seq[t];
						for (jj=t;jj<tt;jj++) {
							seq[jj]=seq[jj+1];
						}
						seq[tt]=local2;
					}
					if ((ttt==2) && (tt!=t+1)) {
						local1=seq[tt];
						local2=seq[t];
						for (jj=tt;jj>t;jj--) {
							seq[jj]=seq[jj-1];
						}
						seq[t]=local1;
					}
					
					C1New = 0; C2New = 0;
					z = SeqEval(seq, Jobs, &C1New, &C2New);
					if (C2New > MO_C2Limit) z = INT_MAX;
					
					if ((z>=oldsol)&& (ttt==0) && (oldsol<INT_MAX)) {
						seq[t]=local2;
						seq[tt]=local1;
					}

					if ((z>=oldsol)&& (ttt==1) && (tt!=t+1) && (oldsol<INT_MAX)) {
						for (jj=tt-1;jj>t;jj--) {
							seq[jj]=seq[jj-1];
						}
						seq[t]=local2;
						seq[tt]=local1;
					}

					if ((z>=oldsol)&& (ttt==2) && (tt!=t+1) && (oldsol<INT_MAX)) {
						for (jj=t+1;jj<tt;jj++) {
							seq[jj]=seq[jj+1];
						}
						seq[t]=local2;
						seq[tt]=local1;
					}
					if (z<oldsol) {
	       
						for (i=0;i<Jobs;i++) {
							LastUB1[i] = seq[i];
							LastUB2[i] = seq[i];
						}
		  
						oldsol=z;						/* considera la nuova se_ */
						basta=1;						/* quenza solo se viene   */
																/* migliorato il valore di*/
																/* somma(Cj)              */
						break;
					}
				}											/* end FOR t    */
				if (basta==1) break;
			}												/* end FOR tst  */
			if (basta==1) break;
		}													/* end FOR tstt */
	}
	while (basta==1);

  LastUBValue = oldsol;
	return(oldsol);
}


/********************************************************************/
/* FUNZIONE : FSUB_PLNUB																						*/
/* INPUT		: void																									*/
/* EFFETTO  : Calcolo dell' Upper Bound al nodo radice con PLNUB		*/		
/* OUTPUT		: L'Upper Bound																					*/
/********************************************************************/
int FSUB_PLNUB(void)
{
	int i,j;
	FILE *Out;
	int OldUB, NewUB;

	Out = fopen("UB.rep", "r");

	if (Out == NULL) { printf("\nRun PLNUB First!\n"); FreeAll(); exit(0); }
 	
	fscanf(Out, "%d ", &NewUB);
	
	OldUB = 0;
	if (OldEuristic) {
		OldUB = FSUB_AtRoot();
		if (OldUB < NewUB) return(OldUB);
	}

	LastUBValue = NewUB;

	if (LastUBValue == INT_MAX) return(INT_MAX);

	for (i=0; i<Jobs; i++) {
		fscanf(Out, "%d ", &j);
		LastUB1[i] = j;
		LastUB2[i] = j;
	}
	
	i = 0; j = 0;
	if (SeqEval(LastUB1, Jobs, &i, &j) != LastUBValue) {
		printf("\nRun PLNUB first!\n");
		FreeAll();
		exit(0);
	}

	fclose(Out);

  return(LastUBValue);
}

/********************************************************************/
/* FUNZIONE : FS_UB																									*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Calcolo dell' Upper Bound al nodo											*/		
/* OUTPUT		: L'Upper Bound																					*/
/********************************************************************/
int FSUB(Node *N)
{
	int i, f, s;
	int S[MAXJOBS+1];
	
	f = 1;
	S[0] = 0;
	for (i=0;i<Jobs;i++)
		if (N->NextWork[P1[i].Order] != 0) { 
			S[f] = P1[i].Order;
			f++;
		}
				
	i = Jobs - N->Pos1 - 1;
	while(i > 0) {
		if((JOB[S[i]].p2 >JOB[S[i+1]].p2)&&(JOB[S[i]].p2 >JOB[S[i+1]].p1)) {

			if (i < Jobs - N->Pos1 -1) 
				if(Imax(0,JOB[S[i-1]].p2-JOB[S[i]].p1) +
					Imax(0,JOB[S[i]].p2-JOB[S[i+1]].p1) +
					Imax(0,JOB[S[i+1]].p2-JOB[S[i+2]].p1) >=
					Imax(0,JOB[S[i-1]].p2-JOB[S[i+1]].p1) +
					Imax(0,JOB[S[i+1]].p2-JOB[S[i]].p1) +
					Imax(0,JOB[S[i]].p2-JOB[S[i+2]].p1) +
					JOB[S[i+1]].p1-JOB[S[i]].p1) {
					
						f = S[i+1];
						S[i+1] = S[i];
						S[i] = f;
						i = Imin(i+2, Jobs - N->Pos1 -1);
						continue;
					}
			
			if (i == Jobs - N->Pos1 -1) 
				if(Imax(0,JOB[S[i-1]].p2-JOB[S[i]].p1) +
					Imax(0,JOB[S[i]].p2-JOB[S[i+1]].p1) >=
					Imax(0,JOB[S[i-1]].p2-JOB[S[i+1]].p1) +
					Imax(0,JOB[S[i+1]].p2-JOB[S[i]].p1) +
					JOB[S[i+1]].p1-JOB[S[i]].p1) {
					
						f = S[i+1];
						S[i+1] = S[i];
						S[i] = f;
						i = Imin(i+2, Jobs - N->Pos1 -1);
						continue;
					}
			
			i--;
		}
		else i--;
  }

	Istrcpy(LastUB1, N->Order1);
	for (i=N->Pos1; i<Jobs; i++) LastUB1[i] = S[i-N->Pos1+1];
	Istrcpy(LastUB2, LastUB1);

	f = 0; s = 0;
	LastUBValue = SeqEval(LastUB1, Jobs, &f, &s);

	if (M_O)
		if (s > MO_C2Limit) LastUBValue = INT_MAX;

  return(LastUBValue);
}

/******************************/
/* JOB SHOP BOUNDS PROCEDURES */
/******************************/

/******************/
/* MAIN FUNCTIONS */
/******************/

/********************************************************************/
/* FUNZIONE : Bounds_Init																						*/
/* INPUT		: void																									*/
/* EFFETTO  : Lancia il BoundInit per Flow Shop o Job Shop					*/	
/* OUTPUT		: 0																											*/
/********************************************************************/
int BoundsInit(void)
{
  if (FlowShop) return(FSBoundsInit());
  
  return(0);
}

/********************************************************************/
/* FUNZIONE : LB																										*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Lancia i Lower Bounds attivi													*/	
/* OUTPUT		: Il miglior lower bound																*/
/********************************************************************/
int LB(Node *N)
{	
  int Max = 0, l, BestSeqVDV;
	int BestLB = -1;

  if (FlowShop) {

		if (A_B == ON) { 
			l = FS_LB_AB(N);
			if (AtRoot)
				printf("Root LowerBound AHMADI_BAGCHI = %d\n", l);
		  if (l > Max) { Max = l;	BestLB = 0;}
		}
		if (IS1 == ON) { 
			l = FS_LB_IS1(N);
			if (AtRoot)
				printf("Root LowerBound IS1 = %d\n", l);
		  if (l > Max) { Max = l;	BestLB = 1;}
		}
		if (IS2 == ON) { 
			l = FS_LB_IS2(N);
			if (AtRoot)
				printf("Root LowerBound IS2 = %d\n", l);
		  if (l > Max) { Max = l;	BestLB = 2;}
		}

		if (HV == ON) { 
			l = FS_LB_HV(N);
			if (AtRoot)
				printf("Root LowerBound HV = %d\n", l);
		  if (l > Max) { Max = l;	BestLB = 3;}
		}


		if (VDV_ORIGINAL == ON) { 
			l = FS_LB_VDV(N, &BestSeqVDV);
			if (AtRoot)
				printf("Root LowerBound VDV_ORIGINAL = %d\n", l);
		  if (l > Max) { Max = l;	BestLB = 4;}
		}
	
		if (VDV_CORRECTED == ON) {
		  l = FS_LB_VDV2(N);
		  if (AtRoot)
				printf("Root LowerBound VDV_CORRECTED = %d\n", l);
			if (l > Max) { Max = l; BestLB = 5;}
		}
		
		if (DNT1 == ON) {
			l = FS_LB_DNT1(N);
			if (AtRoot)
				printf("Root LowerBound DNT1 = %d\n", l);
			if (l > Max) { Max = l;	BestLB = 6;}
		}

		if (DNT2 == ON) {
			l = FS_LB_DNT2(N);
			if (AtRoot)
				printf("Root LowerBound DNT2 = %d\n", l);
			if (l > Max) { Max = l;	BestLB = 7;}
		}

		if (LINDO == ON) {
			l = FS_LB_LINDO(N);
			if (AtRoot)
				printf("Root LowerBound LINDO = %d\n", l);
			if (l >= Max) { Max = l; BestLB = 8;}
		}
	
		if (LA == ON) {
			if (Max >= BestSolValue) { BestLB = -1; return(Max);}
			l = FS_LB_LA(N, BestSeqVDV);
			if (AtRoot)
				printf("Root LowerBound LA = %d (Max. Complexity = %d*n2)\n", l, LAComplex/(Jobs*2));
			if (l >= Max) { Max = l; BestLB = 9;}
		}

		if (BestLB != -1) (LBStats[BestLB])++;

    return(Max);
  }

  return(0);
}

/********************************************************************/
/* FUNZIONE : UB																										*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Lancia l'upperbound per il nodo in input							*/	
/* OUTPUT		: Upper Bound																						*/
/********************************************************************/
int UB(Node *N) 
{
  if (NewEuristic == OFF && OldEuristic == OFF) return(INT_MAX);

	if (AtRoot) {
		if (NewEuristic && M_O == OFF) return(FSUB_PLNUB());
		if (OldEuristic && M_O == OFF) return(FSUB_AtRoot());
		if (M_O == ON) return(FSUB_AtRoot_MO());
	}

  return(FSUB(N));
  
}

/********************************************************************/
/* FUNZIONE : BoundsStat																						*/
/* INPUT		: void																									*/
/* EFFETTO  : Visualizza le statistiche raccolte sui lower bounds		*/	
/* OUTPUT		: 0																											*/
/********************************************************************/
int BoundsStat(void)
{
	if (FlowShop) {
		printf("Best LB : ");
		if (A_B == ON) printf("AB:%d;", LBStats[0]);
		if (IS1 == ON) printf("IS1:%d;", LBStats[1]);
		if (IS2 == ON) printf("IS2:%d;", LBStats[2]);
		if (HV == ON) printf("HV:%d;", LBStats[3]);
		if (VDV_ORIGINAL == ON) printf("VDV:%d;", LBStats[4]);
		if (VDV_CORRECTED == ON) printf("VDVC:%d;", LBStats[5]);
		if (DNT1 == ON) printf("DNT1:%d;", LBStats[6]);
		if (DNT2 == ON) printf("DNT2:%d;", LBStats[7]);
		if (LINDO == ON) printf("LINDO:%d;", LBStats[8]);
		if (LA == ON) {
			printf("LA:%d;", LBStats[9]);
			if (UseEuristic) 
				printf("(Euristic-> N.A.: %d, better/eq./worse: %d-%d-%d", LA2NA, LA2BE, LA2EQ, LA2WO);
		}	
		printf("\n");
	}

	return(0);
}