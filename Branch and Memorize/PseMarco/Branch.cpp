/********************************************************************/
/* MODULO					: Branch.C																				*/
/* FUNZIONALITA'	: Implementa la fase di branch dell'algoritmo di  */
/*								BeB utilizzando funzioni di dominanza e richiaman-*/
/*								do poi i lower-upper bounds  quando necessario.		*/
/********************************************************************/ 

#include "beb.h"
#include "branch.h"
#include "bounds.h"
#include "utils.h"
#include "limits.h"


#include <stdio.h>
#include <stdlib.h>

#include "database.h"

extern int DomStrategy;


#pragma region solmemo
#define  NB MAXJOBS
extern int best[NB + 1];
extern int bestlb[NB + 1];
extern bool memlb[NB + 1];
extern bool Stra6LBMemoOn; 
void UpdateBestOnSolve(Node * node, bool saveToDb, bool isLb);
#pragma  endregion





/**************/
/* PROTOTYPES */
/**************/

int Istrcpy(c_type *Dest, c_type *Source);

int FSPreDominance(void);
int FSDominance1(Node *N, int Next);
int FSDominance2(Node *N, int Next);
int FSDominance3(Node *N, int Next);
int FSDominance4(Node *N, int Next);
int FSDominance5(Node *N, int Next);
int FSDominance6(Node *N, int Next);
int FSDominance7(Node *N, int Next);
int FSDominance8(Node *N, int Next);
int FSDominanceMO(Node *N, int Next);

int FSBranch(Node *N);

/***********/
/* GLOBALS */
/***********/

/* Debug Variables */

int DbgSequence[MAXJOBS] = {9,4,6,3,2,0,12,8,13,5,14,11,7,1,10};
int DbgNode;

/* Statistics */

int StatD1 = 0, StatD2 = 0, StatD3 = 0, StatD4 = 0, StatD4DB = 0;
int StatD5 = 0, StatD6 = 0, StatD7 = 0, StatD8 = 0,  Stat1 = 0, Stat2 = 0; 

/* Dominance Variables : if PreDominance1[i][j] == 1 then */
/* the preliminary condition for i->j (1' dominance) is verified */
/* If PreDominance[i][j][0] == 1 is verified the pre-condition */
/* for the 2' dominance criteria. In PreDominance2[i][j][1,2] */
/* there are pre-computed some useful formulas */

int PreDominance1[MAXJOBS][MAXJOBS];
int PreDominance2[MAXJOBS][MAXJOBS][3];

/***********************/
/* FLOW SHOP BRANCHING */
/***********************/

/********************************************************************/
/* FUNZIONE : FSPreDominance																				*/
/* INPUT		: void																									*/
/* EFFETTO  : Pre-calcolo, ove possibile, di alcuni crit. di domin.	*/		
/* OUTPUT		: 0																											*/
/********************************************************************/
int FSPreDominance(void)
{
  int i,j;

  /* Dominance 1 */

  for (i=0;i<Jobs;i++)
    for (j=0;j<Jobs;j++)
      if (i != j && JOB[i].p1 <= JOB[j].p1 && JOB[i].p2 >= JOB[j].p2)
  	    PreDominance1[i][j] = 1;
	  else
		PreDominance1[i][j] = 0;
	
  /* Dominance 2 */

  for (i=0;i<Jobs;i++)
    for (j=0;j<Jobs;j++)
			if (JOB[i].p2 < JOB[j].p2) {
				PreDominance2[i][j][0] = 1;
				PreDominance2[i][j][1] = JOB[i].p2 - JOB[j].p2 + Imax(0, JOB[i].p1 - JOB[j].p1);
				PreDominance2[i][j][2] = Imin(JOB[i].p1, JOB[j].p2) - Imin(JOB[i].p2, JOB[j].p1);
			}
			else
				PreDominance2[i][j][0] = 0;

  /* Init DB */

  AllocDB(DBMaximumDimension, Jobs);

  return(0);
}

/********************************************************************/
/* FUNZIONE : FSDominance1																					*/
/* INPUT		: Puntatore ad un nodo e un indice j										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominance1(Node *N, int j)//! on no-scheduled jobs, ok.
{
  int i,A,B;

  if (Dom1 == OFF) return(0);
	
  for (i=0;i<Jobs;i++) {

    if (N->NextWork[i] == 0) continue;
    if (i == j) continue;

    if (PreDominance1[i][j] == 0) continue;
    
    A = Imax(N->C1 + JOB[i].p1 + JOB[i].p2, N->C2 + JOB[i].p2);
    B = Imax(N->C1 + JOB[j].p1 + JOB[j].p2, N->C2 + JOB[j].p2);

    if (A>B) continue;

		/* Se uguali ne taglio solo uno! (Tengo quello con davanti */
		/* il job con indice minore) */

		if (JOB[i].p1 == JOB[j].p1 && JOB[i].p2 == JOB[j].p2)
			if (i>j) continue;

    return(1);
  }

  return(0);
}

/********************************************************************/
/* FUNZIONE : FSDominance2																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominance2(Node *N, int i)//!polluting dominance.
{
  int A,j;

  if (Dom2 == OFF || M_O == ON) return(0);
  if (N->Pos1 < 1) return(0);

  j = N->Order1[N->Pos1 - 1];//!last scheduled job is involved.

  if (PreDominance2[i][j][0] == 0) return(0);

  A  = PreDominance2[i][j][2];
  A  = A * (Jobs - N->Pos1 - 1);
  A += PreDominance2[i][j][1];

  if (A > 0) return(0);
  //! need to mark as polluted.
  if (BranchStrategy == SOLLBMEMO)
	  N->Pos2 = -N->Pos2-1;
  return(1);
}

/********************************************************************/
/* FUNZIONE : FSDominance3																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/* NOTA			: Tra due sequenze 'equivalenti' con i job A e B scam-  */
/*						biati, per rendere compatibile questo criterio di			*/
/*					  dominanza con il primo si tiene la sequenza con davan-*/
/*						ti 1) il job con p1 minore 2) il job con p2 maggiore  */
/*						3) il job con indice minore														*/
/********************************************************************/
int FSDominance3(Node *N, int i)
{
  int j, C2j_ji, C2i_ji;
  int Start1, Start2, C1i_ij, C2i_ij, C1j_ij, C2j_ij;

  if (Dom3 == OFF) return(0);
  if (N->Pos1 < 1) return(0);

  j = N->Order1[N->Pos1 - 1];//!involve the last scheduled job

  C2j_ji = N->C2;
  C2i_ji = Imax(N->C1 + JOB[i].p1 + JOB[i].p2, N->C2 + JOB[i].p2);

  if (N->Pos1 == 1) {
    Start1 = 0;
    Start2 = 0;
  }
  else {
    Start1 = N->CFirst[N->Order1[N->Pos1 - 2]];
    Start2 = N->CSecond[N->Order1[N->Pos1 - 2]];
  }

  C1i_ij = Start1 + JOB[i].p1;
  C1j_ij = C1i_ij + JOB[j].p1;
  C2i_ij = Imax(Start1 + JOB[i].p1 + JOB[i].p2, Start2 + JOB[i].p2);
  C2j_ij = Imax(C1j_ij + JOB[j].p1 + JOB[j].p2, C2i_ij + JOB[j].p2);

  /* Se uguali ne pruno uno solo									*/

  if ((C2i_ji == C2j_ij) && (C2j_ji + C2i_ji == C2i_ij + C2j_ij)) {
	  if (JOB[j].p1<JOB[i].p1) return(0);
		if (JOB[j].p2>JOB[i].p2) return(0);
		if (j < i) return(0);
	}

  if (C2i_ji < C2j_ij) return(0);
  if (C2j_ji + C2i_ji < C2i_ij + C2j_ij) return(0);
  if(BranchStrategy==SOLLBMEMO)N->Pos2 = -N->Pos2;
  return(1);
}

/********************************************************************/
/* FUNZIONE : FSDominance4																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominance4(Node *N, int i)
{
  
	int jp,j,k,t, n;
	int CSUMOld, CSUMNew, C2Old, C2New;
	c_type S[MAXJOBS], A, B, C, D, E;

	if (Dom4 == OFF) return(0);
  
	n = Jobs - N->Pos1;

	/* Normale sequenza : JOB i in fondo. */
	C2Old = Imax(N->C1 + JOB[i].p1 + JOB[i].p2, N->C2 + JOB[i].p2);
	CSUMOld = N->CSUM + C2Old;

	for (jp=0; jp<(N->Pos1); jp++) {	//! scheduled jobs involved
	
		j = N->Order1[jp];
		
		A = 0; B = 0; C = 0;
		if (jp != 0) {
			A = N->CFirst[N->Order1[jp-1]];
			B = N->CSecond[N->Order1[jp-1]];
			for (k=0; k<jp; k++) C += N->CSecond[N->Order1[k]];
		}
				
		/* NAPI : Scambio i-j per ogni j*/
			
		S[0] = i;
		for (k= 1; k < N->Pos1 - jp; k++) S[k] = N->Order1[k+jp];
		S[N->Pos1-jp] = j;

		t = A; C2New = B;
		CSUMNew = C + SeqEval(S, N->Pos1+1-jp, &t, &C2New);

		/* Dominanza */
	
		if (CSUMOld >= CSUMNew) {
			if (M_O == OFF) D = n*(C2New - C2Old); else D = C2New;
			if (M_O == OFF) E = CSUMOld - CSUMNew; else E = C2Old;
			if (D <= E) {
				if (CSUMOld == CSUMNew && D == E) {
					if (JOB[j].p1 < JOB[i].p1) continue;
					if (JOB[j].p2 > JOB[i].p2) continue;
					if (j < i) continue;
				}
				if (BranchStrategy == SOLLBMEMO)N->Pos2 = -N->Pos2;
				return(1);
			}
		}
	
		/* BSR : Inserimento di i in tutte le posizioni */ 
	  
		S[0] = i;
		for (k = 1; k <= N->Pos1 - jp; k++) S[k] = N->Order1[k-1+jp];
		
		t = A; C2New = B;
		CSUMNew = C + SeqEval(S, N->Pos1+1-jp, &t, &C2New);

		if (CSUMOld >= CSUMNew) {
			if (M_O == OFF) D = n*(C2New - C2Old); else D = C2New;
			if (M_O == OFF) E = CSUMOld - CSUMNew; else E = C2Old;
			if (D <= E) {
				if (CSUMOld == CSUMNew && D == E) {
					if (JOB[j].p1 < JOB[i].p1) continue;
					if (JOB[j].p2 > JOB[i].p2) continue;
					if (j < i) continue;
				}
				if (BranchStrategy == SOLLBMEMO)N->Pos2 = -N->Pos2;
				return(1);
			}
		}
	
		/* FSR : Spostamento al fondo di tutti i j */
	  
		for (k = 0; k < N->Pos1 - 1 - jp; k++) S[k] = N->Order1[k+1+jp];
		S[N->Pos1 - 1-jp] = i;
		S[N->Pos1-jp] = j;
		
		t = A; C2New = B;
		CSUMNew = C + SeqEval(S, N->Pos1+1-jp, &t, &C2New);

		if (CSUMOld >= CSUMNew) {
			if (M_O == OFF) D = n*(C2New - C2Old); else D = C2New;
			if (M_O == OFF) E = CSUMOld - CSUMNew; else E = C2Old;
			if (D <= E) {
				if (CSUMOld == CSUMNew && D == E) {
					if (JOB[j].p1 < JOB[i].p1) continue;
					if (JOB[j].p2 > JOB[i].p2) continue;
					if (j < i) continue;
				}
				if (BranchStrategy == SOLLBMEMO)N->Pos2 = -N->Pos2;
				return(1);
			}
		}
	
	}
	
	return(0);
}

/********************************************************************/
/* FUNZIONE : FSDominance4withDB																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominance4withDB(Node *N, int i)//! not called
{
  
	int jp,j,k,t, n, *index2;
	int CSUMOld, CSUMNew, C2Old, C2New;
	c_type S[MAXJOBS], SOld[MAXJOBS], A, B, C, D, E;

	if (Dom4 == OFF) return(0);

	n = Jobs - N->Pos1;

	/* Normale sequenza : JOB i in fondo. */

	C2Old = Imax(N->C1 + JOB[i].p1 + JOB[i].p2, N->C2 + JOB[i].p2);
	CSUMOld = N->CSUM + C2Old;

	for (t=0; t<N->Pos1; t++) SOld[t] = N->Order1[t];
	SOld[N->Pos1] = i;
	
	// DB Search
	if (DBAdd(SOld, CSUMOld, C2Old, N->Pos1 + 1, 1, index2) == -1) {
		StatD4DB++;
		return(1);
	}
	
	for (jp=0; jp<(N->Pos1); jp++) {	
	
		j = N->Order1[jp];
		
		A = 0; B = 0; C = 0;
		if (jp != 0) {
			A = N->CFirst[N->Order1[jp-1]];
			B = N->CSecond[N->Order1[jp-1]];
			for (k=0; k<jp; k++) C += N->CSecond[N->Order1[k]];
		}
				
		/* NAPI : Scambio i-j per ogni j*/
			
		S[0] = i;
		for (k= 1; k < N->Pos1 - jp; k++) S[k] = N->Order1[k+jp];
		S[N->Pos1-jp] = j;

		t = A; C2New = B;
		CSUMNew = C + SeqEval(S, N->Pos1+1-jp, &t, &C2New);

		/* Dominanza */
	
		if (CSUMOld >= CSUMNew) {
			if (M_O == OFF) D = n*(C2New - C2Old); else D = C2New;
			if (M_O == OFF) E = CSUMOld - CSUMNew; else E = C2Old;
			if (D <= E) {
				if (CSUMOld == CSUMNew && D == E) {
					if (JOB[j].p1 < JOB[i].p1) continue;
					if (JOB[j].p2 > JOB[i].p2) continue;
					if (j < i) continue;
				}
				return(1);
			}
		}
	
		/* BSR : Inserimento di i in tutte le posizioni */ 
	  
		S[0] = i;
		for (k = 1; k <= N->Pos1 - jp; k++) S[k] = N->Order1[k-1+jp];
		
		t = A; C2New = B;
		CSUMNew = C + SeqEval(S, N->Pos1+1-jp, &t, &C2New);

		if (CSUMOld >= CSUMNew) {
			if (M_O == OFF) D = n*(C2New - C2Old); else D = C2New;
			if (M_O == OFF) E = CSUMOld - CSUMNew; else E = C2Old;
			if (D <= E) {
				if (CSUMOld == CSUMNew && D == E) {
					if (JOB[j].p1 < JOB[i].p1) continue;
					if (JOB[j].p2 > JOB[i].p2) continue;
					if (j < i) continue;
				}
				return(1);
			}
		}
	
		/* FSR : Spostamento al fondo di tutti i j */
	  
		for (k = 0; k < N->Pos1 - 1 - jp; k++) S[k] = N->Order1[k+1+jp];
		S[N->Pos1 - 1-jp] = i;
		S[N->Pos1-jp] = j;
		
		t = A; C2New = B;
		CSUMNew = C + SeqEval(S, N->Pos1+1-jp, &t, &C2New);

		if (CSUMOld >= CSUMNew) {
			if (M_O == OFF) D = n*(C2New - C2Old); else D = C2New;
			if (M_O == OFF) E = CSUMOld - CSUMNew; else E = C2Old;
			if (D <= E) {
				if (CSUMOld == CSUMNew && D == E) {
					if (JOB[j].p1 < JOB[i].p1) continue;
					if (JOB[j].p2 > JOB[i].p2) continue;
					if (j < i) continue;
				}
				return(1);
			}
		}
	
	}
	
	return(0);
}

/********************************************************************/
/* FUNZIONE : FSDB																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDB(Node *N, int *index2)
{
  
	int jp,j,k,t, n;
	int CSUMOld, CSUMNew, C2Old, C2New;
	c_type S[MAXJOBS], SOld[MAXJOBS], A, B, C, D, E;

	n = Jobs - N->Pos1;

	/* Normale sequenza : JOB i in fondo. */

	C2Old = N->C2;
	CSUMOld = N->CSUM;

	for (t=0; t<N->Pos1; t++) SOld[t] = N->Order1[t];
	
	// DB Search
	// We first test with the active nodes//! Note that the current node N is also in the db! 
	*index2=0;
	if (DBAdd(SOld, CSUMOld, C2Old, N->Pos1, 1, index2) == -1) {
		StatD4DB++;
		//if (BranchStrategy == LBORDER){
		//	printf("\nActive nodes are cutting with best first! LbCurr=%d, n_fixed=%d, opt_fixed=%d, C2=%d, jobs:\n ", N->LowerBound, N->Pos1, N->CSUM, N->C2);
		//	for (int i = 0; i < N->Pos1; ++i)printf("(%d,%d,%d,%d)\t", SOld[i], JOB[SOld[i]].ID, JOB[SOld[i]].p1, JOB[SOld[i]].p2);
		//	printf("\n");
		//	getchar();
		//}
		//. Found on 10.17, jobs: Active nodes are cutting with best first! LbCurr=3220, n_fixed=7, opt_fixed=1606, C2=362, jobs
		//  (7, 8, 36, 55)    (9, 10, 38, 18)    (1, 2, 40, 61)     (5, 6, 50, 74)     (3, 4, 62, 10)     (4, 5, 49, 86)     (2, 3, 71, 1)
		return(1);
	}
	// We next test with the done nodes
	*index2=100;
	if (DBAdd(SOld, CSUMOld, C2Old, N->Pos1, 1, index2) == -1) {
		StatD4DB++;
		return(1);
	}
	
	return(0);
}


/********************************************************************/
/* FUNZIONE : FSDominance5																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominance5(Node *N, int j)//! based on unscheduled jobs, nice
{
	int i, k;
	
	if (Dom5 == OFF) return(0);

	for (i=0;i<Jobs;i++)
		for (k=i+1;k<Jobs;k++) {
	
			if (N->NextWork[i] == 0 || N->NextWork[k] == 0) continue;
			
			if (JOB[i].p2 + JOB[k].p2 == JOB[j].p2)
				if (JOB[i].p1 + JOB[k].p1 <= JOB[j].p1)
					return(1);
		}
	
	return(0);
}

/********************************************************************/
/* FUNZIONE : FSDominance6																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/

int FSDominance6(Node *N, int i)//! based on unscheduled jobs
{
	int j, P1MinPos, P2MinPos, P1MinVal, P2MinVal;

	if (Dom6 == OFF) return(0);

	P1MinVal = INT_MAX; P2MinVal = INT_MAX;
	P1MinPos = -1; P2MinPos = 0;
	for (j=0;j<Jobs;j++)
		if (N->NextWork[j] != 0) {
	
			if (JOB[j].p1 < P1MinVal) {
				P1MinVal = JOB[j].p1;
				P1MinPos = j;
			}
			if (JOB[j].p2 < P2MinVal) {
				P2MinVal = JOB[j].p2;
				P2MinPos = j;
			}
	}

	if (P1MinPos == P2MinPos && P1MinVal <= P2MinVal)
		if (P1MinPos != i) return(1);

	return(0);
}


/********************************************************************/
/* FUNZIONE : FSDominance7																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/

int FSDominance7(Node *N, int i)//! based on unscheduled jobs
{
	int j;
	int F = 0, G = 0;

	if (Dom7 == OFF) return(0);

//	if (N->C1 + JOB[i].p1 <= N->C2 && JOB[i].p1 <= JOB[i].p2) {
	
	
		for (j=0;j<Jobs;j++)
			if (N->NextWork[j] != 0) {

				if (JOB[j].p1 <= JOB[i].p1 && JOB[j].p2 < JOB[i].p2 && JOB[j].p1 <= JOB[j].p2)
					F = 1;
				if (JOB[j].p1 <= JOB[i].p1 && JOB[j].p2 < JOB[i].p2 && JOB[j].p1 > JOB[j].p2)
					G = 1;
		}
		if (F && G) return(1);
//	}

	return(0);	
}

/********************************************************************/
/* FUNZIONE : FSDominance8																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice j																						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominance8(Node *N, int i)//! based on prefixed jobs
{
	int Map[MAXJOBS];
	int q,k;
	c_type S[MAXJOBS];
	int Len, C, C2Old, C1Old, CSumNew, C2New, C1New; 

	if (Dom8 == OFF) return(0);

	for (q = 0; q < N->Pos1 - 2; q++) {
	
		/* Start point */
		C = 0;
		if (q==0) {
			C2Old = 0;
			C1Old = 0;
		}
		else {
			C2Old = N->CSecond[N->Order1[q-1]];
			C1Old = N->CFirst[N->Order1[q-1]];
			for (k=0; k<q; k++) C += N->CSecond[N->Order1[k]];
		}

		/* Involved Jobs */
		for (k=0;k<Jobs;k++) Map[k] = 0;
		for (k=q; k < N->Pos1; k++) Map[N->Order1[k]] = 1;
		Map[i] = 1;

		/* Making S */
		Len = 0;
		for (k=0;k<Jobs;k++)
			if (Map[JHSequence[k]]) {
				S[Len] = JHSequence[k];
				Len++;
		}
		
		/* Eval S */

		C1New = C1Old; C2New = C2Old;
		CSumNew = C + SeqEval(S, Len, &C1New, &C2New);

		/* Dominance */

		if (CSumNew < N->CSUM) {
			if (BranchStrategy == SOLLBMEMO)N->Pos2 = -N->Pos2;
			return(1);
		}
	}


	return(0);

}

/********************************************************************/
/* FUNZIONE : FSDominanceMO																					*/
/* INPUT		: Puntatore ad un nodo e un indice i										*/
/* EFFETTO  : Verifica se e' possibile trovare la soluzione ottima	*/
/*					aggiungendo al nodo N come prossimo job quello puntato  */
/*					dall'indice i per il problema MULTIOBIETTIVO						*/		
/* OUTPUT		: 0 (Non eliminabile)																		*/
/*						1 (Eliminabile)																				*/
/********************************************************************/
int FSDominanceMO(Node *N, int Next)
{
	int i, Len;
	c_type S[MAXJOBS];
	int C1, C2;

	Len = 0;
	for (i=0; i<Jobs; i++)
		if (JHSequence[i] != Next && N->NextWork[JHSequence[i]] != 0) {
			S[Len] = JHSequence[i];
			Len++;
	}

	C1 = N->C1 + JOB[Next].p1;
	C2 = Imax(C1, N->C2) + JOB[Next].p2;
	SeqEval(S, Len, &C1, &C2);
	
	if (C2 > MO_C2Limit) return(1);
  
	return(0);
}

/********************************************************************/
/* FUNZIONE : FSBranch																							*/
/* INPUT		: Puntatore ad un nodo																	*/
/* EFFETTO  : Prende il nodo in ingresso e ne fa il branch, inse- 	*/
/*					rendo in lista i nodi dai quali si puo' originare una   */
/*					soluzione ottima (Crit. di dominanza, bounds, ecc)			*/		
/* OUTPUT		: 0																											*/
/********************************************************************/
int FSBranch(Node *N)
{
  int i,j,NewLB, NewUB;
  Node *T;

  if (N->LowerBound >= BestSolValue) {
	  Stat1++;
	  bestlb[N->Pos1] = N->LowerBound - N->CSUM;
	  UpdateBestOnSolve(N, TRUE, TRUE);
	  FreeNode(N);
	  return(0);
  }
  bool isSentinelSaved = false;
  for (i=0;i<Jobs;i++) {

    if (N->NextWork[i] == 0) continue;

    DbgNode = 0;
		if (Debug == ON) {
			DbgNode = 1;
			for (j=0;j<(N->Pos1);j++)
				if (DbgSequence[j] != N->Order1[j]) DbgNode = 0;
			if (i != DbgSequence[N->Pos1]) DbgNode = 0;
		}
		//if (BranchStrategy != SOLLBMEMO){//! disable all dominance conditions
		bool isPolluted = false;
		if (M_O == ON && FSDominanceMO(N, i)) {
				if (DbgNode)
					printf("Dbg_NoticeI");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; } //!cut by external nodes, so still need to evaluate its lb before cut it
				else continue;
		}
		else if (FSDominance1(N, i)) {//! This one+ dom 5,6,7 are no polluting ones. We may put 567 before 2 so that a node can be cut cleanly without being polluted
				StatD1++;
				if (DbgNode)
					printf("Dbg_NoticeA");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
		}
		else if (FSDominance2(N, i)) {
				StatD2++;
				if (DbgNode)
					printf("Dbg_NoticeB");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
		}
		else if (FSDominance3(N, i)) {
				StatD3++;
				if (DbgNode)
					printf("Dbg_NoticeC");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
		}
		else
			//if (FSDominance4withDB(N,i)) {
			if (FSDominance4(N, i)) {
				StatD4++;
				if (DbgNode)
					printf("Dbg_NoticeD");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
			}
			else if (FSDominance5(N, i)) {
				StatD5++;
				if (DbgNode)
					printf("Dbg_NoticeE");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
			}
			else if (FSDominance6(N, i)) {
				StatD6++;
				if (DbgNode)
					printf("Dbg_NoticeF");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
			}
			else if (FSDominance7(N, i)) {
				StatD7++;
				if (DbgNode)
					printf("Dbg_NoticeG");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
			}
			else if (FSDominance8(N, i)) {
				StatD8++;
				if (DbgNode)
					printf("Dbg_NoticeH");
				if (BranchStrategy == SOLLBMEMO && N->Pos2 < 0){ isPolluted = true; N->Pos2 = -N->Pos2 - 1; }
				else continue;
			}
		//}
			if (!isPolluted && BranchStrategy == SOLLBMEMO && !isSentinelSaved&& N->Pos1>1){//!save the sentinel. Without the pos1>1, program never ends since the node with -lb is never distroyed so the list is never empty
				isSentinelSaved = true;
				N->LowerBound = -N->LowerBound;
				AddNode(N);//!no need to do DBAdd since it's always there.
			}
			//if (isPolluted){
			//	if (FSDominance5(N, i) || FSDominance6(N, i) || FSDominance7(N, i)){
			//		printf("Yes!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
			//		getchar();
			//	}
			//}
/*		if ((Nodes % 5000) == 0) { 
			
			if (BranchStrategy == LBORDER) 
				printf("%d(%d-%d)", Nodes, BestLB(), BestSolValue);
			else if (BranchStrategy == AMP) 
				printf("%d(%d-%d)", Nodes, BestLB(), BestSolValue);
			else
				printf("%d(%d)", Nodes, BestSolValue);

			if (DBMaximumDimension != 0)
				printf("(Db=%d) ", GetActualDBDimension());
		}*/

		Nodes++;
		T = NewNode();

		NodeCopy(T,N);
		if (T->LowerBound < 0)T->LowerBound = -T->LowerBound;
		AddaJob(T, i);
		/* Nodi completabili a nodi foglie */

		if (T->Pos1 == Jobs - 1) {
			for (j=0;j<Jobs;j++)
				if (T->NextWork[j]) break;

			AddaJob(T, j);
		}

		/* Nodi eliminabili */

		if (T->CSUM >= BestSolValue) {
			Stat1++;
			bestlb[T->Pos1] = T->LowerBound - T->CSUM;
			UpdateBestOnSolve(T, TRUE, TRUE);
			if (DbgNode)
				printf("Dbg_Notice4");
			FreeNode(T);
			continue;
		}

		/* Nodi Foglie */

		if (T->Pos1 == Jobs) {//!solved

			if (T->CSUM < BestSolValue) {
  				BestSolValue = T->CSUM;
				Istrcpy(BestSol1, T->Order1);
				Istrcpy(BestSol2, T->Order2);

				best[T->Pos1] = bestlb[T->Pos1] = 0;
				UpdateBestOnSolve(T, FALSE, FALSE);//! no need to save since empty pb
			}
			else{
				bestlb[T->Pos1] = 0;
				UpdateBestOnSolve(T, FALSE, TRUE);
			}
			FreeNode(T);
			continue;
		}

		/* Calcolo e confronto LB - UB */

		NewUB = UB(T);
		if (NewUB < BestSolValue) {
			BestSolValue = NewUB;
			Istrcpy(BestSol1, LastUB1);
			Istrcpy(BestSol2, LastUB2);
			//! nothing should be done here, since it's just a ub
			//best[T->Pos1] = bestlb[T->Pos1] = BestSolValue-T->CSUM;
			//UpdateBestOnSolve(T, TRUE, FALSE);
		}
		
		NewLB = LB(T);
		if (NewLB > T->LowerBound) T->LowerBound = NewLB;
				
		if (T->LowerBound >= BestSolValue) {
			Stat2++;
			if (BranchStrategy == SOLLBMEMO){
				bestlb[T->Pos1] = T->LowerBound - T->CSUM;
				UpdateBestOnSolve(T, TRUE, TRUE);
			}
			if (DbgNode)
				printf("Dbg_Notice5\n");
			FreeNode(T);
			continue;
		} 

		/* Caso Generale */
		////! do not add if a fantome node generated by k-perm is already in db 
		//if (DomStrategy & 4){
		//	int MonInd, MonLast;
		//	DBSearch(N->Order1, N->CSUM, N->C2, N->Pos1, &MonInd, &MonLast);
		//	if (MonInd == -1)
		//		DBAdd(T->Order1, T->CSUM, T->C2, T->Pos1, -1, NULL);
		//}else
		if (!isPolluted && !isPolluted){
			DBAdd(T->Order1, T->CSUM, T->C2, T->Pos1, -1, NULL);
			AddNode(T);
			LOG("Add child : %d\n", i);
			Nbnodes++;
		}
		else{//!marked as polluted, should be cut
			memlb[T->Pos1 - 1] = true;
			bestlb[T->Pos1] = T->LowerBound - T->CSUM;
			UpdateBestOnSolve(T, TRUE, TRUE);
			FreeNode(T);
		}
	}
	if (!isSentinelSaved)
		FreeNode(N);
	return(0);
}

/**********************/
/* JOB SHOP BRANCHING */
/**********************/

/******************/
/* MAIN FUNCTIONS */
/******************/

/********************************************************************/
/* FUNZIONE : PreDominance																					*/
/* INPUT		: void																									*/
/* EFFETTO  : Chiama la proc. di PreDominance per il problema in 		*/
/*					esame																										*/		
/* OUTPUT		: 0																											*/
/********************************************************************/
int PreDominance(void)
{
  if (Dom1 == OFF && Dom2 == OFF) return(0);

  if (FlowShop) return(FSPreDominance());

  return(0);
}

/********************************************************************/
/* FUNZIONE : Branch																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Chiama la proc. di Branch per il problema in esame 		*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int Branch(Node *T)
{
  if (FlowShop) return(FSBranch(T));

  return(0);

}

/********************************************************************/
/* FUNZIONE : BranchStat																						*/
/* INPUT		: void																									*/
/* EFFETTO  : Visualizza le statistiche sul branch 									*/
/* OUTPUT		: I nodi tagliati dai criteri di dominanza																											*/
/********************************************************************/
int BranchStat(void)
{
  int DomCutted;

  if (FlowShop) {
    printf("\nNodes pruned by Dom. criteria");
    printf(": 1:%d 2:%d 3:%d 4:%d(%d by DB) 5:%d 6:%d 7:%d 8:%d\n", StatD1, StatD2, StatD3, 
																	StatD4, StatD4DB, StatD5,	
																	StatD6, StatD7, StatD8);
    printf("Nodes pruned by search order : %d\n",Stat1);
	printf("Nodes pruned by LB : %d\n",Stat2);
  }
  
  DomCutted = StatD1 + StatD2 + StatD3 + StatD4 + StatD5 + StatD6 + StatD7 + StatD8;

  return(DomCutted);
}

/********************************************************************/
/* FUNZIONE : FreeDatabase																						*/
/* INPUT		: void																									*/
/* EFFETTO  : Free the database allocated memory 									*/
/* OUTPUT		: 0																											*/
/********************************************************************/

int FreeDatabase(void) {
	FreeDB();
	return(0);
}