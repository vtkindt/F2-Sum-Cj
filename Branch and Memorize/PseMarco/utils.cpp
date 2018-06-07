/********************************************************************/
/* MODULO					: Utils.C																					*/
/* FUNZIONALITA'	: Implementa alcune funzioni di utilita' richiama-*/
/*								te dagli altri moduli del programma.							*/
/********************************************************************/ 

#include "utils.h"
#include "beb.h"

#include <stdio.h>

/**********************/
/* UTILITY PROCEDURES */
/**********************/

/********************************************************************/
/* FUNZIONE : Fmax, Fmin																						*/
/* INPUT		: due double																						*/
/* OUTPUT		: Il maggiore-minore tra i double in input							*/
/********************************************************************/
double Fmax(double A, double B)
{
  if (A > B) return(A);

  return(B);
}
double Fmin(double A, double B)
{
  if (A > B) return(B);

  return(A);
}

/********************************************************************/
/* FUNZIONE : Istrcpy																								*/
/* INPUT		: due stringhe di interi																*/
/* EFFETTO  : Copia la seconda stringa nella prima 									*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int Istrcpy(c_type Dest[MAXJOBS], c_type Source[MAXJOBS])
{
  int i;

  for (i=0;i<Jobs;i++)
    Dest[i] = Source[i];

  return(0);
}

/********************************************************************/
/* FUNZIONE : Istrcmp																								*/
/* INPUT		: due stringhe di interi																*/
/* EFFETTO  : Verifica l'uguaglianza tra le due stringhe						*/
/* OUTPUT		: 0 (diverse)																						*/
/*						1 (uguali)																						*/
/********************************************************************/
int Istrcmp(int A[MAXJOBS], int B[MAXJOBS])
{
  int i;

  for (i=0;i<Jobs;i++)
    if (A[i] !=B[i]) return(0);

  return(1);
}

int Iprint(int A[MAXJOBS])
{
  int i;
  
  for (i=0;i<Jobs;i++)
    printf("%d ", A[i]);

  return(0);
}

/********************************************************************/
/* FUNZIONE : Imax, Imin																						*/
/* INPUT		: due interi																						*/
/* OUTPUT		: Il maggiore-minore tra i interi in input							*/
/********************************************************************/
int Imax(int A, int B)
{
  if (A > B) return(A);

  return(B);
}

int Imin(int A, int B)
{
  if (A > B) return(B);

  return(A);
}

/********************************************************************/
/* FUNZIONE : NodeCopy																							*/
/* INPUT		: due puntatori a Nodo																	*/
/* EFFETTO  : Copia il secondo nodo nel primo			 									*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int NodeCopy(Node *Dest, Node *Source)
{
  /*int i;*/

  Istrcpy(Dest->Order1, Source->Order1);
  Istrcpy(Dest->Order2, Source->Order2);
  Istrcpy(Dest->NextWork, Source->NextWork);
  Dest->C1 = Source->C1;
  Dest->C2 = Source->C2;
  Istrcpy(Dest->CFirst, Source->CFirst);
  Istrcpy(Dest->CSecond, Source->CSecond);
  Dest->CSUM = Source->CSUM;
  Dest->Pos1 = Source->Pos1;
  Dest->Pos2 = Source->Pos2;
  Dest->LowerBound = Source->LowerBound;
  Dest->Next = Source->Next;

  return(0);
}

/********************************************************************/
/* FUNZIONE : SeqEval																								*/
/* INPUT		: Una sequenza e i tempi di partenza sulle due macchine	*/
/* EFFETTO  : Mette gli n job in S sulle due macchina (Flow Shop)		*/
/*						Al termine restituisce gli FStart e SStart modificati	*/
/*						dall'inserimento dei job															*/
/* OUTPUT		: La somma dei tempi di completamento										*/
/********************************************************************/
int SeqEval(c_type *S, int n, int *FStart, int *SStart)
{
	int i, Sum = 0;

	for (i=0; i<n; i++) {
	
		*FStart += JOB[S[i]].p1;
		*SStart = Imax(*FStart, *SStart) + JOB[S[i]].p2;
		Sum += *SStart;
	}

	return(Sum);
}

/********************************************************************/
/* FUNZIONE : AddaJob																								*/
/* INPUT		: Un nodo e un indice a job															*/
/* EFFETTO  : Mette il job i nella sequenza del nodo N (FS)     		*/
/* OUTPUT		: 0																											*/	
/********************************************************************/
int AddaJob(Node *N, int i) 
{
	N->Order1[N->Pos1] = i;
	N->Order2[N->Pos2] = i;
	(N->Pos1)++;
	(N->Pos2)++;
	N->NextWork[i] = 0;
	N->C1 = N->C1 + JOB[i].p1;
	N->C2 = JOB[i].p2 + Imax(N->C2, N->C1);
	N->CFirst[i] = N->C1;
	N->CSecond[i] = N->C2;
	N->CSUM = N->CSUM + N->C2;

	return(0);
}