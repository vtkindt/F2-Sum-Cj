/********************************************************************/
/* MODULO					: Utils.C																					*/
/* FUNZIONALITA'	: Implementa alcune funzioni di utilita' richiama-*/
/*								te dagli altri moduli del programma.							*/
/********************************************************************/ 

#ifndef UTILS

#define UTILS

#define TRUE 1
#define FALSE 0

#include "beb.h"

double Fmax(double A, double B);
double Fmin(double A, double B);
int Istrcpy(c_type *Dest, c_type *Source);
int Iprint(int A[]);
int Istrcmp(int A[], int B[]);
int Imax(int A, int B);
int Imin(int A, int B);
int NodeCopy(Node *Dest, Node *Source);
int SeqEval(c_type *S, int n, int *FStart, int *SStart);
int AddaJob(Node *N, int i);

#endif