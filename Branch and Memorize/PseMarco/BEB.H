//! in case we need a larger type
typedef long c_type;

/********************************************************************/
/* MODULO					: BeB.C																						*/
/* FUNZIONALITA'	: Implementa ad alto livello l'algoritmo di BeB   */
/*								e gestisce le metodologie di allocazione e utiliz-*/
/*								zo della memoria.																	*/
/********************************************************************/ 
#ifndef BEB
#define BEB

#define LOG(...) //printf(__VA_ARGS__);

/* Numero massimo di job allocabili */
#define MAXJOBS 51
/* Codice di errore */
#define ERROR -1

// DATABASE DIMENSIONS

#define HASH 1
#define DBMAXJOBS MAXJOBS

/************************************/
/* STRUCTURE PER I JOB E PER I NODI */
/************************************/

struct J {
  int ID;			/* ID */
  int p1, p2;	/* Tempo di lavorazione sulle due macchine */
  int Dir;		/* Direzione di lavorazione */
};
typedef struct J Job;

struct N {
  c_type Order1[MAXJOBS];		/* Job gia' schedulati sulla 1' macchina */
  c_type Order2[MAXJOBS];		/* Job gia' schedulati sulla 2' macchina */

  c_type NextWork[MAXJOBS];	/* Prossima macchina dove dovra' essere */
													/* lavorato il job i (0 = finito) */

  int C1,C2;							/* Tempi attuali di completamento */
  c_type CFirst[MAXJOBS];		/* Tempi di completamento dei job */
  c_type CSecond[MAXJOBS];

  int CSUM;								/* Somma dei tempi di completamento dei job */
													/* gia' finiti */

  int Pos1, Pos2;					/* Numero di Jobs gia' schedulati */

  int LowerBound;					/* Lower bound del nodo */

  struct N *Next;					/* Prossimo nodo */
};
typedef struct N Node;

/***********/
/* GLOBALS */
/***********/

extern int Mem;

extern Job JOB[MAXJOBS];
extern int Jobs;
extern int Nodes,Nbnodes;
extern int FlowShop;

extern int AtRoot;

extern int BestSolValue;
extern c_type BestSol1[MAXJOBS];
extern c_type BestSol2[MAXJOBS];
extern int JH_C2;
extern c_type JHSequence[MAXJOBS];

extern int BranchStrategy;
#define FIRST 10
#define LBORDER 20
#define AMP 30
#define SOLLBMEMO 6

extern char FILENAME[];
extern int Debug;
extern int RootOnly;
extern int NewEuristic;
extern int OldEuristic;
extern int Dom1, Dom2, Dom3, Dom4, Dom5, Dom6, Dom7, Dom8;
extern int A_B;
extern int IS1;
extern int IS2;
extern int HV;
extern int VDV_ORIGINAL;
extern int VDV_CORRECTED;
extern int DNT1;
extern int DNT2;
extern int LINDO;
extern int LA;
extern int AllSeqExam;
extern int Perturb;
extern int OnlyBest;
extern int UseEuristic;
extern int GetBestVDV;
extern int PertOrderbyDelta;
extern int M_O;
extern int MO_C2Limit;
extern int DBMaximumDimension;
#define ON 1
#define OFF 0
extern int CutActive,CutDone;

/*************/
/* FUNCTIONS */
/*************/

int BestLB(void);

int BeB(char *, int, int);

Node *NewNode(void);
int FreeNode(Node *N);

int AddNode(Node *N);

int FreeAll(void);

#endif