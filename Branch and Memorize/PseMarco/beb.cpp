/********************************************************************/
/* MODULO					: BeB.C																						*/
/* FUNZIONALITA'	: Implementa ad alto livello l'algoritmo di BeB   */
/*								e gestisce le metodologie di allocazione e utiliz-*/
/*								zo della memoria.																	*/
/********************************************************************/ 

#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>
#include <conio.h>

#include "branch.h"
#include "beb.h"
#include "bounds.h"
#include "utils.h"
#include "database.h"
extern int DomStrategy;

//!Memo code is added here

#pragma region solmemo
#include <cassert>
#include <process.h>
#include <algorithm>
using namespace std;
//#define TRUE true
//#define FALSE false
#define BOOL bool
#define  NB MAXJOBS
int tmp[NB + 1];
//! best[l] should always be updated as the currently best solution of the current node on level l. 
//  For a non-leaf node, this value is updated by children nodes on level l+1, for leaf nodes it is updated by the node itself.
//!! it should only be updated when ub is improved. Dom conditions must be disabled in order to not loss the opt node
int best[NB + 1];//!血与泪 = { INT_MAX };
//! used like best but for storing the best lb of a node, computed as the least of all lb of its childen. 
//Note that the lb of the node itself should not be counted if it has children, since it is the lowest.
//!! All ending nodes must be considered, any miss would lead to a too high lb so that the opt sol may be missed. Dom conditions must be disabled.
int bestlb[NB + 1];
bool memlb[NB + 1];
bool Stra6LBMemoOn = true; //! whether enable lb memo for strategy 6
//! when a node is solved, update it's father's best value. Save the current node if needed
//! PREREQUEST: best[niv] must store the optimal value of the current node
//! First piege found: the UB rsc when first computed before branching, may already have a good value. On a node, its children may either be cut or not cut but solved directly with a value worst than rsc. 
//		In this case the optimal value of that node cannot be obtained since its optimal node may be in the cut subtree. Basicly the whole node is implicitely cut.
//! When this is called, must be sure that what we got is the OPTIMAL sol
void UpdateBestOnSolve(Node * node, bool saveToDb, bool isLb){
	int niv = node->Pos1;
	if (memlb[niv])isLb = true;
	if (BranchStrategy!=SOLLBMEMO || niv <= 1 || (isLb && !Stra6LBMemoOn)) return;
	int sol = best[niv];//node could be a sentinel
	if (isLb){
		assert( (sol == INT_MAX || memlb[niv])&& bestlb[niv] < INT_MAX);
		sol = bestlb[niv];
	}
	else assert(sol != INT_MAX);
	//int Csumi[NB];

	//for (int i = 0, Ci = *Csumi = 0; i <= niv - 1; ++i){
	//	Ci +=  pi(node->scheduled.element[i]);
	//	if (i > 0)Csumi[i] = Ci + Csumi[i - 1]; else Csumi[0] = Ci;
	//}
	//PAUSE_ON(Csumi[node->niv-1] != node->brn);
	//update father's best
	int i = niv - 1;
	int Ci = node->C2;
	//if (i > 0) Ci -= Csumi[i - 1];				//! Cost value of the last prefixed job
	//int t0 = 0;	//! t0 of the remaining part: we are in backward branching here
	if (saveToDb){
		i = niv;
		//check sol (not considering lb memo)
		//copy(node->toschedule.element, node->toschedule.element + node->toschedule.taille, tmp);
		//copy(node->candidate.element, node->candidate.element + node->candidate.taille, tmp + node->toschedule.taille);
		DBAddPb(node->Order1, node->Pos1, node->C1, node->C2, sol, isLb);	//! Note we do not store sequence. Only store jobset
	}
	if (sol + Ci < bestlb[niv - 1])
		bestlb[niv - 1] = sol + Ci; //! update father's bestlb: opt is also lb
	if (!isLb && sol + Ci < best[niv - 1])	best[niv - 1] = sol + Ci; //! update father's best
	if (memlb[niv])memlb[niv - 1] = true;
	best[niv] = INT_MAX;					//! Empty levels should have their best value reset
	bestlb[niv] = INT_MAX;
	memlb[niv] = false;
}
#pragma endregion solmemo


/***********************************/
/* GLOBAL VARIABLES AND STRUCTURES */
/***********************************/

/* Nodes allocation - memory management */

/* MM - Dimensions Best:80,8000,10000*/
#define H_CACHEDIM 100
#define N_CACHEDIM 20000
#define N_ZONEDIM 20

/* MM - Memory Zones */
struct TNZone {
	Node Nodes[N_ZONEDIM];
	int Pos;
	struct TNZone *Next;
};
typedef struct TNZone NZone;

NZone *CurrNZone, *FirstNZone;

/* MM - Hash Table */

struct THash {
	int LB;
	Node *NodeList;
	struct THash *Next;
}; 
typedef struct THash Hash;

/* MM - Globals */

int Mem, MemHash, LostNodes;
int Nodes,Nbnodes=0;
Hash *Root;

/* MM - Freed nodes/hash pointers cache */

Hash *HashCache[H_CACHEDIM];
int HashCachePointer;
Node *NodeCache[N_CACHEDIM];
int NodeCachePointer;

/* Jobs */
Job JOB[MAXJOBS];
int Jobs;

/* Utilities */
int AtRoot;
int BestSolValue = INT_MAX;
c_type BestSol1[MAXJOBS];
c_type BestSol2[MAXJOBS];
int JH_C2;
c_type JHSequence[MAXJOBS];

/* Configuration */
char FILENAME[30];
int Debug;
int NodesLimit;
int RootOnly;
int BranchStrategy;
//! 
extern int CleanStrategy;


int NewEuristic;
int OldEuristic;
int Dom1, Dom2, Dom3, Dom4, Dom5, Dom6, Dom7, Dom8;
int FlowShop;
int A_B;
int IS1;
int IS2;
int HV;
int VDV_ORIGINAL;
int VDV_CORRECTED;
int DNT1;
int DNT2;
int LINDO;
int LA;
int AllSeqExam;
int Perturb;
int OnlyBest;
int UseEuristic;
int GetBestVDV;
int PertOrderbyDelta;
int M_O;
int MO_Pareto;
int MO_C2Limit;
int DBMaximumDimension;
int CutActive=0,CutDone=0;
  
/***********************/
/* FUNCTION PROTOTYPES */
/***********************/

int LoadDAT(char *DATName);
int LoadINI(void);
int InitBEB(void);

Hash *NewHash(void);
int FreeHash(Hash *H);

Node *GetNode(void);
int TerminationTest(void);

int MOBeB (char *DATName);

/********************************************************************/
/* FUNZIONE : LoadDat																								*/
/* INPUT		: Nome del file del problema da risolvere								*/
/* EFFETTO  : Caricamento in JOB del problema o uscita dal program-	*/
/*					ma se il file non e' presente														*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int LoadDAT(char *DATName)
{
  FILE *Fp;
  char s[25];
	
	strcpy(FILENAME, DATName);

  Fp = fopen(DATName, "r");

  if (Fp == NULL) { printf("\n\nFile not found\n\n"); exit(0); }

  Jobs = 0;

  while (fgets(s,20,Fp) != NULL) {

    sscanf(s,"%d %d %d",&JOB[Jobs].ID, &JOB[Jobs].p1, &JOB[Jobs].p2);
	JOB[Jobs].Dir = 0;

		if (JOB[Jobs].p1 == 0 && JOB[Jobs].p2 == 0) continue;

    if (JOB[Jobs].Dir != 1 && JOB[Jobs].Dir != 2) JOB[Jobs].Dir = 1;
	
		Jobs++;
  }

  printf("\n'%s' : %d Jobs loaded.\n", DATName, Jobs);

  return(0);
}

/********************************************************************/
/* FUNZIONE : LoadIni																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Inizializzazione delle variabili di configurazione at-*/
/*					traverso il caricamento del file JS.INI									*/
/*					Se JS.INI non e' presente si assumono valori di default */
/* OUTPUT		: 0																											*/
/********************************************************************/
int LoadINI(void)
{
	
	struct rec_Variables {
		char *Name;
		int *Pointer;
		int Initvalue;
	};

	typedef struct rec_Variables TVariable;

	TVariable Variables[]= {
		{"/*"								, NULL,							0},
		{"NodesLimit"						, &NodesLimit,					50000},
		{"RootOnly"							, &RootOnly,					OFF},
		{"BranchStrategy"					, &BranchStrategy,				LBORDER},
		{"NewEuristic"						, &NewEuristic,					ON},
		{"OldEuristic"						, &OldEuristic,					OFF},
		{"Dom1"								, &Dom1,			     		ON},
		{"Dom2"								, &Dom2,			     		ON},
		{"Dom3"								, &Dom3,			     		OFF},
		{"Dom4"								, &Dom4,			     		ON},
		{"Dom5"								, &Dom5,			     		OFF},
		{"Dom6"								, &Dom6,			     		ON},
		{"Dom7"								, &Dom7,			     		OFF},
		{"Dom8"								, &Dom8,			     		OFF},
		{"A_B"								, &A_B,							OFF},
		{"IS1"								, &IS1,							OFF},
		{"IS2"								, &IS2,							OFF},
		{"HV"								, &HV,							OFF},
		{"VDV_ORIGINAL"						, &VDV_ORIGINAL,				OFF},
		{"VDV_CORRECTED"					, &VDV_CORRECTED,				OFF},
		{"DNT1"								, &DNT1,						ON},
		{"DNT2"								, &DNT2,						ON},
		{"LINDO"							, &LINDO,						OFF},
		{"LA"								, &LA,							ON},
		{"AllSeqExam"						, &AllSeqExam,     				OFF},
		{"Perturb"							, &Perturb,						ON},
		{"PertOrderbyDelta"					, &PertOrderbyDelta,			ON},
		{"OnlyBest"							, &OnlyBest,					ON},
		{"GetBestVDV"						, &GetBestVDV,					ON},
		{"UseEuristic"						, &UseEuristic,					OFF},
		{"M_O"								, &M_O,							OFF},
		{"MO_C2Limit"						, &MO_C2Limit,					0},
		{"MO_Pareto"						, &MO_Pareto,					0},
		{"DBDimension"						, &DBMaximumDimension,			500000}
	};

	int NumVariables=sizeof(Variables)/sizeof(TVariable);

	FILE *Fileconfig;
	char Readline[80],Name[40];
	int Check;
	int  Value,Count,LineRead=0;

	for  (Count=1;Count<NumVariables;Count++)
		*Variables[Count].Pointer=Variables[Count].Initvalue;

	if ((Fileconfig = fopen("JS.INI","rt"))== NULL) {
		printf("\nFile JS.INI not found. Using default configuration.\n\n");
	}
	else {
		while (!feof(Fileconfig)) {

			fgets(Readline,80,Fileconfig);
			if (feof(Fileconfig)) break;

			LineRead++;
			if (sscanf(Readline,"%s = %d",Name,&Value) == EOF) continue;

			Check = 1;
			for(Count=0; Count < NumVariables; Count++) {
				Check=strncmp(Name, Variables[Count].Name, 
					strlen(Variables[Count].Name));
				if (Check == 0) break;
			}

			if(Check)
				printf("\nWarning : Unknown message in Config File at line %d\n", LineRead);
			else
				if (Variables[Count].Pointer != NULL) *Variables[Count].Pointer = Value;
		}
  
		fclose(Fileconfig);
	}
  
	return(0);
}

/********************************************************************/
/* FUNZIONE : InitBeB																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Init del branch and bound. Al termine il nodo Root  	*/
/*						e' stato esaminato e introdotto nella lista dei nodi  */
/*						aperti. Si occupa di lanciare anche gli Init per il   */
/*						precalcolamento necessario da alcuni lower bound e da */
/*						alcuni criteri di dominanza.													*/
/* OUTPUT		: 1	(Soluzione trovata al root-node, elaborazione di al-*/
/*							tri nodi non richiesta, rilevato possibile errore   */
/*						0	(altrimenti)																				*/
/********************************************************************/
int InitBEB(void)
{
  int i,j;
	Node *RootNode;

	Nodes = 1; 
  AtRoot = 1;
	Mem = 0;
	MemHash = 0;
	LostNodes = 0;
	HashCachePointer = 0;
	NodeCachePointer = 0;
	CurrNZone = NULL;
	Root = NULL;

	Root = NewHash();
	RootNode = NewNode();
	Root->NodeList = RootNode;
	Root->Next = NULL;

  for (i=0;i<Jobs;i++)
    if (JOB[i].Dir == 1) RootNode->NextWork[i] = 1; else RootNode->NextWork[i] = 2;

  RootNode->CSUM = 0;
  RootNode->Pos1 = 0;
  RootNode->Pos2 = 0;
  RootNode->C1   = 0;
  RootNode->C2   = 0;

  RootNode->Next = NULL;

  /* Detect Flow Shops */

  FlowShop = 1;
  for (i=0;i<Jobs;i++) {
		JOB[i].Dir = 0;
	  if (JOB[0].Dir != JOB[i].Dir) {
			FlowShop = 0;
			break;
		}
  }
  if (FlowShop) {
    printf("FlowShop problem detected");
    if (JOB[0].Dir == 2) {
      for (i=0;i<Jobs;i++) {
				RootNode->NextWork[i] = 1;
				j = JOB[i].p1;
				JOB[i].p1 = JOB[i].p2;
				JOB[i].p2 = j;
      }
      printf("(Switched machine 1 and 2)");
    }
  }
  printf("\n\n");

	if (!FlowShop) {
		printf("This version of JS solve flow shop problems only.\n");
		BestSolValue = INT_MAX;
		return(1);
	}

  /* Pre-Dominance */

  PreDominance();

  /* Bounds for root-node */

  BoundsInit();

	BestSolValue = UB(RootNode);
	RootNode->LowerBound = LB(RootNode);
  Root->LB = RootNode->LowerBound;
	
  printf("Root UpperBound = %d\n", BestSolValue);
  for (i=0;i<Jobs;i++) BestSol1[i] = LastUB1[i];
  for (i=0;i<Jobs;i++) BestSol2[i] = LastUB2[i];
  
	if (M_O == ON) {
		printf("Johnson C2 Max = %d\n", JH_C2);
		printf("MultiObj Limit = %d\n", MO_C2Limit);
	}
	printf("\n");

  if (RootNode->LowerBound == BestSolValue) {
    printf("\nSolution found at root node.\n");
    return(1);
  }
  
  if (RootNode->LowerBound > BestSolValue) {
    printf("\nSomething's wrong in upper-lower bounds!\n");
		BestSolValue = INT_MAX;
		return(1);
  }

  if (RootOnly == ON) {
	  printf("\nBeB stopped by 'RootOnly' configuration.\n");
	  BestSolValue = INT_MAX;
	  return(1);
  }

  AtRoot = 0;

  return(0);
}

/********************************************************************/
/* FUNZIONE : NewHash																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Allocazione o richiesta alla cache di un nuovo nodo di*/
/*					hash.																										*/
/* OUTPUT		: Il nodo allocato																			*/
/********************************************************************/
Hash *NewHash(void)
{
  Hash *H;

	if (HashCachePointer != 0) {
		HashCachePointer--;
		return(HashCache[HashCachePointer]);
	}


	H = (Hash *)malloc(sizeof(Hash));

	if (H == NULL) {
		printf("\nMemory Error\n"); 
		FreeAll(); 
		exit(1);	
	} 

	MemHash++;
	return(H);
}

/********************************************************************/
/* FUNZIONE : FreeHash																							*/
/* INPUT		: Puntatore al nodo hash da liberare										*/
/* EFFETTO  : Libera le zone di memoria del nodo in input o lo in-	*/
/*					serisce nella cache se possibile												*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int FreeHash(Hash *H)
{
  if (HashCachePointer < H_CACHEDIM) {
		HashCache[HashCachePointer] = H;
		HashCachePointer++;
		return(0);
	}
	
	free(H);
	MemHash--;
	return(0);

}

/********************************************************************/
/* FUNZIONE : GetNode																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Estrae il primo nodo dalla lista dei nodi (gestita da */
/*						AddNode() come LIFO o come lista ordinata)						*/
/* OUTPUT		: Il nodo estratto																			*/
/********************************************************************/
Node *GetNode(void)
{
  Node *N;
  Hash *H;
  int MonInd, MonLast, index2;

  if (Root == NULL || Root->NodeList == NULL) { 
		printf("Error : GetNode()"); 
		FreeAll(); 
		exit(0); 
	}
	
  N = Root->NodeList;
  Root->NodeList = Root->NodeList->Next;

	if (Root->NodeList == NULL) {
		H = Root;
		Root = Root->Next;
		FreeHash(H);
	}
	  
 // We now check the dominance condition with the database
	if ( (GetActualDBDimension() != 0) && BranchStrategy!=SOLLBMEMO &&(FSDB(N, &index2)))//! node memo and solmemo not compatible
	{
		// We delete the corresponding item in the database
		DBSearch(N->Order1, N->CSUM, N->C2, N->Pos1, &MonInd, &MonLast);
		if (MonInd != -1)
		{
			if (ItemsD[index2].Done == 100) CutDone++;
			else
				CutActive++;
			DBDelete(&MonInd, &MonLast);
		}
		else
			CutActive++;
		FreeNode(N);
		if (Root == NULL || Root->NodeList == NULL) N = NULL;
		else N = GetNode();
	}
	else if (GetActualDBDimension() != 0)
	{//! Try cut by generating k-perm
		bool cut = false;
		//! Generate k perm
		if ((DomStrategy & 4) && N->Pos1 >= 3)
		{ // The current node is not dominated so we try to generate alternative sequences to try 
			// to find one dominating the current node : in this case it is added to the database
			cut = DBGenerate(N->Order1, N->CSUM, N->C2, N->Pos1);
		}
		//! Sol Memo 
		if (BranchStrategy == SOLLBMEMO){
			Node* courant = N;
			int niv = N->Pos1;
			// We search in solved nodes
			if (N->LowerBound < 0){//! This is a sentinel node. it is just solved and should be saved to database (solution memo)
				if (best[niv] != INT_MAX)//INTMAX when the node has no solution: all children are cut. we wanted to also memo this in order to indicate the node as not promising, however it is wrong since what is unpromising is not the subpb but the partial seq+subpb.
					UpdateBestOnSolve(courant, TRUE, FALSE);
				else {
					if (bestlb[niv] == INT_MAX) //! if lb is not updated by children, remember the computed one.
						bestlb[niv] = -courant->LowerBound - courant->CSUM;
					UpdateBestOnSolve(courant, TRUE, TRUE);	//! if some updates are missed, nodes may be cut innocently since the lb is higher than what it should be
				}
				cut = 1; //since this is a sentinel node
				//delete courant;
			}
			else if (niv > 1){
				//!Find sol from db
				int sol = 999999;
				//int t0 = 0;
				int isLB = 0, ind=-1;
				//copy(courant->toschedule.element, courant->toschedule.element + courant->toschedule.taille, tmp);
				//copy(courant->candidate.element, courant->candidate.element + courant->candidate.taille, tmp + courant->toschedule.taille);

				if ((sol = DBSearchPb(courant->Order1, courant->Pos1, courant->C1, courant->C2, &isLB, &ind)) != -1){
					//! opt sol is also lb
					if ((courant->LowerBound > sol + courant->CSUM)){
						if (!isLB){
							printf("not ok\n");
							getch();
						}
						else if (courant->LowerBound > sol + courant->CSUM){
							//printf("weired\n"); update db
							sol=ItemsD[ind].CSum = courant->LowerBound - courant->CSUM;
							//getch();
						}
					}
					else 
						courant->LowerBound = sol + courant->CSUM;
					//assert(bestlb[v->niv] > sol); 
					bestlb[niv] = courant->LowerBound-courant->CSUM;
					//UpdateBestOnSolve(v, FALSE, TRUE);

					if (!isLB){//!opt
						if (sol + courant->CSUM <= BestSolValue) {
							best[niv] = sol;
							BestSolValue = sol + courant->CSUM;
							//!also need to update its father. Only do this when sol<rsc since otherwise this is a cut node, which is not optimal. !!! Caution on this
							UpdateBestOnSolve(courant, FALSE, FALSE);
						}
						else{//not improving best, but it's still valid as a lb.
							//bestlb[v->niv] = sol;
							UpdateBestOnSolve(courant, FALSE, TRUE);
						}
						cut = 1;
						CutDone++;
						//LOG("\nSolMemo cut size %d\n", nb_task - v->niv);
					}
					else if (Stra6LBMemoOn){
						UpdateBestOnSolve(courant, FALSE, TRUE);
						if (sol + courant->CSUM >= BestSolValue){//Cut by UB
							cut = 1;
							//delete courant;
							CutActive++;
							LOG("\nLb cut. t0=%d/%d, niv=%d, last=%d. %d+%d>=%d. \n", courant->C1, courant->C2, courant->Pos1, courant->Order1[courant->Pos1-1],sol , courant->CSUM , BestSolValue);
						}
					}
				}
				else if (courant->LowerBound >= BestSolValue){//cut by ub, which may have been updated after the creation of node v
					bestlb[niv] = courant->LowerBound - courant->CSUM;
					UpdateBestOnSolve(courant, TRUE, TRUE);
					cut = 1;
					//delete courant;
				}
			}

		}
		
		if (cut){
			DBSearch(N->Order1, N->CSUM, N->C2, N->Pos1, &MonInd, &MonLast);
			if (MonInd != -1)
			{
				DBDelete(&MonInd, &MonLast);
			}
			FreeNode(N);
			if (Root == NULL || Root->NodeList == NULL) N = NULL;
			else N = GetNode();
		}
		else{
			DBSearch(N->Order1, N->CSUM, N->C2, N->Pos1, &MonInd, &MonLast);
			ItemsD[MonInd].Done = 100;
		}
	}

	return(N);
}

/********************************************************************/
/* FUNZIONE : TerminationTest																				*/
/* INPUT		: void																									*/
/* EFFETTO  : Controlla se il Branch and Bound e' terminato corret-	*/
/*					tamente o ha raggiunto un limite massimo di nodi.				*/
/* OUTPUT		: 0 (BeB terminato)																			*/
/*						1 (altrimenti)																				*/
/********************************************************************/
int TerminationTest(void)
{
	/* Nessun nodo da esaminare : BeB terminato correttamente */

	if (Root == NULL) return(0);
	if (BranchStrategy == LBORDER && Root->LB >= BestSolValue)
		return(0);
	
  /* Numero limite di nodi superato. BeB interrotto */
  //if (DBMaximumDimension<=500000 && Nodes > NodesLimit) { //! disable node limit for our new versions. For all versions (21/07/2017)
	 // printf("Nodes limit exceeded. Report at the moment :\n\n");	  
	 // return(0);
  //}

	return(1);
}

/********************************************************************/
/* FUNZIONE : FreeAll																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Libera tutta la memoria allocata per Hash Table, Nodi	*/
/*					e tabelle di cache.																			*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int FreeAll(void)
{
	NZone *Z;
	Hash *H;
  int i, M;
	
	M = (100 *(Nodes - LostNodes)) / Nodes;
	printf("\nFreeing Memory... (MM Usage : %d %%)\n", M);

	/* Free Nodes */

	while (FirstNZone != NULL) {
		Z = FirstNZone;
		FirstNZone = FirstNZone->Next;
		free(Z);
		Mem--;
	}
	
	/* Free Hash */
	
	while (Root != NULL) {
  
		H = Root;
		Root = Root->Next;
		free(H); MemHash--;
	}

	for (i=0;i<HashCachePointer;i++) { free(HashCache[i]); MemHash--; }
	
	/* Debug */

	if (Mem != 0) printf("WARNING : Abnormal memory use!\n");
	if (MemHash != 0) printf("WARNING : Abnormal memory use!\n");

	FreeDatabase();

  return(0);
}

int MOBeB(char *DATName) 
{
  Node *N;
	int C1, C2, CS, i;

	int Limit = INT_MAX;
	int NodesSum = 0;
	int OldSol = INT_MAX;
	int Pareto = 0;
	int Executions = 0;
	
	do {

		MO_C2Limit = Limit;
		LoadDAT(DATName);

		if (InitBEB() == 0)

			do {
				
				N = GetNode();

				Branch(N);

				FreeNode(N);

			} while (TerminationTest());

		FreeAll();

		if (BestSolValue != INT_MAX) { 
			BranchStat(); 
			BoundsStat(); 

  		C1 = 0; C2 = 0;
			CS = SeqEval(BestSol1, Jobs, &C1, &C2);
	  
			printf("\n");
			for (i=0;i<Jobs;i++) printf("%d ",JOB[BestSol1[i]].ID);
			printf(" (%d)\n", C1);
			for (i=0;i<Jobs;i++) printf("%d ",JOB[BestSol2[i]].ID);
			printf(" (%d)\n\n", C2);
			printf("FO           = %d\n", BestSolValue);
			printf("Opened Nodes = %d\n", Nodes);
			printf("\n");
			if (BestSolValue != CS) printf("Dbg_Warning<main>");
			Limit = C2 - 1;
			
			NodesSum += Nodes;
			if (OldSol != CS) Pareto++;
			OldSol = CS;
			Executions++;
		}
		else
			printf("\nNo solutions found\n\n");
	  
	} while (BestSolValue != INT_MAX);

	printf("\n\n");
	printf("EXECUTIONS = %d\n", Executions);
	printf("PARETO     = %d\n", Pareto);
	printf("TOT. NODES = %d\n", NodesSum);
	
	return(0);
}
  

/******************/
/* MAIN FUNCTIONS */
/******************/

/********************************************************************/
/* FUNZIONE : BestLB																								*/
/* INPUT		: void																									*/
/* OUTPUT		: Il miglior lower bound tra i nodi attualmente aperti. */
/********************************************************************/
int BestLB(void)
{
  return(Root->LB);
}

/********************************************************************/
/* FUNZIONE : BeB																										*/
/* INPUT		: Nome del file del problema da risolvere								*/
/* EFFETTO  : Implementa ad alto livello il Branch and Bound				*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int BeB(char *DATName, int BranchS, int DatabDim)
{
  Node *N;
	int C1, C2, CS, DC, i;
	FILE *FFF;
	time_t now; time(&now);
	LoadINI();
	//! Overwriting ini config
	BranchStrategy = BranchS;
	DBMaximumDimension = DatabDim;
	printf("\n====== In solver: stra=%d, dbdim=%d, cleanstra=%d, domstra=%d, (%s)\n", BranchStrategy, DBMaximumDimension, CleanStrategy, DomStrategy, ctime(&now));
	if (M_O == ON && MO_Pareto == ON) { 
		MOBeB(DATName);
    return(0);
	}

  LoadDAT(DATName);

  if (BranchStrategy == SOLLBMEMO){
	  DomStrategy = 1;
	  printf("DomStrategy set to 1 for Strategy 6. (no effect)\n");
	  for (i = 0; i < NB + 1; ++i){
		  best[i] = INT_MAX;
		  bestlb[i] = INT_MAX;
		  memlb[i] = false;
	  }
	  //printf("70/6.txt should = 88787\n");
  }

  if (InitBEB() == 0) {


    do {

      N = GetNode();

	  if (N!=NULL)
	  {
		  LOG("Node to branch: %d/%d, niv=%d, lb=%d, last=%d\n", N->C1, N->C2, N->Pos1, N->LowerBound, N->Order1[N->Pos1-1]);
       Branch(N);
  	   //!FreeNode(N);//! moved this to FSBranch so that no need to copy it to the sentinel node
	  }

    } while (TerminationTest());

  }
  FreeAll();

  if (BestSolValue != INT_MAX) { 
		DC = BranchStat(); 
		BoundsStat(); 

  	C1 = 0; C2 = 0;
		CS = SeqEval(BestSol1, Jobs, &C1, &C2);
	  
		printf("\n");
    for (i=0;i<Jobs;i++) printf("%d ",JOB[BestSol1[i]].ID);
    printf(" (%d)\n", C1);
    for (i=0;i<Jobs;i++) printf("%d ",JOB[BestSol2[i]].ID);
    printf(" (%d)\n\n", C2);
    printf("FO            = %d\n", BestSolValue);
    printf("Created Nodes = %d (After  the Dominance Criteria)\n", Nodes);
    printf("Visited Nodes = %d (Before the Dominance Criteria)\n\n", Nodes+DC);
    printf("\n");
		if (BestSolValue != CS) printf("Dbg_Warning<main>");
  }
  else
		printf("\nNo solutions found\n\n");

 

 /* FFF = fopen("js.txt", "w");

  fprintf(FFF, "%d ", Nodes);

  fclose(FFF);*/



  return(0);
}

/********************************************************************/
/* FUNZIONE : NewNode																								*/
/* INPUT		: void																									*/
/* EFFETTO  : Restituisce il puntatore ad un nuovo nodo, prendedolo	*/
/*					dalla cache dei nodi liberati o dalla corrente zona di 	*/
/*					memoria. Se tali operazioni non sono possibili alloca   */
/*					una nuova zona di memoria.															*/
/* OUTPUT		: Il nuovo nodo																					*/
/********************************************************************/
Node *NewNode(void)
{
  Node *N;

	if (NodeCachePointer != 0) {
		NodeCachePointer--;
		return(NodeCache[NodeCachePointer]);
	}

	if (CurrNZone == NULL) {
		CurrNZone = (NZone *)malloc(sizeof(NZone));
		if (CurrNZone == NULL) {
			printf("\nMemory Error\n"); 
			FreeAll(); 
			exit(1);	
		} 
		Mem++;
		CurrNZone->Pos = 0;
		CurrNZone->Next = NULL;
		FirstNZone = CurrNZone;
	}

	if (CurrNZone->Pos == N_ZONEDIM) {
		CurrNZone->Next = (NZone *)malloc(sizeof(NZone));
		CurrNZone = CurrNZone->Next;
		if (CurrNZone == NULL) {
			printf("\nMemory Error\n");
			FreeAll(); 
			_getch();			
			exit(1);	
		} 
		Mem++;
		CurrNZone->Pos = 0;
		CurrNZone->Next = NULL;
	} 

	N = &(CurrNZone->Nodes[CurrNZone->Pos]);
	(CurrNZone->Pos++);

	return(N);
}

/********************************************************************/
/* FUNZIONE : FreeNode																							*/
/* INPUT		: Puntatore al nodo da liberare													*/
/* EFFETTO  : Inserisce, se possibile, il nodo in input in cache.		*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int FreeNode(Node *N)
{
	if (NodeCachePointer < N_CACHEDIM) {
		NodeCache[NodeCachePointer] = N;
		NodeCachePointer++;
		return(0);
	}
  else LostNodes++;

	return(0);
}

/********************************************************************/
/* FUNZIONE : AddNode																								*/
/* INPUT		: Puntatore al nodo da inserire.												*/
/* EFFETTO  : Inserisce un nodo nella lista dei nodi secondo la			*/
/*					strategia LIFO o in ordine di lower-bound. Gestisce			*/
/*					la tabella di hash nel secondo caso.										*/
/* OUTPUT		: 0																											*/
/********************************************************************/
int AddNode(Node *N)
{
	Hash *PLast, *P;
	Hash *H;

	if (BranchStrategy == FIRST || BranchStrategy==SOLLBMEMO) {
		if (Root == NULL) {
			Root = NewHash();
			Root->NodeList = NULL;
			Root->LB = 0;
			Root->Next = NULL;
		}

		N->Next = Root->NodeList;
		Root->NodeList = N;
		return(0);
	}

	if (BranchStrategy == LBORDER) {
	
		if (Root == NULL || Root->LB > N->LowerBound) {
      
			H = NewHash();
			H->NodeList = N;
			H->LB = N->LowerBound;
			H->Next = Root;
			N->Next = NULL;
			Root = H;
			return(0);
		}

		if (Root->LB == N->LowerBound) {
			N->Next = Root->NodeList;
			Root->NodeList = N;
			return(0);
		}


		PLast = Root;
		P = Root->Next;
	
		while (P != NULL) {
			if (P->LB >= N->LowerBound) break;
			PLast = P;
			P = P->Next;
		}

		if (P != NULL && P->LB > N->LowerBound) {
			H = NewHash();
			H->LB = N->LowerBound;
			H->NodeList = N;
			H->Next = P;
			PLast->Next = H;
			N->Next = NULL;
			
			return(0);
		} 

		if (P != NULL && P->LB == N->LowerBound) {
			N->Next = P->NodeList;
			P->NodeList = N;
		  return(0);
		}

		H = NewHash();
		PLast->Next = H;
		H->LB = N->LowerBound;
		H->NodeList = N;
		N->Next = NULL;
		H->Next = NULL;

		return(0);
  }
  
  if (BranchStrategy == AMP) {
	
	if (Root == NULL || Root->LB > N->Pos1) {
			H = NewHash();
			H->NodeList = N;
			H->LB = N->Pos1;
			H->Next = Root;
			N->Next = NULL;
			Root = H;
			return(0);
	}

	if (Root->LB == N->Pos1) {
		N->Next = Root->NodeList;
		Root->NodeList = N;
		return(0);
	}


	PLast = Root;
	P = Root->Next;
	
    while (P != NULL) {
		if (P->LB >= N->Pos1) break;
			PLast = P;
			P = P->Next;
	}

	if (P != NULL && P->LB > N->Pos1) {
		H = NewHash();
		H->LB = N->Pos1;
		H->NodeList = N;
		H->Next = P;
		PLast->Next = H;
		N->Next = NULL;
			
		return(0);
	} 

	if (P != NULL && P->LB == N->Pos1) {
		N->Next = P->NodeList;
		P->NodeList = N;
		return(0);
	}

	H = NewHash();
	PLast->Next = H;
	H->LB = N->Pos1;
	H->NodeList = N;
	N->Next = NULL;
	H->Next = NULL;

	return(0);
  }

  printf("Error : unknown BranchStrategy in AddNode()");
  FreeAll();
  exit(1);
  return(0);
}