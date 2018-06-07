///////////////////////////////////////////////////////////////////////
//
// Database.h: interface for the Database class. 
// (Working: dont worry of the code in an header file, please!!!!)
//
///////////////////////////////////////////////////////////////////////

#ifndef MYDATABASE

#define MYDATABASE

#include <stdlib.h>
#include <stdio.h>
#include "beb.h"

#define HASHITEMS 500 //! default 500, could be 2000

extern int IsOn; // ON;OFF
struct S_ItemD {

	c_type Jobs;
	c_type Seq[DBMAXJOBS];
	int CSum;
	int CMax;
	int CMax2;
	int Hash;
	char Done;
	char isLB;
	char NbUsed;
};	

typedef struct S_ItemD ItemD;


extern int Dimension;			// DB Dimension
extern int N_Jobs;				// Number of jobs

extern ItemD *ItemsD;

extern int *Indexes;			 // The indexes vector
	
extern int Starting[HASHITEMS*DBMAXJOBS];  // The starting points for each
									// dimension of the subsequence
									// 0 = empty list.

extern int AllocDB(int Dimmax, int Jobs);
extern int FreeDB(void);

extern int DBAdd(c_type *Seq, int CS, int C2, int Len, int DoNotAdd, int *index2);
							// DoNotAdd =	1 -> only the dominance testing is done.		
							//				-1-> Always add.
							//				0 -> Both.
							// Returns  1 if added (non dominated)
							//			-1 if dominated.

//!MEMO Add (t0, jobset, induced Csum)
signed int DBAddPb(c_type *Seq, int Len, int t0, int t1, int sol, int isLB);

//!MEMO Search a solved pb in Memo. If found, return sol, otherwise return -1.
int DBSearchPb(c_type *Seq, int Len, int t0, int t1, int* isLB, int* ind);

unsigned int DBGenerate(c_type *Seq, int CS, int C2, int Len);
extern int GetActualDBDimension();
extern int PrintDB(void);
void DBSearch(c_type *Seq, int CS, int C2, int Len, int *Rindex, int *lastindex);
extern int DomTest(int N, int C2a, int CSa, int C2b, int CSb); // 1  - b is dominated
														// 2  - a is dominated
														// 0  - equal
														// -1 - non dominated


extern int SeqTest(int N, c_type *A, c_type *B); // 1 - Same jobs, 0 - no.
	
extern int DBDelete(int *Index, int *LastIndex);	// Delete Items[index], pointed by Lastindex 
											// -1 = first of the list

extern int RemovalCriteria(void);	
						// Removes an item from the db. Used when the DB is full.






#endif 
