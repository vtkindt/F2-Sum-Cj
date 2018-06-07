#include "database.h"
//!
int lastDim = 0;
int IsOn; // ON;OFF

int Dimension;			// DB Dimension
int N_Jobs;				// Number of jobs

ItemD *ItemsD;

int *Indexes;			 // The indexes vector
	
int Starting[HASHITEMS*DBMAXJOBS];  // The starting points for each
									// dimension of the subsequence
									// 0 = empty list.

int MaxDimension;

//////////////////////////////////////////////////////////////////////
// Construction/Destruction
//////////////////////////////////////////////////////////////////////

int AllocDB(int MaxDim, int Jobs)
{
	int i, RealDimension = MaxDim + 1;  // 1 item is lost for the implementation
										// of the linked list.
    MaxDimension=MaxDim;

	if (MaxDim == 0) {
		IsOn = 0;
		return(0);
	}
	else 
		IsOn = 1;

	N_Jobs = Jobs;
	Dimension = 0;

	ItemsD = (ItemD *)malloc(RealDimension * sizeof(ItemD));

	Indexes = (int *)malloc(RealDimension * sizeof(int));
	
	if (ItemsD == NULL || Indexes == NULL) {
		printf("\nDB_MEMORY_ERROR: Using NO Database\n");
		
		IsOn = 0;
	}

	// Indexes init

	for (i=0;i<MaxDim;i++)
	{
		Indexes[i] = i+1;
		ItemsD[i].Done=0;
	}

	Indexes[RealDimension-1] = -1;
	
	for (i=0;i<Jobs*HASHITEMS;i++) /**/
		Starting[i] = -1;

	Starting[0] = 1;

	return(0);
}

int FreeDB()
{
	if (IsOn) {

		free (Indexes);
		free (ItemsD);
	}

	return(0);

}

//////////////////////////////////////////////////////////////////////
// Implementation
//////////////////////////////////////////////////////////////////////

int DomTest(int NJ, int C2a, int CSa, int C2b, int CSb)
{	
	int D, E, n = Jobs - NJ;
	

	if (M_O == OFF) {
		if (CSa >= CSb) {
			D = n*(C2b - C2a);
			E = CSa - CSb;
			if (D < E) return(2);
		}

		if (CSb >= CSa) {
			D = n*(C2a - C2b);
			E = CSb - CSa;
			if (D < E) return(1);	
		}

		if (C2a == C2b && CSa == CSb) return(0);
		return(-1);
	}

	if (C2a < C2b && CSa <= CSb) return(1);
	if (C2a <= C2b && CSa < CSb) return(1);
	if (C2a > C2b && CSa >= CSb) return(2);
	if (C2a >= C2b && CSa > CSb) return(2);
	if (C2a == C2b && CSa == CSb) return(0);

	return(-1);
}

int SeqTest(int NJ, short *A, short *B)
{
	int J[DBMAXJOBS];
	int i, Ret;

	for(i=0;i<N_Jobs;i++) J[i] = 0;

	for(i=0;i<NJ;i++) J[A[i]] = 1;

	Ret = 1;

	for(i=0;i<NJ;i++) 
		if (J[B[i]] == 0) { 
			Ret = 0;
			break;
		}
		
	return(Ret);
}

int DBDelete(int *Index, int *LastIndex)
{
	int k, nj = ItemsD[*Index].Jobs;

	/**/nj = (nj-1) * HASHITEMS + (ItemsD[*Index].Hash % HASHITEMS)+1 ;

	if (*LastIndex == -1) {
	
		k = Starting[0];
		Starting[0] = Starting[nj];
		Starting[nj] = Indexes[Starting[nj]];
		Indexes[Starting[0]] = k;

		*Index = Starting[nj];
		*LastIndex = -1;
	}
	else {

		k = Starting[0];
		Starting[0] = Indexes[*LastIndex];
		Indexes[*LastIndex] = Indexes[*Index];
		Indexes[*Index] = k;

		*Index = Indexes[*LastIndex];
	}

	Dimension--;
	if (Dimension>MaxDimension) printf("\r Database exceeded: %ld",Dimension);
	return(0);
}

int RemovalCriteria()
{
	int i,j;

	for(i=1; i<N_Jobs*HASHITEMS; i++) /**/
		if (Starting[i] != -1) break;

	// Deleting the first item of the list with less jobs.

	i = Starting[i];
	j = -1;
	DBDelete(&i, &j);

	return(Starting[0]); // Returns the freed item.
}


void DBSearch(short *Seq, int CS, int C2, int Len, int *Rindex, int *lastindex)
{
	int i, index, l_index, Sum;
	
	int NH_NJobs;
	int N_NJobs = Len;
	int N_CMax  = C2; 
	int N_CSum  = CS;

	if (IsOn == 0) return;	

	// Search for a dominated sequence to be deleted
	// or for a dominating sequence.
	
	Sum = 0;	
	if (HASH) {
		for (i=0; i<N_NJobs; i++) Sum += Seq[i];
	}

	NH_NJobs = (N_NJobs-1)*HASHITEMS + (Sum % HASHITEMS)+1;

	index = Starting[NH_NJobs]; /**/
	l_index = -1;

	while(index != -1) {
	
			if (Sum == ItemsD[index].Hash) {

				if ((N_CMax==ItemsD[index].CMax)&&(N_CSum==ItemsD[index].CSum)
					&&(SeqTest(N_NJobs, Seq, ItemsD[index].Seq)))
				{
				 *Rindex=index;
				 *lastindex=l_index;
				 return;
				}
			}
		
			l_index = index;
			index = Indexes[index];
		}
 *Rindex=index;
 *lastindex=l_index;
}

int DBAdd(short *Seq, int CS, int C2, int Len, int DoNotAdd, int *index2)
{
	int i, index, l_index, Sum;
	

	int NH_NJobs;
	int N_NJobs = Len;
	int N_CMax  = C2; 
	int N_CSum  = CS;

	if (IsOn == 0) return(1);	

	// Search for a dominated sequence to be deleted
	// or for a dominating sequence.
	
	Sum = 0;	
	if (HASH) {
		for (i=0; i<N_NJobs; i++) Sum += Seq[i];
	}

	NH_NJobs = (N_NJobs-1)*HASHITEMS + (Sum % HASHITEMS)+1;

	if (DoNotAdd != -1) {

		index = Starting[NH_NJobs]; /**/
		l_index = -1;

		while(index != -1) {
	
			if (Sum == ItemsD[index].Hash) {

				i = DomTest(N_NJobs, N_CMax, N_CSum, ItemsD[index].CMax, ItemsD[index].CSum);

				if ((i == 2)&&((*index2)==0)&&(ItemsD[index].Done!=100)) {
					if (SeqTest(N_NJobs, Seq, ItemsD[index].Seq))	/*Cut by active*/
					{
						*index2=index;
						return(-1); // N is Dominated by a seq. in the DB
					}
				}
				if ((i == 2)&&((*index2)==100)&&(ItemsD[index].Done==100)) {
					if (SeqTest(N_NJobs, Seq, ItemsD[index].Seq))	/*Cut by done*/
					{
						*index2=index;
						return(-1); // N is Dominated by a seq. in the DB
					}
				}

				if (i == 1) {
					if (SeqTest(N_NJobs, Seq, ItemsD[index].Seq)) { /**/

						DBDelete(&index, &l_index); // Delete index from the db
						continue;					// and move the indexes.
					}
				}
			}
		
			l_index = index;
			index = Indexes[index];
		}

	}

	// Free list insertion (if possible)

	index = Starting[0];

	if (index == -1) index = RemovalCriteria(); // db full
	
	if (DoNotAdd == 1) return(1);

	// REAL INSERTION
	
	// New empty list starting
	Starting[0] = Indexes[Starting[0]];
		
	// New item.jobs startings

	i = Starting[NH_NJobs];		
	Starting[NH_NJobs] = index;
	Indexes[index] = i;
	
	// Copying data into Items[index]
		
	ItemsD[index].Jobs = N_NJobs;

	for (i=0; i<N_NJobs; i++) ItemsD[index].Seq[i] = Seq[i]; /**/

	ItemsD[index].Hash = Sum;
	ItemsD[index].CSum = N_CSum;
	ItemsD[index].CMax = N_CMax;
	ItemsD[index].Done=0;

	Dimension++;
	if (lastDim < Dimension && Dimension % 100000 == 0){
		lastDim = Dimension;
		printf("Current DBDimension : %d\n", Dimension);
	}
	return(1);
}

int GetActualDBDimension()
{
	return(Dimension);
}

int PrintDB(void)
{
	int i,j;
	
	printf("Empty Slots = ");
	
	i = Starting[0];
	j = 0;

	while(i != -1) {
		j++;
		i = Indexes[i];
	}
	
	printf("%d\n", j);

	for(i=1; i<N_Jobs; i++)
		
		if (Starting[i] != -1) {
		
			printf("%d Jobs:\n", i);

			j = Starting[i];

			while(j != -1) {

				printf("  C2 = %3d, CS = %3d \n", ItemsD[j].CMax, ItemsD[j].CSum);
			
			
				j = Indexes[j];
			}
		}

	printf("=================================================\n");
	return(0);
}

