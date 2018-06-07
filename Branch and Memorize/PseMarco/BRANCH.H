/********************************************************************/
/* MODULO					: Branch.C																				*/
/* FUNZIONALITA'	: Implementa la fase di branch dell'algoritmo di  */
/*								BeB utilizzando funzioni di dominanza e richiaman-*/
/*								do poi i lower-upper bounds  quando necessario.		*/
/********************************************************************/ 

#ifndef BRANCH

#define BRANCH

#include "beb.h"

/***********/
/* GLOBALS */
/***********/
 
/*************/
/* FUNCTIONS */
/*************/

int FSDB(Node *N, int *index);

int PreDominance(void);

int Branch(Node *);

int BranchStat(void);

int FreeDatabase(void);

#endif