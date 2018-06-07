/********************************************************************/
/* MODULO					: Bounds.C																				*/
/* FUNZIONALITA'	: Implementa tutti i lower bounds e gli upper     */
/*								bounds utilizzati per il flow o il job shop.      */
/********************************************************************/ 
#ifndef BOUNDS

#define BOUNDS

#include "beb.h"

/***********/
/* GLOBALS */
/***********/

extern int LastUBValue;
extern c_type LastUB1[MAXJOBS];
extern c_type LastUB2[MAXJOBS];

/*************/
/* FUNCTIONS */
/*************/

int BoundsInit(void);
int LB(Node *);
int UB(Node *);
int BoundsStat(void);

#endif