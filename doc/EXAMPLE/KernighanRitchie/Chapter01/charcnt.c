//
// K&R, 2nd edition, page 18
//

#include <stdio.h>

int main () {
  double nc ;
  for (nc = 0; getchar () != EOF; nc++) ;
  printf ("%.0f\n", nc) ;
} /* end of main */

/* ****** ****** */

/* end of [charcnt.c] */
