//
// K&R, 2nd edition, page 19
//

#include <stdio.h>

int main () {
  int c ; int nl ;
  while ((c = getchar()) != EOF) if (c == '\n') ++nl ;
  printf ("%.d\n", nl) ;
} /* end of [main] */

/* ****** ****** */

/* end of [linecnt.c] */
