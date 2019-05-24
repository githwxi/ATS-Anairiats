//
// K&R, 2nd edition, page 22
//

#include <stdio.h>

/* count digits, while space, others */

int main () {
  int c, i, nwhite, nother ;
  int ndigit[10] ;
  nwhite = nother = 0 ;

  for (i = 0; i < 10; ++i) ndigit[i] = 0 ;

  while ((c = getchar()) != EOF)
    if (c >= '0' && c <= '9')
      ++ndigit[c-'0'] ;
    else if (c == ' ' || c == '\n' || c == '\t')
      ++nwhite ;
    else
      ++nother ;

  printf("digit =");

  for (i = 0; i < 10; ++i)
    printf(" %d", ndigit[i]) ;

  printf(", white space = %d, other = %d\n",
    nwhite, nother
  ) ;
} /* end of [main] */

/* ****** ****** */

/* end of [digit_space_other_cnt.c] */
