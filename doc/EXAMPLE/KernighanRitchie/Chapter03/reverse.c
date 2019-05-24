//
// K&R, 2nd edition, page 62
//

#include <string.h>

/* reverse string in place */

void reverse (char s[]) {
  int c, i, j;
  for (i = 0, j = strlen(s) - 1; i < j; i++, j--) {
    c = s[i]; s[i] = s[j]; s[j] = c;
  }
  return ;
} /* end of [reverse] */

/* ****** ****** */

/* end of [reverse.c] */
