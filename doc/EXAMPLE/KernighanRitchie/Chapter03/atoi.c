//
// K&R, 2nd edition, page 61
//

int atoi (char s[]) {
  int i, n, sgn ;
  n = 0 ;
  for (i = 0; isspace(s[i]); ++i) ; /* skip white space */
  sgn = (s[i] == '-') ? -1 : 1 ;
  if (s[i] == '+' || s[i] == '-') ++i ;
  for (i = 0; s[i] >= '0' && s[i] <= '9'; ++i)
    n = 10 * n + (s[i] - '0') ;
  return sgn * n ;
} /* end of [atoi] */

/* ****** ****** */

/* end of [atoi.c] */
