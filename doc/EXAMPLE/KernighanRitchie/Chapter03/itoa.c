//
// K&R, 2nd edition, page 64
//

/* itoa: convert n t characters in s */
void itoa (int n, char s[]) {
  int i, sgn ;
  if ((sgn = n) < 0) n = -n ;
  i = 0 ;
  do { /* generate digits in reverse order */
    s[i++] = n % 10 + '0' ;
  } while ((n /= 10) > 0) ;
  if (sgn < 0) s[i++] = '-' ;
  s[i] = '\0' ;
  reverse (s) ;
  return ;
} /* end of [iota] */

/* ****** ****** */

/* end of [itoa.c] */

