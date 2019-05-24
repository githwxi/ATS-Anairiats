/*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*/

/* ****** ****** */

//
// some library functions for the Tiger programming language
//

/* ****** ****** */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ****** ****** */

void*
tiger_array_alloc (size_t asz) {
  void **p0_arr ;
  p0_arr = (void**)malloc(asz * sizeof(void*)) ;
  if (!p0_arr) {
    fprintf (stderr, "FATAL ERROR: [tiger_array_alloc] failed\n") ;
  }
  return p0_arr ;
} /* tiger_array_alloc */

void*
tiger_array_make_elt (size_t asz, void *elt) {
  int i ;
  void **p0_arr, **p_arr ;
/*
  fprintf
    (stderr, "tiger_array_make_elt: asz = %li\n", asz) ;
  fprintf
    (stderr, "tiger_array_make_elt: elt = %li\n", elt) ;
*/
  p0_arr = p_arr = (void**)malloc(asz * sizeof(void*)) ;
  if (!p0_arr) {
    fprintf (stderr, "FATAL ERROR: [tiger_array_make_elt] failed\n") ;
  }
  for (i = 0; i < asz; i += 1) *p_arr++ = elt ;
  return p0_arr ;
} /* tiger_array_make_elt */

/* ****** ****** */

void
tiger_flush () {
  fflush (stdout) ; return ;
} /* tiger_flush */

void
tiger_print (char *str) {
  fprintf (stdout, "%s", str) ; return ;
} /* tiger_print */

void
tiger_print_int (int i) {
  fprintf (stdout, "%i", i) ; return ;
} /* tiger_print_int */

/* ****** ****** */

int
tiger_ord (char* s) { return s[0] ; }

char*
tiger_chr (int c) {
  char *p_res ;
  p_res = malloc (2) ;
  if (!p_res) {
    fprintf (stderr, "FATAL ERROR: [tiger_chr]: failed\n") ;
  }
  p_res[0] = c ; p_res[1] = '\000' ; return p_res ;
} /* end of [tiger_chr] */

char*
tiger_getchar () { return tiger_chr (getchar ()) ; }

/* ****** ****** */

int
tiger_eq_string_string
  (char* s1, char* s2) {
  return (strcmp (s1, s2) == 0 ? 1 : 0) ;
} /* end of [tiger_eq_string_string] */

char*
tiger_concat (char* s1, char* s2) {
  int n, n1, n2 ; char* p_res ;
  n1 = strlen (s1) ; n2 = strlen (s2) ; n = n1 + n2 ;
  p_res = malloc (n + 1) ;
  if (!p_res) {
    fprintf (stderr, "FATAL ERROR: [tiger_concat]: failed\n") ;
  }
  memcpy (p_res, s1, n1);
  memcpy (p_res + n1, s2, n2);
  p_res[n] = '\000' ;
  return p_res ;
} /* end of [tiger_concat] */

/* ****** ****** */

int main () {
  tiger_main () ; return 0 ;
}

/* ****** ****** */

/* end of [tiger_prelude.c] */
