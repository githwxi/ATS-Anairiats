/*
**
** An interface for ATS to interact with gsl/gsl_rng
**
** Contributed by William Blair (wdblair AT cs DOT bu DOT edu)
** Contributed/Reviewed  by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Starting time: October, 2011
**
*/

/* ****** ****** */
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
/* ****** ****** */

#ifndef ATSCTRB_GSL_RNG_CATS
#define ATSCTRB_GSL_RNG_CATS

/* ****** ****** */

#include <gsl/gsl_rng.h>

/* ****** ****** */

#define atsctrb_gsl_rng_default ((void*)gsl_rng_default)

#define atsctrb_gsl_rng_random128_bsd ((void*)gsl_rng_random128_bsd)
#define atsctrb_gsl_rng_random128_libc5 ((void*)gsl_rng_random128_libc5)
#define atsctrb_gsl_rng_random128_glibc2 ((void*)gsl_rng_random128_glibc2)

/* ****** ****** */

#define atsctrb_gsl_rng_env_setup gsl_rng_env_setup

/* ****** ****** */

ATSinline()
ats_ptr_type
atsctrb_gsl_rng_alloc_exn
  (ats_ptr_type prngt) {
  void *r = gsl_rng_alloc ((gsl_rng_type*)prngt) ;
  if (!r) {
    fprintf (stderr, "[gsl_rng_alloc] failed.\n"); exit (1);
  } // end of [if]
  return r ;
} // end of [atsctrb_gsl_rng_alloc_exn]

/* ****** ****** */

#define atsctrb_gsl_rng_set gsl_rng_set

/* ****** ****** */

#define atsctrb_gsl_rng_get gsl_rng_get
#define atsctrb_gsl_rng_uniform gsl_rng_uniform
#define atsctrb_gsl_rng_uniform_pos gsl_rng_uniform_pos
#define atsctrb_gsl_rng_uniform_int gsl_rng_uniform_int

/* ****** ****** */

#endif // end of [ATSCTRB_GSL_RNG_CATS]

/* end of [gsl_rng.cats] */
