/*
**
** An interface for ATS to interact with gsl/gsl_randist
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

#ifndef ATSCTRB_GSL_RANDIST_CATS
#define ATSCTRB_GSL_RANDIST_CATS

/* ****** ****** */

#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>

/* ****** ****** */

#define atsctrb_gsl_ran_exponential gsl_ran_exponential
#define atsctrb_gsl_ran_exponential_pdf gsl_ran_exponential_pdf

/* ****** ****** */

#define atsctrb_gsl_ran_flat gsl_ran_flat
#define atsctrb_gsl_ran_flat_pdf gsl_ran_flat_pdf

/* ****** ****** */

#define atsctrb_gsl_ran_gaussian gsl_ran_gaussian
#define atsctrb_gsl_ran_gaussian_pdf gsl_ran_gaussian_pdf
#define atsctrb_gsl_ran_gaussian_ratio_method gsl_ran_gaussian_ratio_method
#define atsctrb_gsl_ran_gaussian_ziggurat gsl_ran_gaussian_ziggurat

/* ****** ****** */

#endif // end of [ATSCTRB_GSL_RANDIST_CATS]

/* end of [gsl_randist.cats] */
