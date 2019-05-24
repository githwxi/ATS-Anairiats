(*
**
** An interface for ATS to interact with gsl/gsl_randist
**
** Contributed by William Blair (wdblair AT cs DOT bu DOT edu)
** Contributed/Reviewed  by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Starting time: October, 2011
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

staload "contrib/gsl/SATS/gsl_rng.sats"

(* ****** ****** *)

%{#
#include "contrib/gsl/CATS/gsl_randist.cats"
%} // end of [%{#]

(* ****** ****** *)

(*
double gsl_ran_exponential
  (const gsl_rng * r, const double mu);
*)
fun gsl_ran_exponential
  {l:agz} (
  r: !gsl_prng l, mu: double
) : double = "mac#gsl_ran_exponential"
// end of [gsl_ran_exponential]

(*
double gsl_ran_exponential_pdf
  (const double x, const double mu);
*)
fun gsl_ran_exponential_pdf
  (x: double, mu: double): double = "mac#gsl_ran_exponential_pdf"
// end of [gsl_ran_exponential_pdf]

(* ****** ****** *)

(*
double gsl_ran_flat (const gsl_rng * r, const double a, const double b);
*)
fun gsl_ran_flat
  {l:agz} (
  r: !gsl_prng l, a: double, b: double
) : double = "mac#atsctrb_gsl_ran_flat"

(*
double gsl_ran_flat_pdf
  (double x, const double a, const double b);
*)
fun gsl_ran_flat_pdf (
  x: double, a: double, b: double
) : double = "mac#atsctrb_gsl_ran_flat_pdf"

(* ****** ****** *)

(*
double gsl_ran_gaussian
  (const gsl_rng * r, const double sigma);
*)
fun gsl_ran_gaussian
  {l:agz} (
  r: !gsl_prng l, sigma: double
) : double = "mac#atsctrb_gsl_ran_gaussian"

(*
double gsl_ran_gaussian_pdf
  (const double x, const double sigma);
*)
fun gsl_ran_gaussian_pdf (
  x: double, sigma: double
) : double = "mac#atsctrb_gsl_ran_gaussian_pdf"

(*
double gsl_ran_gaussian_ratio_method
  (const gsl_rng * r, const double sigma);
*)
fun gsl_ran_gaussian_ratio_method
  {l:agz} (
  r: !gsl_prng l, sigma: double
) : double = "mac#atsctrb_gsl_ran_gaussian_ratio_method"

(*
double gsl_ran_gaussian_ziggurat
  (const gsl_rng * r, const double sigma);
*)
fun gsl_ran_gaussian_ziggurat
  {l:agz} (
  r: !gsl_prng l, sigma: double
) : double = "mac#atsctrb_gsl_ran_gaussian_ziggurat"

(* ****** ****** *)

(* end of [gsl_randist.sats] *)
