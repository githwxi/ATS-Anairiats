(*
**
** An interface for ATS to interact with gsl/gsl_rng
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

%{#
#include "contrib/gsl/CATS/gsl_rng.cats"
%} // end of [%{#]

(* ****** ****** *)

/*
typedef struct {
  const char *name;
  unsigned long int max;
  unsigned long int min;
  size_t size;
  void (*set) (void *state, unsigned long int seed);
  unsigned long int (*get) (void *state);
  double (*get_double) (void *state);
} gsl_rng_type;
*/
typedef
gsl_rng_type =
$extype_struct "gsl_rng_type" of {
  name= ptr // char*
, max= ulint
, min= ulint
, size= size_t
, set= (ptr(*state*), ulint(*seed*)) -> void
, get= (ptr(*state*)) -> ulint
, get_double= (ptr) -> double
} // end of [gsl_rng_type]

abstype
gsl_prng_type = ptr // gsl_rng_type*

fun gsl_rng_type_get_name
  {l1:addr} (
  x: gsl_prng_type
) : [l:addr] (
  (strptr l) -<lin,prf> void | strptr l
) = "atsctrb_gsl_rng_type_get_name"

(* ****** ****** *)

val gsl_rng_default
  : gsl_prng_type = "mac#atsctrb_gsl_rng_default"
// end of [gsl_rng_default]

val gsl_rng_random128_bsd
  : gsl_prng_type = "mac#atsctrb_gsl_rng_random128_bsd"
// end of [gsl_rng_random128_bsd]

val gsl_rng_random128_libc5
  : gsl_prng_type = "mac#atsctrb_gsl_rng_random128_libc5"
// end of [gsl_rng_random128_libc5]

val gsl_rng_random128_glibc2
  : gsl_prng_type = "mac#atsctrb_gsl_rng_random128_glibc2"
// end of [gsl_rng_random128_glibc2]

(* ****** ****** *)

fun gsl_rng_env_setup
  (): gsl_prng_type = "mac#atsctrb_gsl_rng_env_setup"
// end of [gsl_rng_env_setup]

(* ****** ****** *)

viewtypedef gsl_rng =
$extype_struct "gsl_rng" of {
  type= gsl_prng_type, state= ptr
} // end of [gsl_rng]

absviewtype gsl_prng (l:addr) = ptr // gsl_rng*
viewtypedef gsl_prng0 = [l:addr] gsl_prng (l)
viewtypedef gsl_prng1 = [l:addr | l > null] gsl_prng (l)

castfn
gsl_prng_takeout
  {l:agz} (
  p: gsl_prng l
) : (
  gsl_rng @ l
, minus (gsl_prng l, gsl_rng @ l)
| ptr l
) // end of [gsl_prng_takeout]

(* ****** ****** *)

fun
gsl_rng_alloc_exn (
  type: gsl_prng_type
) : gsl_prng1 = "ext#atsctrb_gsl_rng_alloc_exn"
// end of [gsl_rng_alloc_exn]

fun gsl_rng_free (r: gsl_prng0): void = "mac#gsl_rng_free"

(* ****** ****** *)

(*
void gsl_rng_set (const gsl_rng * r, unsigned long int seed);
*)
fun gsl_rng_set
  {l:agz} (
  r: !gsl_prng l, seed: ulint
) : void = "mac#atsctrb_gsl_rng_set"

(* ****** ****** *)

(*
unsigned long int gsl_rng_get (const gsl_rng * r);
*)
fun gsl_rng_get
  {l:agz} (
  r: !gsl_prng l
) : ulint = "mac#atsctrb_gsl_rng_get"
// end of [gsl_rng_get]

(*
double gsl_rng_uniform (const gsl_rng * r);
*)
fun gsl_rng_uniform
  {l:agz} (
  r: !gsl_prng l
) : double = "mac#atsctrb_gsl_rng_uniform"
// end of [gsl_rng_uniform]

(*
double gsl_rng_uniform_pos (const gsl_rng * r);
*)
fun gsl_rng_uniform_pos
  {l:agz} (
  r: !gsl_prng l
) : double = "mac#atsctrb_gsl_rng_uniform_pos"
// end of [gsl_rng_uniform_pos]

(*
unsigned long int
gsl_rng_uniform_int (const gsl_rng * r, unsigned long int n);
*)
fun gsl_rng_uniform_int
  {l:agz} (
  r: !gsl_prng l, n: ulint
) : ulint = "mac#atsctrb_gsl_rng_uniform_int"
// end of [gsl_rng_uniform_int]

(* ****** ****** *)

(* end of [gsl_rng.sats] *)
