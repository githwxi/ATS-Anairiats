(*
** some code for testing various functions in gsl_randist
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/time.sats"

(* ****** ****** *)

staload "contrib/gsl/SATS/gsl_rng.sats"
staload "contrib/gsl/SATS/gsl_randist.sats"

(* ****** ****** *)

implement
main () = {
//
  val _(*prng*) = gsl_rng_env_setup ()
//
  val my_rng = gsl_rng_alloc_exn (gsl_rng_default)
  val t1 = time_get ()
  val () = gsl_rng_set (my_rng, $UN.cast2ulint (t1))
//
  #define N 10
  var i: int // uninitialized
//
  val () = print "(****** Uniform: ******)\n"
  val () = for (i := 0; i < N; i := i+1) {
    val () = printf("%lf\n", @(gsl_ran_flat(my_rng,0.0,100.0)))
  } // end of [val]
//
  val () = print "(****** Normal: ******)\n"
  val () = for (i := 0; i < N; i := i+1) {
    val mean = 12.0
    val standard = gsl_ran_gaussian(my_rng, 2.0)
    val () = printf ("%lf\n", @(mean+standard))
  } // end of [val]
//
  val () = print "(****** Exponential: ******)\n"
  val () = for(i := 0; i < N; i := i+1) {
    val () = printf ("%lf\n", @(gsl_ran_exponential(my_rng,25.0)))
  } // end of [val]
//
  val () = gsl_rng_free (my_rng)
//
} // end of [main]

(* ****** ****** *)

(* end of [test_randist.dats] *)
