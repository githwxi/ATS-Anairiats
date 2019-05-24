(*
** some code for testing various functions in gsl_rng
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/time.sats"

(* ****** ****** *)

staload "contrib/gsl/SATS/gsl_rng.sats"

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
  val d1 = gsl_rng_uniform (my_rng)
  val () = println! ("d1 = ", d1)
  val d2 = gsl_rng_uniform (my_rng)
  val () = println! ("d2 = ", d2)
//
  val () = gsl_rng_free (my_rng)
//
} // end of [main]

(* ****** ****** *)

(* end of [test_rng.dats] *)
