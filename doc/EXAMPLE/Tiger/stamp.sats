(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

abst@ype stamp_t = $extype "ats_int64_type"

(* ****** ****** *)

fun stamp_make (): stamp_t // generate a fresh stamp

(* ****** ****** *)

fun fprint_stamp (out: FILEref, s: stamp_t): void

fun print_stamp (s: stamp_t): void
fun prerr_stamp (s: stamp_t): void

(* ****** ****** *)

fun eq_stamp_stamp (s1: stamp_t, s2: stamp_t): bool
fun neq_stamp_stamp (s1: stamp_t, s2: stamp_t): bool

overload = with eq_stamp_stamp
overload <> with neq_stamp_stamp

(* ****** ****** *)

(* end of [stamp.sats] *)
