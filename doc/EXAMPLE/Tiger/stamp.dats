(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "stamp.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

assume stamp_t = int64

(* ****** ****** *)

val stamp_count = ref_make_elt<int64> (int64_of_int 0)

(* ****** ****** *)

implement stamp_make () = let
  val n = !stamp_count
  val () = !stamp_count := n + int64_of_int 1
in
  n
end // end of [stamp_make]

(* ****** ****** *)

implement fprint_stamp (out, s) = fprint_int64 (out, s)

implement print_stamp (s) = fprint_stamp (stdout_ref, s)
implement prerr_stamp (s) = fprint_stamp (stderr_ref, s)

(* ****** ****** *)

implement eq_stamp_stamp (s1, s2) = eq_int64_int64 (s1, s2)
implement neq_stamp_stamp (s1, s2) = neq_int64_int64 (s1, s2)

(* ****** ****** *)

(* end of [stamp.dats] *)
