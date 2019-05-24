(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

abstype tempset_t

(* ****** ****** *)

fun tempset_nil ():<> tempset_t

fun templst_of_tempset (ts: tempset_t):<> $TL.templst
fun tempset_make_templst (ts: $TL.templst):<> tempset_t

(* ****** ****** *)

fun fprint_tempset (out: FILEref, ts: tempset_t): void

(* ****** ****** *)

fun tempset_size (ts: tempset_t): Nat

(* ****** ****** *)

fun tempset_is_empty (ts: tempset_t):<> bool
fun tempset_isnot_empty (ts: tempset_t):<> bool

(* ****** ****** *)

fun tempset_ismem (ts: tempset_t, t: $TL.temp_t): bool

(* ****** ****** *)

fun tempset_add
  (ts: tempset_t, t: $TL.temp_t): tempset_t

fun tempset_add_flag
  (ts: tempset_t, t: $TL.temp_t, flag: &int): tempset_t

(* ****** ****** *)

fun tempset_union
  (ts1: tempset_t, ts2: tempset_t): tempset_t

fun tempset_union_flag
  (ts1: tempset_t, ts2: tempset_t, flag: &int): tempset_t

(* ****** ****** *)

fun tempset_diff
  (ts1: tempset_t, ts2: tempset_t): tempset_t

(* ****** ****** *)

fun tempset_remove
  (ts: tempset_t, t: $TL.temp_t): tempset_t
// end of [tempset_remove]

fun tempset_remove_flag
  (ts: tempset_t, t: $TL.temp_t, flag: &int): tempset_t
// end of [tempset_remove_flag]

(* ****** ****** *)

(* end of [temp.sats] *)
