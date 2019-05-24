(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

//
// it is probably not necessary to make [fgnode_t]
// abstract, but I really don't have the desire to
// re-write the code.
//
abst@ype fgnode_t = $extype "ats_int_type"

castfn int_of_fgnode (_: fgnode_t): Nat
castfn fgnode_of_int (_: Nat): fgnode_t

(* ****** ****** *)

fun fgnode_make_int (n: Nat): fgnode_t

(* ****** ****** *)

fun fprint_fgnode (out: FILEref, fgn: fgnode_t): void
fun print_fgnode (fgn: fgnode_t): void
fun prerr_fgnode (fgn: fgnode_t): void

(* ****** ****** *)

abstype fgnodelst_t // this list is assumed to be ordered

castfn fgnodelst_list_get (fgns: fgnodelst_t): List (fgnode_t)

(* ****** ****** *)

fun fprint_fgnodelst (out: FILEref, fgns: fgnodelst_t): void
fun print_fgnodelst (fgns: fgnodelst_t): void
fun prerr_fgnodelst (fgns: fgnodelst_t): void

(* ****** ****** *)

fun eq_fgnode_fgnode (fgn1: fgnode_t, fgn2: fgnode_t):<> bool
overload = with eq_fgnode_fgnode

fun compare_fgnode_fgnode (fgn1: fgnode_t, fgn2: fgnode_t):<> Sgn
overload compare with compare_fgnode_fgnode

(* ****** ****** *)

fun fgnodelst_nil ():<> fgnodelst_t
fun fgnodelst_sing (fgn: fgnode_t):<> fgnodelst_t

(* ****** ****** *)

fun fgnodelst_ismem (fgns: fgnodelst_t, fgn: fgnode_t): bool

fun fgnodelst_add
  (fgns: fgnodelst_t, fgn: fgnode_t): fgnodelst_t

(* ****** ****** *)

(* end of [fgnode.sats] *)
