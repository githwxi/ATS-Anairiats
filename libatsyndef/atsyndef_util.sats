(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
staload Syn = "ats_syntax.sats"
typedef tmpqi0de = $Syn.tmpqi0de

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

fun prerr_loc_syndef (loc: loc_t): void

(* ****** ****** *)

fun d1exp_binop
  (loc: loc_t, fid: sym_t, d1e1: d1exp, d1e2: d1exp): d1exp

(* ****** ****** *)

fun d1ec_sym_exp (loc: loc_t, x_id: sym_t, d1e: d1exp): d1ec

(* ****** ****** *)

(* end of [atsyndef_util.sats] *)
