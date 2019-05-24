(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Start Time: February 2008
//
(* ****** ****** *)

(* for representing and handling constraints *)

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
#include "ats_solver_fm.cats"
%} // end of [%{^]

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_patcst2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_solver_fm.sats"
staload "ats_constraint.sats"

(* ****** ****** *)

overload ~ with $IntInf.neg_intinf
overload + with $IntInf.add_intinf_intinf
overload - with $IntInf.sub_intinf_intinf
overload * with $IntInf.mul_intinf_intinf

overload < with $IntInf.lt_intinf_int
overload <= with $IntInf.lte_intinf_int
overload > with $IntInf.gt_intinf_int
overload >= with $IntInf.gte_intinf_int
overload = with $IntInf.eq_intinf_int
overload <> with $IntInf.neq_intinf_int

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_constraint)"
fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_constraint)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

implement s3aexp_null = S3AEnull ()

implement s3aexp_cst (s2c) = S3AEcst (s2c)
implement s3aexp_var (s2v) = S3AEvar (s2v)

implement
s3aexp_padd (s3ae1, s3ie2) = begin
  case+ s3ae1 of
  | S3AEpadd (s3ae11, s3ie12) => begin
      s3aexp_padd (s3ae11, s3iexp_iadd (s3ie12, s3ie2))
    end // end of [S3AEpadd]
  | _ => S3AEpadd (s3ae1, s3ie2)
end // end of [s3aexp_padd]

implement
s3aexp_psub (s3ae1, s3ie2) = begin
  case+ s3ae1 of
  | S3AEpadd (s3ae11, s3ie12) => begin
      s3aexp_padd (s3ae11, s3iexp_isub (s3ie12, s3ie2))
    end // end of [S3AEpadd]
  | _ => S3AEpadd (s3ae1, s3iexp_ineg s3ie2)
end // end of [s3aexp_psub]

implement s3aexp_psucc (s3ae) = s3aexp_padd (s3ae, s3iexp_1)
implement s3aexp_ppred (s3ae) = s3aexp_psub (s3ae, s3iexp_1)

(* ****** ****** *)

implement s3bexp_true = S3BEbool (true)
implement s3bexp_false = S3BEbool (false)

implement s3bexp_cst (s2c) = S3BEcst (s2c)
implement s3bexp_var (s2v) = S3BEvar (s2v)

implement
s3bexp_bneg (s3be0) = case+ s3be0 of
  | S3BEbool b => S3BEbool (not b)
  | S3BEbadd (s3be1, s3be2) => S3BEbmul (S3BEbneg s3be1, S3BEbneg s3be2)
  | S3BEbmul (s3be1, s3be2) => S3BEbadd (S3BEbneg s3be1, S3BEbneg s3be2)
  | S3BEbneg s3be => s3be
  | S3BEiexp (knd, s3ie) => S3BEiexp (~knd, s3ie)
  | _ => S3BEbneg s3be0
// end of [s3bexp_bneg]

implement
s3bexp_beq (s3be1, s3be2) = begin case+ s3be1 of
  | S3BEbool b1 => if b1 then s3be2 else s3bexp_bneg s3be2
  | _ => begin case+ s3be2 of
    | S3BEbool b2 => if b2 then s3be1 else s3bexp_bneg s3be1
    | _ => let
        val _s3be1 = s3bexp_bneg s3be1 and _s3be2 = s3bexp_bneg s3be2
      in
        S3BEbadd (S3BEbmul (s3be1, s3be2), S3BEbmul (_s3be1, _s3be2))
      end // end of [_]
    end // end of [_]
end // end of [s3bexp_beq]

implement
s3bexp_bneq (s3be1, s3be2) = begin case+ s3be1 of
  | S3BEbool b1 => if b1 then s3bexp_bneg s3be2 else s3be2
  | _ => begin case+ s3be2 of
    | S3BEbool b2 => if b2 then s3bexp_bneg s3be1 else s3be1
    | _ => let
        val _s3be1 = s3bexp_bneg s3be1 and _s3be2 = s3bexp_bneg s3be2
      in
        S3BEbadd (S3BEbmul (s3be1, _s3be2), S3BEbmul (_s3be1, s3be2))
      end // end of [_]
    end // end of [_]
end // end of [s3bexp_bneq]

(* ****** ****** *)

implement
s3bexp_badd (s3be1, s3be2) = begin
  case+ s3be1 of
  | S3BEbool b1 => if b1 then s3bexp_true else s3be2
  | _ => begin case+ s3be2 of
    | S3BEbool b2 => if b2 then s3bexp_true else s3be1
    | _ => S3BEbadd (s3be1, s3be2)
    end // end of [_]
end // end of [s3bexp_badd]

implement
s3bexp_bmul (s3be1, s3be2) = begin
  case+ s3be1 of
  | S3BEbool b1 => if b1 then s3be2 else s3bexp_false
  | _ => begin case+ s3be2 of
    | S3BEbool b2 => if b2 then s3be1 else s3bexp_false
    | _ => S3BEbmul (s3be1, s3be2)
    end // end of [_]
end // end of [s3bexp_bmul]

(* ****** ****** *)

implement
s3bexp_iexp (knd, s3ie) = begin case+ s3ie of
  | S3IEint i => begin case+ knd of
    | 2(*gte*) => if i >= 0 then s3bexp_true else s3bexp_false
    | 1(*eq*) => if i = 0 then s3bexp_true else s3bexp_false
    | ~1(*neq*) => if i <> 0 then s3bexp_true else s3bexp_false
    | ~2(*lt*) => if i < 0 then s3bexp_true else s3bexp_false
    | _ => begin
        prerr_interror ();
        prerr ": s3bexp_iexp: knd = "; prerr knd; prerr_newline ();
        $Err.abort {s3bexp} ()
      end // end of [_]
    end // end of [S3IEint]
  | S3IEintinf i => begin case+ knd of
    | 2(*gte*) => if i >= 0 then s3bexp_true else s3bexp_false
    | 1(*eq*) => if i = 0 then s3bexp_true else s3bexp_false
    | ~1(*neq*) => if i <> 0 then s3bexp_true else s3bexp_false
    | ~2(*lt*) => if i < 0 then s3bexp_true else s3bexp_false
    | _ => begin
        prerr_interror ();
        prerr ": s3bexp_iexp: knd = "; prerr knd; prerr_newline ();
        $Err.abort {s3bexp} ()
      end // end of [_]
    end // end of [S2IEintinf]
  | _ => S3BEiexp (knd, s3ie)
end // end of [s3bexp_iexp]

(* ****** ****** *)

implement s3bexp_igt (s3ie1, s3ie2) =
  s3bexp_iexp (~2(*lt*), s3iexp_isub (s3ie2, s3ie1))
// end of [s3bexp_igt]

implement s3bexp_igte (s3ie1, s3ie2) =
  s3bexp_iexp (2(*gte*), s3iexp_isub (s3ie1, s3ie2))
// end of [s3bexp_igte]

implement s3bexp_ilt (s3ie1, s3ie2) =
  s3bexp_iexp (~2(*lt*), s3iexp_isub (s3ie1, s3ie2))
// end of [s3bexp_ilt]

implement s3bexp_ilte (s3ie1, s3ie2) =
  s3bexp_iexp (2(*gte*), s3iexp_isub (s3ie2, s3ie1))
// end of [s3bexp_ilte]

(* ****** ****** *)

implement s3bexp_ieq (s3ie1, s3ie2) =
  s3bexp_iexp (1(*eq*), s3iexp_isub (s3ie1, s3ie2))
// end of [s3bexp_ieq]

implement s3bexp_ineq (s3ie1, s3ie2) =
  s3bexp_iexp (~1(*neq*), s3iexp_isub (s3ie1, s3ie2))
// end of [s3bexp_ineq]

(* ****** ****** *)

implement s3bexp_pgt (s3ae1, s3ae2) =
  s3bexp_iexp (~2(*lt*), s3iexp_pdiff (s3ae2, s3ae1))
// end of [s3bexp_pgt]

implement s3bexp_pgte (s3ae1, s3ae2) =
  s3bexp_iexp (2(*gte*), s3iexp_pdiff (s3ae1, s3ae2))
// end of [s3bexp_pgte]

implement s3bexp_plt (s3ae1, s3ae2) =
  s3bexp_iexp (~2(*lt*), s3iexp_pdiff (s3ae1, s3ae2))
// end of [s3bexp_plt]

implement s3bexp_plte (s3ae1, s3ae2) =
  s3bexp_iexp (2(*gte*), s3iexp_pdiff (s3ae2, s3ae1))
// end of [s3bexp_plte]

implement s3bexp_peq (s3ae1, s3ae2) =
  s3bexp_iexp (1(*eq*), s3iexp_pdiff (s3ae1, s3ae2))
// end of [s3bexp_peq]

implement s3bexp_pneq (s3ae1, s3ae2) =
  s3bexp_iexp (~1(*neq*), s3iexp_pdiff (s3ae1, s3ae2))
// end of [s3bexp_pneq]

(* ****** ****** *)

fn s3iexp_is_const (s3ie: s3iexp): bool = begin
  case+ s3ie of S3IEint _ => true | S3IEintinf _ => true | _ => false
end // end of [s3iexp_is_const]

(* ****** ****** *)

implement s3iexp_0 = S3IEint 0
implement s3iexp_1 = S3IEint 1
implement s3iexp_neg_1 = S3IEint (~1)

implement s3iexp_cst (s2c) = S3IEcst s2c
implement s3iexp_int (i) = S3IEint i
implement s3iexp_intinf (i) = S3IEintinf i
implement s3iexp_var (s2v) = S3IEvar s2v

implement
s3iexp_ineg (s3ie) = begin
  case+ s3ie of
  | S3IEint i => S3IEint (~i)
  | S3IEintinf i => S3IEintinf (~i)
  | S3IEineg s3ie => s3ie
  | _ => S3IEineg s3ie // end of [_]
end // end of [s3iexp_ineg]

implement
s3iexp_iadd (s3ie1, s3ie2) = begin
  case+ (s3ie1, s3ie2) of
  | (S3IEint i, _) when i = 0 => s3ie2
  | (_, S3IEint i) when i = 0 => s3ie1
  | (S3IEintinf i, _) when i = 0 => s3ie2
  | (_, S3IEintinf i) when i = 0 => s3ie1
(*
  // avoid it: potential arithmetic overflow/underflow
  | (S3IEint i1, S3IEint i2) => S3IEint (i1 + i2)
*)
  | (S3IEintinf i1, S3IEintinf i2) => S3IEintinf (i1 + i2)
  | (_, _) => S3IEiadd (s3ie1, s3ie2)
end // end of [s3iexp_iadd]

implement
s3iexp_isub (s3ie1, s3ie2) = begin
  case+ (s3ie1, s3ie2) of
  | (S3IEint i, _) when i = 0 => s3iexp_ineg s3ie2
  | (_, S3IEint i) when i = 0 => s3ie1
  | (S3IEintinf i, _) when i = 0 => s3iexp_ineg s3ie2
  | (_, S3IEintinf i) when i = 0 => s3ie1
(* 
  // avoid it: potential arithmetic overflow/underflow
  | (S3IEint i1, S3IEint i2) => S3IEint (i1 - i2)
*)
  | (S3IEintinf i1, S3IEintinf i2) => S3IEintinf (i1 - i2)
  | (_, _) => S3IEisub (s3ie1, s3ie2)
end // end of [s3iexp_isub]

implement
s3iexp_imul (s3ie1, s3ie2) = begin
  case+ (s3ie1, s3ie2) of
  | (S3IEint i, _) when i = 0 => s3ie1 // 0
  | (S3IEint i, _) when i = 1 => s3ie2
  | (_, S3IEint i) when i = 0 => s3ie2 // 0
  | (_, S3IEint i) when i = 1 => s3ie1
  | (S3IEintinf i, _) when i = 0 => s3ie1 // 0
  | (S3IEintinf i, _) when i = 1 => s3ie2
  | (_, S3IEintinf i) when i = 0 => s3ie2 // 0
  | (_, S3IEintinf i) when i = 1 => s3ie1
  | (S3IEintinf i1, S3IEintinf i2) => S3IEintinf (i1 * i2)
  | (_, _) => S3IEimul (s3ie1, s3ie2)
end // end of [s3iexp_imul]

implement s3iexp_pdiff (s3ae1, s3ae2) = S3IEpdiff (s3ae1, s3ae2)

implement s3iexp_isucc (s3ie: s3iexp): s3iexp = s3iexp_iadd (s3ie, s3iexp_1)
implement s3iexp_ipred (s3ie: s3iexp): s3iexp = s3iexp_isub (s3ie, s3iexp_1)

(* ****** ****** *)

fun s2cfdeflst_free
  (fds: s2cfdeflst_vt): void = begin
  case+ fds of
  | ~S2CFDEFLSTcons (_, _, _, os3be, fds) => let
      val () = case+ os3be of ~Some_vt _ => () | ~None_vt () => ()
    in
      s2cfdeflst_free (fds)
    end // end of [S2CFDEFLSTcons]
  | ~S2CFDEFLSTmark (fds) => s2cfdeflst_free (fds)
  | ~S2CFDEFLSTnil () => ()
end // end of [s2cfdeflst_free]

(* ****** ****** *)

fn s2cfdeflst_pop
  (fds0: &s2cfdeflst_vt): void = let
  fun aux (fds: s2cfdeflst_vt): s2cfdeflst_vt = case+ fds of
    | ~S2CFDEFLSTcons (s2c, s2es, s2v, os3be, fds) => let
        val () = case+ os3be of ~Some_vt _ => () | ~None_vt () => ()
      in
        aux (fds)
      end (* end of [S2CFDEFLSTcons] *)
    | ~S2CFDEFLSTmark (fds) => fds
    | ~S2CFDEFLSTnil () => S2CFDEFLSTnil ()
  // end of [aux]  
in
  fds0 := aux (fds0)
end (* end of [s2cfdeflst_pop] *)

fn s2cfdeflst_push (fds0: &s2cfdeflst_vt): void = begin
  fds0 := S2CFDEFLSTmark (fds0)
end // end of [s2cfdeflst_push]

fun s2cfdeflst_find (
  fds0: &s2cfdeflst_vt
, s2c0: s2cst_t, s2es0: s2explst
) : Option_vt s2var_t = let
in
//
case+ fds0 of
| S2CFDEFLSTcons
    (s2c, s2es, s2v, _, !fds) => let
    val test = (
      if eq_s2cst_s2cst (s2c0, s2c)
        then s2explst_syneq (s2es0, s2es) else false
    ) : bool // end of [val]
  in
    if test then begin
      fold@ fds0; Some_vt s2v
    end else let
      val ans = s2cfdeflst_find (!fds, s2c0, s2es0)
    in
      fold@ fds0; ans
    end (* end of [if] *)
  end // end of [S2CFDEFLSTcons]
| S2CFDEFLSTmark (!fds) => let
    val ans = s2cfdeflst_find (!fds, s2c0, s2es0)
  in
    fold@ fds0; ans
  end // end of [S2CFDEFLSTmark]
| S2CFDEFLSTnil () => (
    fold@ fds0; None_vt ()
  ) // end of [S2CFDEFLSTnil]
//
end // end of [s2cfdeflst_find]

(* ****** ****** *)
//
// HX: for handling a special static function
//
fn s2cfdeflst_add
  (s2c: s2cst_t, s2es: s2explst, s2v: s2var_t,
   s2cs: &s2cstlst, fds: &s2cfdeflst_vt): void = let
(*
  val () = begin
    print "s2cfdeflst_add: s2c = "; print s2c; print_newline ();
    print "s2cfdeflst_add: s2es = "; print s2es; print_newline ();
    print "s2cfdeflst_add: s2v = "; print s2v; print_newline ();
  end // end of [val]
*)
  val s2e_s2c = s2exp_cst s2c
  val s2e_s2v = s2exp_var s2v
  val s2es_arg = $Lst.list_extend (s2es, s2e_s2v)
  val s2e_rel = s2exp_app_srt (s2rt_bool, s2e_s2c, s2es_arg)
  val os3be = s3bexp_make_s2exp (s2e_rel, s2cs, fds)
in
  fds := S2CFDEFLSTcons (s2c, s2es, s2v, os3be, fds)
end // end of [s2cfdeflst_add]

//
// HX: for handling a generic static function
//
fn s2cfdeflst_add_none
  (s2c: s2cst_t, s2es: s2explst, s2v: s2var_t,
   s2cs: &s2cstlst, fds: &s2cfdeflst_vt): void = let
(*
  val () = begin
    print "s2cfdeflst_add: s2c = "; print s2c; print_newline ();
    print "s2cfdeflst_add: s2es = "; print s2es; print_newline ();
    print "s2cfdeflst_add: s2v = "; print s2v; print_newline ();
  end // end of [val]
*)
in
  fds := S2CFDEFLSTcons (s2c, s2es, s2v, None_vt (), fds)
end // end of [s2cfdeflst_add_none]

(* ****** ****** *)
//
// HX: for handling a special static function
//
fn s2cfdeflst_replace (
    s2t: s2rt
  , s2c: s2cst_t, s2es: s2explst
  , s2cs: &s2cstlst, fds: &s2cfdeflst_vt
  ) : s2var_t =
  case+ s2cfdeflst_find (fds, s2c, s2es) of
  | ~None_vt () => let
      val s2v = s2var_make_srt (s2t)
      val () = s2cfdeflst_add (s2c, s2es, s2v, s2cs, fds)
    in
      s2v
    end // end of [None_vt]
  | ~Some_vt s2v => s2v // end of [Some_vt]
// end of [s2cfdeflst_replace]

//
// HX: for handling a generic static function
//
fn s2cfdeflst_replace_none (
    s2t: s2rt
  , s2c: s2cst_t, s2es: s2explst
  , s2cs: &s2cstlst, fds: &s2cfdeflst_vt
  ) : s2var_t =
  case+ s2cfdeflst_find (fds, s2c, s2es) of
  | ~None_vt () => let
      val s2v = s2var_make_srt (s2t)
      val () = s2cfdeflst_add_none (s2c, s2es, s2v, s2cs, fds)
    in
      s2v
    end // end of [None_vt]
  | ~Some_vt s2v => s2v // end of [Some_vt]
// end of [s2cfdeflst_replace_none]

(* ****** ****** *)

extern
fun s3aexp_make_s2cst_s2explst
  (s2c: s2cst_t, s2es: s2explst, s2cs: &s2cstlst, fds: &s2cfdeflst_vt)
  : s3aexpopt_vt
// end of [fun s3aexp_make_s2cst_s2explst]

implement
s3aexp_make_s2cst_s2explst
  (s2c, s2es, s2cs, fds) = let
  fn errmsg (s2c: s2cst_t): s3aexpopt_vt = begin
    prerr_interror ();
    prerr ": s3aexp_make_s2cst_s2explst: s2c = "; prerr s2c; prerr_newline ();
    $Err.abort {s3aexpopt_vt} ()
  end // end of [errmsg]
in
  case+ 0 of // this looks prettier than [if-then-else] sequence
  | _ when s2cstref_equ_cst (Add_addr_int_addr, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3aexp_padd (s3ae1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Add_addr_int_addr]
  | _ when s2cstref_equ_cst (Sub_addr_int_addr, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3aexp_psub (s3ae1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Sub_addr_int_addr]
  | _ => let
      val s2v = s2cfdeflst_replace_none (s2rt_addr, s2c, s2es, s2cs, fds)
    in
      Some_vt (s3aexp_var s2v)
    end // end of [_]
(*
  // a function cannot be handled
  | _ => let
      val () = begin
        print "s3aexp_make_s2cst_s2explst: s2c = "; print s2c; print_newline ();
        print "s3aexp_make_s2cst_s2explst: s2es = "; print s2es; print_newline ();
      end // end of [val]
    in
      None_vt ()
    end // end of [_]
*)
end // end of [s3aexp_make_s2cst_s2explst]

(* ****** ****** *)

extern
fun s3bexp_make_s2cst_s2explst
  (s2c: s2cst_t, s2es: s2explst, s2cs: &s2cstlst, fds: &s2cfdeflst_vt)
  : s3bexpopt_vt
// end of [fun s3bexp_make_s2cst_s2explst]

//
// this is a large but simple function
//
implement
s3bexp_make_s2cst_s2explst
  (s2c, s2es, s2cs, fds) = let
  fn errmsg (s2c: s2cst_t): s3bexpopt_vt = begin
    prerr_interror ();
    prerr ": s3bexp_make_s2cst_s2explst: s2c = "; prerr s2c; prerr_newline ();
    $Err.abort {s3bexpopt_vt} ()
  end // end of [_]
in
  case+ 0 of
  // boolean negation
  | _ when s2cstref_equ_cst (Neg_bool_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e, list_nil ()) => begin
      case+ s3bexp_make_s2exp (s2e, s2cs, fds) of
      | ~Some_vt s3be => Some_vt (s3bexp_bneg s3be) | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Neg_bool_bool]
  // boolean addition/disjunction
  | _ when s2cstref_equ_cst (Add_bool_bool_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3bexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3be1 => begin
        case+ s3bexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3be2 => Some_vt (s3bexp_badd (s3be1, s3be2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Add_bool_bool_bool]
  // boolean multiplication/conjuction
  | _ when s2cstref_equ_cst (Mul_bool_bool_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3bexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3be1 => begin
        case+ s3bexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3be2 => Some_vt (s3bexp_bmul (s3be1, s3be2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Mul_bool_bool_bool]
  // boolean equality
  | _ when s2cstref_equ_cst (Eq_bool_bool_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3bexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3be1 => begin
        case+ s3bexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3be2 => Some_vt (s3bexp_beq (s3be1, s3be2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Eq_bool_bool_bool]
  // boolean inequality
  | _ when s2cstref_equ_cst (Neq_bool_bool_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3bexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3be1 => begin
        case+ s3bexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3be2 => Some_vt (s3bexp_bneq (s3be1, s3be2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Neq_bool_bool_bool]
  // charater GT relation
  | _ when s2cstref_equ_cst (Gt_char_char_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_igt (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Gt_char_char_bool]
  // character GTE relation
  | _ when s2cstref_equ_cst (Gte_char_char_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_igte (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Gte_char_char_bool]
  // character LT relation
  | _ when s2cstref_equ_cst (Lt_char_char_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ilt (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lt_char_char_bool]
  // charater LTE relation
  | _ when s2cstref_equ_cst (Lte_char_char_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ilte (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lte_char_char_bool]
  // character equality
  | _ when s2cstref_equ_cst (Eq_char_char_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ieq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Eq_char_char_bool]
  // character inequality
  | _ when s2cstref_equ_cst (Neq_char_char_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ineq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Neq_char_char_bool]
  // integer GT relation
  | _ when s2cstref_equ_cst (Gt_int_int_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_igt (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Gt_int_int_bool]
  // integer GTE relation
  | _ when s2cstref_equ_cst (Gte_int_int_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_igte (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Gte_int_int_bool]
  // integer LT relation
  | _ when s2cstref_equ_cst (Lt_int_int_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ilt (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lt_int_int_bool]
  // integer LTE relation
  | _ when s2cstref_equ_cst (Lte_int_int_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ilte (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lte_int_int_bool]
  // integer equality
  | _ when s2cstref_equ_cst (Eq_int_int_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ieq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Eq_int_int_bool]
  // integer inequality
  | _ when s2cstref_equ_cst (Neq_int_int_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ineq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Neq_int_int_bool]
  // address GT relation
  | _ when s2cstref_equ_cst (Gt_addr_addr_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_pgt (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Gt_addr_addr_bool]
  // address GTE relation
  | _ when s2cstref_equ_cst (Gte_addr_addr_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_pgte (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Gte_addr_addr_bool]
  // address LT relation
  | _ when s2cstref_equ_cst (Lt_addr_addr_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_plt (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lt_addr_addr_bool]
  // address LTE relation
  | _ when s2cstref_equ_cst (Lte_addr_addr_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_plte (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lte_addr_addr_bool]
  // address equality
  | _ when s2cstref_equ_cst (Eq_addr_addr_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_peq (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Eq_addr_addr_bool]
  // address inequality
  | _ when s2cstref_equ_cst (Neq_addr_addr_bool, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_pneq (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Neq_addr_addr_bool]
  // subclass relation
  | _ when s2cstref_equ_cst (Lte_cls_cls_bool, s2c) => begin
    case+ s2es of
    | list_cons (
        s2e1, list_cons (s2e2, list_nil ())
      ) => let
        val sgn = s2exp_subclass_test (s2e1, s2e2) in
        case+ 0 of
        | _ when sgn > 0 => Some_vt s3bexp_true
        | _ when sgn < 0 => Some_vt s3bexp_false
        | _ => let
            val s2v = s2cfdeflst_replace_none (s2rt_bool, s2c, s2es, s2cs, fds)
          in
            Some_vt (s3bexp_var s2v)
          end (* end of [if] *)
        // end of [case]       
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Lte_cls_cls_bool]
  | _ => let
      val s2v = s2cfdeflst_replace_none (s2rt_bool, s2c, s2es, s2cs, fds)
    in
      Some_vt (s3bexp_var s2v)
    end // end of [_]
(*
  // a function cannot be handled
  | _ => let
      val () = begin
        print "s3bexp_make_s2cst_s2explst: s2c = "; print s2c; print_newline ();
        print "s3bexp_make_s2cst_s2explst: s2es = "; print s2es; print_newline ();
      end // end of [val]
    in
      None_vt ()
    end // end of [_]
*)
end // end of [s3bexp_make_s2cst_s2explst]

(* ****** ****** *)

extern
fun s3iexp_make_s2cst_s2explst
  (s2c: s2cst_t, s2es: s2explst, s2cs: &s2cstlst, fds: &s2cfdeflst_vt)
  : s3iexpopt_vt
// end of [fun s3iexp_make_s2cst_s2explst]

implement
s3iexp_make_s2cst_s2explst
  (s2c, s2es, s2cs, fds) = let
  fn errmsg (s2c: s2cst_t): s3iexpopt_vt = begin
    prerr_interror ();
    prerr ": s3iexp_make_s2cst_s2explst: s2c = "; prerr s2c; prerr_newline ();
    $Err.abort {s3iexpopt_vt} ()
  end // end of [errmsg]
in
  case+ 0 of
  // integer negation
  | _ when s2cstref_equ_cst (Neg_int_int, s2c) => begin
    case+ s2es of
    | list_cons (s2e, list_nil ()) => begin
      case+ s3iexp_make_s2exp (s2e, s2cs, fds) of
      | ~Some_vt s3ie => Some_vt (s3iexp_ineg s3ie) | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Neg_int_int]
  // integer addition
  | _ when s2cstref_equ_cst (Add_int_int_int, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3iexp_iadd (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Add_int_int_int]
  // integer subtraction
  | _ when s2cstref_equ_cst (Sub_int_int_int, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3iexp_isub (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Sub_int_int_int]
  // integer multiplication
  | _ when s2cstref_equ_cst (Mul_int_int_int, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => let
          val islin = s3iexp_is_const s3ie1
        in
          case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
          | ~Some_vt s3ie2 => let
              val islin = islin orelse (s3iexp_is_const s3ie2)
            in
              if islin then
                Some_vt (s3iexp_imul (s3ie1, s3ie2)) // linear term
              else let // nonlinear term
                val s2v = s2cfdeflst_replace_none (s2rt_int, s2c, s2es, s2cs, fds)
              in
                Some_vt (s3iexp_var s2v)
              end // end of [if]
            end // end of [Some_v]
          | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Mul_int_int_int]
  // addr difference
  | _ when s2cstref_equ_cst (Sub_addr_addr_int, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3iexp_pdiff (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Sub_addr_addr_int]
  // char difference
  | _ when s2cstref_equ_cst (Sub_char_char_int, s2c) => begin
    case+ s2es of
    | list_cons (s2e1, list_cons (s2e2, list_nil ())) => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3iexp_isub (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
      end // end of [list_cons]
    | _ => errmsg s2c
    end // end of [Sub_addr_addr_int]
  // integer division
  | _ when s2cstref_equ_cst (Div_int_int_int, s2c) => let
      val s2c_rel = s2cstref_get_cst (Div_int_int_int_bool)
      val s2v = s2cfdeflst_replace (s2rt_int, s2c_rel, s2es, s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end
  // integer absolute value function
  | _ when s2cstref_equ_cst (Abs_int_int, s2c) => let
      val s2c_rel = s2cstref_get_cst (Abs_int_int_bool)
      val s2v = s2cfdeflst_replace (s2rt_int, s2c_rel, s2es, s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end
  // integer maximum
  | _ when s2cstref_equ_cst (Max_int_int_int, s2c) => let
      val s2c_rel = s2cstref_get_cst (Max_int_int_int_bool)
      val s2v = s2cfdeflst_replace (s2rt_int, s2c_rel, s2es, s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end
  // integer minimum
  | _ when s2cstref_equ_cst (Min_int_int_int, s2c) => let
      val s2c_rel = s2cstref_get_cst (Min_int_int_int_bool)
      val s2v = s2cfdeflst_replace (s2rt_int, s2c_rel, s2es, s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end
  | _ when s2cstref_equ_cst (IntOfBool_bool_int, s2c) => let
      val s2c_rel = s2cstref_get_cst (IntOfBool_bool_int_bool)
      val s2v = s2cfdeflst_replace (s2rt_int, s2c_rel, s2es, s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end // end of [IntOfBool_bool_int]
  | _ => let
      val s2v = s2cfdeflst_replace_none (s2rt_int, s2c, s2es, s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end // end of [_]
(*
  // a function cannot be handled
  | _ => let
      val () = begin
        print "s3iexp_make_s2cst_s2explst: s2c = "; print s2c; print_newline ();
        print "s3iexp_make_s2cst_s2explst: s2es = "; print s2es; print_newline ();
      end // end of [val]
    in
      None_vt ()
    end // end of [_]
*)
end // end of [s3iexp_make_s2cst_s2explst]

(* ****** ****** *)

local

fn aux_equal
  (s2e1: s2exp, s2e2: s2exp, s2cs: &s2cstlst, fds: &s2cfdeflst_vt)
  : s3bexpopt_vt = let
  val s2t1 = s2e1.s2exp_srt
in
  case+ 0 of // this seems prettier than [if-then-else] sequence
  | _ when s2t1 <= s2rt_int => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ieq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
    end // end of [s2t1 = s2rt_int]
  | _ when s2t1 <= s2rt_addr => begin
      case+ s3aexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ae1 => begin
        case+ s3aexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ae2 => Some_vt (s3bexp_peq (s3ae1, s3ae2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
    end // end of [s2t1 = s2rt_addr]
  | _ when s2t1 <= s2rt_bool => begin
      case+ s3bexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3be1 => begin
        case+ s3bexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3be2 => Some_vt (s3bexp_beq (s3be1, s3be2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
    end // end of [s2t1 = s2rt_bool]
  | _ when s2t1 <= s2rt_char => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ieq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
    end // end of [s2t1 = s2rt_char]
// (*
  // this is an experimental feature!!!
  | _ when s2rt_is_dat s2t1 => begin
      case+ s3iexp_make_s2exp (s2e1, s2cs, fds) of
      | ~Some_vt s3ie1 => begin
        case+ s3iexp_make_s2exp (s2e2, s2cs, fds) of
        | ~Some_vt s3ie2 => Some_vt (s3bexp_ieq (s3ie1, s3ie2))
        | ~None_vt () => None_vt ()
        end // end of [Some_vt]
      | ~None_vt () => None_vt ()
    end // end of [s2rt_is_dat s2t1]
// *)
  | _ => begin
      if s2exp_syneq (s2e1, s2e2) then Some_vt (s3bexp_true) else None_vt ()
    end // end of [_]
end // end of [aux_equal]

fn aux_bind
  (loc: loc_t, s2v1: s2var_t, s2e2: s2exp, s2cs: &s2cstlst, fds: &s2cfdeflst_vt)
  : s3bexpopt_vt = let
(*
  val () = begin
    print "aux_bind: s2v1 = "; print s2v1; print_newline ();
    print "aux_bind: s2e2 = "; print s2e2; print_newline ();
  end // end of [val]
*)
  val os3be = aux_equal (s2exp_var s2v1, s2e2, s2cs, fds)
  val () = trans3_env_hypo_add_bind (loc, s2v1, s2e2)
in
  os3be
end // end of [aux_bind]

in // in of [local]

fun s2cstlst_add (s2cs: s2cstlst, s2c0: s2cst_t): s2cstlst = let
  fun aux (s2cs: s2cstlst, s2c0: s2cst_t): bool = begin
    case+ s2cs of
    | S2CSTLSTcons (s2c, s2cs) =>
        if eq_s2cst_s2cst (s2c0, s2c) then true else aux (s2cs, s2c0)
    | S2CSTLSTnil () => false
  end // end of [aux]
in
  if aux (s2cs, s2c0) then s2cs else S2CSTLSTcons (s2c0, s2cs)
end // end of [s2cstlst_add]

implement
s3aexp_make_s2exp
  (s2e0, s2cs, fds) = let
  val s2e0 = s2exp_whnf s2e0
(*
  val () = begin
    print "s3aexp_make_s2exp: s2e0 = "; print s2e0; print_newline ();
  end // end of [val]
*)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e1, s2es2) => begin case+ s2e1.s2exp_node of
    | S2Ecst s2c1 => s3aexp_make_s2cst_s2explst (s2c1, s2es2, s2cs, fds)
    | _ => None_vt ()
    end // end of [S2Eapp]
  | S2Ecst s2c => begin case+ s2c of
    | _ when s2cstref_equ_cst (Null_addr, s2c) => Some_vt (s3aexp_null)
    | _ => (s2cs := s2cstlst_add (s2cs, s2c); Some_vt (s3aexp_cst s2c))
    end // end of [S2Ecst]
  | S2Evar s2v => Some_vt (s3aexp_var s2v)
  | _ => let // an expression that cannot be handled
      val () = begin
        prerr "warning(3): s3aexp_make_s2exp: s2e0 = "; prerr s2e0; prerr_newline ();
      end // end of [val]
    in
      None_vt ()
    end // end of [S2Evar]
end // end of [s3aexp_make_s2exp]

(* ****** ****** *)

fun s2exp_synlt (s2e1: s2exp, s2e2: s2exp): bool = let
  val s2e2 = s2exp_whnf s2e2
(*
  val () = begin
    print "s2exp_synlt: s2e1 = "; print s2e1; print_newline ();
    print "s2exp_synlt: s2e2 = "; print s2e2; print_newline ();
  end // end of [val]
*)
in
  case+ s2e2.s2exp_node of
  | S2Eapp (_, s2es2) => s2explst_synlte (s2e1, s2es2)
  | _ => false
end // end pf [s2exp_synlt]

and s2exp_synlte (s2e1: s2exp, s2e2: s2exp): bool =
  s2exp_syneq (s2e1, s2e2) orelse s2exp_synlt (s2e1, s2e2)

and s2explst_synlte
  (s2e1: s2exp, s2es2: s2explst): bool = begin
  case+ s2es2 of
  | list_cons (s2e2, s2es2) => begin
      s2exp_synlte (s2e1, s2e2) orelse s2explst_synlte (s2e1, s2es2)
    end
  | list_nil () => false
end // end of [s2explst_synlte]

fn s2exp_metlt_reduce {n:nat}
  (met: s2explst n, met_bound: s2explst n): s2exp = let
  fn auxlt
    (isint: bool, s2e1: s2exp, s2e2: s2exp, lt: &int >> int)
    : s2exp = begin
    if isint then
      s2exp_lt_int_int_bool (s2e1, s2e2)
    else begin
      if s2exp_synlt (s2e1, s2e2) then (lt := 1; s2exp_bool true)
      else (lt := ~1; s2exp_bool false)
    end
  end // end of [auxlt]

  fn auxlte
    (isint: bool, s2e1: s2exp, s2e2: s2exp, lte: &int >> int)
    : s2exp = begin
    if isint then
      s2exp_lte_int_int_bool (s2e1, s2e2)
    else begin
      if s2exp_synlte (s2e1, s2e2) then (lte := 1; s2exp_bool true)
      else (lte := ~1; s2exp_bool false)
    end
  end // end of [auxlte]

  fun auxlst {n:nat}
    (s2es1: s2explst n, s2es2: s2explst n): s2exp = begin
    case+ s2es1 of
    | list_cons (s2e1, s2es1) => let
        var lt: int = 0 and lte: int = 0
        val+ list_cons (s2e2, s2es2) = s2es2
        val isint = s2rt_is_int (s2e1.s2exp_srt)
        val s2p_lt = auxlt (isint, s2e1, s2e2, lt)
        val s2p_lte = auxlte (isint, s2e1, s2e2, lte)
      in
        case+ lt of
        | _ when lt = 0 => begin
            s2exp_add_bool_bool_bool (
              s2p_lt
            , s2exp_mul_bool_bool_bool (s2p_lte, auxlst (s2es1, s2es2))
            )
          end // end of [lt = 0]
        | _ when lt > 0 => s2p_lt (* true *) // end of [lt > 0]
        | _ (* lt < 0 *) => // HX: lte != 0
            if lte >= 0 then auxlst (s2es1, s2es2) else s2p_lte (* false *)
          // end of [lt < 0]
      end // end of [list_cons]
    | list_nil () => s2exp_bool false
  end // end of [auxlst]
in
  auxlst (met, met_bound)
end // end of [s2exp_metlt_reduce]

implement
s3bexp_make_s2exp
  (s2e0, s2cs, fds) = let
  val s2e0 = s2exp_whnf s2e0
(*
  val () = begin
    print "s3bexp_make_s2exp: s2e0 = "; print s2e0; print_newline ()
  end // end of [val]
*)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e1, s2es2) => begin case+ s2e1.s2exp_node of
    | S2Ecst s2c1 => s3bexp_make_s2cst_s2explst (s2c1, s2es2, s2cs, fds)
    | _ => None_vt ()
    end // end of [S2Eapp]
  | S2Ecst s2c => begin case+ s2c of
    | _ when s2cstref_equ_cst (True_bool, s2c) => Some_vt (s3bexp_true)
    | _ when s2cstref_equ_cst (False_bool, s2c) => Some_vt (s3bexp_false)
    | _ => (s2cs := s2cstlst_add (s2cs, s2c); Some_vt (s3bexp_cst s2c))
    end // end of [S2Ecst]
  | S2Evar s2v => Some_vt (s3bexp_var s2v)
  | S2Eeqeq (s2e1, s2e2) => aux_equal (s2e1, s2e2, s2cs, fds)
  | S2Emetlt (met, met_bound) => let
      val s2e_met = s2exp_metlt_reduce (met, met_bound)
    in
      s3bexp_make_s2exp (s2e_met, s2cs, fds)
    end // end of [S3Emetlt]
  | _ => let // an expression that cannot be handled
      val () = begin
        prerr "warning(3): s3bexp_make_s2exp: s2e0 = "; prerr s2e0; prerr_newline ();
      end // end of [val]
    in
      None_vt ()
    end // end of [_]
end // end of [s3bexp_make_s2exp]

implement
s3bexp_make_h3ypo
  (h3p, s2cs, fds) = begin
  case+ h3p.h3ypo_node of
  | H3YPOprop s2p => s3bexp_make_s2exp (s2p, s2cs, fds)
  | H3YPObind (s2v1, s2e2) => aux_bind (h3p.h3ypo_loc, s2v1, s2e2, s2cs, fds)
  | H3YPOeqeq (s2e1, s2e2) => aux_equal (s2e1, s2e2, s2cs, fds)
end // end of [s3bexp_make_h3ypo]

end // end of [local]

(* ****** ****** *)

implement
s3iexp_make_s2exp
  (s2e0, s2cs, fds) = let
  val s2e0 = s2exp_whnf s2e0
(*
  val () = begin
    print "s3iexp_make_s2exp: s2e0 = "; print s2e0; print_newline ()
  end // end of [val]
*)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e1, s2es2) => begin case+ s2e1.s2exp_node of
    | S2Ecst s2c1 => s3iexp_make_s2cst_s2explst (s2c1, s2es2, s2cs, fds)
    | _ => None_vt ()
    end // end of [S2Eapp]
  | S2Echar c => let
      val i = int_of_char c in Some_vt (s3iexp_int i)
    end // end of [S2Echar]
  | S2Ecst s2c => begin
      s2cs := s2cstlst_add (s2cs, s2c); Some_vt (s3iexp_cst s2c)
    end // end of [S2Ecst]
  | S2Eint i => Some_vt (s3iexp_int i)
  | S2Eintinf i => Some_vt (s3iexp_intinf i)
  | S2Esize s2ze => let
      val s2c_rel = s2cstref_get_cst (Size_int_int_bool)
      val s2v = s2cfdeflst_replace (s2rt_int, s2c_rel, '[s2e0], s2cs, fds)
    in
      Some_vt (s3iexp_var s2v)
    end // end of [S2Esize]
  | S2Evar s2v => Some_vt (s3iexp_var s2v)
  | _ => let // an expression that cannot be handled
      val () = begin
        prerr "warning(3): s3iexp_make_s2exp: s2e0 = "; prerr s2e0; prerr_newline ();
      end // end of [val]
    in
      None_vt ()
    end // end of [_]
end // end of [s3iexp_make_s2exp]

(* ****** ****** *)

staload Map = "ats_map_lin.sats"
staload _(*anonymous*) = "ats_map_lin.dats" // for template definition

viewtypedef s2cst_index_map = $Map.map_vt (stamp_t, Pos)
viewtypedef s2var_index_map = $Map.map_vt (stamp_t, Pos)

//

overload compare with $Stamp.compare_stamp_stamp

fn s2cst_index_map_make (): s2cst_index_map =
  $Map.map_make {stamp_t, Pos} (lam (s1, s2) => compare (s1, s2))
// end of [s2cst_index_map_make]

fn s2var_index_map_make (): s2var_index_map =
  $Map.map_make {stamp_t, Pos} (lam (s1, s2) => compare (s1, s2))
// end of [s2cst_index_map_make]

//

fn s2cst_index_find {n:pos}
  (loc0: loc_t, m: !s2cst_index_map, s2c: s2cst_t, n: int n)
  : intBtw (1, n) = let
(*
  val () = print "s2cst_index_find: s2c = "; print s2c; print_newline ()
*)
  val stamp = s2cst_get_stamp s2c
in
  case+ $Map.map_search (m, stamp) of
  | ~Some_vt (i) => if i < n then i else begin
      prerr_loc_interror (loc0);
      prerr ": s2cst_index_find: the static constant [";
      prerr_s2cst s2c;
      prerr "] is associated with an index that is out-of-range.";
      prerr_newline ();
      $Err.abort {intBtw (1, n)} ()
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr_loc_interror (loc0);
      prerr ": s2cst_index_find: the static constant [";
      prerr_s2cst s2c;
      prerr "] is not associated with any index.";
      prerr_newline ();
      $Err.abort {intBtw (1, n)} ()
    end // end of [None_vt]
end // end of [s2cst_index_find]

fn s2var_index_find {n:pos}
  (loc0: loc_t, m: !s2var_index_map, s2v: s2var_t, n: int n)
  : intBtw (1, n) = let
(*
  val () = print "s2var_index_find: s2v = "; print s2v; print_newline ()
*)
  val stamp = s2var_get_stamp s2v
in
  case+ $Map.map_search (m, stamp) of
  | ~Some_vt (i) => if i < n then i else begin
      prerr_loc_interror (loc0);
      prerr ": s2var_index_find: the static variable [";
      prerr_s2var s2v;
      prerr "] is associated with an index that is out-of-range.";
      prerr_newline ();
      $Err.abort {intBtw (1, n)} ()
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr_loc_interror (loc0);
      prerr ": s2var_index_find: the static variable [";
      prerr_s2var s2v;
      prerr "] is not associated with any index.";
      prerr_newline ();
      $Err.abort {intBtw (1, n)} ()
    end // end of [None_vt]
end // end of [s2var_index_find]

//

fn s2cst_index_insert
  (cim: !s2cst_index_map, s2c: s2cst_t, i: Pos): void =
  $Map.map_insert (cim, s2cst_get_stamp s2c, i)

fn s2var_index_insert
  (vim: !s2var_index_map, s2v: s2var_t, i: Pos): void =
  $Map.map_insert (vim, s2var_get_stamp s2v, i)

(* ****** ****** *)

staload FM = "ats_solver_fm.sats"

stadef i0nt = $FM.i0nt
stadef intvec = $FM.intvec

(* ****** ****** *)

extern
fun s3aexp_intvec_update_err {n:pos} {l:addr} (
    pf_arr: !intvec n @ l
  | loc0: loc_t
  , cim: !s2cst_index_map
  , vim: !s2var_index_map
  , ivp: ptr l, n: int n
  , coef: i0nt, s3ae0: s3aexp
  , errno: &int
  ) : void
// end of [s3aexp_intvec_update_err]

extern
fun s3bexp_intvec_update_err {n:pos} {l:addr} (
    pf_arr: !intvec n @ l
  | loc0: loc_t
  , cim: !s2cst_index_map
  , vim: !s2var_index_map
  , ivp: ptr l, n: int n
  , coef: i0nt, s3be0: s3bexp
  , errno: &int
  ) : void
// end of [s3bexp_intvec_update_err]

extern
fun s3iexp_intvec_update_err {n:pos} {l:addr} (
    pf_arr: !intvec n @ l
  | loc0: loc_t
  , cim: !s2cst_index_map
  , vim: !s2var_index_map
  , ivp: ptr l, n: int n
  , coef: i0nt, s3ie0: s3iexp
  , errno: &int
  ) : void
// end of [s3iexp_intvec_update_err]

(* ****** ****** *)

implement
s3aexp_intvec_update_err
  (pf_arr | loc0, cim, vim, ivp, n, coef, s3ae0, errno) = let
(*
  val () = begin
    print "s3aexp_intvec_update_err: coef = "; print coef; print_newline ();
    print "s3aexp_intvec_update_err: s3ae0 = "; print s3ae0; print_newline ();
  end // end of [val]
*)
in
  case+ s3ae0 of
  | S3AEcst s2c => let
      val ind = s2cst_index_find (loc0, cim, s2c, n)
    in
      ivp->[ind] := ivp->[ind] + coef
    end // end of [S3AEcst]
  | S3AEvar s2v => let
      val ind = s2var_index_find (loc0, vim, s2v, n)
    in
      ivp->[ind] := ivp->[ind] + coef
    end // end of [S3AEvar]
  | S3AEnull () => ()
  | S3AEpadd (s3ae1, s3ie2) => begin
      s3aexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ae1, errno);
      s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie2, errno);
    end // end of [S3AEpadd]
  | S3AEexp _ => begin
      prerr_interror ();
      prerr ": s3aexp_intvec_update_err: unsupported term: s3ae0 = "; prerr s3ae0;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [S3IEexp]
end // end of [s3aexp_intvec_update_err]

//

implement
s3iexp_intvec_update_err
  (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie0, errno) = let
(*
  val () = begin
    print "s3iexp_intvec_update_err: coef = "; print_i0nt coef; print_newline ();
    print "s3iexp_intvec_update_err: s3ie0 = "; print_s3iexp s3ie0; print_newline ();
  end // end of [val]
*)
in
  case+ s3ie0 of
  | S3IEcst s2c => let
      val ind = s2cst_index_find (loc0, cim, s2c, n)
    in
      ivp->[ind] := ivp->[ind] + coef
    end // end of [S3IEcst]
  | S3IEvar s2v => let
      val ind = s2var_index_find (loc0, vim, s2v, n)
    in
      ivp->[ind] := ivp->[ind] + coef
    end // end of [S3IEvar]
  | S3IEint (i) => let
      val i0 = $FM.i0nt_of_int i in ivp->[0] := ivp->[0] + coef * i0
    end // end of [S3IEint]
  | S3IEintinf (i) => begin
      let val i0 = $FM.i0nt_of_intinf i in ivp->[0] := ivp->[0] + coef * i0 end
    end // end of [S3IEintinf]
  | S3IEineg (s3ie) => begin
      s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, ~coef, s3ie, errno);
    end // end of [S3IEineg]
  | S3IEiadd (s3ie1, s3ie2) => begin
      s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie1, errno);
      s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie2, errno);
    end // end of [S3IEiadd]
  | S3IEisub (s3ie1, s3ie2) => begin
      s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie1, errno);
      s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, ~coef, s3ie2, errno);
    end // end of [S3IEisub]
  | S3IEimul (s3ie1, s3ie2) => begin case+ s3ie1 of
    | S3IEint i1 => let
        val coef = coef * $FM.i0nt_of_int (i1)
      in
        s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie2, errno)
      end // end of [S3IEint]
    | S3IEintinf i1 => let
        val coef = coef * $FM.i0nt_of_intinf (i1)
      in
        s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie2, errno)
      end // end of [S3IEintinf]
    | _ => begin case+ s3ie2 of
      | S3IEint i2 => let
          val coef = coef * $FM.i0nt_of_int (i2) in
          s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie1, errno)
        end // end of [S3IEint]
      | S3IEintinf i2 => let
          val coef = coef * $FM.i0nt_of_intinf (i2) in
          s3iexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ie1, errno)
        end // end of [S3IEintinf]
      | _ => begin
          $Loc.prerr_location loc0; prerr ": error(3)";
          prerr ": it is not allowed to have a nonlinear term appear in a constraint: [";
          prerr s3ie0; prerr "]"; prerr_newline ();
          $Err.abort {void} ()
        end // end of [_]
      end (* end of [_] *)
    end // end of [S3IEimul]
  | S3IEpdiff (s3ae1, s3ae2) => begin
      s3aexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, coef, s3ae1, errno);
      s3aexp_intvec_update_err (pf_arr | loc0, cim, vim, ivp, n, ~coef, s3ae2, errno);
    end // end of [S3IEpdiff]
  | S3IEexp _ => begin
      prerr_interror ();
      prerr ": s3iexp_intvec_update_err: unsupported term: s3ie0 = "; prerr s3ie0;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [S3IEexp]
end // end of [s3iexp_intvec_update_err]

(* ****** ****** *)

extern
fun s3bexp_icstr_make_err {n:pos} (
    loc0: loc_t
  , cim: !s2cst_index_map
  , vim: !s2var_index_map
  , n: int n (* 1 + number of variables *)
  , s3be0: s3bexp
  , errno: &int
  ) : $FM.icstr n
// end of [s3bexp_icstr_make_err]

implement
s3bexp_icstr_make_err
  (loc0, cim, vim, n, s3be0, errno) = let
(*
  val () = begin
    print "s3bexp_icstr_err: s3be0 = "; print_s3bexp s3be; print_newline ()
  end // end of [val]
*)
  macdef aux (s3be) = s3bexp_icstr_make_err (loc0, cim, vim, n, ,(s3be), errno)
in
  case+ s3be0 of
  | S3BEbool b => begin
      if b then begin
        $FM.ICveclst (0(*conj*), list_vt_nil ())
      end else begin
        $FM.ICveclst (1(*disj*), list_vt_nil ())
      end // end of [if]
    end // end of [S3BEbool]
  | S3BEcst s2c => let
      val ind = s2cst_index_find (loc0, cim, s2c, n)
      val (pf_gc, pf_arr | ivp) = $FM.intvec_ptr_make (n)
      val () = (ivp->[ind] := $FM.i0nt_1; ivp->[0] := $FM.i0nt_neg_1)
    in
      $FM.ICvec (2(*gte*), $FM.intvecptr_make_view_ptr (pf_gc, pf_arr | ivp))
    end // end of [S3BEcst]
  | S3BEvar s2v => let
      val ind = s2var_index_find (loc0, vim, s2v, n)
      val (pf_gc, pf_arr | ivp) = $FM.intvec_ptr_make (n)
      val () = (ivp->[ind] := $FM.i0nt_1; ivp->[0] := $FM.i0nt_neg_1)
    in
      $FM.ICvec (2(*gte*), $FM.intvecptr_make_view_ptr (pf_gc, pf_arr | ivp))
    end // end of [S3BEvar]
  | S3BEbneg s3be => $FM.icstr_negate (aux s3be)
  | S3BEbadd (s3be1, s3be2) => let
      val ic1 = aux s3be1 and ic2 = aux s3be2
      val ics = list_vt_cons (ic1, list_vt_cons (ic2, list_vt_nil ()))
    in
      $FM.ICveclst (1(*disj*), ics)
    end // end of [S3BEbadd]
  | S3BEbmul (s3be1, s3be2) => let
      val ic1 = aux s3be1 and ic2 = aux s3be2
      val ics = list_vt_cons (ic1, list_vt_cons (ic2, list_vt_nil ()))
    in
      $FM.ICveclst (0(*conj*), ics)
    end // end of [S3BEbmul]
  | S3BEiexp (knd, s3ie) => let (* gte/lt: 2/~2; eq/neq: 1/~1 *)
      val (pf_gc, pf_arr | ivp) = $FM.intvec_ptr_make (n)
      val () = s3iexp_intvec_update_err (
        pf_arr | loc0, cim, vim, ivp, n, $FM.i0nt_1, s3ie, errno
      ) // end of [s3iexp_intvec_update_err]
    in
      $FM.ICvec (knd, $FM.intvecptr_make_view_ptr (pf_gc, pf_arr | ivp))
    end // end of [S3BEiexp]
  | S3BEexp _ => begin
      prerr_interror ();
      prerr ": s3bexp_intvec_make_err: unsupported term: s3be0 = "; prerr s3be0;
      prerr_newline ();
      $Err.abort ()
    end // end of [S3BEexp]
end // end of [s3bexp_icstr_make_err]

(* ****** ****** *)

extern
fun s3bexplst_s2exp_solve_fm (
    loc0: loc_t
  , s2vs: s2varlst
  , s3bes: s3bexplst
  , s2p: s2exp
  , s2cs: &s2cstlst
  , fds: &s2cfdeflst_vt
  , errno: &int
  ) : intBtw (~1, 1)
// end of [s3bexplst_s2exp_solve_fm]

implement
s3bexplst_s2exp_solve_fm
  (loc0, s2vs, s3bes, s2p, s2cs, fds, errno) = let
(*
  val () = begin
    print "s3bexplst_s2exp_solve_fm: s2vs = "; print s2vs; print_newline ();
    print "s3bexplst_s2exp_solve_fm: s3bes = "; print s3bes; print_newline ();
    print "s3bexplst_s2exp_solve_fm: s2p = "; print s2p; print_newline ();
  end // end of [val]
*)
  viewtypedef cim_vt = s2cst_index_map and vim_vt = s2var_index_map
  val os3p = s3bexp_make_s2exp (s2p, s2cs, fds)
  var s3bes_asmp: s3bexplst = s3bes
  val () = aux (s3bes_asmp, fds) where {
    fun aux (s3bes: &s3bexplst, fds: !s2cfdeflst_vt): void =
      case+ fds of
      | S2CFDEFLSTcons (_, _, _, !rel, !fds_nxt) => let
          val () = case+ !rel of
            | Some_vt s3be => begin
                fold@ (!rel); s3bes := list_cons (s3be, s3bes)
              end
            | None_vt () => fold@ (!rel)
        in
          aux (s3bes, !fds_nxt); fold@ (fds)
        end // end of [S2CFDEFLSTcons]
      | S2CFDEFLSTmark (!fds_nxt) => begin
          aux (s3bes, !fds_nxt); fold@ (fds)
        end // end of [S2CFDEFLSTmark]
      | S2CFDEFLSTnil () => fold@ (fds)
  } // end of [where]

  val s3p = begin case+ os3p of
    | ~Some_vt s3p => s3p | ~None_vt () => let
        val () = begin
          $Loc.prerr_location loc0;
          prerr ": warning(3)"; prerr ": the constraint ["; prerr_s2exp s2p;
          prerr "] cannot be translated into a form accepted by the constraint solver.";
          prerr_newline ()
        end // end of [val]
      in
        s3bexp_false (* make it the worst scenario *)
      end // end of [None_vt]
  end // end of [val]
//
  var cnt: Pos = 1
  var cim = s2cst_index_map_make ()
  val () = aux (cim, cnt, s2cs) where {
    fun aux (cim: !cim_vt, cnt: &Pos, s2cs: s2cstlst): void =
      case+ s2cs of
      | S2CSTLSTcons (s2c, s2cs) => let
          val () = s2cst_index_insert (cim, s2c, cnt)
        in
          cnt := cnt + 1; aux (cim, cnt, s2cs)
        end
      | S2CSTLSTnil () => ()
  } // end of [where]
  var vim = s2var_index_map_make ()
//
  val () = aux (vim, cnt, s2vs) where {
    fun aux (vim: !vim_vt, cnt: &Pos, s2vs: s2varlst): void =
      case+ s2vs of
      | list_cons (s2v, s2vs) => let
          val () = s2var_index_insert (vim, s2v, cnt)
        in
          cnt := cnt + 1; aux (vim, cnt, s2vs)
        end
      | list_nil () => ()
  } // end of [where]
//
  val () = aux (vim, cnt, fds) where {
    fun aux (vim: !vim_vt, cnt: &Pos, fds: !s2cfdeflst_vt): void =
      case+ fds of
      | S2CFDEFLSTcons (_, _, s2v_res, _, !fds_nxt) => let
          val () = s2var_index_insert (vim, s2v_res, cnt)
        in
          cnt := cnt + 1; aux (vim, cnt, !fds_nxt); fold@ fds
        end
      | S2CFDEFLSTmark (!fds_nxt) => begin
          aux (vim, cnt, !fds_nxt); fold@ (fds)
        end
      | S2CFDEFLSTnil () => fold@ (fds)
  } // end of [where]
//
  val cnt = cnt // the [cnt] variable is shadowed intentionally!
  val ics_asmp = ics where {
    viewtypedef T = [n,s:int] $FM.icstrlst (n, s)
    fun aux {n:pos} (
        loc0: loc_t
      , cim: !cim_vt
      , vim: !vim_vt
      , n: int n
      , s3bes: s3bexplst
      , ics: &T? >> $FM.icstrlst n
      , errno: &int
      ) : void = begin case+ s3bes of
      | list_cons (s3be, s3bes) => let
          val ic = s3bexp_icstr_make_err (loc0, cim, vim, n, s3be, errno)
          val+ () = ics := list_vt_cons {$FM.icstr n} {0} (ic, ?)
          val+ list_vt_cons (_, !ics_nxt) = ics
        in
          aux (loc0, cim, vim, n, s3bes, !ics_nxt, errno); fold@ ics
        end
      | list_nil () => (ics := list_vt_nil ())
    end // end of [aux]
    var ics: T // uninitialized
    val () = aux (loc0, cim, vim, cnt, s3bes_asmp, ics, errno)
  }
//
  val ic_conc = s3bexp_icstr_make_err (loc0, cim, vim, cnt, s3p, errno)
  val () = $Map.map_free cim and () = $Map.map_free vim
(*
  val () = begin
    print "s3bexp_s2exp_solve_fm: ics_asmp = \n";
    print_icstrlst (ics_asmp, cnt); print_newline ();
    print "s3bexp_s2exp_solve_fm: ic_conc = "; 
    print_icstr (ic_conc, cnt); print_newline ()
  end // end of [val]
*)
  var ics_all = list_vt_cons ($FM.icstr_negate ic_conc, ics_asmp)
(*
  val () = begin
    print "s3bexp_s2exp_solve_fm: ics_all = \n";
    print_icstrlst (ics_all, cnt);
    print_newline ()
  end // end of [val]
*)
  val ans = $FM.icstrlst_solve (ics_all, cnt)
  val () = $FM.icstrlst_free ics_all
in
  ans
end // end of [s3bexplst_s2exp_solve_fm]

(* ****** ****** *)

extern
fun c3str_solve_main (
    s2vs: s2varlst
  , s3bes: s3bexplst
  , c3t: c3str
  , s2cs: &s2cstlst
  , fds: &s2cfdeflst_vt
  , unsolved: &uint
  , errno: &int
  ) : intBtw (~1, 1)
// end of [c3str_solve_main]

extern
fun c3str_solve_prop (
    loc0: loc_t
  , s2vs: s2varlst
  , s3bes: s3bexplst
  , s2p: s2exp
  , s2cs: &s2cstlst
  , fds: &s2cfdeflst_vt
  , errno: &int
  ) : intBtw (~1, 1)
// end of [c3str_solve_prop]

extern
fun c3str_solve_itmlst (
    loc0: loc_t
  , s2vs: s2varlst
  , s3bes: s3bexplst
  , s3is: s3itemlst
  , s2cs: &s2cstlst
  , fds: &s2cfdeflst_vt
  , unsolved: &uint
  , errno: &int
  ) : intBtw (~1, 1)
// end of [c3str_solve_itmlst]

extern
fun c3str_solve_itmlst_disj (
    loc0: loc_t
  , s2vs: s2varlst
  , s3bes: s3bexplst
  , s3is: s3itemlst
  , s3iss: s3itemlstlst
  , s2cs: &s2cstlst
  , fds: &s2cfdeflst_vt
  , unsolved: &uint
  , errno: &int
  ) : intBtw (~1, 1)
// end of [c3str_solve_itmlst_disj]

(* ****** ****** *)

fn pattern_match_exhaustiveness_msg
  (loc0: loc_t, knd: int, p2tcs: p2atcstlst) = let
  fun aux (p2tcs: p2atcstlst): void = case+ p2tcs of
    | list_cons (p2tc, p2tcs) => begin
        prerr p2tc; prerr_newline (); aux p2tcs
      end // end of [list_cons]
    | list_nil () => ()
  // end of [aux]
in
  case+ knd of
  | 0 => begin
      $Loc.prerr_location loc0;
      prerr ": warning(3)";
      prerr ": pattern match is nonexhaustive:\n";
      aux p2tcs;
    end
  | 1 => begin
      $Loc.prerr_location loc0;
      prerr ": error(3)";
      prerr ": pattern match is nonexhaustive:\n";
      aux p2tcs;
    end
  | _ => () // ignore
end // end of [pattern_match_exhaustiveness_msg]

implement
c3str_solve_main
  (s2vs, s3bes, c3t, s2cs, fds, unsolved, errno) = let
(*
  val () = begin
    print "c3str_solve_main: s2vs = "; print s2vs; print_newline ();
    print "c3str_solve_main: s3bes = "; print s3bes; print_newline ();
    print "c3str_solve_main: c3t = "; print c3t; print_newline ();
  end // end of [val]
*)
  val loc0 = c3t.c3str_loc
  val s2cs0 = s2cs; val () = s2cfdeflst_push (fds)
  val ans = (case+ c3t.c3str_node of
    | C3STRprop s2p => c3str_solve_prop
        (loc0, s2vs, s3bes, s2p, s2cs, fds, errno)
    | C3STRitmlst s3is => c3str_solve_itmlst
        (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno)
  ) : intBtw (~1, 1) // end of [val]
(*
  val () = begin
    print "c3str_solve_main: ans = "; print ans; print_newline ()
  end // end of [val]
*)
  val () = s2cfdeflst_pop (fds); val () = s2cs := s2cs0
//
  fn prerr_c3str_if (unsolved: uint, c3t: c3str): void = begin
    if (unsolved > 0U) then () else (prerr ": "; prerr_c3str c3t)
  end // end of [prerr_c3str_if]
//
  var ans: intBtw (~1, 1) = ans
  val () = begin case+ ans of
    | _ when ans >= 0 => begin case+ c3t.c3str_kind of
      | C3STRKINDmain () => begin
          if unsolved > 0U then begin
            // an error message has already been reported
          end else begin
            $Loc.prerr_location loc0; prerr ": error(3)";
            prerr ": unsolved constraint"; prerr_c3str_if (unsolved, c3t);
            prerr_newline ()
          end
        end // end of [C3STRKINDmain]
      | C3STRKINDmetric_nat () => begin
          $Loc.prerr_location loc0; prerr ": error(3)";
          prerr ": unsolved constraint for termination metric being welfounded";
          prerr_c3str_if (unsolved, c3t);
          prerr_newline ()
        end // end of [C3STRKINDmetric_nat]
      | C3STRKINDmetric_dec () => begin
          $Loc.prerr_location loc0; prerr ": error(3)";
          prerr ": unsolved constraint for termination metric being decreasing";
          prerr_c3str_if (unsolved, c3t);
          prerr_newline ()
        end // end of [C3STRKINDmetric_dec]
      | C3STRKINDpattern_match_exhaustiveness (knd, p2tcs) => let
          val () = pattern_match_exhaustiveness_msg (loc0, knd, p2tcs)
        in
          if knd <= 0 then(*warning*) ans := (~1) else(*error*) ()
        end // end of [C3STRKINDpattern...]
      | C3STRKINDvarfin (d2v, s2e, s2e_fin) => begin
          $Loc.prerr_location loc0; prerr ": error(3)";
          prerr ": unsolved constraint for the dynamic variable [";
          prerr d2v; prerr "]";
          prerr_c3str_if (unsolved, c3t);
          prerr_newline ()
(*
          prerr ": it is expected to have the type [";
          prerr s2e_fin; prerr "]";
          prerr ", but it is given the type ["; prerr s2e_fin; prerr "]";
          prerr_newline ()
*)
        end // end of [C3STRKINDvarfin]
      | C3STRKINDloop (knd) => begin
          $Loc.prerr_location loc0; prerr ": error(3)";
          if knd = 0 then prerr ": unsolved constraint for loop enter";
          if knd = 1 then prerr ": unsolved constraint for loop exit";
          if knd = 2 then prerr ": unsolved constraint for loop repeat";
          prerr_c3str_if (unsolved, c3t);
          prerr_newline ()
        end // end of [C3STRKINDloop]
      end (* end of [ans >= 0] *)
    | _ => ()
    end // end of [case]
  val () = if ans >= 0 then (unsolved := unsolved + 1U)
in
  ans (* 0: unsolved; ~1: solved *)
end // end of [c3str_solve_main]

(* ****** ****** *)

implement
c3str_solve_prop
  (loc0, s2vs, s3bes, s2p, s2cs, fds, errno) = let
(*
  val () = begin
    print "c3str_solve_prop: s2vs = "; print s2vs; print_newline ();
    print "c3str_solve_prop: s3bes = "; print s3bes; print_newline ();
    print "c3str_solve_prop: s2p = "; print s2p; print_newline ();
  end // end of [val]
*)
in
  s3bexplst_s2exp_solve_fm (loc0, s2vs, s3bes, s2p, s2cs, fds, errno)
end // end of [c3str_solve_prop]

(* ****** ****** *)

implement
c3str_solve_itmlst
  (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno) = let
(*
  val () = begin
    print "c3str_solve_itmlst: s2vs = "; print s2vs; print_newline ();
    print "c3str_solve_itmlst: s3bes = "; print s3bes; print_newline ();
    print "c3str_solve_itmlst: s3is = "; print s3is; print_newline ();
  end // end of [val]
*)
in
  case+ s3is of
  | list_cons (s3i, s3is) => begin case+ s3i of
    | S3ITEMcstr c3t => let
        val ans1 = c3str_solve_main
          (s2vs, s3bes, c3t, s2cs, fds, unsolved, errno)
        val ans2 = c3str_solve_itmlst
          (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno)
      in
        if ans1 >= 0 then 0 else ans2
      end // end of [S3ITEMcstr]
    | S3ITEMcstr_ref c3t_r => let
        val ans1 = (
          case+ !c3t_r of
          | Some c3t => c3str_solve_main
              (s2vs, s3bes, c3t, s2cs, fds, unsolved, errno)
          | None () => ~1 (*solved*)
        ) : intBtw (~1, 1)
        val ans2 = c3str_solve_itmlst
          (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno)
      in
        if ans1 >= 0 then 0 else ans2
      end // end of [S3ITEMcstr_ref]
    | S3ITEMdisj s3iss_disj => c3str_solve_itmlst_disj (
        loc0, s2vs, s3bes, s3is, s3iss_disj, s2cs, fds, unsolved, errno
      ) // end of [c3str_solve_itmlst_disj]
    | S3ITEMhypo h3p => let
        val () = the_s2varbindmap_push ()
        val s3bes = (
          case+ s3bexp_make_h3ypo (h3p, s2cs, fds) of
          | ~Some_vt s3be => list_cons (s3be, s3bes)
          | ~None_vt () => let
(*
              val () = begin
                $Loc.prerr_location loc0;
                prerr "warning(3): unused hypothesis: ["; prerr h3p; prerr "]";
                prerr_newline ()
              end // end of [val]
*)
            in
              s3bes
            end // end of [None_vt]
        ) : s3bexplst
        val ans = begin
          c3str_solve_itmlst (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno)
        end // end of [val]
        val () = the_s2varbindmap_pop ()
      in
        ans
      end // end of [S3ITEMhypo]
    | S3ITEMsvar s2v => let
        val s2vs = list_cons (s2v, s2vs)
      in
        c3str_solve_itmlst (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno)
      end // end of [S3ITEMsvar]
    | S3ITEMsVar s2V => let
(*
        val () = begin
          $Loc.prerr_location loc0;
          prerr "warning(3): c3str_solve_itmlst: s2V = "; prerr s2V;
          prerr_newline ()
        end // end of [val]
*)
      in
        c3str_solve_itmlst (loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno)
      end // end of [S3ITEMsVar]
    end // end of [list_cons]
  | list_nil () => ~1(*solved*)
end // end of [c3str_solve_itmlst]

(* ****** ****** *)

implement
c3str_solve_itmlst_disj
  (loc0, s2vs, s3bes, s3is0, s3iss_disj, s2cs, fds, unsolved, errno) = begin
  case+ s3iss_disj of
  | list_cons (s3is_disj, s3iss_disj) => let
      val s2cs0 = s2cs; val () = s2cfdeflst_push (fds)
      val s3is = $Lst.list_append (s3is_disj, s3is0)
      val ans = c3str_solve_itmlst (
        loc0, s2vs, s3bes, s3is, s2cs, fds, unsolved, errno
      ) // end of [c3str_solve_itmlst]
      val () = s2cfdeflst_pop (fds); val () = s2cs := s2cs0
    in
      c3str_solve_itmlst_disj (
        loc0, s2vs, s3bes, s3is0, s3iss_disj, s2cs, fds, unsolved, errno
      )
    end // end of [list_cons]
  | list_nil () => ~1(*solved*)
end // end of [c3str_solve_itmlst_disj]

(* ****** ****** *)

implement
c3str_solve (c3t) = let
(*
  val () = begin
    print "c3str_solve: c3t = "; print c3t; print_newline ()
  end // end of [val]
*)
//
// HX-2010-09-09: this is needed for solving top-level constraints!!!
  val () = the_s2varbindmap_initize ()
//
  val s2vs0 = list_nil () and s3bes0 = list_nil ()
  var s2cs: s2cstlst = S2CSTLSTnil ()
  var fds: s2cfdeflst_vt = S2CFDEFLSTnil ()
  var unsolved: uint = 0U
  var errno: int = 0
  val _(*ans*) = c3str_solve_main
    (s2vs0, s3bes0, c3t, s2cs, fds, unsolved, errno)
  val () = s2cfdeflst_free (fds)
in
  if unsolved > 0U then begin
    prerr "type-checking has failed";
    if unsolved <= 1U then prerr ": there is one unsolved constraint";
    if unsolved >= 2U then prerr ": there are some unsolved constraints";
    prerr ": please inspect the above reported error message(s) for information.";
    prerr_newline ();
    $Err.abort {void} ()
  end else begin
    // prerr "type-checking has been done successfully"; prerr_newline ()
  end // end of [if]
end // end of [c3str_solve]

(* ****** ****** *)

(* end of [ats_constraint.dats] *)
