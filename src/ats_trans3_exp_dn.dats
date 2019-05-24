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
// Time: December 2007
//
(* ****** ****** *)

(* Mainly for handling dynamic expressions during type-checking *)

(* ****** ****** *)

%{^
#include "ats_intinf.cats" // this for the ATS/Geizeilla compiler
%} // end of [%{^]

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload SOL = "ats_staexp2_solve.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload MAC = "ats_macro2.sats"

(* ****** ****** *)

staload "ats_stadyncst2.sats"
staload "ats_patcst2.sats"
staload "ats_string_parse.sats"
staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

#define THISFILENAME "ats_trans3_exp_dn.dats"

(* ****** ****** *)

overload = with $Lab.eq_label_label
overload prerr with $Loc.prerr_location
overload prerr with $Lab.prerr_label

(* ****** ****** *)

fn prerr_loc_error3 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(3)")
// end of [prerr_loc_error3]
fn prerr_loc_warning3 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": warning(3)")
// end of [prerr_loc_warning3]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans3_exp_dn)"

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_trans3_exp_dn)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

fn pfarity_check_rec (
  loc_rec: loc_t, npf1: int, npf2: int
) : void =
  if npf1 = npf2 then () else begin
    prerr_loc_error3 loc_rec;
    prerr ": the proof arity of the record is [";
    prerr npf1;
    prerr "] but it is expected to be [";
    prerr npf2;
    prerr "].";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
// end of [pfarity_check_rec]

(* ****** ****** *)

fn reckind_check (
  loc_rec: loc_t, k1: int, k2: tyreckind
) : void = begin
  if k1 > 0 then begin case+ k2 of
    | TYRECKINDbox () => () | _ => begin
        prerr_loc_error3 loc_rec;
        prerr ": the record is boxed but it is expected to be flat.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [_]
  end else begin case+ k2 of // k1 = 0
    | TYRECKINDflt0 _ => ()
    | TYRECKINDflt1 _ => ()
    | TYRECKINDflt_ext _ => ()
    | _ => begin
        prerr_loc_error3 loc_rec;
        prerr ": the record is flat but it is expected to be boxed.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [_]
  end // end of [if]
end // end of [reckind_check]

(* ****** ****** *)

typedef funclo = $Syn.funclo
viewtypedef funcloopt_vt = Option_vt funclo

fn d2exp_funclo_opt_of_d2exp
  (d2e0: d2exp, ofc0: &(funcloopt_vt?) >> funcloopt_vt): d2exp =
  case+ :(ofc0: Option_vt funclo) => d2e0.d2exp_node of
  | D2Eann_funclo (d2e, fc) => (ofc0 := Some_vt fc; d2e)
  | _ => (ofc0 := None_vt (); d2e0)
// end of [d2exp_funclo_opt_of_d2exp]

viewtypedef s2effopt_vt = Option_vt s2eff
fn d2exp_s2eff_opt_of_d2exp
  (d2e0: d2exp, os2fe0: &(s2effopt_vt?) >> s2effopt_vt): d2exp =
  case+ :(os2fe0: s2effopt_vt) => d2e0.d2exp_node of
  | D2Eann_seff (d2e, s2fe) => (os2fe0 := Some_vt s2fe; d2e)
  | _ => (os2fe0 := None_vt (); d2e0)
// end of [d2exp_s2eff_opt_of_d2exp]

(* ****** ****** *)

implement
d3exp_tr_dn (d3e, s2e) = let
(*
  val () = begin
    print "d3exp_tr_dn: d3e.d3exp_typ = "; print d3e.d3exp_typ; print_newline ()
  end // end of [val]
  val () = begin
    print "d3exp_tr_dn: s2e = "; print s2e; print_newline ()
  end // end of [val]
*)
in
  $SOL.s2exp_tyleq_solve (d3e.d3exp_loc, d3e.d3exp_typ, s2e)
end // end of [d3exp_tr_dn]

(* ****** ****** *)

fn d2exp_float_tr_dn
  (d2e0: d2exp, fcst: string, s2e0: s2exp): d3exp = let
  fn err (loc0: loc_t, s2e0: s2exp): d3exp = begin
    prerr_loc_error3 loc0;
    prerr ": the type ["; prerr s2e0;
    prerr "] cannot be assigned to a float constant.";
    prerr_newline ();
    $Err.abort {d3exp} ()
  end
  val loc0 = d2e0.d2exp_loc
  val s2e0 = s2exp_whnf s2e0
in
  case+ s2e0.s2exp_node of
  | S2Ecst s2c => begin case+ s2c of
    | _ when s2cstref_equ_cst (Double_t0ype, s2c) => begin
        d3exp_float (loc0, s2e0, fcst)
      end
    | _ when s2cstref_equ_cst (Float_t0ype, s2c) => begin
        d3exp_float (loc0, s2e0, fcst)
      end
    | _ when s2cstref_equ_cst (Double_long_t0ype, s2c) => begin
        d3exp_float (loc0, s2e0, fcst)
      end
    | _ => err (loc0, s2e0)
    end // end of [S2Ecst]
  | _ => d2exp_tr_dn_rest (d2e0, s2e0)
end // end of [d2exp_float_tr_dn]

(* ****** ****** *)

fn c2lau_make_if_d2exp
  (loc_cond: loc_t, b: bool, d2e: d2exp): c2lau 1 = let
  val p2t = p2at_bool (loc_cond, b); val gua = list_nil ()
in
  c2lau_make (d2e.d2exp_loc, '[p2t], gua, 0, 0, d2e)
end // end of [c2lau_make_of_d2exp]

// [loc0] is the location for the whole if-expression
fn c2lau_make_if_d2expopt
  (loc0: loc_t, loc_cond: loc_t, b: bool, od2e: d2expopt)
  : c2lau 1 = let
  val d2e = (case+ od2e of
    | Some d2e => d2e | None () => d2exp_empty (loc0)
  ) : d2exp
in
  c2lau_make_if_d2exp (loc_cond, b, d2e)
end // end of [c2lau_make_if_d2expopt]

(* ****** ****** *)

implement
d2exp_if_tr_dn
  (loc0, res, d2e_cond, d2e_then, od2e_else, s2e0) = let
  val loc_cond = d2e_cond.d2exp_loc
  val c2l_then = c2lau_make_if_d2exp (loc_cond, true, d2e_then)
  val c2l_else = c2lau_make_if_d2expopt (loc0, loc_cond, false, od2e_else)
in
  d2exp_caseof_tr_dn (
    loc0, 1(*knd*), res, 1, '[d2e_cond], '[c2l_then, c2l_else], s2e0
  ) // end of [d2exp_caseof_tr_dn]
end // end of [d2exp_if_tr_dn]

(* ****** ****** *)

implement
d2exp_sif_tr_dn (
  loc0, res, s2p_cond, d2e_then, d2e_else, s2e0
) = let
//
  val res = i2nvresstate_update (res)
//
  val
  sbis =
  the_d2varset_env_stbefitemlst_save ()
//
  val sac = staftscstr_initize (res, sbis)
//
  val d3e_then = let
    val () = trans3_env_push_sta ()
    val () = trans3_env_hypo_add_prop (loc0, s2p_cond)
    val d3e_then = d2exp_tr_dn (d2e_then, s2e0)
    val () = staftscstr_stbefitemlst_merge (loc0, sac, sbis)
    val () = trans3_env_pop_sta_and_add_none (d2e_then.d2exp_loc)
  in
    d3e_then
  end // end of [val]
//
  val () = stbefitemlst_restore_lin_typ (sbis)
//
  val d3e_else = let
    val () = trans3_env_push_sta ()
    val () = trans3_env_hypo_add_prop (loc0, s2exp_neg_bool_bool s2p_cond)
    val d3e_else = d2exp_tr_dn (d2e_else, s2e0)
    val () = staftscstr_stbefitemlst_merge (loc0, sac, sbis)
    val () = trans3_env_pop_sta_and_add_none (d2e_else.d2exp_loc)
  in
    d3e_else
  end // end of [val]
//
  val () = staftscstr_stbefitemlst_check (loc0, sac, sbis)
  val () = staftscstr_stbefitemlst_update (loc0, sac, sbis)
//
in
  d3exp_sif (loc0, s2e0, s2p_cond, d3e_then, d3e_else)
end // end of [d2exp_sif_tr_dn]

(* ****** ****** *)

fn d2exp_int_tr_dn (
    d2e0: d2exp
  , istr: string, icst: intinf_t
  , s2e0: s2exp
  ) : d3exp = let
  fn err (loc0: loc_t, s2e0: s2exp): d3exp = begin
    prerr_loc_error3 loc0;
    prerr ": the type ["; prerr s2e0;
    prerr "] cannot be assigned to an integer constant.";
    prerr_newline ();
    $Err.abort {d3exp} ()
  end
  fn szcheck (loc0: loc_t, icst: intinf_t): void = begin
    if $IntInf.gte_intinf_int (icst, 0) then () else begin
      prerr_loc_error3 loc0;
      $Deb.debug_prerrf (": %s: d2exp_int_tr_dn", @(THISFILENAME));
      prerr ": the negative number [";
      $IntInf.prerr_intinf icst;
      prerr "] cannot be a size."; prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
  end // end of [szcheck]
  val loc0 = d2e0.d2exp_loc
  val s2e0 = s2exp_whnf s2e0
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
    case+ s2e_fun.s2exp_node of
    | S2Ecst s2c => begin case+ s2c of
      | _ when s2cstref_equ_cst (Int_int_t0ype, s2c) => let
          val s2i = (case+ s2es_arg of
            | list_cons (s2e, _) => s2e
            | _ => begin
                prerr_interror ();
                prerr ": d2exp_int_tr_dn: Int_int_t0ype"; prerr_newline ();
                $Err.abort {s2exp} ()
              end // end of [_]
          ) : s2exp
          val () = $SOL.s2exp_equal_solve (loc0, s2exp_intinf icst, s2i)
        in
          d3exp_int (loc0, s2e0, istr, icst)
        end // [Int_int_t0ype]
      | _ when s2cstref_equ_cst (Size_int_t0ype, s2c) => let
          val () = szcheck (loc0, icst)
          val s2i = (case+ s2es_arg of
            | list_cons (s2e, _) => s2e
            | _ => begin
                prerr_interror ();
                prerr ": d2exp_int_tr_dn: Int_int_t0ype"; prerr_newline ();
                $Err.abort {s2exp} ()
              end // end of [_]
          ) : s2exp
          val () = $SOL.s2exp_equal_solve (loc0, s2exp_intinf icst, s2i)
        in
          d3exp_int (loc0, s2e0, istr, icst)
        end // [Size_int_t0ype]
      | _ => err (loc0, s2e0)
      end // end of [S2Ecst]
    | _ => d2exp_tr_dn_rest (d2e0, s2e0)
    end // end [S2Eapp]
  | S2Ecst s2c => begin case+ s2c of
    | _ when s2cstref_equ_cst (Int_t0ype, s2c) => begin
        d3exp_int (loc0, s2e0, istr, icst)
      end // end of [_ when ...]
    | _ when s2cstref_equ_cst (Size_t0ype, s2c) => let
        val () = szcheck (loc0, icst)
      in
        d3exp_int (loc0, s2e0, istr, icst)
      end // end of [_ when ...]
    | _ => err (loc0, s2e0)
    end // end of [S2Ecst]
  | _ => d2exp_tr_dn_rest (d2e0, s2e0)
end // end of [d2exp_int_tr_dn]

(* ****** ****** *)

fun labd2explst_tr_dn
  (loc0: loc_t, ld2es: labd2explst, ls2es: labs2explst): labd3explst =
  case+ (ld2es, ls2es) of
  | (LABD2EXPLSTcons (l1, d2e, ld2es), 
     LABS2EXPLSTcons (l2, s2e, ls2es)) => begin
      if l1 = l2 then let
        val d3e = d2exp_tr_dn (d2e, s2e) in
        LABD3EXPLSTcons (l1, d3e, labd2explst_tr_dn (loc0, ld2es, ls2es))
      end else begin
        prerr_loc_error3 d2e.d2exp_loc;
        $Deb.debug_prerrf (": %s: labd2explst_tr_dn", @(THISFILENAME));
        prerr ": label mismatch";
        prerr ": the label for the dynamic expression is [";
        prerr l1;
        prerr "] but it is expected to be [";
        prerr l2;
        prerr "].";
        prerr_newline ();
        $Err.abort {labd3explst} ()
      end // end of [if]
    end (* end of [LABD2EXPLSTcons, LABS2EXPLSTcons] *)
  | (LABD2EXPLSTnil (), LABS2EXPLSTnil ()) => LABD3EXPLSTnil ()
  | (LABD2EXPLSTcons (l1, _, _), LABS2EXPLSTnil ()) => begin
      prerr_loc_error3 loc0;
      $Deb.debug_prerrf (": %s: labd2explst_tr_dn", @(THISFILENAME));
      prerr ": the tuple/record needs fewer components";
      prerr ": a component with the label ["; prerr l1; prerr "] should be removed.";
      prerr_newline ();
      $Err.abort {labd3explst} ()
    end (* end of [LABD2EXPLSTcons, LABS2EXPLSTnil] *)
  | (LABD2EXPLSTnil (), LABS2EXPLSTcons (l2, _, _)) => begin
      prerr_loc_error3 loc0;
      $Deb.debug_prerrf (": %s: labd2explst_tr_dn", @(THISFILENAME));
      prerr ": the tuple/record needs more components";
      prerr ": a component with the label ["; prerr l2; prerr "] should be inserted.";
      prerr_newline ();
      $Err.abort {labd3explst} ()
    end (* end of [LABD2EXPLSTnil, LABS2EXPLSTcons] *)
// end of [labd2explst_tr_dn]

(* ****** ****** *)

fn d2exp_seq_tr_dn
  (loc0: loc_t, d2es: d2explst, s2e0: s2exp): d3exp = let
  fun aux (
      d2e: d2exp
    , d2es: d2explst
    , s2e0: s2exp, s2e_void: s2exp
    ) : d3explst = case+ d2es of
    | cons (d2e1, d2es1) => let
        val d3e = d2exp_tr_dn (d2e, s2e_void)
      in
        cons (d3e, aux (d2e1, d2es1, s2e0, s2e_void))
      end // end of [cons]
    | nil () => begin
        cons (d2exp_tr_dn (d2e, s2e0), nil ())
      end // end of [nil]
  // end of [aux]
  val s2e_void = s2exp_void_t0ype ()
in
  case+ d2es of
  | cons (d2e, d2es) => begin
      d3exp_seq (loc0, s2e0, aux (d2e, d2es, s2e0, s2e_void))
    end // end of [cons]
  | nil () => let
      val () = $SOL.s2exp_tyleq_solve (loc0, s2e_void, s2e0)
    in
      d3exp_empty (loc0, s2e0)
    end // end of [nil]
end // end of [d2exp_seq_tr_dn]

(* ****** ****** *)

fn d2exp_string_tr_dn
  (d2e0: d2exp, str: string, len: int, s2e0: s2exp): d3exp = let
  fn err (loc0: loc_t, s2e0: s2exp): d3exp = begin
    prerr_loc_error3 loc0;
    prerr ": the type ["; prerr s2e0;
    prerr "] cannot be assigned to a string constant.";
    prerr_newline ();
    $Err.abort {d3exp} ()
  end
  val loc0 = d2e0.d2exp_loc
  val s2e0 = s2exp_whnf s2e0
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
    case+ s2e_fun.s2exp_node of
    | S2Ecst s2c => begin case+ s2c of
      | _ when s2cstref_equ_cst (String_int_type, s2c) => let
          val s2i = (case+ s2es_arg of
            | list_cons (s2e, _) => s2e | _ => begin
                prerr_interror ();
                prerr ": d2exp_string_tr_dn: String_int_type"; prerr_newline ();
                $Err.abort {s2exp} ()
              end // end of [_]
          ) : s2exp // end of [val]
          val n = string0_length (str)
          val n = size1_of_size (n); val n = int1_of_size1 (n)
          val () = $SOL.s2exp_equal_solve (loc0, s2exp_int n, s2i)
        in
          d3exp_string (loc0, s2e0, str, len)
        end // [String_int_type]
      | _ when s2cstref_equ_cst (Printf_c_types_type, s2c) => let
          val s2e_arg = (case+ s2es_arg of
            | list_cons (s2e, _) => s2e | list_nil () => begin
                prerr_interror ();
                prerr ": d2exp_string_tr_dn: Printf_c_types_type"; prerr_newline ();
                $Err.abort {s2exp} ()
              end // end of [list_nil]
          ) : s2exp // end of [val]
          val fats = (case+ printf_c_string_parse (str) of
            | ~Some_vt (fats) => fats | ~None_vt () => begin
                prerr_loc_error3 loc0;
                prerr ": the c-format string is invalid."; prerr_newline ();
                $Err.abort ()
              end // end of [None_vt]
          ) : printf_c_argtypes // end of [val]
          val s2e_fats = s2exp_make_printf_c_argtypes fats
(*
          val () = begin
            print "d2exp_string_tr_dn: s2e_arg = "; print s2e_arg;
            print_newline ();
            print "d2exp_string_tr_dn: s2e_fats = "; print s2e_fats;
            print_newline ();
          end (* end of [val] *)
*)
          (* printf_c_types_type is contravariant! *)
          val () = $SOL.s2exp_tyleq_solve (loc0, s2e_arg, s2e_fats)
        in
          d3exp_string (loc0, s2e0, str, len)
        end // [Printf_c_types_type]
      | _ => err (loc0, s2e0)
      end // end of [S2Ecst]
    | _ => err (loc0, s2e0)
    end // end of [S2Eapp]
  | S2Ecst s2c => begin case+ s2c of
    | _ when s2cstref_equ_cst (String_type, s2c) => begin
        d3exp_string (loc0, s2e0, str, len)
      end
    | _ => err (loc0, s2e0)
    end // end of [S2Ecst]
  | _ => d2exp_tr_dn_rest (d2e0, s2e0)
end // end of [d2exp_string_tr_dn]

(* ****** ****** *)

implement
d2exp_tr_dn (d2e0, s2e0) = let
(*
val () = begin
  print "d2exp_tr_dn: d2e0 = "; print d2e0; print_newline ()
  print "d2exp_tr_dn: s2e0 = "; print s2e0; print_newline ()
end // end of [val]
*)
val loc0 = d2e0.d2exp_loc
val d3e0 = case+ d2e0.d2exp_node of
  | D2Eapps (d2e_fun, d2as_arg) => begin
    case+ d2e_fun.d2exp_node of
    | D2Emac d2m => let
        val d2e0 =
          $MAC.macro_eval_app_short (loc0, d2m, d2as_arg)
        // end of [val]
      in
        d2exp_tr_dn (d2e0, s2e0)
      end // end of [D2Emac]
    | _ => d2exp_tr_dn_rest (d2e0, s2e0)
    end // end of [D2Eapps]
  | D2Ecaseof (casknd, res, n, d2es, c2ls) => begin
      d2exp_caseof_tr_dn (loc0, casknd, res, n, d2es, c2ls, s2e0)
    end // end of [D2Ecaseof]
  | D2Eeffmask (effs, d2e) => let
      val (pf_effect | ()) = the_effect_env_push_effmask (effs)
      val d3e = d2exp_tr_dn (d2e, s2e0)
      val () = the_effect_env_pop (pf_effect | (*none*))
    in
      d3exp_effmask (loc0, effs, d3e)
    end // end of [D2Eeffmask]
  | D2Eexist (s2a, d2e) => let
      val s2e0 = s2exp_whnf s2e0
      val s2e = (case+ s2e0.s2exp_node of
        | S2Ewth (s2e1, wths2e2) => let
            val s2e1 = s2exp_exi_instantiate_sexparg (loc0, s2e1, s2a)
          in
            s2exp_wth (s2e1, wths2e2)
          end // end of [S2Ewth]
        | _ => s2exp_exi_instantiate_sexparg (loc0, s2e0, s2a)
      ) : s2exp
    in
      d2exp_tr_dn (d2e, s2e)
    end // end of [D2Eexist]
  | D2Efloat fcst => d2exp_float_tr_dn (d2e0, fcst, s2e0)
  | D2Eif (res, d2e_cond, d2e_then, od2e_else) => begin
      d2exp_if_tr_dn (loc0, res, d2e_cond, d2e_then, od2e_else, s2e0)
    end // end of [D2Eif]
  | D2Eint (istr, icst) => d2exp_int_tr_dn (d2e0, istr, icst, s2e0)
  | D2Elam_dyn (lin, npf, p2ts_arg, d2e_body) => let
(*
      val () = begin
        print "d2exp_tr_dn: D2Elam_dyn: p2ts_arg = "; print p2at_arg; print_newline ();
        print "d2exp_tr_dn: D2Elam_dyn: d2e_body = "; print d2e_body; print_newline ();
      end // end of [val]
*)
      val s2e0 = s2exp_whnf s2e0
    in
      case+ s2e0.s2exp_node of
      | S2Efun (
          fc_fun, lin_fun, s2fe_fun, npf_fun, s2es_fun_arg, s2e_fun_res
        ) => let
          val () = if lin <> lin_fun then begin // linearity check
            prerr_loc_error3 loc0;
            if lin > lin_fun then
              prerr " linear function is given a nonlinear type .";
            if lin < lin_fun then
              prerr " nonlinear function is given a linear type .";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [if]
          val () = if npf <> npf_fun then begin // pfarity check
            prerr_loc_error3 loc0;
            prerr ": this function is expected to have";
            if npf > npf_fun then prerr " fewer proof arguments.";
            if npf < npf_fun then prerr " more proof arguments.";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [if]
          val () = trans3_env_push_sta ()
          var ofc: funcloopt_vt
          val d2e_body = d2exp_funclo_opt_of_d2exp (d2e_body, ofc)
          val () = case+ ofc of
            | ~Some_vt fc => begin
                $SOL.funclo_equal_solve (loc0, fc, fc_fun)
              end // end of [Some_vt]
            | ~None_vt () => ()
          var os2fe: s2effopt_vt
          val d2e_body = d2exp_s2eff_opt_of_d2exp (d2e_body, os2fe)
          val () = case+ os2fe of
            | ~Some_vt s2fe => $SOL.s2eff_leq_solve (loc0, s2fe, s2fe_fun)
            | ~None_vt () => ()
          val (pf_effect | ()) = the_effect_env_push_lam s2fe_fun
          val (pf_d2varset | ()) = the_d2varset_env_push_lam lin
          val () = the_d2varset_env_add_p2atlst p2ts_arg
          val [sgn:int] sgn = $Lst.list_length_compare (p2ts_arg, s2es_fun_arg)
          val () = ( // arity check
            if sgn <> 0 then begin
              prerr_loc_error3 loc0;
              prerr ": the funcion is expected to have";
              if sgn > 0 then prerr " fewer arguments.";
              if sgn < 0 then prerr " more arguments.";
              prerr_newline ();
              $Err.abort ();
              assert (sgn = 0)
            end else begin
              () // [sgn = 0] holds!
            end
          ) : [sgn==0] void // end of [if]

          // checking for pattern match exhaustiveness
          val p2tcss = p2atcstlst_complement (p2atcstlst_of_p2atlst p2ts_arg)
(*
          val () = begin
            print "d2exp_tr_dn: D2Elam_dyn: p2tcss = "; print p2tcss; print_newline ()
          end // end of [val]
*)
//
          val cmplt = (
            case+ p2tcss of cons _ => 0(*incomplete*) | nil _ => 1
          ) : int
          val () = if cmplt = 0 then begin
            trans3_env_add_p2atcstlstlst_false (loc0, 1(*casknd*), p2tcss, s2es_fun_arg)
          end // end of [val]
//
          val p3ts_arg = p2atlst_arg_tr_dn (npf, p2ts_arg, s2es_fun_arg)
          val (pf_lamloop | ()) = the_lamloop_env_push_lam (p3ts_arg)
          val d3e_body = d2exp_tr_dn (d2e_body, s2e_fun_res)
          val () = the_d2varset_env_check loc0
          val () = if lin > 0 then the_d2varset_env_check_llam loc0
          val () = the_lamloop_env_pop (pf_lamloop | (*none*))
          val () = the_d2varset_env_pop_lam (pf_d2varset | (*none*))
          val () = the_effect_env_pop (pf_effect | (*none*))
          val () = trans3_env_pop_sta_and_add_none (loc0)
        in
          d3exp_lam_dyn (loc0, s2e0, lin, npf, p3ts_arg, d3e_body)
        end // end of [S2Efun]
      | S2Euni (s2vs, s2ps, s2e) => let
          val () = trans3_env_push_sta ()
          val () = trans3_env_add_svarlst s2vs
          val () = trans3_env_hypo_add_proplst (loc0, s2ps)
          val d3e0 = d2exp_tr_dn (d2e0, s2e)
          val () = trans3_env_pop_sta_and_add_none (loc0)
          val () = d3exp_set_typ (d3e0, s2e0)
        in
          d3e0
        end // end of [S2Euni]
      | _ when s2exp_is_non_fun s2e0 => begin
          prerr_loc_error3 loc0;
          prerr ": the function is assigned a non-function type [";
          prerr s2e0;
          prerr "].";
          prerr_newline ();
          $Err.abort {d3exp} ()
        end // end of [_]
      | _ => let
          val d3e0 = d2exp_tr_up d2e0 in d3exp_tr_dn (d3e0, s2e0); d3e0
        end // end of [let]
    end // end of [D2Elam_dyn]
  | D2Elist (npf, d2es) => let
      val d2e0 = d2exp_tup (loc0, 0(*knd*), npf, d2es)
    in
      d2exp_tr_dn (d2e0, s2e0)
    end // end of [D2Elist]
  | D2Elet (d2cs, d2e) => let
      val (pf_effect | ()) = the_effect_env_push ()
      val (pf_s2cstlst | ()) = the_s2cstlst_env_push ()
      val (pf_d2varset | ()) = the_d2varset_env_push_let ()
      val d3cs = d2eclst_tr d2cs
      val d3e = d2exp_tr_dn (d2e, s2e0)
      val () = the_d2varset_env_check loc0
      val () = the_d2varset_env_pop_let (pf_d2varset | (*none*))
      val () = the_s2cstlst_env_pop_and_unbind (pf_s2cstlst | (*none*))
      val () = the_effect_env_pop (pf_effect | (*none*))
    in
      d3exp_let (loc0, d3cs, d3e)
    end // end of [D2Elet]
  | D2Erec (recknd, npf1, ld2es) => let
      var iswth: int = 0
      val s2e0 = s2exp_whnf s2e0
      var s2e0: s2exp = s2e0
      val () =
        if s2exp_is_wth s2e0 then begin
          iswth := 1;
          s2e0 := s2exp_wth_instantiate (loc0, s2e0);
          s2e0 := s2exp_whnf s2e0
        end
      val s2e0 = s2e0
    in
      case+ s2e0.s2exp_node of
      | S2Etyrec (tyrecknd, npf2, ls2es) => let
          val () = reckind_check (loc0, recknd, tyrecknd)
          val () = pfarity_check_rec (loc0, npf1, npf2)
          val ld3es = labd2explst_tr_dn (loc0, ld2es, ls2es)
          val d3e0 = d3exp_rec (loc0, s2e0, recknd, npf1, ld3es)
          val () = if iswth > 0 then funarg_varfin_check (loc0)
        in
          d3e0
        end // end of [S2Etyrec]
      | _ when s2exp_is_non_tyrec s2e0 => begin
          prerr_loc_error3 loc0;
          prerr ": the record is assigned a non-record type [";
          prerr s2e0;
          prerr "].";
          prerr_newline ();
          $Err.abort {d3exp} ()
        end // end of [_ when ...]
      | _ => let
          val d3e0 = d2exp_tr_up d2e0
          val () = $SOL.s2exp_tyleq_solve (loc0, d3e0.d3exp_typ, s2e0)
          val () = if iswth > 0 then funarg_varfin_check (loc0)
          val () = d3exp_set_typ (d3e0, s2e0)
        in
          d3e0
        end // end of [_]
    end // end of [let]
  | D2Escaseof (res, s2e_val, sc2ls) => begin
      d2exp_scaseof_tr_dn (loc0, res, s2e_val, sc2ls, s2e0)
    end // end of [D2Escaseof]
  | D2Eseq d2es => d2exp_seq_tr_dn (loc0, d2es, s2e0)
  | D2Esif (res, s2p_cond, d2e_then, d2e_else) => begin
      d2exp_sif_tr_dn (loc0, res, s2p_cond, d2e_then, d2e_else, s2e0)
    end // end of [D2Esif]
  | D2Estring (str, len) => d2exp_string_tr_dn (d2e0, str, len, s2e0)
  | D2Estruct ld2es => let
      var iswth: int = 0
      val s2e0 = (
        if s2exp_is_wth s2e0 then begin
          iswth := 1; s2exp_wth_instantiate (loc0, s2e0)
        end else begin
          s2exp_whnf s2e0
        end
      ) : s2exp
    in
      case+ s2e0.s2exp_node of
      | S2Etyrec (tyrecknd, npf, ls2es) => let
          val () = (case+ tyrecknd of // flatness checking
            | TYRECKINDbox () => begin
                prerr_loc_error3 loc0;
                $Deb.debug_prerrf (": %s: d2exp_tr_dn", @(THISFILENAME));
                prerr ": the type for a struct cannot be boxed.";
                prerr_newline ();
                $Err.abort {void} ()
              end // end of [TYRECKINDbox]
            | TYRECKINDflt0 () => begin
                prerr_loc_error3 loc0;
                $Deb.debug_prerrf (": %s: d2exp_tr_dn", @(THISFILENAME));
                prerr ": the type for a struct cannot be a record type.";
                prerr_newline ();
                $Err.abort {void} ()
              end // end of [TYRECKINDflt0]
            | TYRECKINDflt1 _ => ()
            | TYRECKINDflt_ext _ => ()
          ) : void // end of [val]
          val () = if npf > 0 then begin
            prerr_loc_error3 loc0;
            $Deb.debug_prerrf (": %s: d2exp_tr_dn", @(THISFILENAME));
            prerr ": the proof arity of a struct cannot be [";
            prerr npf;
            prerr "].";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [val]
          val ld3es = labd2explst_tr_dn (loc0, ld2es, ls2es)
          val d3e0 = d3exp_struct (loc0, s2e0, ld3es)
          val () = if iswth > 0 then funarg_varfin_check (loc0)
        in
          d3e0
        end // end of [S2Etyrec]
      | _ when s2exp_is_non_fun s2e0 => begin
          prerr_loc_error3 loc0;
          prerr ": the struct is assigned a non-record type [";
          prerr s2e0;
          prerr "].";
          prerr_newline ();
          $Err.abort {d3exp} ()
        end // end of [_ when ...]
      | _ => begin
          prerr_loc_error3 loc0;
          $Deb.debug_prerrf (": %s: d2exp_tr_dn", @(THISFILENAME));
          prerr ": the struct is given a type of an incorrect form [";
          prerr s2e0;
          prerr "].";
          prerr_newline ();
          $Err.abort {d3exp} ()
        end // end of [_]
    end // end of [D2Estruct]
  | D2Etop () => begin
      // for datatype constructors taking uninitialized arguments
      d3exp_top (loc0, s2exp_topize_0 s2e0)
    end // end of [D2Etop]
  | D2Etrywith (r2es, d2e, c2ls) => let
      val (pf_d2varset | ()) = the_d2varset_env_push_try ()
(*
      // [r2es] is not in use; it is always [in2vresstate_nil]
      val r2es = i2nvresstate_update (r2es) // each var is replaced with its view
*)
      val d3e = d2exp_tr_dn (d2e, s2e0)
      val s2e_pat = s2exp_exception_viewtype ()
      val d3e_dummy = d3exp_top (d3e.d3exp_loc, s2e_pat)
      var cmplt: int = 0
      val c3ls = c2laulst_tr_dn (
        loc0, cmplt, ~1(*knd*), r2es, c2ls, '[d3e_dummy], 1, '[s2e_pat], s2e0
      ) // end of [c2laulst_tr_dn]
      val () = the_d2varset_env_pop_try (pf_d2varset | (*none*))
    in
      d3exp_trywith (loc0, d3e, c3ls)
    end // end of [D2Etrywith]
  | _ => d2exp_tr_dn_rest (d2e0, s2e0)
in
  d3e0
end // end of [d2exp_tr_dn]

(* ****** ****** *)

implement
d2exp_tr_dn_rest (d2e0, s2e0) = let
  val loc0 = d2e0.d2exp_loc
  var iswth: int = 0
  val d3e0 = d2exp_tr_up d2e0
  val s2e0: s2exp =
    if s2exp_is_wth s2e0 then let
      val () = iswth := 1; val () = d3exp_open_and_add d3e0
    in
      s2exp_wth_instantiate (loc0, s2e0)
    end else begin
      s2e0 // not a type with state
    end // end of [if]
  val () = $SOL.s2exp_tyleq_solve (loc0, d3e0.d3exp_typ, s2e0)
  val () = if iswth > 0 then funarg_varfin_check (loc0)
  val () = d3exp_set_typ (d3e0, s2e0)
in
  d3e0
end // end of [d2exp_tr_dn_rest]

(* ****** ****** *)

implement
assert_bool_tr_dn (loc0, b, s2e0) = let
  val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) when
      s2cstref_equ_exp (Bool_bool_t0ype, s2e_fun) => let
      val s2e_arg = case+ s2es_arg of
      | cons (s2e, _) => s2e
      | nil _ => begin
          prerr_loc_interror loc0;
          prerr ": assert_bool_tr_dn"; prerr_newline ();
          $Err.abort {s2exp} ()
        end // end of [nil]
      // end of [s2e_arg]
    in
      trans3_env_hypo_add_eqeq (loc0, s2exp_bool b, s2e_arg)
    end // end of [S2Eapp]
  | _ => begin
      $SOL.s2exp_tyleq_solve (loc0, s2e0, s2exp_bool_t0ype ())
    end // end of [_]
end // end of [assert_bool_tr_dn]

(* ****** ****** *)

fn m2atch_tr_up
  (m2at: m2atch): m3atch = let
  val loc0 = m2at.m2atch_loc
  val d3e = d2exp_tr_up (m2at.m2atch_exp)
  val op3t = (
    case+ m2at.m2atch_pat of
    | Some p2t => begin
        Some (p2at_tr_dn (p2t, d3e.d3exp_typ))
      end // end of [Some]
    | None () => let
        val () = assert_bool_tr_dn (loc0, true, d3e.d3exp_typ)
      in
        None ()
      end // end of [None]
  ) : p3atopt // end of [val]
in
  m3atch_make (loc0, d3e, op3t)
end // end of [m2atch_tr_up]

fn m2atchlst_tr_up (m2ats: m2atchlst): m3atchlst =
  $Lst.list_map_fun (m2ats, m2atch_tr_up)

implement
c2lau_tr_dn (
  c2l, op2tcss, d3es, n, s2es_pat, s2e0, osacsbis
) = let
  val loc0 = c2l.c2lau_loc
  val p2ts = c2l.c2lau_pat
(*
  val () = begin
    print "c2lau_tr_dn: p2ts = "; print p2ts; print_newline ();
    print "c2lau_tr_dn: s2es_pat = "; print s2es_pat; print_newline ();
    print "c2lau_tr_dn: s2e0 = "; print s2e0; print_newline ();
  end
*)
  val () = trans3_env_push_sta ()
  val (pf_d2varset | ()) = the_d2varset_env_push_let ()
  val () = the_d2varset_env_add_p2atlst (p2ts)
  val () = case+ op2tcss of
    | ~Some_vt p2tcss => begin // adding nonsequentiality assumptions
        trans3_env_hypo_add_p2atcstlstlst (loc0, p2tcss, s2es_pat)
      end // end of [Some_vt]
    | ~None_vt () => ()
  val p3ts = p2atlst_tr_dn (p2ts, s2es_pat)
//
  val () = aux (d3es, p3ts) where {
    fun aux {n:nat} (d3es: d3explst n, p3ts: p3atlst n): void =
      case+ d3es of
      | cons (d3e, d3es) => let
          val+ cons (p3t, p3ts) = p3ts
        in
          d3exp_lval_set_typ_pat (d3e, p3t); aux (d3es, p3ts)
        end // end of [cons]
      | nil () => () // end of [nil]
  } // end of [where]
//
  val gua = m2atchlst_tr_up (c2l.c2lau_gua)
  val seq = c2l.c2lau_seq and neg = c2l.c2lau_neg
  val d3e_exp = d2exp_tr_dn (c2l.c2lau_exp, s2e_exp) where {
    val s2e_exp = begin
      if neg > 0 then s2exp_bottom_viewt0ype_exi () else s2e0
    end // end of [val]
  } // end of [val]
//
  val () = case+ osacsbis of
    | ~SACSBISsome (sac, sbis) =>
        if c2lau_is_raised c2l then () else begin
          staftscstr_stbefitemlst_merge (loc0, sac, sbis)
        end // end of [if]
    | ~SACSBISnone () => ()
  val () = the_d2varset_env_check loc0
  val () = the_d2varset_env_pop_let (pf_d2varset | (*none*))
  val () = trans3_env_pop_sta_and_add_none (loc0)
in
  c3lau_make (loc0, p3ts, gua, seq, neg, d3e_exp)
end // end of [c2lau_tr_dn]

(* ****** ****** *)

fn pattern_match_is_redundant_errmsg
  (loc0: loc_t): void = begin
  prerr_loc_error3 loc0;
  prerr ": this pattern match clause is redundant."; prerr_newline ();
  $Err.abort {void} ()
end // end of [pattern_match_is_redundant_errmsg]

(* ****** ****** *)

fn
c2laulst0_tr_dn
  {n:nat} (
  loc0: loc_t
, casknd: int
, res: i2nvresstate
, n: int n, s2es_pat: s2explst n
, s2e0: s2exp
) : void = let
in
//
case+ 0 of
| _ when casknd = 0 => let
    val () = prerr_loc_warning3 (loc0)
    val () = prerr ": a case-expression is expected to have at least one match clause."
    val () = prerr_newline ()
  in
    // nothing
  end // end of [CK_case]
| _ when casknd > 0 => let
    val () = prerr_loc_error3 (loc0)
    val () = prerr ": a case+-expression is required to have at least one match clause."
    val () = prerr_newline ()
  in
    $Err.abort {void} ()
  end // end of [CK_case_pos]
| _ (*casknd < 0*) => ()
//
end // end of [c2laulst0_tr_dn]

fn
c2laulst1_tr_dn
  {n:nat} (
  loc0: loc_t
, cmplt: &int
, casknd: int
, res: i2nvresstate
, c2l: c2lau n
, d3es: d3explst n
, n: int n, s2es_pat: s2explst n
, s2e0: s2exp
) : c3lau n = let
  val p2tcss = c2lau_pat_complement c2l
  val () = case+ p2tcss of cons _ => () | nil _ => cmplt := 1
  val c3l = c2lau_tr_dn
    (c2l, None_vt (), d3es, n, s2es_pat, s2e0, SACSBISnone ())
  // checking for pattern matching exhaustiveness
  val () = if cmplt = 0 then begin
    trans3_env_add_p2atcstlstlst_false (loc0, casknd, p2tcss, s2es_pat)
  end // end of [val]
in
  c3l
end (* end of [c2laulst1_tr] *)

fun
c2laulst2_tr_dn
  {n:nat} (
  loc0: loc_t
, cmplt: &int
, casknd: int
, res: i2nvresstate
, c2l: c2lau n, c2ls: c2laulst n
, d3es: d3explst n
, n: int n, s2es_pat: s2explst n
, s2e0: s2exp
) : c3laulst n = let
(*
  val () = begin
    print "c2laulst2_tr_dn: s2es_pat = "; print s2es_pat; print_newline ();
  end // end of [val]
*)
//
  var
  p2tcss:
  p2atcstlstlst(n) =
  c2lau_pat_complement(c2l)
//
  val
  sbis =
  the_d2varset_env_stbefitemlst_save()
  val sac = staftscstr_initize(res, sbis)
//
  val c3l = c2lau_tr_dn
    (c2l, None_vt (), d3es, n, s2es_pat, s2e0, SACSBISsome (sac, sbis))
  val c3ls = c2laulst2_rest_tr_dn
    (loc0, casknd, c3l, c2ls, p2tcss, d3es, n, s2es_pat, s2e0, sac, sbis)
  val () = case+ p2tcss of cons _ => () | nil _ => cmplt := 1
  // checking for pattern matching exhaustiveness
  val () = if cmplt = 0 then begin
    trans3_env_add_p2atcstlstlst_false (loc0, casknd, p2tcss, s2es_pat)
  end // end of [val]
  val () = staftscstr_stbefitemlst_check (loc0, sac, sbis)
  val () = staftscstr_stbefitemlst_update (loc0, sac, sbis)
in
  c3ls
end (* end of [c2laulst2_tr_dn] *)

and c2laulst2_rest_tr_dn
  {n,ni:nat} (
  loc0: loc_t
, casknd: int
, c3l_fst: c3lau n
, c2ls_rst: c2laulst n
, p2tcss0: &p2atcstlstlst n
, d3es: d3explst n
, n: int n, s2es_pat: s2explst n
, s2e0: s2exp
, sac: staftscstr_t ni
, sbis: stbefitemlst ni
) : c3laulst n = let
//
  fun aux_main (
    c3ls: List_vt (c3lau n)
  , p2tcss0: &p2atcstlstlst n
  , c2ls: c2laulst n
  ) :<cloref1> c3laulst n = begin case+ c2ls of
  | cons (c2l, c2ls) => let
      val p2ts = c2l.c2lau_pat
      val p2tcs0 = p2atcstlst_of_p2atlst p2ts
(*
      val () = begin
        print "c2laulst2_rest_tr_dn: p2tcs0 = "; print p2tcs0; print_newline ();
        print "c2laulst2_rest_tr_dn: p2tcss0 = "; print p2tcss0; print_newline ();
      end (* end of [val] *)
*)
      val p2tcss1 = aux (p2tcss0, list_vt_nil ()) where {
        fun aux (
          p2tcss: p2atcstlstlst n
        , res: List_vt (p2atcstlst n)
        ) :<cloref1> p2atcstlstlst n =
        case+ p2tcss of
        | list_cons (p2tcs, p2tcss) => (
            if p2atcstlst_intersect_test (p2tcs, p2tcs0)
              then aux (p2tcss, list_vt_cons (p2tcs, res)) else aux (p2tcss, res)
            // end of [if]
          ) // end of [list_cons]
        | list_nil () => $Lst.list_vt_reverse_list (res)
      } // end of [where]
(*
      val () = begin
        print "c2laulst2_rest_tr_dn: p2tcss1 = "; print p2tcss1; print_newline ();
      end // end of [val]
*)
      val () = case+ p2tcss1 of
        | cons _ => ()
        | nil () => begin case+ casknd of
          | 0 => pattern_match_is_redundant_errmsg c2l.c2lau_loc
          | 1 => pattern_match_is_redundant_errmsg c2l.c2lau_loc
          | _ => ()        
          end
      val op2tcss = (
        if c2l.c2lau_seq > 0 then Some_vt p2tcss1 else None_vt ()
      ) : Option_vt (p2atcstlstlst n)
      val () = case+ c2l.c2lau_gua of
        | list_nil _ => p2tcss0 := aux (p2tcss0, nil ()) where {
            fun aux (
              p2tcss: p2atcstlstlst n, res: p2atcstlstlst n
              ) :<cloref1> p2atcstlstlst n = case+ p2tcss of
              | cons (p2tcs, p2tcss) => let
                  val p2tcss_diff = p2atcstlst_difference (p2tcs, p2tcs0)
                in
                  aux (p2tcss, $Lst.list_append (p2tcss_diff, res))
                end // end of [cons]
              | nil () => res
          } // end of [where]
        | list_cons _ => ()
      // end of [val]
(*
      val () = begin
        print "c2laulst_rest_tr_dn: p2tcss0 = "; print p2tcss0; print_newline ();
      end // end of [val]
*)
      val () = stbefitemlst_restore_lin_typ (sbis)
      val c3l = c2lau_tr_dn
        (c2l, op2tcss, d3es, n, s2es_pat, s2e0, SACSBISsome (sac, sbis))
      // end of [val]
    in
      aux_main (list_vt_cons (c3l, c3ls), p2tcss0, c2ls)
    end // end of [cons]
  | nil () => $Lst.list_vt_reverse_list c3ls
  end (* end of [aux_main] *)
  val c3ls_rst  = aux_main (list_vt_nil (), p2tcss0, c2ls_rst)
(*
  val () = begin
    print "c2laulst2_rest_tr_dn: p2tcss0 = "; print p2tcss0; print_newline ();
  end // end of [val]
*)
in
  c3l_fst :: c3ls_rst
end (* end of [c2laulst2_rest_tr_dn] *)

implement c2laulst_tr_dn
  (loc0, cmplt, casknd, res, c2ls, d3es, n, s2es_pat, s2e0) = begin
  case+ c2ls of
  | cons (c2l, c2ls) => begin case+ c2ls of
    | cons _ => c2laulst2_tr_dn (
        loc0, cmplt, casknd, res, c2l, c2ls, d3es, n, s2es_pat, s2e0
      ) // end [cons_]
    | nil () => let
        val c3l = c2laulst1_tr_dn
          (loc0, cmplt, casknd, res, c2l, d3es, n, s2es_pat, s2e0)
      in
        cons (c3l, nil ())
      end // end of [nil]
    end (* end of [cons] *)
  | nil () => let
      val () = c2laulst0_tr_dn (loc0, casknd, res, n, s2es_pat, s2e0)
    in
      nil ()
    end (* end of [nil] *)
end (* end of [c2laulst_tr_dn] *)

(* ****** ****** *)

implement
d2exp_caseof_tr_dn
  (loc0, casknd, r2es, n, d2es, c2ls, s2e0) = let
(*
  val () = begin
    print "d2exp_caseof_tr_dn: s2e0 = "; print_s2exp s2e0; print_newline ()
  end // end of [val]
*)
  val d3es = d2explst_tr_up d2es
  val () = d3explst_open_and_add d3es
  val s2es_pat = d3explst_get_typ d3es
  val r2es = i2nvresstate_update (r2es) // each var is replaced with its view
  var cmplt: int = 0
  val c3ls = c2laulst_tr_dn
    (loc0, cmplt, casknd, r2es, c2ls, d3es, n, s2es_pat, s2e0)
  val () = begin
    if cmplt = 0 then (if casknd < 1 then the_effect_env_check_exn (loc0))
  end // end of [val]
in
  d3exp_caseof (loc0, s2e0, casknd, d3es, c3ls)
end (* end of [d2exp_caseof_tr_dn] *)

(* ****** ****** *)

implement d2exp_scaseof_tr_dn
  (loc0, r2es, s2e_val, sc2ls, s2e0) = let
//
  val
  r2es = i2nvresstate_update (r2es)
  val
  sbis =
  the_d2varset_env_stbefitemlst_save ()
  val sac = staftscstr_initize (r2es, sbis)
//
  fun
  aux_one
  (
    sc2l: sc2lau
  ) :<cloref1> sc3lau = let
    val sp2t = sc2l.sc2lau_pat
    val d2e_body = sc2l.sc2lau_exp
    val () = trans3_env_push_sta ()
    val () = let
      val+ SP2Tcon (_, s2vs) = sp2t.sp2at_node in trans3_env_add_svarlst s2vs
    end // end of [val]
    val () = $SOL.s2exp_hypo_equal_solve (sp2t.sp2at_loc, s2e_val, sp2t.sp2at_exp)
    val d3e_body = d2exp_tr_dn (d2e_body, s2e0)
    val () = staftscstr_stbefitemlst_merge (loc0, sac, sbis)
    val () = trans3_env_pop_sta_and_add_none (d2e_body.d2exp_loc)
  in
    sc3lau_make (sc2l.sc2lau_loc, sp2t, d3e_body)
  end // end of [aux_one]

  fun aux_rest
    (sc2ls: sc2laulst):<cloref1> sc3laulst =
    case+ sc2ls of
    | list_cons (sc2l, sc2ls) => let
        val () = stbefitemlst_restore_lin_typ (sbis)
      in
        list_cons (aux_one sc2l, aux_rest sc2ls)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux_rest]

  val sc3ls = (case+ sc2ls of
    | list_cons (sc2l, sc2ls) => let
        val sc3l = aux_one (sc2l); val sc3ls = aux_rest (sc2ls)
      in
        list_cons (sc3l, sc3ls)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  ) : sc3laulst // end of [val]

  val () = staftscstr_stbefitemlst_check (loc0, sac, sbis)
  val () = staftscstr_stbefitemlst_update (loc0, sac, sbis)
in
  d3exp_scaseof (loc0, s2e0, s2e_val, sc3ls)
end // end of [d2exp_scaseof_tr_dn]

(* ****** ****** *)

(* end of [ats_trans3_exp_dn.dats] *)
