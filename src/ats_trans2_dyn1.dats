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
// Time: November 2007
//
(* ****** ****** *)

staload Arr = "ats_array.sats"
staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Glo = "ats_global.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload NS = "ats_namespace.sats"
staload PM = "ats_posmark.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload "ats_trans2.sats"

(* ****** ****** *)

staload MAC = "ats_macro2.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_array.dats"

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_symenv.dats"

(* ****** ****** *)

#define THISFILENAME "ats_trans2_dyn1.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef loc_t = $Loc.location_t
typedef funclo = $Syn.funclo
typedef funcloopt = $Syn.funcloopt
typedef efc = $Eff.effcst
typedef efcopt = Option efc
typedef sym_t = $Sym.symbol_t
typedef symopt_t = Option sym_t

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol

overload prerr with $Syn.prerr_d0ynq
overload prerr with $Sym.prerr_symbol
overload prerr with $Loc.prerr_location

(* ****** ****** *)

fn prerr_loc_error2
  (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(2)")
// end of [prerr_loc_error2]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans2_dyn1)"

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_trans2_dyn1)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

fn dyncstuseloc_posmark
  (loc: loc_t, d2c: d2cst_t): void = let
  val loc_d2c = d2cst_get_loc (d2c)
  val loc_begoff = $Loc.location_begpos_toff loc
  val () = $PM.posmark_insert_dyncstuse_beg (loc_begoff, loc_d2c)
  val loc_endoff = $Loc.location_endpos_toff loc
  val () = $PM.posmark_insert_dyncstuse_end (loc_endoff, loc_d2c)
in
  // empty
end // end of [dyncstuseloc_posmark]

(* ****** ****** *)

fun s2exp_arity_list
  (s2e: s2exp): List int = begin
  case+ s2e.s2exp_node of
  | S2Efun (_, _, _, _, s2es, s2e) => begin
      cons ($Lst.list_length s2es, s2exp_arity_list s2e)
    end // end of[S2Efun]
  | S2Eexi (_, _, s2e) => s2exp_arity_list s2e
  | S2Euni (_, _, s2e) => s2exp_arity_list s2e
  | S2Emetfn (_, _, s2e) => s2exp_arity_list s2e
  | _ => nil ()
end // end of [s2exp_arity_list]

(* ****** ****** *)

fn d1cstdec_tr (
    dck: $Syn.dcstkind, s2vpslst: s2qualst, d1c: d1cstdec
  ) : d2cst_t = let
  val id = d1c.d1cstdec_sym
  val loc = d1c.d1cstdec_loc
  val fil = d1c.d1cstdec_fil
  val typ = d1c.d1cstdec_typ
  var s2e_cst = (
//
// HX: it must be a prop or a t@ype; it cannot be linear
//
    if $Syn.dcstkind_is_proof (dck)
      then s1exp_tr_dn_prop (typ) else s1exp_tr_dn_t0ype (typ)
    // end of [if]
  ) : s2exp // end of [var]
  val arilst = s2exp_arity_list s2e_cst
  val extdef = d1c.d1cstdec_extdef
  val d2c = d2cst_make (id, fil, loc, dck, s2vpslst, arilst, s2e_cst, extdef)
in
  the_d2expenv_add_dcst d2c; d2c
end // end of [d1cstdec_tr]

implement
d1cstdeclst_tr
  (dck, s2vpslst, d1cs) = begin
  case+ d1cs of
  | cons (d1c, d1cs) => let
      val d2c = d1cstdec_tr (dck, s2vpslst, d1c)
    in
      cons (d2c, d1cstdeclst_tr (dck, s2vpslst, d1cs))
    end // end of [cons]
  | nil () => nil ()
end // end of [d1cstdeclst_tr]

(* ****** ****** *)

fn s1arg_arg_tr
  (s1a: s1arg): s2arg = begin
  s2arg_make (s1a.s1arg_loc, s1a.s1arg_sym, s1rtopt_tr s1a.s1arg_srt)
end // end of [s1arg_arg_tr]

fun s1arglst_arg_tr
  (s1as: s1arglst): s2arglst = begin case+ s1as of
  | cons (s1a, s1as) => cons (s1arg_arg_tr s1a, s1arglst_arg_tr s1as)
  | nil () => nil ()
end // end of [s1arglst_arg_tr]

(* ****** ****** *)

fun d2con_select_arity
  (d2cs: d2conlst, n: int): d2conlst = (
  case+ d2cs of
  | D2CONLSTcons (d2c, d2cs) =>
      if d2con_get_arity_full (d2c) = n then begin
        D2CONLSTcons (d2c, d2con_select_arity (d2cs, n))
      end else begin
        d2con_select_arity (d2cs, n)
      end // end of [if]
  | D2CONLSTnil () => D2CONLSTnil ()
) // end of [d2con_select_arity]

(*
//
// HX-2011-09-19: no longer in use
//
fun d2con_select_arity_err_some
  (loc_id: loc_t, q: d0ynq, id: sym_t, n: int): d2con_t = begin
  prerr_loc_error2 loc_id;
  prerr ": the dynamic identifier [";
  prerr q; prerr id;
  prerrf ("] refers to multiple constructors of arity %i.", @(n));
  prerr_newline ();
  $Err.abort {d2con_t} ()
end // end of [d2con_select_arity_err_some]
*)

fun d2con_select_arity_err_none
  (loc_id: loc_t, q: d0ynq, id: sym_t, n: int): d2con_t = begin
  prerr_loc_error2 loc_id;
  prerr ": the dynamic identifier [";
  prerr q; prerr id;
  prerrf ("] does not refer to any constructor of arity %i.", @(n));
  prerr_newline ();
  $Err.abort {d2con_t} ()
end // end of [d2con_select_arity_err_none]

(* ****** ****** *)

fun p1at_make_p1at
  (p1t: p1at): p1at = begin
  case+ p1t.p1at_node of
  | P1Tqid (q, id) => let
      val ans = the_d2expenv_find_qua (q, id)
    in
      case+ ans of
      | ~Some_vt d2i => begin case+ d2i of
        | D2ITEMe1xp e1xp => let
            val p1t = p1at_make_e1xp (p1t.p1at_loc, e1xp)
          in
            p1at_make_p1at (p1t)
          end // end of [D2ITEMe1xp]
        | _ => p1t // end of [_]
        end // end of [Some_vt]
      | ~None_vt () => p1t
    end // end of [P2Tqid]
  | _ => p1t
end // end of [p1at_make_p1at]

fun d1exp_make_d1exp
  (d1e: d1exp): d1exp = begin
  case+ d1e.d1exp_node of
  | D1Eqid (q, id) => let
      val ans = the_d2expenv_find_qua (q, id)
    in
      case+ ans of
      | ~Some_vt d2i => begin case+ d2i of
        | D2ITEMe1xp e1xp => let
            val d1e = d1exp_make_e1xp (d1e.d1exp_loc, e1xp)
          in
            d1exp_make_d1exp (d1e)
          end // end of [D2ITEMe1xp]
        | _ => d1e // end of [_]
        end // end of [Some_vt]
      | ~None_vt () => d1e // end of [_]
    end // end of [D1Eqid]
  | _ => d1e
end // end of [d1exp_make_d1exp]

(* ****** ****** *)

local // implementing [p1at_con_tr]

fun aux1
  (d2c: d2con_t, sub: stasub_t,
   s2vpslst: s2qualst, out: &s2qualst): s2exp = begin
  case+ s2vpslst of
  | cons (s2vps, s2vpslst) => let
      val @(sub, s2vs) = stasub_extend_svarlst (sub, s2vps.0)
      val s2ps = s2explst_subst (sub, s2vps.1)
    in
      out := @(s2vs, s2ps) :: out; aux1 (d2c, sub, s2vpslst, out)
    end // end of [cons]
  | nil () => let
      val npf = d2con_get_npf (d2c)
      val s2es_arg =
        s2explst_subst (sub, d2con_get_arg d2c)
      val s2c = d2con_get_scst d2c
      val s2e_res = (
        case+ d2con_get_ind d2c of
        | Some s2es_ind => let
            val s2es_ind = s2explst_subst (sub, s2es_ind)
          in
            s2exp_cstapp (s2c, s2es_ind)
          end // end of [Some]
        | None () => s2exp_cst s2c // end of [None]
      ) : s2exp // end of [val]
    in
      out := s2qualst_reverse out;
      s2exp_confun (npf, s2es_arg, s2e_res)
    end // end of [nil]
end // end [aux1]

fun aux2 (
    loc_sap: loc_t
  , d2c: d2con_t
  , sub: stasub_t
  , s2vpss: s2qualst
  , s1as: s1vararglst
  , out: &s2qualst
  ) : s2exp = let
  fn err (loc_sap: loc_t, d2c: d2con_t): s2exp = begin
    prerr_loc_error2 loc_sap;
    $Deb.debug_prerrf (": %s: p1at_con_tr: aux2", @(THISFILENAME));
    prerr ": the constructor [";
    prerr d2c;
    prerr "] is applied to too many static arguments.";
    prerr_newline ();
    $Err.abort {s2exp} ()
  end // end of [err]
in // in of [let]
  case+ s1as of
  | cons (s1a, s1as) => begin case+ s1a of
    | S1VARARGone () => begin case+ s2vpss of
      | cons (s2vps, s2vpss) => let
          val @(sub, s2vs) = stasub_extend_svarlst (sub, s2vps.0)
          val s2ps = s2explst_subst (sub, s2vps.1)
        in
          out := @(s2vs, s2ps) :: out;
          aux2 (loc_sap, d2c, sub, s2vpss, s1as, out)
        end // end of [cons]
      | nil () => err (loc_sap, d2c)
      end // end of [S1VARARGone]
    | S1VARARGall () => aux1 (d2c, sub, s2vpss, out)
    | S1VARARGseq arg => begin case+ s2vpss of
      | cons (s2vps, s2vpss) => let
          val arg = s1arglst_arg_tr arg
          val @(sub, s2vs) =
            stasub_extend_sarglst_svarlst (loc_sap, sub, arg, s2vps.0)
          val s2ps = s2explst_subst (sub, s2vps.1)
        in
          out := @(s2vs, s2ps) :: out;
          aux2 (loc_sap, d2c, sub, s2vpss, s1as, out)
        end // end of [cons]
      | nil () => err (loc_sap, d2c)
      end // end of [S1VARARGseq]
    end // end of [cons]
  | nil () => aux1 (d2c, sub, s2vpss, out)
end // end of [aux2]

in // in of [local]

fn p1at_con_tr (
    loc_dap: loc_t, loc_sap: loc_t
  , d2c: d2con_t, s1as: s1vararglst, npf: int, p1ts: p1atlst
  ) : p2at = let
  val s2vpss = d2con_get_qua (d2c)
  var out: s2qualst = nil ()
  val s2e = aux2 (loc_sap, d2c, stasub_nil, s2vpss, s1as, out)
  val p2ts = p1atlst_tr p1ts
in
  p2at_con (loc_dap, 1(*freeknd*), d2c, out, s2e, npf, p2ts)
end // end of [p1at_con_tr]

implement
p1at_con_instantiate (loc_sap, d2c) = let
  var out: s2qualst = nil (); val s2e = begin
    aux2 (loc_sap, d2c, stasub_nil, d2con_get_qua d2c, nil (), out)
  end // end of [val]
in
  @(out, s2e)
end // end of [p1at_con_instantiate]

end // end of [local]

(* ****** ****** *)

fn p1at_qid_app_dyn_tr (
    loc_dap: loc_t
  , loc_sap: loc_t
  , loc_id: loc_t
  , q: $Syn.d0ynq
  , id: sym_t
  , s1as: s1vararglst
  , npf: int
  , p1ts: p1atlst
  ) : p2at = let
//
  fn err1 (
      loc_id: loc_t, q: $Syn.d0ynq, id: sym_t
    ) : d2conlst = begin
    prerr_loc_error2 loc_id;
    $Deb.debug_prerrf (": %s: p1at_qid_app_dyn_tr", @(THISFILENAME));
    prerr ": the dynamic identifier [";
    prerr q; prerr id;
    prerr "] does not refer to a constructor.";
    prerr_newline ();
    $Err.abort {d2conlst} ()     
  end // end of [err1]
//
  fn err2 (
      loc_id: loc_t, q: $Syn.d0ynq, id: sym_t
    ) : d2conlst = begin
    prerr_loc_error2 loc_id;
    $Deb.debug_prerrf (": %s: p1at_qid_app_dyn_tr", @(THISFILENAME));
    prerr ": unrecognized dynamic constructor [";
    prerr q; prerr id;
    prerr "].";
    prerr_newline ();
    $Err.abort {d2conlst} ()
  end // end of [err2]
//
  val d2cs = let
    val ans = the_d2expenv_find_qua (q, id) in case+ ans of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMcon d2cs => d2cs | _ => err1 (loc_id, q, id)
      end // end of [Some_vt]
    | ~None_vt () => err2 (loc_id, q, id)
  end // end of [val]
  val is_arg_omit = (
    case+ p1ts of
    | cons (p1t, nil ()) => (
        case+ p1t.p1at_node of P1Tany () => true | _ => false
      ) // end of [cons (_, nil)]
    | _ => false // end of [_]
  ) : bool // end of [val]
  val np1ts = $Lst.list_length p1ts
  val d2cs = (
    if is_arg_omit then d2cs else d2con_select_arity (d2cs, np1ts)
  ) : d2conlst
  val d2c = begin case+ d2cs of
    | D2CONLSTcons (d2c, _) => d2c
(*
// HX-2011-09-19: removed due to being too clumsy
    | D2CONLSTcons (d2c, d2cs) => begin case+ d2cs of
      | D2CONLSTcons _ => begin
          d2con_select_arity_err_some (loc_id, q, id, np1ts)
        end
      | D2CONLSTnil _ => d2c
      end // end of [D2CONLSTcons]
*)
    | _ => begin
        d2con_select_arity_err_none (loc_id, q, id, np1ts)
      end // end of [_]
  end // end of [val]
  val p1ts = if is_arg_omit then begin
    case+ p1ts of
    | cons (p1t, nil ()) => let
        val npf = d2con_get_npf (d2c)
        and s2es = d2con_get_arg (d2c)
        fun aux (
          loc: loc_t, s2es: s2explst
        ) : p1atlst = case+ s2es of
          | cons (_, s2es) => cons (p1at_any loc, aux (loc, s2es))
          | nil () => nil ()
        // end of [aux]
      in
        aux (p1t.p1at_loc, s2es)
      end // end of [cons (_, nil)]
    | _ => p1ts // deadcode
  end else begin
    p1ts // there are no omitted arguments
  end // end of [val]
in
  p1at_con_tr (loc_dap, loc_sap, d2c, s1as, npf, p1ts)
end // end of [p1at_qid_app_dyn_tr]

(* ****** ****** *)

fn p1at_app_tr
  (loc_dap: loc_t, loc_sap: loc_t,
   p1t_fun: p1at, sarg: s1vararglst, npf: int, darg: p1atlst)
  : p2at = let
  val p1t_fun = p1at_make_p1at (p1t_fun)
in
  case+ p1t_fun.p1at_node of
  | P1Tqid (q, id) => let
      val loc_id = p1t_fun.p1at_loc
    in
      p1at_qid_app_dyn_tr (loc_dap, loc_sap, loc_id, q, id, sarg, npf, darg)
    end // end of [P1Tqid]
  | _ => begin
     prerr_loc_error2 loc_dap;
     $Deb.debug_prerrf (": %s: p1at_app_tr", @(THISFILENAME));
     prerr ": the application in the pattern is not allowed.";
     prerr_newline ();
     $Err.abort {p2at} ()
   end // end of [_]
end // end of [p1at_app_tr]

(* ****** ****** *)
//
// [freeknd]: 0: nonlinear; 1: preserve; ~1: free
//
fn p1at_free_tr (loc0: loc_t, p1t: p1at): p2at = let
  val p2t = p1at_tr p1t
in
  case+ p2t.p2at_node of
  | P2Tcon (freeknd, d2c, s2vpss, s2e, npf, p2ts) => begin
      p2at_con (loc0, ~freeknd, d2c, s2vpss, s2e, npf, p2ts)
    end // end of [P2Tcon]
  | _ => begin
      prerr_loc_error2 loc0;
      $Deb.debug_prerrf (": %s: p1at_free_tr", @(THISFILENAME));
      prerr ": values that match this pattern are not allowed to be freed.";
      prerr_newline ();
      $Err.abort {p2at} ()
    end // end of [_]
end // end of [p1at_free_tr]

(* ****** ****** *)

fn qid_is_vbox
  (q: $Syn.d0ynq, id: sym_t): bool = begin
  case+ q.d0ynq_node of
  | $Syn.D0YNQnone () => id = $Sym.symbol_VBOX | _ => false
end // end of [qid_is_vbox]

fn p1at_vbox_tr (loc: loc_t, npf: int, p1ts: p1atlst): p2at = let
//
  fn err {a:viewt@ype} (loc: loc_t): a = begin
    prerr_loc_error2 loc;
    prerr ": the [vbox] pattern is syntactically incorrect.";
    prerr_newline ();
    $Err.abort {a} ()
  end // end of [err]
//
  val () = if npf <> 0 then err {void} (loc) else ()
  val p1t = (
    case+ p1ts of cons (p1t, nil ()) => p1t | _ => err {p1at} (loc)
  ) : p1at
  val p2t = p1at_tr p1t
in
  case+ p2t.p2at_node of
  | P2Tvar (refknd, d2v) when refknd = 0 => p2at_vbox (loc, d2v)
  | _ => err {p2at} (loc)
end // end of [p2at_vbox_tr]

(* ****** ****** *)

implement
p1at_tr (p1t0) = let
//
val loc0 = p1t0.p1at_loc
var linearity_check: int = 0
//
val p2t0 = (
  case+ p1t0.p1at_node of
  | P1Tann (p1t, s1e) => let
      val p2t = p1at_tr p1t
      val s2e = s1exp_tr_dn_impredicative s1e
    in
      p2at_ann (loc0, p2t, s2e)
    end // end of [P1Tann]
  | P1Tany _ => p2at_any (loc0)
  | P1Tany2 _ => p2at_any (loc0)
  | P1Tapp_dyn (p1t_fun, _(*loc_arg*), npf, darg) => let
      val loc1 = p1t_fun.p1at_loc
      val p1t_fun = p1at_make_p1at p1t_fun
    in
      case+ p1t_fun.p1at_node of
      | P1Tqid (q, id) => begin case+ 0 of
        | _ when qid_is_vbox (q, id) => p1at_vbox_tr (loc0, npf, darg)
        | _ => begin
            linearity_check := 2;
            p1at_qid_app_dyn_tr (loc0, loc1, loc1, q, id, '[], npf, darg)
          end // end of [_]
        end (* end of [P1Tqid] *)
      | P1Tapp_sta (p1t_fun, sarg) => begin
          linearity_check := 2;
          p1at_app_tr (loc0, loc1, p1t_fun, sarg, npf, darg)
        end // end of [P1Tapp_sta]
      | _ => begin
          prerr_loc_error2 loc0;
          $Deb.debug_prerrf (": %s: p1at_tr", @(THISFILENAME));
          prerr ": the application in the pattern is not allowed.";
          prerr_newline ();
          $Err.abort {p2at} ()
        end // end of [_]
    end // end of [P1Tapp_dyn]
  | P1Tapp_sta (p1t_fun, sarg) => let
      val loc1 = p1t_fun.p1at_loc
      val () = (linearity_check := 1)
    in
      p1at_app_tr (loc0, loc1, p1t_fun, sarg, 0, '[])
    end // end of [P1Tapp_sta]
  | P1Tas (id, p1t) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
      val () = (linearity_check := 2)
    in
      p2at_as (loc0, 0(*refknd*), d2v, p1at_tr p1t)
    end // end of [P1Tas]
  | P1Tchar c(*char*) => p2at_char (loc0, c)
  | P1Texist (s1as, p1t) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val s2vs = s1arglst_var_tr s1as
      val p2t = p1at_tr p1t
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
      val () = (linearity_check := 1)
    in
      p2at_exist (loc0, s2vs, p2t)
    end // end of [P1Texist]
  | P1Tempty () => p2at_empty (loc0)
  | P1Tfloat f(*string*) => p2at_float (loc0, f)
  | P1Tfree p1t => p1at_free_tr (loc0, p1t)
  | P1Tint str(*string*) => let
      val int = $IntInf.intinf_make_string str
    in
      p2at_int (loc0, str, int)
    end // end of [P1Tint]
  | P1Tqid (q, id) => begin case+ q.d0ynq_node of
    | $Syn.D0YNQnone () => begin case+ the_d2expenv_find id of
      | ~Some_vt d2i => begin case+ d2i of
        | D2ITEMe1xp e1xp => begin
            let val p1t = p1at_make_e1xp (loc0, e1xp) in p1at_tr p1t end
          end // end of [D2ITEMe1xp]
//
// HX-2010-08-01: for handling [true] and [false] patterns
//
        | D2ITEMcst d2c => let
            val sym = d2cst_get_sym d2c in case+ 0 of
            | _ when sym = $Sym.symbol_TRUE => p2at_bool (loc0, true)
            | _ when sym = $Sym.symbol_FALSE => p2at_bool (loc0, false)
            | _ => p2at_var (loc0, 0(*refknd*), d2var_make (loc0, id))
          end // end of [D2ITEMcst]
//
        | _ => p2at_var (loc0, 0(*refknd*), d2var_make (loc0, id))
        end // end of [Some_vt]
      | ~None_vt () => p2at_var (loc0, 0(*refknd*), d2var_make (loc0, id))
      end // end of [D0YNQnone]
    | _ => begin
        p1at_qid_app_dyn_tr (loc0, loc0, loc0, q, id, '[], 0(*npf*), '[])
      end // end of [_]
    end // end of [P1Tqid]
  | P1Tlist (npf, p1ts) => (
    case+ p1ts of
    | cons _ => let
        val p2ts = p1atlst_tr p1ts
      in
        linearity_check := 2; p2at_tup (loc0, 0(*tupknd*), npf, p2ts)
      end // end of [cons]
    | nil _ => p2at_empty (loc0)
    ) // end of [P1Tlist]
  | P1Tlst (p1ts) => begin
      linearity_check := 2; p2at_lst (loc0, p1atlst_tr p1ts)
    end // end of [P1Tlst]
  | P1Trec (recknd, lp1ts) => let
      val lp2ts = labp1atlst_tr lp1ts
      val () = (linearity_check := 2)
    in
      p2at_rec (loc0, recknd, 0(*npf*), lp2ts)
    end // end of [P1Trec]
  | P1Tref (id) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
    in
      p2at_var (loc0, 1(*refknd*), d2v)
    end // end of [P1Tref]
  | P1Trefas (id, p1t) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
      val () = (linearity_check := 2)
    in
      p2at_as (loc0, 1(*refknd*), d2v, p1at_tr p1t)
    end // end of [P1Trefas]
  | P1Tstring str => p2at_string (loc0, str)
  | P1Tsvararg _ => begin
      prerr_loc_interror loc0;
      prerr ": p1at_tr: P1Tsvararg"; prerr_newline ();
      $Err.abort {p2at} ()
    end // end of [P1Tavararg]
  | P1Ttup (tupknd, npf, p1ts) => let
      val () = (linearity_check := 2) in
      p2at_tup (loc0, tupknd, npf, p1atlst_tr p1ts)
    end // end of [P1Ttup]
) : p2at // end of [val]
//
in // in of [p1at_tr]
//
if linearity_check >= 1 then begin
  s2varlstord_linearity_test (loc0, p2t0.p2at_svs);
end;
//
if linearity_check >= 2 then begin
  d2varlstord_linearity_test (loc0, p2t0.p2at_dvs);
end;
//
p2t0 // the return value
//
end // end of [p1at_tr]

implement
p1atlst_tr (p1ts) = $Lst.list_map_fun (p1ts, p1at_tr)

implement
labp1atlst_tr (lp1ts) = begin
  case+ lp1ts of
  | LABP1ATLSTcons (l0, p1t, lp1ts) => begin
      LABP2ATLSTcons (l0.l0ab_lab, p1at_tr p1t, labp1atlst_tr lp1ts)
    end // end of [LABP1ATLSTcons]
  | LABP1ATLSTnil () => LABP2ATLSTnil ()
  | LABP1ATLSTdot () => LABP2ATLSTdot ()
end // end of [labp1atlst_tr]

(* ****** ****** *)

implement
p1at_arg_tr
  (p1t0, wths1es) =
  case+ p1t0.p1at_node of
  | P1Tann (p1t, s1e) => let
      val p2t = p1at_tr p1t
      val s2e = s1exp_arg_tr_dn_impredicative (s1e, wths1es)
    in
      p2at_ann (p1t0.p1at_loc, p2t, s2e)
    end // end of [P1Tann]
  | P1Tlist (npf, p1ts) => let
      val p2ts = p1atlst_arg_tr (p1ts, wths1es)
    in
      p2at_list (p1t0.p1at_loc, npf, p2ts)
    end // end of [P1Tlist]
  | _ => p1at_tr (p1t0)
// end of [p1at_arg_tr]

implement
p1atlst_arg_tr
  (p1ts, wths1es) = case+ p1ts of
  | list_cons (p1t, p1ts) => let
      val p2t = p1at_arg_tr (p1t, wths1es)
      val p2t = (
        case+ p2t.p2at_node of
        | P2Tlist (npf, p2ts) =>
            p2at_tup (p2t.p2at_loc, 0(*tupknd*), npf, p2ts)
          // end of [P2Tlist]
        | _ => p2t // end of [_]
      ) : p2at // end of [val]
      val p2ts = p1atlst_arg_tr (p1ts, wths1es)
    in
      list_cons (p2t, p2ts)
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [p1atlst_arg_tr]

(* ****** ****** *)

fn d2sym_lrbrackets
  (loc: loc_t): d2sym = let
  val id = $Sym.symbol_LRBRACKETS
  var d2is0: d2itemlst = list_nil () and err: int = 0
  val () = begin case+ the_d2expenv_find (id) of
    | ~Some_vt d2i => begin
        case+ d2i of D2ITEMsymdef d2is => d2is0 := d2is | _ => err := 1
      end // end of [Some_vt]
    | ~None_vt () => (err := 1)
  end // end of [val]
  val () = if err > 0 then begin // run-time checking
    prerr_loc_interror loc; prerr ": d2sym_lrbrackets"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
in
  d2sym_make (loc, $Syn.d0ynq_none (), id, d2is0)
end // end of [d2sym_lrbrackets]

fn d1exp_arrsub_tr
  (loc0: loc_t, d1e_arr: d1exp, loc_ind: loc_t, d1ess_ind: d1explstlst)
  : d2exp = let
  val d2s = d2sym_lrbrackets (loc0)
  val d2e_arr = d1exp_tr d1e_arr
  val d2ess_ind = d1explstlst_tr d1ess_ind
in
  d2exp_arrsub (loc0, d2s, d2e_arr, loc_ind, d2ess_ind)
end // end of [d1exp_arrsub_tr]

(* ****** ****** *)

fn d1exp_assgn_tr
  (loc0: loc_t, d1es: d1explst): d2exp = begin
  case+ d1es of
  | cons (d1e1, cons (d1e2, nil ())) => begin
      d2exp_assgn (loc0, d1exp_tr d1e1, d1exp_tr d1e2)
    end
  | _ => begin
      prerr_loc_interror loc0; prerr ": d1exp_assgn_tr"; prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [_]
end // end of [d1exp_assgn_tr]

fn d1exp_deref_tr (
    loc0: loc_t, d1es: d1explst
  ) : d2exp = begin case+ d1es of
  | cons (d1e, nil ()) => d2exp_deref (loc0, d1exp_tr d1e)
  | _ => begin
      prerr_loc_interror loc0; prerr ": d1exp_deref_tr"; prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [_]
end // end of [d1exp_deref_tr]

(* ****** ****** *)

fn macro_def_check
  (loc0: loc_t, knd: int, id: sym_t): void = let
  val level = macro_level_get ()
in
  if level > 0 then begin
    if knd > 0 then begin (* long form *)
      prerr_loc_error2 loc0;
      prerr ": the identifier ["; prerr id;
      prerr "] refers to a macro definition in long form";
      prerr ", but one in short form is expected.";
      prerr_newline ();
      $Err.abort {void} ()
    end
  end else begin (* level = 0 *)
    if knd = 0 then begin (* short form *)
      prerr_loc_error2 loc0;
      prerr ": the identifier ["; prerr id;
      prerr "] refers to a macro definition in short form";
      prerr ", but one in long form is expected.";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
  end (* end of [if] *)
end (* end of [macro_def_check] *)

fn macro_var_check (
    loc0: loc_t, id: sym_t
  ) : void = let
  val level = macro_level_get ()
in
  if level > 0 then begin
    prerr_loc_error2 loc0;
    prerr ": the identifier ["; prerr id;
    prerr "] incorrectly refers to a macro argument variable.";
    prerr_newline ();
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [macro_var_check]

(* ****** ****** *)

dataviewtype
specdynid = SPDIDassgn | SPDIDderef | SPDIDnone
// end of [specdynid]

fn specdynid_of_qid
  (q: d0ynq, id: sym_t): specdynid = begin
  case+ q.d0ynq_node of
  | $Syn.D0YNQnone () => begin
      if id = $Sym.symbol_COLONEQ then SPDIDassgn ()
      else if id = $Sym.symbol_BANG then SPDIDderef ()
      else SPDIDnone ()        
    end // end of [D0YNQnone]
  | _ => SPDIDnone ()
end // end of [specdynid_of_qid]

(* ****** ****** *)

fn d1exp_qid_tr (
    loc0: loc_t, q: $Syn.d0ynq, id: sym_t
  ) : d2exp = let
  val ans = the_d2expenv_find_qua (q, id) in
  case+ ans of
  | ~Some_vt d2i => begin case+ d2i of
    | D2ITEMcon d2cs => let
        val d2cs = d2con_select_arity (d2cs, 0)
        val d2c: d2con_t = case+ d2cs of
          | D2CONLSTcons (d2c, _) => d2c
(*
// HX-2011-09-19: removed due to being too clumsy
          | D2CONLSTcons (d2c, d2cs) => begin case+ d2cs of
            | D2CONLSTcons _ => begin
                d2con_select_arity_err_some (loc0, q, id, 0)
              end // end of [D2CONLSTcons]
            | _ => d2c
            end // end of [D2CONLSTcons]
*)
          | _ => begin
              d2con_select_arity_err_none (loc0, q, id, 0)
            end // end of [_]
      in
        d2exp_con (loc0, d2c, nil (), 0(*npf*), nil ())
      end // end of [D2ITEMcon]
    | D2ITEMcst d2c => let
        val () = dyncstuseloc_posmark (loc0, d2c) in
        d2exp_cst (loc0, d2c)
      end // end of [D2ITEMcst]
    | D2ITEMe1xp e1xp => d1exp_tr (d1exp_make_e1xp (loc0, e1xp))
    | D2ITEMmacdef d2m => let
        val knd = d2mac_get_kind d2m
        val () = macro_def_check (loc0, knd, id)
      in
        d2exp_mac (loc0, d2m)
      end // end of [D2ITEMmacdef]
    | D2ITEMmacvar d2v => let
        val () = macro_var_check (loc0, id)
      in
        d2exp_var (loc0, d2v)
      end // end of [D2ITEMmacvar]
    | D2ITEMsymdef d2is => let
        val d2s = d2sym_make (loc0, q, id, d2is)
      in
        d2exp_sym (loc0, d2s)
      end // end of [D2ITEMsymdef]
    | D2ITEMvar d2v => d2exp_var (loc0, d2v)
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr_loc_error2 loc0;
      $Deb.debug_prerrf (": %s: d1exp_qid_tr", @(THISFILENAME));
      prerr ": the dynamic identifier [";
      prerr q; prerr id;
      prerr "] is unrecognized.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [None_vt]
end // end of [d1exp_qid_tr]

(* ****** ****** *)

fn d1exp_qid_app_sta_tr
  (loc_sap: loc_t, loc_id: loc_t, q: d0ynq, id: sym_t, s1as: s1exparglst)
  : d2exp = let
  val s2as = s1exparglst_tr s1as
  val od2i = the_d2expenv_find_qua (q, id)
in
  case+ od2i of
  | ~Some_vt d2i => begin case+ d2i of
    | D2ITEMcon d2cs => let
        val d2cs = d2con_select_arity (d2cs, 0)
        val d2c = (case+ d2cs of
          | D2CONLSTcons (d2c, _) => d2c
(*
// HX-2011-09-19: removed due to being too clumsy
          | D2CONLSTcons (d2c, d2cs) => begin case+ d2cs of
            | D2CONLSTcons _ =>
                d2con_select_arity_err_some (loc_id, q, id, 0)
              // end of [D2CONLSTcons]
            | _ => d2c
            end // end of [D2CONLSTcons]
*)
          | D2CONLSTnil _ => d2con_select_arity_err_none (loc_id, q, id, 0)
        ) : d2con_t // end of [val]
      in
        d2exp_con (loc_sap, d2c, s2as, 0(*npf*), nil ())
      end // end of [D2ITEMcon]
    | D2ITEMcst d2c => let
        val d2e_fun = d2exp_cst (loc_id, d2c)
      in
        d2exp_app_sta (loc_sap, d2e_fun, s2as)
      end // end of [D2ITEMcst]
    | D2ITEMvar d2v => let
        val d2e_fun = d2exp_var (loc_id, d2v)
      in
        d2exp_app_sta (loc_sap, d2e_fun, s2as)
      end // end of [D2ITEMvar]
    | D2ITEMmacdef _ => begin
        prerr_loc_error2 loc_id;
        $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
        prerr ": the identifier refers to a macro definition";
        prerr ", which cannot be applied to static arguments.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end // end of [D2ITEMmacdef]
    | D2ITEMmacvar _ => begin
        prerr_loc_error2 loc_id;
        $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
        prerr ": the identifier refers to a macro argument variable";
        prerr ", which cannot be applied.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end // end of [D2ITEMmacvar]
    | _ => begin
        prerr_loc_error2 loc_id;
        $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
        prerr ": the identifier refers to a dynamic term that cannot be applied.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end // end of [_]
    end (* end of [Some_vt] *)
  | ~None_vt () => begin
      prerr_loc_error2 loc_id;
      $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
      prerr ": unrecognized dynamic identifier [";
      prerr q; prerr id;
      prerr "]";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [None_vt]
end (* end of [d2exp_qid_app_sta_tr] *)

(* ****** ****** *)

fn d1exp_qid_app_dyn_tr (
    loc_dap: loc_t
  , loc_sap: loc_t
  , loc_qid: loc_t
  , q: d0ynq, id: sym_t // qid
  , sarg: s1exparglst
  , loc_arg: loc_t
  , npf: int, darg: d1explst
  ) : d2exp = let
  val sarg = s1exparglst_tr (sarg)
  val d2es_arg = d1explst_tr (darg)
  val od2i = the_d2expenv_find_qua (q, id)
in
  case+ od2i of
  | ~Some_vt d2i => begin case+ d2i of
    | D2ITEMcon d2cs => let
        val n = $Lst.list_length darg
        val d2cs = d2con_select_arity (d2cs, n)
        val d2c = (case+ d2cs of
          | D2CONLSTcons (d2c,__) => d2c
(*
// HX-2011-09-19: removed due to being too clumsy
          | D2CONLSTcons (d2c, _) => begin
              d2con_select_arity_err_some (loc_qid, q, id, n)
            end // end of [D2CONLST]
*)
          | D2CONLSTnil () => begin
              d2con_select_arity_err_none (loc_qid, q, id, n)
            end // end of [D2CONLSTnil]
        ) : d2con_t // end of [val]
      in
        d2exp_con (loc_dap, d2c, sarg, npf, d2es_arg)
      end // end of [D2ITEMcon]
    | D2ITEMcst d2c => let
//
        val () = dyncstuseloc_posmark (loc_qid, d2c)
//
        val d2e_fun = d2exp_cst (loc_qid, d2c) in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, d2es_arg)
      end // end of [D2ITEMcst]
    | D2ITEMe1xp _ => begin
        prerr_loc_interror loc_qid;
        prerr ": d1exp_qid_app_dyn_tr: D2ITEMe1xp"; prerr_newline ();
        $Err.abort {d2exp} ()
      end // end of [D2ITEMe1xp]
    | D2ITEMmacdef d2m => let
        val knd = d2mac_get_kind d2m
        val () = macro_def_check (loc_qid, knd, id)
        val d2e_fun = d2exp_mac (loc_qid, d2m)
      in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, d2es_arg)
      end // end of [D2ITEMmacdef]
    | D2ITEMmacvar _ => begin
        prerr_loc_error2 loc_qid;
        prerr ": the identifer refers to a macro argument variable";
        prerr ", which cannot be applied.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end // end of [D2ITEMmacvar]
    | D2ITEMsymdef d2is => let
        val d2s =
          d2sym_make (loc_qid, q, id, d2is)
        // end of [val]
        val d2e_fun = d2exp_sym (loc_qid, d2s) in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, d2es_arg)
      end // end of [D2ITEMsym]
    | D2ITEMvar d2v => let
        val d2e_fun = d2exp_var (loc_qid, d2v) in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, d2es_arg)
      end // end of [D2ITEMvar]
    end (* end of [Some_vt] *)
  | ~None_vt () => begin
      prerr_loc_error2 loc_qid;
      $Deb.debug_prerrf (": %s: d1exp_qid_app_dyn_tr", @(THISFILENAME));
      prerr ": the dynamic identifier [";
      prerr q; prerr id;
      prerr "] is unrecognized.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [None_vt]
end (* end of [d1exp_qid_app_dyn_tr] *)

(* ****** ****** *)

fun d1exp_idextapp_tr (
  loc0: loc_t, id: sym_t, d1es: d1explst
) : d2exp = begin
//
case+ 0 of
| _ => let
    val () = prerr_loc_error2 (loc0)
    val () = (
      prerr ": the external id ["; prerr id; prerr "] cannot be handled."
    ) // end of [val]
    val () = prerr_newline ()
  in
    $Err.abort {d2exp} ()
  end // end of [_]
//
end // end of [d1exp_idextapp_tr]
  
(* ****** ****** *)

// [wths1es] is assumed to be not empty
fun d1exp_wths1explst_tr
  (d1e0: d1exp, wths1es: wths1explst): d2exp = begin
  case+ d1e0.d1exp_node of
  | D1Eann_type (d1e, s1e) => let
      val d2e = d1exp_tr d1e
      val s2e = s1exp_res_tr_dn_impredicative (s1e, wths1es)
    in
      d2exp_ann_type (d1e0.d1exp_loc, d2e, s2e)
    end // end of [D1Eann_type]
  | D1Eann_effc (d1e, efc) => let
      val d2e = d1exp_wths1explst_tr (d1e, wths1es)
      val s2fe = effcst_tr (efc)
    in
      d2exp_ann_seff (d1e0.d1exp_loc, d2e, s2fe)
    end // end of [D1Eann_effc]
  | D1Eann_funclo (d1e, fc) => let
      val d2e = d1exp_wths1explst_tr (d1e, wths1es)
    in
      d2exp_ann_funclo (d1e0.d1exp_loc, d2e, fc)
    end // end of[D1Eann_funclo]
  | _ => begin
      prerr_loc_error2 d1e0.d1exp_loc;
      $Deb.debug_prerrf (": %s: d1exp_wths1explst_tr", @(THISFILENAME));
      prerr ": the dynamic expression is expected to be ascribed a type but it is not.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [_]
end (* end of [d1exp_wths1explst_tr] *)

(* ****** ****** *)

fun i1nvarglst_tr
  (xs: i1nvarglst): i2nvarglst = begin case+ xs of
  | cons (x, xs) => begin
    case+ the_d2expenv_find x.i1nvarg_sym of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMvar d2v => let
          val os2e = (case+ x.i1nvarg_typ of
            | Some s1e => Some (s1exp_tr_dn_impredicative s1e)
            | None () => None ()
          ) : s2expopt
          val arg = i2nvarg_make (d2v, os2e)
        in
          cons (arg, i1nvarglst_tr xs)
        end // end of [D2ITEMvar]
      | _ => begin
          prerr_loc_error2 x.i1nvarg_loc;
          $Deb.debug_prerrf (": %s: i1nvarglst_tr", @(THISFILENAME));
          prerr ": the dynamic identifier [";
          prerr x.i1nvarg_sym;
          prerr "] does not refer to a variable.";
          prerr_newline ();
          $Err.abort ()
        end // end of [_]
      end (* end of [Some_vt] *)
    | ~None_vt () => begin
        prerr_loc_error2 x.i1nvarg_loc;
        $Deb.debug_prerrf (": %s: i1nvarglst_tr", @(THISFILENAME));
        prerr ": the dynamic identifier [";
        prerr x.i1nvarg_sym;
        prerr "] is unrecognized.";
        prerr_newline ();
        $Err.abort ()
      end // end of [None_vt]
    end (* end of [cons] *)
  | nil () => nil ()
end // end of [i1nvarglst_tr]

fn i1nvresstate_tr
  (r1es: i1nvresstate): i2nvresstate = let
  val @(s2vs, s2ps) = s1qualst_tr (r1es.i1nvresstate_qua)
  val body = i1nvarglst_tr r1es.i1nvresstate_arg
in
  i2nvresstate_make (s2vs, s2ps, body)
end // end of [i1nvresstate_tr]

fn loopi1nv_tr (inv: loopi1nv): loopi2nv = let
  val @(s2vs, s2ps) = s1qualst_tr (inv.loopi1nv_qua)
  val met = (case+ inv.loopi1nv_met of
    | Some s1es => Some (s1explst_tr_dn_int s1es) | None () => None ()
  ) : s2explstopt
  val arg = i1nvarglst_tr inv.loopi1nv_arg
  val res = i1nvresstate_tr inv.loopi1nv_res
in
  loopi2nv_make (inv.loopi1nv_loc, s2vs, s2ps, met, arg, res)
end // end of [loopi1nv_tr]

(* ****** ****** *)

fn m1atch_tr
  (m1at: m1atch): m2atch = let
  val d2e = d1exp_tr (m1at.m1atch_exp)
  val op2t = (case+ m1at.m1atch_pat of
    | Some p1t => let
        val p2t = p1at_tr p1t
        val s2vs = s2varlst_of_s2varlstord (p2t.p2at_svs)
        val () = the_s2expenv_add_svarlst s2vs
        val d2vs = d2varlst_of_d2varlstord (p2t.p2at_dvs)
        val () = the_d2expenv_add_dvarlst d2vs
      in
        Some p2t
      end // end of [Some]
    | None () => None ()
  ) : p2atopt // end of [val]
in
  m2atch_make (m1at.m1atch_loc, d2e, op2t)
end // end of [m1atch_tr]

fn m1atchlst_tr (m1ats: m1atchlst)
  : m2atchlst = $Lst.list_map_fun (m1ats, m1atch_tr)
// end of [m1atchlst_tr]

(* ****** ****** *)

fn c1lau_tr {n:nat} (n: int n, c1l: c1lau): c2lau n = let
  val p1t = c1l.c1lau_pat
  val p1ts = (
    case+ p1t.p1at_node of
    | P1Tlist (_(*npf*), p1ts) => p1ts | _ => cons (p1t, nil ())
  ) : p1atlst
  val p2ts: p2atlst = p1atlst_tr p1ts
  stavar np2ts: int
  val np2ts: int np2ts = $Lst.list_length p2ts
(*
  val () = begin
    printf ("c1lau_tr: n = %i and np2ts = %i\n", @(n, np2ts))
  end // end of [val]
*)
  val () = (if np2ts <> n then begin
    prerr_loc_error2 c1l.c1lau_loc;
    $Deb.debug_prerrf (": %s: c1lau_tr", @(THISFILENAME));
    if np2ts < n then prerr ": this clause should contain more patterns.";
    if np2ts > n then prerr ": this clause should contain fewer patterns.";
    prerr_newline ();
    $Err.abort {void} ();
    assert (np2ts = n) // deadcode
  end else begin
    () // [np2ts = n] holds!
  end) : [np2ts==n] void // end of [val]
  val (pf_env2 | ()) = trans2_env_push ()
  val () = let
    val s2vs = s2varlst_of_s2varlstord (p2atlst_svs_union p2ts)
  in
    the_s2expenv_add_svarlst s2vs
  end // end of [val]
  val () = let
    val d2vs = d2varlst_of_d2varlstord (p2atlst_dvs_union p2ts)
  in
    the_d2expenv_add_dvarlst d2vs
  end // end of [val]
  val gua = m1atchlst_tr (c1l.c1lau_gua)
  val d2e = d1exp_tr (c1l.c1lau_exp)
  val () = trans2_env_pop (pf_env2 | (*none*))
in
  c2lau_make (c1l.c1lau_loc, p2ts, gua, c1l.c1lau_seq, c1l.c1lau_neg, d2e)
end // end of [c1lau_tr]

fun c1laulst_tr {n:nat}
  (n: int n, c1ls: c1laulst): c2laulst n = begin case+ c1ls of
  | cons (c1l, c1ls) => cons (c1lau_tr (n, c1l), c1laulst_tr (n, c1ls))
  | nil () => nil ()
end // end of [c1laulst_tr]

(* ****** ****** *)

fn sc1lau_tr_dn
  (sc1l: sc1lau, s2t_pat: s2rt): sc2lau = let
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val sp2t = sp1at_tr_dn (sc1l.sc1lau_pat, s2t_pat)
  val d2e = d1exp_tr (sc1l.sc1lau_exp)
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))  
in
  sc2lau_make (sc1l.sc1lau_loc, sp2t, d2e)
end // end of [sc1lau_tr]

fun sc1laulst_tr_dn
  (sc1ls: sc1laulst, s2t_pat: s2rt): sc2laulst =
  case+ sc1ls of
  | list_cons (sc1l, sc1ls) => let
      val sc2l = sc1lau_tr_dn (sc1l, s2t_pat)
      val sc2ls = sc1laulst_tr_dn (sc1ls, s2t_pat)
    in
      list_cons (sc2l, sc2ls)
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [sc1laulst_tr_dn]

fn sc2laulst_covercheck
  (loc0: loc_t, sc2ls: sc2laulst, s2t_pat: s2rt): void = let
  val s2tb_pat = (case+ s2t_pat of
    | S2RTbas s2tb => s2tb | _ => begin
        prerr_loc_error2 loc0;
        prerr ": the static expression being analyzed is of the sort [";
        prerr s2t_pat; prerr "], which is not a base sort as is required.";
        prerr_newline ();
        $Err.abort {s2rtbas} ()
      end // end of [_]
  ) : s2rtbas // end of [val]
  val s2tdat_pat = (case+ s2tb_pat of
    | S2RTBASdef s2td => s2td | _ => begin
        prerr_loc_error2 loc0;
        prerr ": the static expression being analyzed is of the sort [";
        prerr s2t_pat; prerr "], which is not a datasort as is required.";
        prerr_newline ();
        $Err.abort {s2rtdat_t} ()
      end // end of [_]
  ) : s2rtdat_t // end of [val]
  val s2cs = s2rtdat_get_conlst (s2tdat_pat)
  val ns2cs = s2cstlst_length (s2cs)
  val (pf_gc, pf_arr | A) = $Arr.array_ptr_make_elt<int> (ns2cs, 0)
  val () = check (pf_arr | A, ns2cs, sc2ls) where {
    fun check {n:nat} {l:addr} (
        pf: !array_v (int, n, l) | p: ptr l, n: int n, sc2ls: sc2laulst
      ) : void = case+ sc2ls of
      | list_cons (sc2l, sc2ls) => let
          val sp2t = sc2l.sc2lau_pat
          val+ SP2Tcon (s2c, _) = sp2t.sp2at_node
          val tag = s2cst_get_tag (s2c); val tag = int1_of_int tag
          val () = assert (tag >= 0); val () = assert (tag < n)
          val () = (p->[tag] := p->[tag] + 1) // end of [val]
        in
          check (pf | p, n, sc2ls)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [check]
  } // end of [val]
  val err = loop_errmsg
    (pf_arr | loc0, A, ns2cs, s2cs, 0, 0) where {
    fun loop_errmsg {n,i:nat | i <= n} {l:addr} .<n-i>. (
        pf: !array_v (int, n, l)
      | loc0: loc_t, p: ptr l, n: int n, s2cs: s2cstlst, i: int i, err: int
      ) : int =
      if i < n then let
        val times = p->[i] in case+ s2cs of
        | S2CSTLSTcons (s2c, s2cs) => begin case+ 0 of
          | _ when times = 1 => loop_errmsg (pf | loc0, p, n, s2cs, i+1, err)
          | _ when times = 0 => begin
              prerr_loc_error2 loc0;
              prerr ": ill-formed static case-expression";
              prerr ": the constructor ["; prerr s2c; prerr "] is missing.";
              prerr_newline ();
              loop_errmsg (pf | loc0, p, n, s2cs, i+1, err+1)
            end // end of [_ when times = 0]
          | _ (* times > 1 *) => begin
              prerr_loc_error2 loc0;
              prerr ": ill-formed static case-expression";
              prerr ": the constructor ["; prerr s2c; prerr "] occurs repeatedly.";
              prerr_newline ();
              loop_errmsg (pf | loc0, p, n, s2cs, i+1, err+1)
            end // end of [_ when times > 0]
          end (* end of [S2CSTLSTcons] *)
        | S2CSTLSTnil () => err // deadcode!
      end else begin
        err // loop exists
      end (* end of [if] *)
  } (* end of [loop_errmsg] *)
  val () = $Arr.array_ptr_free {int} (pf_gc, pf_arr | A)
  val () = if err > 0 then $Err.abort {void} ()
in
  // empty
end // end of [sc2laulst_covercheck]

(* ****** ****** *)

fn lamvararg_proc
  (p2ts: p2atlst): p2atlst = let
  fun proc (p2ts: p2atlst, flag: &int): p2atlst =
    case+ p2ts of
    | list_cons (p2t, p2ts1) => begin case+ p2t.p2at_node of
      | P2Tann (p2t1, s2e1) => (case+ 0 of
          | _ when s2exp_is_types (s2e1) => begin case+ p2ts1 of
            | list_nil () => let
                val p2t = p2at_ann (p2t.p2at_loc, p2t1, s2exp_vararg s2e1)
                val () = flag := flag + 1
              in
                list_cons (p2t, list_nil ())
              end // end of [list_nil]
            | list_cons _ => begin
                prerr_loc_error2 p2t.p2at_loc;
                $Deb.debug_prerrf (": %s: lamvararg_proc: proc", @(THISFILENAME));
                prerr ": this function argument must be the last one.";
                prerr_newline ();
                $Err.abort ()
              end // end of [list_cons]
            end // end of [_ when ...]
          | _ => let
              val flag0 = flag; val p2ts1 = proc (p2ts1, flag)
            in
              if flag > flag0 then list_cons (p2t, p2ts1) else p2ts
            end // end of [_]
        ) // end of [P2Tann]
      | _ => let
          val flag0 = flag; val p2ts1 = proc (p2ts1, flag)
        in
          if flag > flag0 then list_cons (p2t, p2ts1) else p2ts
        end // end of [_]
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [proc]
  var flag: int = 0
in
  proc (p2ts, flag)
end // end of [lamvararg_proc]

fn d1exp_arg_body_tr
  (p1t_arg: p1at, d1e_body: d1exp)
  : @(int, p2atlst, d2exp) = let
  var wths1es = WTHS1EXPLSTnil ()
  val p2t_arg = p1at_arg_tr (p1t_arg, wths1es)
  val () = wths1es := wths1explst_reverse wths1es
  var npf: int = 0
  val p2ts_arg = (
    case+ p2t_arg.p2at_node of
    | P2Tlist (npf1, p2ts) => (npf := npf1; p2ts)
    | _ => cons (p2t_arg, nil ())
  ) : p2atlst
  val (pf_env | ()) = trans2_env_push ()
  val () = let
    val s2vs = s2varlst_of_s2varlstord p2t_arg.p2at_svs
  in
    the_s2expenv_add_svarlst s2vs
  end // end of [val]
  val () = let
    val d2vs = d2varlst_of_d2varlstord p2t_arg.p2at_dvs
  in
    the_d2expenv_add_dvarlst d2vs
  end // end of [val]
  val (pf_level | ()) = d2var_current_level_inc ()
  val d2e_body = begin
    if wths1explst_is_none wths1es then begin
      d1exp_tr d1e_body // regular translation
    end else begin
      d1exp_wths1explst_tr (d1e_body, wths1es)
    end // end of [if]
  end : d2exp // end of [val]
  val () = d2var_current_level_dec (pf_level | (*none*))
  val () = trans2_env_pop (pf_env | (*none*))
//
  val p2ts_arg = lamvararg_proc (p2ts_arg) // HX-2010-08-26: for handling variadic functions
//
in
  @(npf, p2ts_arg, d2e_body)
end // end of [d1exp_arg_body_tr]

(* ****** ****** *)

implement
d1exp_tr (d1e0) = let
(*
  val () = begin
    print "d1exp_tr: d1e0 = "; print_d1exp d1e0; print_newline ()
  end // end of [val]
*)
  val loc0 = d1e0.d1exp_loc
in
  case+ d1e0.d1exp_node of
  | D1Eann_type (d1e, s1e) => let
      val d2e = d1exp_tr d1e
      val s2e = s1exp_tr_dn_impredicative (s1e)
    in
      d2exp_ann_type (loc0, d2e, s2e)
    end // end of [D1Eann_type]
  | D1Eann_effc (d1e, efc) => let
      val d2e = d1exp_tr d1e; val s2fe = effcst_tr (efc)
    in
      d2exp_ann_seff (loc0, d2e, s2fe)
    end // end of [D1Eann_effc]
  | D1Eann_funclo (d1e, fc) => let
      val d2e = d1exp_tr d1e in d2exp_ann_funclo (loc0, d2e, fc)
    end // end of [D1Efunclo]
  | D1Eapp_dyn (
      d1e_fun, loc_arg, npf, darg
    ) => let
      val loc1 = d1e_fun.d1exp_loc
      val d1e_fun = d1exp_make_d1exp (d1e_fun)
    in
      case+ d1e_fun.d1exp_node of
      | D1Eqid (q, id) => let
          val spdid = specdynid_of_qid (q, id)
        in
          case+ spdid of
          | ~SPDIDnone () => d1exp_qid_app_dyn_tr (
              loc0, loc1, loc1, q, id, '[], loc_arg, npf, darg
            ) // end of [SPDIDnone]
          | ~SPDIDassgn () => d1exp_assgn_tr (loc0, darg)
          | ~SPDIDderef () => d1exp_deref_tr (loc0, darg)
        end // end of [D1Eapp_dyn]
      | D1Eapp_sta (d1e_fun, sarg) => let
          val d1e_fun = d1exp_make_d1exp d1e_fun
        in
          case+ d1e_fun.d1exp_node of
          | D1Eqid (q, id) => let
              val loc_qid = d1e_fun.d1exp_loc
            in
              d1exp_qid_app_dyn_tr (
                loc0, loc1, loc_qid, q, id, sarg, loc_arg, npf, darg
              ) // end of [d1exp_qid_app_dyn_tr]
            end // end of [D1Eqid]
          | _ => let
              val d2e_fun = d1exp_tr d1e_fun
              val sarg = s1exparglst_tr sarg
              val d2es_arg = d1explst_tr (darg)
            in
              d2exp_app_sta_dyn (
                loc0, loc1, d2e_fun, sarg, loc_arg, npf, d2es_arg
              ) // end of [d1exp_app_sta_dyn]
            end // end of [_]
        end // end of [D1Eapp_sta]
      | _ => let
          val d2e_fun = d1exp_tr d1e_fun
          val d2es_arg = d1explst_tr (darg)
        in
          d2exp_app_dyn (loc0, d2e_fun, loc_arg, npf, d2es_arg)
        end // end of [_]
    end // end of [D1Eapp_dyn]
  | D1Eapp_sta (d1e_fun, sarg) => let
      val d1e_fun = d1exp_make_d1exp d1e_fun
    in
      case+ d1e_fun.d1exp_node of
      | D1Eqid (q, id) => begin
          d1exp_qid_app_sta_tr (loc0, d1e_fun.d1exp_loc, q, id, sarg)
        end // end of [D1Eqid]
      | _ => let
          val d2e_fun = d1exp_tr d1e_fun
          val sarg = s1exparglst_tr sarg
        in
          d2exp_app_sta (loc0, d2e_fun, sarg)
        end // end of [_]
    end // end of [D1Eapp_sta]
  | D1Earrinit (s1e_elt, od1e_asz, d1es_elt) => let
      val s2t_elt = (case+ od1e_asz of
        | Some _ => begin case+ d1es_elt of
          | list_cons _ (*initialized*) => s2rt_t0ype // cannot be linear
          | list_nil () (*uninitialized*) => s2rt_viewt0ype // can be linear
          end // end of [Some]
        | None () => s2rt_viewt0ype // can be linear
      ) : s2rt // end of [val]
      val s2e_elt = s1exp_tr_dn (s1e_elt, s2t_elt)
      val od2e_asz = d1expopt_tr od1e_asz; val d2es_elt = d1explst_tr d1es_elt
    in
      d2exp_arrinit (loc0, s2e_elt, od2e_asz, d2es_elt)
    end // end of [D1Earrinit]
  | D1Earrpsz (os1e_elt, d1es_elt) => let
      val os2e_elt = (case+ os1e_elt of
        | Some s1e => Some (s1exp_tr_dn (s1e, s2rt_viewt0ype))
        | None () => None ()
      ) : s2expopt // end of [val]
      val d2es_elt = d1explst_tr d1es_elt
    in
      d2exp_arrpsz (loc0, os2e_elt, d2es_elt)
    end // end of [D1Earrpsz]
  | D1Earrsub (d1e_arr, loc_ind, d1ess_ind) => begin
      d1exp_arrsub_tr (loc0, d1e_arr, loc_ind, d1ess_ind)
    end // end of [D1Earrsub]
  | D1Ebool tf => d2exp_bool (loc0, tf)
  | D1Echar chr => d2exp_char (loc0, chr)
  | D1Ecstsp cst => d2exp_cstsp (loc0, cst)
  | D1Ecaseof (knd, r1es, d1es, c1ls) => let
      val r2es = i1nvresstate_tr r1es
      val d2es = d1explst_tr d1es
      val nd2es = $Lst.list_length d2es
      val c2ls = c1laulst_tr (nd2es, c1ls)
    in
      d2exp_caseof (loc0, knd, r2es, nd2es, d2es, c2ls)
    end // end of [D1Ecaseof]
  | D1Ecrypt (knd, d1e) => begin
      d2exp_crypt (loc0, knd, d1exp_tr d1e)
    end // end of [D1Ecrypt]
//
  | D1Edecseq (d1cs) => let
      val (pf_env | ()) = trans2_env_push ()
      val d2cs = d1eclst_tr (d1cs)
      val () = trans2_env_pop (pf_env | (*none*))
      val d2e = d2exp_empty (loc0)
    in
      d2exp_let (loc0, d2cs, d2e)
    end // end of [D1Edecseq]
//
  | D1Edynload fil => d2exp_dynload (loc0, fil)
  | D1Eeffmask (effs, d1e) => begin
      d2exp_effmask (loc0, effs, d1exp_tr d1e)
    end // end of [D1Eeffmask]
  | D1Eempty () => d2exp_empty (loc0)
  | D1Eexist (s1a, d1e) =>
      d2exp_exist (loc0, s1exparg_tr s1a, d1exp_tr d1e)
  | D1Eextval (s1e, code) =>
      d2exp_extval (loc0, s1exp_tr_dn_viewt0ype s1e, code)
  | D1Efix (knd, id, d1e_def) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
      val () = d2var_set_isfix (d2v, true)
      val (pf_d2expenv | ()) = the_d2expenv_push ()
      val () = the_d2expenv_add_dvar d2v
      val d2e_def = d1exp_tr (d1e_def)
      val () = the_d2expenv_pop (pf_d2expenv | (*none*))
    in
      d2exp_fix (loc0, knd, d2v, d2e_def)
    end // end of [D1Efix]
  | D1Efloat f(*string*) => d2exp_float (d1e0.d1exp_loc, f)
  | D1Efloatsp f(*string*) => d2exp_floatsp (d1e0.d1exp_loc, f)
  | D1Efoldat (s1as, d1e) => begin
      d2exp_foldat (loc0, s1exparglst_tr s1as, d1exp_tr d1e)
    end // end of [D1Efoldat]
  | D1Efor (
      inv, ini, test, post, body
    ) => let
      val ini = d1exp_tr ini
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val inv = loopi1nv_tr inv
      val test = (case+ test.d1exp_node of
        | D1Eempty () => d2exp_bool (loc0, true) | _ => d1exp_tr test
      ) : d2exp // end of [val]
      val post = d1exp_tr post
      val body = d1exp_tr body
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2exp_for (loc0, inv, ini, test, post, body)
    end // end of [D1Efor]
  | D1Efreeat (s1as, d1e) => begin
      d2exp_freeat (loc0, s1exparglst_tr s1as, d1exp_tr d1e)
    end // end of [D1Efreeat]
  | D1Eidextapp (id, _(*ns*), d1es) => d1exp_idextapp_tr (loc0, id, d1es)
  | D1Eif (
      r1es, d1e_cond, d1e_then, od1e_else
    ) => let
      val r2es = i1nvresstate_tr r1es
      val d2e_cond = d1exp_tr d1e_cond
      val d2e_then = d1exp_tr d1e_then
      val od2e_else = d1expopt_tr od1e_else
    in
      d2exp_if (loc0, r2es, d2e_cond, d2e_then, od2e_else)
    end // end of [D1Eif]
  | D1Eint str(*string*) => begin
      d2exp_int (loc0, str, $IntInf.intinf_make_string str)
    end // end of [D1Eint]
  | D1Eintsp str(*string*) => begin
      d2exp_intsp (loc0, str, $IntInf.intinf_make_stringsp str)
    end // end of [D1Eintsp]
  | D1Elam_dyn (lin, p1t_arg, d1e_body) => let
      val @(npf, p2ts_arg, d2e_body) = d1exp_arg_body_tr (p1t_arg, d1e_body)
    in
      d2exp_lam_dyn (loc0, lin, npf, p2ts_arg, d2e_body)
    end // end of [D1Elam_dyn]
  | D1Elaminit_dyn (lin, p1t_arg, d1e_body) => let
      val @(npf, p2ts_arg, d2e_body) = d1exp_arg_body_tr (p1t_arg, d1e_body)
    in
      d2exp_laminit_dyn (loc0, lin, npf, p2ts_arg, d2e_body)
    end // end of [D1Elam_dyn]
  | D1Elam_met (_, met, body) => let
      val met = s1explst_tr_up met; val body = d1exp_tr body
    in
      d2exp_lam_met_new (loc0, met, body)
    end // end of [D1Elam_met]
  | D1Elam_sta_ana _ => begin
      prerr_loc_error2 loc0;
      $Deb.debug_prerrf (": %s: d1exp_tr: D1Elam_sta_ana: ", @(THISFILENAME));
      prerr ": illegal use of static lambda-abstraction in analysis form.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [D1Elam_sta_ana]
  | D1Elam_sta_syn (_, s1qs, d1e) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val @(s2vs, s2ps) = s1qualst_tr (s1qs)
      val d2e = d1exp_tr d1e
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2exp_lam_sta (loc0, s2vs, s2ps, d2e)
    end // end of [D1Elam_sta_syn]
  | D1Elazy_delay (lin, d1e) => begin case+ 0 of
    | _ when lin = 0 => let
        val d2e = d1exp_tr d1e in d2exp_lazy_delay (loc0, d2e)
      end // end of [_ when lin = 0]
    | _ (* lin = 1 *) => begin case+ d1e.d1exp_node of
      | D1Elist (_(*npf*), d1es) => begin case+ d1es of
        | cons (d1e1, cons (d1e2, nil ())) => let
            val d2e1 = d1exp_tr d1e1 and d2e2 = d1exp_tr d1e2
          in
            d2exp_lazy_ldelay (loc0, d2e1, d2e2)
          end // end of [cons (_, cons (_, nil))]
        | _ => $Err.abort {d2exp} () where {
            val n = $Lst.list_length d1es
            val () = prerr_loc_error2 loc0
            val () = if n > 2 then prerr ": fewer arguments should be given."
            val () = if n < 2 then prerr ": more arguments should be given."
            val () = prerr_newline ()
          } // end of [_]
        end // end of [D1Elist]
      | _ => let
          val d2e1 = d1exp_tr d1e and d2e2 = d2exp_empty (d1e.d1exp_loc)
        in
          d2exp_lazy_ldelay (loc0, d2e1, d2e2)
        end // end of [_]
      end // end of [_ when lin = 1]
    end (* end of [D1Elazy_delay] *)
  | D1Elet (d1cs, d1e) => let
      val (pf_env | ()) = trans2_env_push ()
      val d2cs = d1eclst_tr d1cs; val d2e = d1exp_tr d1e
      val () = trans2_env_pop (pf_env | (*none*))
    in
      d2exp_let (loc0, d2cs, d2e)
    end // end of [D1Elet]
  | D1Elist (npf, d1es) => let
    in
      case+ d1es of
      | cons _ => let
          val d2es = d1explst_tr d1es in d2exp_list (loc0, npf, d2es)
        end // end of [cons]
      | nil () => d2exp_empty (loc0)
    end // end of [D1Elist]
  | D1Eloopexn flag => d2exp_loopexn (loc0, flag)
  | D1Elst (lin, os1e_elt, d1es_elt) => let
      val s2t_elt: s2rt =
        if lin > 0 then s2rt_viewt0ype else s2rt_t0ype
      val os2e_elt = (
        case+ os1e_elt of
        | Some s1e_elt => Some (s1exp_tr_dn (s1e_elt, s2t_elt))
        | None () => None ()
      ) : s2expopt // end of [val]
      val d2es_elt = d1explst_tr (d1es_elt)
    in
      d2exp_lst (loc0, lin, os2e_elt, d2es_elt)
    end // end of [D1Elst]
  | D1Emacsyn (knd, d1e) => let
(*
      val () = begin
        print "d1exp_tr: D1Emacsyn: knd = "; print d1e; print_newline ();
        print "d1exp_tr: D1Emacsyn: d1e = "; print d1e; print_newline ();
      end // end of [val]
*)
    in
      case+ knd of
      | $Syn.MACSYNKINDcross () => let
          // val mdef = macdef_get ()
          val () = macro_level_dec (loc0)
          // val level = macro_level_get ()
          val d2e0 = d2exp_macsyn (loc0, knd, d1exp_tr d1e)
          val () = macro_level_inc (loc0)
        in
          d2e0 // if (mdef + level = 0) then $MAC.macro_eval_cross (d2e0) else d2e0
        end // end of [MACSYNKINDcross]
      | $Syn.MACSYNKINDdecode () => let
          // val mdef = macdef_get ()
          val () = macro_level_dec (loc0)
          // val level = macro_level_get ()
          val d2e0 = d2exp_macsyn (loc0, knd, d1exp_tr d1e)
          val () = macro_level_inc (loc0)
        in
          d2e0 // if (mdef + level = 0) then $MAC.macro_eval_decode (d2e0) else d2e0
        end // end of [MACSYNKINDdecode]
      | $Syn.MACSYNKINDencode () => let
          val () = macro_level_inc (loc0)
          val d2e0 = d2exp_macsyn (loc0, knd, d1exp_tr d1e)
          val () = macro_level_dec (loc0)
        in
          d2e0
        end // end of [DACSYNKINDencode]
    end // end of [D1Emacsyn]
(*
  | D1Emod (m1ids) => d2exp_mod (loc, mid1_list_tr m1ids)
*)
  | D1Eqid (q, id) => d1exp_qid_tr (loc0, q, id)
  | D1Eptrof d1e => d2exp_ptrof (loc0, d1exp_tr d1e)
  | D1Eraise (d1e) => begin
      d2exp_raise (loc0, d1exp_tr d1e)
    end // end of [D1Eraise]
  | D1Erec (recknd, ld1es) => begin
      d2exp_rec (loc0, recknd, 0(*npf*), labd1explst_tr ld1es)
    end // end of [D1Erec]
  | D1Escaseof (r1es, s1e, sc1ls) => let
      val r2es = i1nvresstate_tr r1es
      val s2e = s1exp_tr_up s1e; val s2t_pat = s2e.s2exp_srt
      val sc2ls = sc1laulst_tr_dn (sc1ls, s2t_pat)
      val () = sc2laulst_covercheck (loc0, sc2ls, s2t_pat)
    in
      d2exp_scaseof (loc0, r2es, s2e, sc2ls)
    end // end of [D1Escaseof]
  | D1Esel (ptr, d1e, d1l) => let
      val d2e = d1exp_tr d1e; val d2l = d1lab_tr d1l
    in
      if ptr > 0 then d2exp_sel_ptr (loc0, d2e, d2l)
      else begin case+ d2e.d2exp_node of
      | D2Esel (d2e_root, d2ls) => begin
          d2exp_sel (loc0, d2e_root, $Lst.list_extend (d2ls, d2l))
        end
       | _ => begin
          d2exp_sel (loc0, d2e, cons (d2l, nil ()))
         end // end of [_]
      end // end of [if]
    end (* end of [D1Esel] *)
  | D1Eseq d1es => d2exp_seq (d1e0.d1exp_loc, d1explst_tr d1es)
  | D1Eshowtype (d1e) => begin
      d2exp_showtype (loc0, d1exp_tr d1e)
    end // end of [D1Eshowtype]
  | D1Esif (r1es, s1e_cond, d1e_then, d1e_else) => let
      val r2es = i1nvresstate_tr r1es
      val s2e_cond = s1exp_tr_dn_bool s1e_cond
      val d2e_then = d1exp_tr d1e_then
      val d2e_else = d1exp_tr d1e_else
    in
      d2exp_sif (loc0, r2es, s2e_cond, d2e_then, d2e_else)
    end // end of [D1Esif]
  | D1Estring (str, len) => d2exp_string (loc0, str, len)
  | D1Estruct ld1es => d2exp_struct (loc0, labd1explst_tr ld1es)
  | D1Etmpid (qid, ts1ess) => let
      val loc_id = qid.tmpqi0de_loc
      val q = qid.tmpqi0de_qua and id = qid.tmpqi0de_sym
      val d2e_qid = d1exp_qid_tr (loc_id, q, id)
      val ts2ess = tmps1explstlst_tr_up ts1ess
    in
      d2exp_tmpid (loc0, d2e_qid, ts2ess)
    end // end of [D1Etmpid]
  | D1Etop () => d2exp_top (loc0)
  | D1Etrywith (r1es, d1e, c1ls) => let
      val r2es = i1nvresstate_tr r1es
      val d2e = d1exp_tr d1e; val c2ls = c1laulst_tr (1, c1ls)
    in
      d2exp_trywith (loc0, r2es, d2e, c2ls)
    end // end of [D1Etrywith]
  | D1Etup (tupknd, npf, d1es) => begin
      d2exp_tup (loc0, tupknd, npf, d1explst_tr d1es)
    end // end of [D1Etup]
  | D1Eviewat d1e => d2exp_viewat (loc0, d1exp_tr d1e)
  | D1Ewhere (d1e, d1cs) => let
      val (pf_env | ()) = trans2_env_push ()
      val d2cs = d1eclst_tr d1cs; val d2e = d1exp_tr d1e
      val () = trans2_env_pop (pf_env | (*none*))
    in
      d2exp_where (loc0, d2e, d2cs)
    end // end of [D1Ewhere]
  | D1Ewhile (inv, test, body) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val inv = loopi1nv_tr inv
      val test = d1exp_tr test
      val body = d1exp_tr body
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2exp_while (loc0, inv, test, body)
    end // end of [D1Ewhile]
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": d1exp_tr: d1e0 = "; prerr_d1exp d1e0; prerr_newline ();
      $Err.abort {d2exp} ()
    end // end of [_]
end // end of [d1exp_tr]

implement
d1explst_tr (d1es) = $Lst.list_map_fun (d1es, d1exp_tr)
implement
d1explstlst_tr (d1ess) = $Lst.list_map_fun (d1ess, d1explst_tr)

implement
d1expopt_tr (od1e) = case+ od1e of
  | Some d1e => Some (d1exp_tr d1e) | None () => None ()
// end of [d1expopt_tr]

implement
labd1explst_tr (ld1es) = case+ ld1es of
  | LABD1EXPLSTcons (l0, d1e, ld1es) =>
      LABD2EXPLSTcons (l0.l0ab_lab, d1exp_tr d1e, labd1explst_tr ld1es)
  | LABD1EXPLSTnil () => LABD2EXPLSTnil ()
// end of [labd1explst_tr]

implement
d1lab_tr (d1l) = case+ d1l.d1lab_node of
  | D1LABlab lab => d2lab_lab (d1l.d1lab_loc, lab)
  | D1LABind ind => d2lab_ind (d1l.d1lab_loc, d1explstlst_tr ind)
// end of [d1lab_tr]

(* ****** ****** *)

(* end of [ats_trans2_dyn1.dats] *)
