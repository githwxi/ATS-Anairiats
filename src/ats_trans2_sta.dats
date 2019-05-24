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

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload PM = "ats_posmark.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans2_env.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

staload "ats_trans2.sats"

(* ****** ****** *)

#define THISFILENAME "ats_trans2_sta.dats"

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

(* ****** ****** *)

fn prerr_loc_error2 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(2)")
// end of [prerr_loc_error2]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans2_sta)"

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_trans2_sta)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

fn stacstuseloc_posmark
  (loc: loc_t, s2c: s2cst_t): void = let
  val loc_s2c = s2cst_get_loc (s2c)
  val loc_begoff = $Loc.location_begpos_toff loc
  val () = $PM.posmark_insert_stacstuse_beg (loc_begoff, loc_s2c)
  val loc_endoff = $Loc.location_endpos_toff loc
  val () = $PM.posmark_insert_stacstuse_end (loc_endoff, loc_s2c)
in
  // empty
end // end of [stacstuseloc_posmark]

(* ****** ****** *)

fun s1rt_app_tr (
    loc0: loc_t
  , s1t_fun: s1rt
  , s1ts_arg: s1rtlst
  ) : s2rt = begin case+ 0 of
  | _ when s1rt_is_arrow s1t_fun => begin
    case+ s1ts_arg of
    | cons (s1t1, cons (s1t2, nil ())) => let
        val s1ts1 = (
          case+ s1t1.s1rt_node of
          | S1RTlist s1ts => s1ts | _ => cons (s1t1, nil ())
        ) : s1rtlst
        val s2ts1 = s1rtlst_tr s1ts1 and s2t2 = s1rt_tr s1t2
      in
        S2RTfun (s2ts1, s2t2)
      end
    | _ => begin
        prerr_interror ();
        prerr ": [s1rt_app_tr]: [->] is not an infix operator!";
        prerr_newline ();
        $Err.abort {s2rt} ()
      end // end of [_]
    end // end of [s1rt_is_arrow]
  | _ => begin
      prerr_loc_error2 loc0;
      $Deb.debug_prerrf (": %s: s1rt_app_tr", @(THISFILENAME));
      prerr ": sort application is not supported.";
      prerr_newline ();
      $Err.abort {s2rt} ()
    end // end of [_]
end // end of [s1rt_app_tr]

implement
s1rt_tr (s1t0) = begin
  case+ s1t0.s1rt_node of
  | S1RTapp (s1t, s1ts) => begin
(*
      print "s1rt_tr: S1RTapp: "; print s1t0.s1rt_loc; print_newline ();
*)
      s1rt_app_tr (s1t0.s1rt_loc, s1t, s1ts)
    end // end of [S1RTapp]
  | S1RTlist s1ts => S2RTtup (s1rtlst_tr s1ts) 
  | S1RTqid (q, id) => begin
    case+ the_s2rtenv_find_qua (q, id) of
    | ~Some_vt s2te => begin case+ s2te of
      | S2TEsrt s2t => s2t | _ => begin
          prerr_loc_error2 s1t0.s1rt_loc;
          $Deb.debug_prerrf (": %s: s1rt_tr", @(THISFILENAME));
          prerr ": the identifier ["; $Sym.prerr_symbol id;
          prerr "] refers to an extended sort but not a sort.";
          prerr_newline ();
          $Err.abort ()
        end // end of [_]
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr_loc_error2 s1t0.s1rt_loc;
        $Deb.debug_prerrf (": %s: s1rt_tr", @(THISFILENAME));
        prerr ": the identifier [";
        $Syn.prerr_s0rtq q; $Sym.prerr_symbol id;
        prerr "] refers to an unrecognized sort.";
        prerr_newline ();
        $Err.abort ()
      end // end of [None_vt]
    end // end of [S1RTqid]
  | S1RTtup s1ts => S2RTtup (s1rtlst_tr s1ts)
(*
  | _ => begin
      prerr_loc_interror s1t0.s1rt_loc;
      prerr ": not yet implemented: ["; prerr s1t0; prerr "]";
      prerr_newline ();
      $Err.abort ()
    end // end of [_]
*)
end // end of [s1rt_tr]

implement
s1rtlst_tr (s1ts) = begin case+ s1ts of
  | cons (s1t, s1ts) => cons (s1rt_tr s1t, s1rtlst_tr s1ts)
  | nil () => nil ()
end // end of [s1rtlst_tr]

implement
s1rtopt_tr (os1t) = begin case+ os1t of
  | Some s1t => Some (s1rt_tr s1t) | None () => None () 
end // end of [s1rtopt_tr]

(* ****** ****** *)

(* static special identifier *)
datatype staspecid = SPSIDarrow | SPSIDnone

fn staspecid_of_qid (q: s0taq, id: sym_t): staspecid = begin
  case+ q.s0taq_node of
  | $Syn.S0TAQnone () => begin
      if id = $Sym.symbol_MINUSGT then SPSIDarrow () else SPSIDnone ()
    end
  | _ => SPSIDnone ()
end // end of [staspecid_of_qid]

(* ****** ****** *)

fn effvar_tr
  (efv: $Eff.effvar): s2exp = begin
  case+ the_s2expenv_find efv.i0de_sym of
  | ~Some_vt s2i => begin case+ s2i of
    | S2ITEMvar s2v => let
        val () = s2var_check_tmplev (efv.i0de_loc, s2v)
      in
        s2exp_var (s2v)
      end // end of [S2ITEMvar]
    | _ => begin
        prerr_loc_error2 efv.i0de_loc;
        $Deb.debug_prerrf (": %s: effvar_tr", @(THISFILENAME));
        prerr ": the static identifer [";
        $Sym.prerr_symbol efv.i0de_sym;
        prerr "] should refer to a variable but it does not.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end // end of [_]
    end // end of [Some_vt]
  | ~None_vt () => begin 
      prerr_loc_error2 efv.i0de_loc;
      $Deb.debug_prerrf (": %s: effvar_tr", @(THISFILENAME));
      prerr ": unrecognized static identifer [";
      $Sym.prerr_symbol efv.i0de_sym;
      prerr "].";
      prerr_newline ();
      $Err.abort {s2exp} ()
    end // end of [None_vt]
end // end of [effvar_tr]

fn effvarlst_tr (efvs: $Eff.effvarlst): s2explst =
  $Lst.list_map_fun (efvs, effvar_tr)

implement
effcst_tr (efc): s2eff = begin
  case+ efc of
  | $Eff.EFFCSTall () => S2EFFall ()
  | $Eff.EFFCSTnil () => S2EFFnil ()
  | $Eff.EFFCSTset (efs, efvs) => S2EFFset (efs, effvarlst_tr efvs)
end // end of [effcst_tr]

(* ****** ****** *)

implement
s1arglst_var_tr (s1as) = let
  fun s1rtopt_search (s1as: s1arglst): s1rtopt = case+ s1as of
    | list_cons (s1a, s1as) => let
        val os1t = s1a.s1arg_srt in
        case+ os1t of Some _ => os1t | None () => s1rtopt_search s1as
      end // end of [list_cons]
    | list_nil () => None ()
  // end of [s1rtopt_search]
in
  case+ s1as of
  | list_cons (s1a_fst, s1as_rst) => let
      val os1t = s1rtopt_search s1as; val s1t = case+ os1t of
        | Some s1t => s1t | None () => begin
            prerr_loc_error2 s1a_fst.s1arg_loc;
            $Deb.debug_prerrf (": %s: s1arglst_var_tr", @(THISFILENAME));
            prerr ": the static variable [";
            $Sym.prerr_symbol s1a_fst.s1arg_sym;
            prerr "] must be ascribed a sort.";
            prerr_newline ();
            $Err.abort ()
          end // end of [None]
      val s2t = s1rt_tr s1t
      val s2v_fst = s2var_make_id_srt (s1a_fst.s1arg_sym, s2t)
      val s2vs_rst = s1arglst_var_tr s1as_rst
      val s2vs = list_cons (s2v_fst, s2vs_rst)
    in
      the_s2expenv_add_svarlst s2vs; s2vs
    end // end of [list_cons]
  | list_nil () => list_nil ()
end // end of [s1arglst_var_tr]

implement
s1arglstlst_var_tr (s1ass) =
  $Lst.list_map_fun (s1ass, s1arglst_var_tr)
// end of [s1arglstlst_var_tr]

implement
s1arg_var_tr_srt
  (s1a, s2t0) = let
  val s2t = (
    case+ s1a.s1arg_srt of
    | Some s1t => let
        val s2t = s1rt_tr s1t
      in
        if s2t0 <= s2t then s2t else begin
          prerr_loc_error2 s1a.s1arg_loc;
          $Deb.debug_prerrf (": %s: s1arg_var_tr_srt", @(THISFILENAME));
          prerr ": the static variable [";
          $Sym.prerr_symbol s1a.s1arg_sym;
          prerr "] is expected to be of the sort [";
          prerr s2t0;
          prerr "].";
          prerr_newline ();
          $Err.abort {s2rt} ()
        end // end of [if]
      end // end of [Some]
    | None () => s2t0
  ) : s2rt // end of [val]
  val s2v = s2var_make_id_srt (s1a.s1arg_sym, s2t)
in
  the_s2expenv_add_svar s2v; s2v
end // end of [s1arg_var_tr_srt]

(* ****** ****** *)

fun sp1at_arg_tr_dn (
  loc0: loc_t
, q: s0taq, id: sym_t, s1as: s1arglst, s2ts: s2rtlst
) : s2varlst = begin
  case+ (s1as, s2ts) of
  | (list_cons (s1a, s1as), list_cons (s2t, s2ts)) => let
      val s2v = s1arg_var_tr_srt (s1a, s2t)
      val s2vs = sp1at_arg_tr_dn (loc0, q, id, s1as, s2ts)
    in
      list_cons (s2v, s2vs)
    end // end of [list_cons, list_cons]
  | (list_nil (), list_nil ()) => list_nil ()
  | (_, _) => begin
      prerr_loc_error2 loc0;
      prerr ": the static constructor [";
      $Syn.prerr_s0taq q; $Sym.prerr_symbol id; prerr "] requires ";
      case+ s1as of list_cons _ => prerr "fewer" | _ => prerr "more";
      prerr " arguments.";
      prerr_newline ();
      $Err.abort {s2varlst} ()
    end // end of [list_cons, list_nil]
end // end of [sp2at_arg_tr_dn]

fun sp1at_argcheck
  (s2vs: s2varlst): Option_vt s2var_t = let
  fun check (
    name: sym_t, s2vs: s2varlst
  ) : Option_vt s2var_t =
    case+ s2vs of
    | list_cons (s2v, s2vs) => begin
        if (name = s2var_get_sym s2v) then Some_vt s2v else check (name, s2vs)
      end // end of [list_cons]
    | list_nil () => None_vt ()
  // end of [check]
in
  case+ s2vs of
  | list_cons (s2v, s2vs) => let
      val ans = check (s2var_get_sym s2v, s2vs) in case+ ans of
      | Some_vt _ => (fold@ ans; ans) | ~None_vt () => sp1at_argcheck s2vs
    end // end of [list_cons]
  | list_nil () => None_vt ()
end // end of [sp1at_argcheck]

implement
sp1at_tr_dn (sp1t, s2t_pat) = let
//
val loc0 = sp1t.sp1at_loc
//
fn err1
  (q: s0taq, id: sym_t):<cloref1> sp2at = begin
  prerr_loc_error2 loc0;
  $Deb.debug_prerrf (": %s: sp1at_tr_dn", @(THISFILENAME));
  prerr ": the static identifier [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] does not refer to a constructor associated with the sort [";
  prerr s2t_pat; prerr_newline ();
  $Err.abort {sp2at} ()
end // end of [err1]
//
fn err2 
  (q: s0taq, id: sym_t):<cloref1> sp2at = begin
  prerr_loc_error2 loc0;
  $Deb.debug_prerrf (": %s: sp1at_tr_dn", @(THISFILENAME));
  prerr ": the static identifier [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] does not refer to a static constructor.";
  prerr_newline ();
  $Err.abort {sp2at} ()
end // end of [err2]
//
fn err3
  (q: s0taq, id: sym_t):<cloref1> sp2at = begin
  prerr_loc_error2 loc0;
  $Deb.debug_prerrf (": %s: sp1at_tr_dn", @(THISFILENAME));
  prerr ": the static identifier [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id; prerr "] is unrecognized.";
  prerr_newline ();
  $Err.abort {sp2at} ()
end // end of [err3]
//
fn argcheck_err (s2v: s2var_t):<cloref1> void = begin
  $Loc.prerr_location loc0; prerr ": warning(2)";    
  prerr ": the static variable ["; prerr s2v; prerr "] occurs repeatedly.";
  prerr_newline ()
end // end of [argcheck_err]
//
in
  case+ sp1t.sp1at_node of
  | SP1Tcon (q, id, s1as) => let
    val ans =
      the_s2expenv_find_qua (q, id) in
    case+ ans of
    | ~Some_vt s2i => begin case+ s2i of
      | S2ITEMcst s2cs => let
          var s2ts_arg: s2rtlst = list_nil ()
          val s2cs = sel (s2cs, s2t_pat, s2ts_arg) where {
            fun sel (
                s2cs: s2cstlst, s2t_pat: s2rt, s2ts_arg: &s2rtlst
              ) : s2cstlst = case+ s2cs of
              | S2CSTLSTcons (s2c, s2cs1) => let
                  val s2t_s2c = s2cst_get_srt s2c in case+ s2t_s2c of
                  | S2RTfun (s2ts, s2t) => begin case+ 0 of
                    | _ when s2t_pat <= s2t => (s2ts_arg := s2ts; s2cs)
                    | _ => sel (s2cs1, s2t_pat, s2ts_arg)
                    end // end of [S2RTfun]
                  | _ => sel (s2cs1, s2t_pat, s2ts_arg)
                end // end of [S2CSTLSTcons]
              | S2CSTLSTnil () => S2CSTLSTnil ()
          } // end of [val]
        in
          case+ s2cs of
          | S2CSTLSTcons (s2c, _) => let
              val s2vs = sp1at_arg_tr_dn (loc0, q, id, s1as, s2ts_arg)
              val () = (case+ sp1at_argcheck (s2vs) of
                | ~Some_vt s2v => argcheck_err (s2v) | ~None_vt () => ()
              ) : void // end of [val]
            in
              sp2at_con (loc0, s2c, s2vs)
            end // end of [S2CSTLSTcons]
          | S2CSTLSTnil () => err1 (q, id)
        end // end of [S2ITEMcst]
      | _ => err2 (q, id)
      end // end of [Some_vt]
    | ~None_vt () => err3 (q, id)
  end // end of [SP1Tcon]
end // end of [sp1at_tr_dn]

(* ****** ****** *)

implement
s1exp_tr_dn_bool
  (s1e) = s1exp_tr_dn (s1e, s2rt_bool)
// end of [s1exp_tr_dn_bool]

implement s1explst_tr_dn_bool (s1es) =
  $Lst.list_map_fun (s1es, s1exp_tr_dn_bool)

implement
s1exp_tr_dn_cls (s1e) = s1exp_tr_dn (s1e, s2rt_cls)

implement s1explst_tr_dn_cls (s1es) =
  $Lst.list_map_fun (s1es, s1exp_tr_dn_cls)

implement
s1exp_tr_dn_int (s1e) = s1exp_tr_dn (s1e, s2rt_int)

implement
s1explst_tr_dn_int (s1es) = $Lst.list_map_fun (s1es, s1exp_tr_dn_int)
// end of [s1explst_tr_dn_int]

(* ****** ****** *)

implement s1exp_tr_dn_prop (s1e) = s1exp_tr_dn (s1e, s2rt_prop)
implement s1exp_tr_dn_type (s1e) = s1exp_tr_dn (s1e, s2rt_type)
implement s1exp_tr_dn_t0ype (s1e) = s1exp_tr_dn (s1e, s2rt_t0ype)

fun s1explst_tr_dn_t0ype
  (s1es: s1explst): s2explst = $Lst.list_map_fun (s1es, s1exp_tr_dn_t0ype)
// end of [s1explst_tr_dn_t0ype]

implement s1exp_tr_dn_view (s1e) = s1exp_tr_dn (s1e, s2rt_view)
implement s1exp_tr_dn_viewtype (s1e) = s1exp_tr_dn (s1e, s2rt_viewtype)
implement s1exp_tr_dn_viewt0ype (s1e) = s1exp_tr_dn (s1e, s2rt_viewt0ype)

fun s1explst_tr_dn_viewt0ype
  (s1es: s1explst): s2explst = $Lst.list_map_fun (s1es, s1exp_tr_dn_viewt0ype)
// end of [s1explst_tr_dn_viewt0ype]
fun s1explstlst_tr_dn_viewt0ype
  (s1ess: s1explstlst): s2explstlst = $Lst.list_map_fun (s1ess, s1explst_tr_dn_viewt0ype)
// end of [s1explstlst_tr_dn_viewt0ype]

implement
s1exp_tr_dn_impredicative (s1e) = let
  val s2e = s1exp_tr_up s1e; val s2t = s2e.s2exp_srt
in
  if s2rt_is_impredicative s2t then s2e else begin
    prerr_loc_error2 s1e.s1exp_loc;
    $Deb.debug_prerrf (": %s: s1exp_tr_dn_impredicative", @(THISFILENAME));
    prerr ": the static expression needs to be impredicative";
    prerr " but is assigned the sort [";
    prerr s2t;
    prerr "].";
    prerr_newline ();
    $Err.abort ()
  end // end of [if]
end // end of [s1exp_tr_dn_impredicative]

implement
s1expopt_tr_dn_impredicative (os1e) = case+ os1e of
  | Some s1e => Some (s1exp_tr_dn_impredicative s1e) | None () => None ()
// end of [s1expopt_tr_dn_impredicative]

(* ****** ****** *)

fn s1exp_any_tr_up (loc0: loc_t): s2exp = begin
  prerr_loc_error2 loc0;
  $Deb.debug_prerrf (": %s: s1exp_any_tr_up", @(THISFILENAME));
  prerr "the static expression needs to be ascribed a sort.";
  prerr_newline ();
  $Err.abort {s2exp} ()
end // end of [s1exp_any_tr_up]

(* ****** ****** *)

fn s1exp_app_tr_up
  (loc_app: loc_t, loc_fun: loc_t, s2e: s2exp, s1ess: s1explstlst)
  : s2exp = loop (loc_app, loc_fun, s2e, s1ess) where {
  fun loop
    (loc_app: loc_t, loc_fun: loc_t, s2e: s2exp, s1ess: s1explstlst)
    : s2exp = begin case+ s1ess of
    | s1es :: s1ess => let
        val @(s2ts, s2t) = (
          case+ un_s2rt_fun (s2e.s2exp_srt) of
          | ~Some_vt s2ts_s2t => s2ts_s2t
          | ~None_vt () => begin
              prerr_loc_error2 loc_fun;
              $Deb.debug_prerrf (": %s: s1exp_app_tr_up", @(THISFILENAME));
              prerr ": the static expresstion [";
              prerr s2e;
              prerr "] is expected to be of a functional sort";
              prerr ", but is assigned the sort [";
              prerr s2e.s2exp_srt;
              prerr "].";
              prerr_newline ();
              $Err.abort ()
            end
        ) : @(s2rtlst, s2rt)
        val ns2es = $Lst.list_length s1es and ns2ts = $Lst.list_length s2ts
        val s2es = case+ compare (ns2es, ns2ts) of
          |  0 => s1explst_tr_dn (s1es, s2ts)
          |  1 => begin
              prerr_loc_error2 loc_app;
              $Deb.debug_prerrf (": %s: s1exp_app_tr_up", @(THISFILENAME));
              prerr ": the static application needs fewer arguments.";
              prerr_newline ();
              $Err.abort ()
            end // end of [1]
          | _ (* ~1 *) => begin
              prerr_loc_error2 loc_app;
              $Deb.debug_prerrf (": %s: s1exp_app_tr_up", @(THISFILENAME));
              prerr ": the static application needs more arguments.";
              prerr_newline ();
              $Err.abort ()
            end // end [_]
      in
        loop (loc_app, loc_fun, s2exp_app_srt (s2t, s2e, s2es), s1ess)
      end // end of [::]
    | nil () => s2e
  end // end of [loop]
} // end of [s1exp_app_tr_up]

(* ****** ****** *)

fn s1exp_app_datconptr_tr_up
  (loc_app: loc_t, d2c: d2con_t, s1ess: s1explstlst)
  : s2exp = let
  val s1es = (
    case+ s1ess of
    | cons (s1es, s1ess) => begin
      case+ s1ess of
      | nil _ => s1es | cons _ => begin
          prerr_loc_error2 loc_app;
          $Deb.debug_prerrf (": %s: s1exp_app_datconptr_tr_up", @(THISFILENAME));
          prerr ": the type constructor [";
          prerr d2c;
          prerr "] is overly applied.";
          prerr_newline ();
          $Err.abort {s1explst} ()
        end // end of [cons]
      end // end of [cons]
    | nil () => nil ()
  ) : s1explst
  val s2es = aux s1es where {
    fun aux (s1es: s1explst): s2explst = case+ s1es of
      | cons (s1e, s1es) => begin
          cons (s1exp_tr_dn (s1e, s2rt_addr), aux s1es)
        end
      | nil () => nil ()
  } // end of [where]
  val ns2es = $Lst.list_length (s2es)
  val arity = d2con_get_arity_full (d2c)
  val () =
    if ns2es > arity then begin
      prerr_loc_error2 loc_app;
      $Deb.debug_prerrf (": %s: s1exp_app_datcon_tr_up", @(THISFILENAME));
      prerr ": the type constructor [";
      prerr d2c;
      prerr "] expects fewer arguments.";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
  val () =
    if ns2es < arity then begin
      prerr_loc_error2 loc_app;
      $Deb.debug_prerrf (": %s: s1exp_app_datcon_tr_up", @(THISFILENAME));
      prerr ": the type constructor [";
      prerr d2c;
      prerr "] expects more arguments.";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [if]
in
  s2exp_datconptr (d2c, s2es)
end // end [s1exp_app_datconptr_tr_up]

(* ****** ****** *)

fn s1exp_app_datcontyp_tr_up
  (loc_app: loc_t, d2c: d2con_t, s1ess: s1explstlst)
  : s2exp = let
  fn err (loc_app: loc_t, d2c: d2con_t): s1explst = begin
     prerr_loc_error2 loc_app;
     $Deb.debug_prerrf (": %s: s1exp_app_datcon_tr_up", @(THISFILENAME));
     prerr ": the type constructor [";
     prerr d2c;
     prerr "_t0ype] is overly applied.";
     prerr_newline ();
     $Err.abort {s1explst} ()
  end // end of [err]
  val s1es = (case+ s1ess of
    | list_cons (s1es, s1ess) => begin
        case+ s1ess of list_nil () => s1es | _ => err (loc_app, d2c)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  ) : s1explst
  val s2es = s1explst_tr_dn_viewt0ype s1es
in
  s2exp_datcontyp (d2c, s2es)
end // end of [s1exp_app_datcontyp_tr_up]

(* ****** ****** *)

fun s1exp_qid_app_tr_up (
    loc_app: loc_t
  , loc_qid: loc_t
  , q: s0taq, id: sym_t
  , s2i: s2item
  , s1ess: s1explstlst
  ) : s2exp = begin case+ s2i of
  | S2ITEMcst s2cs => let
      val s2ess = s1explstlst_tr_up s1ess
    in
      case+ s2cst_select_s2explstlst (s2cs, s2ess) of
      | S2CSTLSTcons (s2c, _) => let
//
          val () = stacstuseloc_posmark (loc_qid, s2c) in
//
          s2exp_app_wind (s2exp_cst s2c, s2ess)
        end // end of [S2CSTLSTcons]
      | _ => begin
          prerr_loc_error2 loc_app;
          $Deb.debug_prerrf (": %s: s1exp_qid_app_tr_up", @(THISFILENAME));
          prerr ": none of the static constants referred to by [";
          $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
          prerr "] is applicable.";
          prerr_newline ();
          $Err.abort ()
        end // end of [_]
    end // end of [S2ITEMcst]
  | S2ITEMvar s2v => let
      val () = s2var_check_tmplev (loc_qid, s2v)
    in
      s1exp_app_tr_up (loc_app, loc_qid, s2exp_var s2v, s1ess)
    end // end of [S2ITEMvar]
  | S2ITEMdatconptr d2c => s1exp_app_datconptr_tr_up (loc_app, d2c, s1ess)
  | S2ITEMdatcontyp d2c => s1exp_app_datcontyp_tr_up (loc_app, d2c, s1ess)
(*
  | S2ITEMfil _ => s1exp_qid_app_tr_up_errmsg_fil loc_qid qid
*)
  | _ => begin
      prerr_loc_interror loc_qid;
      prerr ": s1exp_qid_app_tr_up: not implemented yet: s2i = "; prerr s2i;
      prerr_newline ();
      $Err.abort ()
    end // end of [_]
end // end of [s1exp_qid_app_tr_up]

(* ****** ****** *)

fn s1exp_qid_tr_up (
  loc0: loc_t, q: $Syn.s0taq, id: sym_t
) : s2exp = let
  val ans = the_s2expenv_find_qua (q, id)
in
//
case+ ans of
| ~Some_vt s2i => begin case+ s2i of
  | S2ITEMcst s2cs => begin case+ s2cs of
    | S2CSTLSTcons (s2c, _) => let
//
        fun loop (
          s2cs: s2cstlst, s2c0: s2cst_t
        ) : s2cst_t = // find the first non-functional one if it exists
          case+ s2cs of
          | S2CSTLSTcons (s2c, s2cs) => let
              val s2t = s2cst_get_srt (s2c) in
              if s2rt_is_fun (s2t) then loop (s2cs, s2c0) else s2c
            end // end of [list_cons]
          | S2CSTLSTnil () => s2c0 // end of [list_nil]
        val s2c = loop (s2cs, s2c)
//
        val () = stacstuseloc_posmark (loc0, s2c)
//
        val s2t = s2cst_get_srt s2c; val s2e_s2c = s2exp_cst s2c
      in
        case+ s2t of
        | S2RTfun (nil (), _res) when s2rt_is_dat _res => begin
            // a nullary constructor is automatically applied!!!
            s2exp_app_srt (_res, s2e_s2c, nil ())
          end // end of [S2RTfun]
        | _ => s2e_s2c
      end // end of [S2CSTLSTcons]
    | S2CSTLSTnil () => begin // this clause should be unreachable
        prerr_interror ();
        prerr ": s1exp_qid_tr_up: Some: S2ITEMcst: S2CSTLSTnil";
        prerr_newline ();
        $Err.abort ()
      end // end of [S2CSTLSTnil]
    end // end of [S2ITEMcst]
  | S2ITEMe1xp e1xp => s1exp_tr_up (s1exp_make_e1xp (loc0, e1xp))
  | S2ITEMvar s2v => let
      val () = s2var_check_tmplev (loc0, s2v) in s2exp_var s2v
    end // end of [S2ITEMvar]
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": s1exp_qid_tr_up: s2i = "; prerr s2i; prerr_newline ();
      $Err.abort ()
    end // end of [_]
  end // end of [Some_vt]
| ~None_vt () => begin
    prerr_loc_error2 loc0;
    $Deb.debug_prerrf (": %s: s1exp_qid_tr_up", @(THISFILENAME));
    prerr ": the static identifier [";
    $Syn.prerr_s0taq q; $Sym.prerr_symbol id; prerr "] is unrecognized.";
    prerr_newline ();
    $Err.abort ()
  end // end of [None_vt]
//
end // end of [s1exp_qid_tr_up]

(* ****** ****** *)

fn s1exp_invar_tr_up
  (refval: int, s1e: s1exp): s2exp = let
  val s2t: s2rt =
    if refval = 0 then s2rt_view (*val*) else s2rt_viewt0ype (*ref*)
  val s2e: s2exp = s1exp_tr_dn (s1e, s2t)
in
  s2exp_refarg (refval, s2e)
end // end of [s1exp_invar_tr_up]

(* ****** ****** *)

fn s1exp_read_tr_up (_v: s1exp, s1e: s1exp): s2exp = let
  val _v = s1exp_tr_dn_view (_v)
  val s2e = s1exp_tr_up s1e; val s2t_s2e = s2e.s2exp_srt
  val () =
    if s2rt_is_impredicative s2t_s2e then () else begin
      prerr_loc_error2 s1e.s1exp_loc;
      $Deb.debug_prerrf (": %s: s1exp_read_tr_up", @(THISFILENAME));
      prerr ": the static expression needs to be impredicative";
      prerr " but is assigned the sort [";
      prerr s2t_s2e;
      prerr "].";
      prerr_newline ();
      $Err.abort ()
    end // end of [if]
in
  s2exp_readize (_v, s2e)
end // end of [s1exp_read_tr_up]

(* ****** ****** *)

fn s1exp_top_tr_up (
  knd: int, s1e: s1exp
) : s2exp = let
  val s2e = s1exp_tr_up s1e
  val s2t_fun = s2e.s2exp_srt
  val s2t_res = s2rt_base_fun s2t_fun
  val () =
    if s2rt_is_impredicative s2t_res then () else begin
      prerr_loc_error2 s1e.s1exp_loc;
      $Deb.debug_prerrf (": %s: s1exp_top_tr_up", @(THISFILENAME));
      prerr ": the static expression needs to be impredicative";
      prerr " but is assigned the sort [";
      prerr s2t_fun;
      prerr "].";
      prerr_newline ();
      $Err.abort ()
    end // end of [if]
in
  s2exp_topize (knd, s2e)
end // end of [s1exp_top_tr_up]

(* ****** ****** *)

implement
s1exp_arg_tr_up
  (s1e0, wths1es) = begin
  case+ s1e0.s1exp_node of
  | S1Einvar (refval, s1e) => let
      val () = begin
        wths1es := WTHS1EXPLSTcons_some (refval, s1e, wths1es)
      end // end of [val]
    in
      s1exp_invar_tr_up (refval, s1e)
    end // end of [S1Einvar]
  | S1Etrans (s1e1, s1e2) => begin case+ s1e1.s1exp_node of
    | S1Einvar (refval, s1e_arg) => let
        val () = begin
          wths1es := WTHS1EXPLSTcons_some (refval, s1e2, wths1es)
        end // end of [val]
      in
        s1exp_invar_tr_up (refval, s1e_arg)
      end // end of [S1Einvar]
    | _ => begin
        prerr_loc_error2 s1e1.s1exp_loc;
        $Deb.debug_prerrf (": %s: s1exp_arg_tr_up", @(THISFILENAME));
        prerr ": a refval type must begin with !(call-by-value) or &(call-by-reference)";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end // end of [_]
    end // end of [S1Etrans]
  | _ => let
      val () = wths1es := WTHS1EXPLSTcons_none wths1es
    in
      s1exp_tr_up s1e0
    end // end of [_]
end // end of [s1exp_arg_tr_up]

implement
s1exp_arg_tr_dn_impredicative
  (s1e, wths1es) = let
  val s2e = s1exp_arg_tr_up (s1e, wths1es); val s2t = s2e.s2exp_srt
in
  if s2rt_is_impredicative s2t then s2e else begin
    prerr_loc_error2 s1e.s1exp_loc;
    $Deb.debug_prerrf (": %s: s1exp_arg_tr_dn_impredicative", @(THISFILENAME));
    prerr ": the static expression needs to be impredicative";
    prerr " but is assigned the sort [";
    prerr s2t;
    prerr "].";
    prerr_newline ();
    $Err.abort {s2exp} ()
  end // end of [if]
end // end of [s1exp_arg_tr_dn_impredicative]

(* ****** ****** *)

implement
s1exp_res_tr_dn_impredicative
  (s1e0, wths1es) = let
//
  fun auxwth (
    wths1es: wths1explst
  ) : wths2explst = begin
    case+ wths1es of
    | WTHS1EXPLSTcons_some (refval, s1e, wths1es) => let
        val s2t: s2rt = 
          if refval = 0 then s2rt_view (*call-by-val*)
          else s2rt_viewt0ype (*call-by-ref*)
        val s2e = s1exp_tr_dn (s1e, s2t)
      in
        WTHS2EXPLSTcons_some (refval, s2e, auxwth wths1es)
      end
    | WTHS1EXPLSTcons_none (wths1es) => begin
        WTHS2EXPLSTcons_none (auxwth wths1es)
      end
    | WTHS1EXPLSTnil () => WTHS2EXPLSTnil ()
  end // endof [auxwth]
//
  fun auxres (
    s1e: s1exp, wths1es: wths1explst
  ) : s2exp =
    case+ s1e.s1exp_node of
    | S1Eexi (1(*funres*), s1qs, s1e_scope) => let
        val (pf_s2expenv | ()) = the_s2expenv_push ()
        val @(s2vs, s2ps) = s1qualst_tr (s1qs)
        val s2e_scope = auxres (s1e_scope, wths1es)
        val () = the_s2expenv_pop (pf_s2expenv | (*none*))
      in
        s2exp_exi (s2vs, s2ps, s2e_scope)
      end // end of [S1Eexi]
    | _ => let
        val s2e = s1exp_tr_dn_impredicative (s1e)
        val wths2es = auxwth wths1es
      in
        s2exp_wth (s2e, wths2es)
      end // end of [_]
  (* end of [auxres] *)
//
in
  if wths1explst_is_none (wths1es)
    then s1exp_tr_dn_impredicative (s1e0) else auxres (s1e0, wths1es)
  // end of [if]
end // end of [s1exp_res_tr_dn_impredicative]

(* ****** ****** *)

fn s1exp_arrow_tr_up // arrow is a special type constructor
  (loc0: loc_t, ofc: funcloopt,
   islin: bool, isprf: bool, oefc: efcopt, s1ess: s1explstlst)
  : s2exp = let
  val s1es = (
    case+ s1ess of
    | cons (s1es, nil ()) => s1es | _ => begin
        prerr_loc_error2 loc0;
        $Deb.debug_prerrf (": %s: s1exp_arrow_tr_up", @(THISFILENAME));
        prerr ": illegal static application.";
        prerr_newline ();
        $Err.abort ()
      end // end of [_]
  ) : s1explst
  val @(s1e_arg, s1e_res) = (
    case+ s1es of
    | cons (s1e1, cons (s1e2, nil ())) => @(s1e1, s1e2)
    | _ => begin
        prerr_loc_interror loc0;
        prerr ": s1exp_arrow_tr_up: s1es = "; prerr_s1explst s1es;
        prerr_newline ();
        $Err.abort ()
      end // end of [_]
  ) : @(s1exp, s1exp) // end of [val]
  var npf: int = 0 and s1es_arg: s1explst = nil ()
  val () = case+ s1e_arg.s1exp_node of
    | S1Elist (n, s1es) => (npf := n; s1es_arg := s1es)
    | _ => s1es_arg := cons (s1e_arg, nil ())
  var wths1es: wths1explst = WTHS1EXPLSTnil () // restoration
  val s2es_arg: s2explst = aux (s1es_arg, wths1es) where {
    fun aux (s1es: s1explst, wths1es: &wths1explst): s2explst =
      case+ s1es of
      | cons (s1e, s1es) => let
          val s2e = s1exp_arg_tr_up (s1e, wths1es)
          val s2t = s2e.s2exp_srt
          var imp: int = 0 and types: int = 0
          val () = case+ s2t of
            | S2RTbas s2tb => begin case+ s2tb of
              | S2RTBASimp (id, _, _) => begin
                  imp := 1; if id = $Sym.symbol_TYPES then types := 1
                end // end of [S2RTBASimp]
              | _ => () // end of [_]
              end
            | _ => ()
        in
          case+ 0 of
          | _ when types > 0 => begin case+ s1es of
            | nil () => cons (s2exp_vararg s2e, nil ())
            | cons _ => begin
                prerr_loc_error2 s1e.s1exp_loc;
                $Deb.debug_prerrf (": %s: s1exp_arrow_tr_up", @(THISFILENAME));
                prerr ": this static expression must be the last argument.";
                prerr_newline ();
                $Err.abort ()
              end // end of [cons]
            end // end of [_ when types > 0]
          | _ when (imp > 0) => cons (s2e, aux (s1es, wths1es))
          | _ => begin
              prerr_loc_error2 s1e.s1exp_loc;
              $Deb.debug_prerrf (": %s: s1exp_arrow_tr_up", @(THISFILENAME));
              prerr ": the static expression needs to be impredicative";
              prerr " but is assigned the sort [";
              prerr s2t;
              prerr "].";
              prerr_newline ();
              $Err.abort ()
            end // end of [_]
        end // end of [cons]
      | nil () => nil ()
    } // end of [where]
  val () = wths1es := wths1explst_reverse wths1es
  val s2e_res = s1exp_res_tr_dn_impredicative (s1e_res, wths1es)
  val s2t_res = s2e_res.s2exp_srt
  val isprf: bool = if isprf then isprf else s2rt_is_proof s2t_res
  val fc = (
    case+ ofc of // default is [function]
    | Some fc => fc | None () => $Syn.FUNCLOfun ()
  ) : $Syn.funclo
  val s2t_fun = s2rt_prf_lin_fc (loc0, isprf, islin, fc)
  val lin: int = if islin then 1 else 0
  val sf2e = (case+ oefc of
    | None () => begin
        if isprf then S2EFFnil () else S2EFFall ()
      end // end of [None]
    | Some efc => effcst_tr efc
  ) : s2eff
in
  s2exp_fun_srt (s2t_fun, fc, lin, sf2e, npf, s2es_arg, s2e_res)
end // end of [s1exp_arrow_tr_up]

(* ****** ****** *)

fun s1rtext_tr
  (s1te0: s1rtext): s2rtext = begin
  case+ s1te0.s1rtext_node of
  | S1TEsrt s1t => begin case+ s1t.s1rt_node of
    | S1RTqid (q, id) => begin
      case+ the_s2rtenv_find_qua (q, id) of
      | ~Some_vt s2te => s2te | ~None_vt () => begin
          prerr_loc_error2 s1t.s1rt_loc;
          $Deb.debug_prerrf (": %s: s1rtext_tr", @(THISFILENAME));
          prerr ": the identifier [";
          $Syn.prerr_s0rtq q; $Sym.prerr_symbol id;
          prerr "] refers to an unrecognized sort.";
          prerr_newline ();
          $Err.abort ()
        end // end of [None_vt]
      end // end of [S1RTqid]
    | _ => S2TEsrt (s1rt_tr s1t)
    end // end of [S1TEsrt]
  | S1TEsub (id, s1te, s1ps) => let
      val s2te = s1rtext_tr s1te
      val s2t = begin case+ s2te of
        | S2TEsrt s2t => s2t | S2TEsub (_, s2t, _) => s2t
      end // end of [val]
      val s2v = s2var_make_id_srt (id, s2t)
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val () = the_s2expenv_add_svar s2v
      val s2ps = s1explst_tr_dn_bool s1ps
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
      val s2ps = (
        case+ s2te of
        | S2TEsrt _ => s2ps
        | S2TEsub (s2v1, _, s2ps1) => begin
            $Lst.list_append (s2ps, s2explst_alpha (s2v1, s2v, s2ps1))
          end
      ) : s2explst // end of [val]
    in
      S2TEsub (s2v, s2t, s2ps)
    end // end of [S1TEsub]
end // end of [s1rtext_tr]

(* ****** ****** *)

implement s1qualst_tr (s1qs) = let
//
fun loop (
  s1qs: s1qualst, s2vs: &s2varlst, s2ps: &s2explst
) : void = begin
  case+ s1qs of
  | cons (s1q, s1qs) => begin case+ s1q.s1qua_node of
    | S1Qprop s1e => let
        val s2p = s1exp_tr_dn_bool s1e
      in
        s2ps := cons (s2p, s2ps); loop (s1qs, s2vs, s2ps)
      end
    | S1Qvars (ids, s1te) => begin case+ s1rtext_tr s1te of
      | S2TEsrt s2t1 => let
          fun aux (s2t1: s2rt, ids: i0delst, s2vs: &s2varlst): void =
            case+ ids of
            | cons (id, ids) => let
                val s2v = s2var_make_id_srt (id.i0de_sym, s2t1)
              in
                the_s2expenv_add_svar s2v; s2vs := cons (s2v, s2vs);
                aux (s2t1, ids, s2vs)
              end
            | nil () => ()          
        in
          aux (s2t1, ids, s2vs); loop (s1qs, s2vs, s2ps)
        end // end of [S2TEsrt]
      | S2TEsub (s2v1, s2t1, s2ps1) => let
//
          fun aux1 (
            s2ps1: s2explst, s2v: s2var_t, s2ps: &s2explst
          ) :<cloref1> void = case+ s2ps1 of
            | cons (s2p1, s2ps1) => let
                val s2p = s2exp_alpha (s2v1, s2v, s2p1)
              in
                s2ps := cons (s2p, s2ps); aux1 (s2ps1, s2v, s2ps)
              end // end of [cons]
            | nil () => ()
          // end of [aux1]
//
          fun aux2 (
            ids: i0delst, s2vs: &s2varlst, s2ps: &s2explst
          ) :<cloref1> void = case+ ids of
            | cons (id, ids) => let
                val s2v = s2var_make_id_srt (id.i0de_sym, s2t1)
              in
                the_s2expenv_add_svar s2v;
                s2vs := cons (s2v, s2vs); aux1 (s2ps1, s2v, s2ps);
                aux2 (ids, s2vs, s2ps)
              end // end of [cons]
            | nil () => ()
          // end of [aux2]
//
        in
          aux2 (ids, s2vs, s2ps); loop (s1qs, s2vs, s2ps)
        end // end of [S2TEsub]
      end // end of [S1Qvars]
    end // end of [cons]
  | nil () => ()
end // end of [loop]
//
var s2vs: s2varlst = list_nil () and s2ps: s2explst = list_nil ()
val () = loop (s1qs, s2vs, s2ps)
//
in // in of [let]
//
($Lst.list_reverse s2vs, $Lst.list_reverse s2ps)
//
end // end of [s1qualst_tr]

implement
s1qualstlst_tr
  (s1qss) = begin case+ s1qss of
  | list_cons (s1qs, s1qss) => begin
      list_cons (s1qualst_tr s1qs, s1qualstlst_tr s1qss)
    end // end of [list_cons]
  | list_nil () => list_nil ()
end // end of [s1qualstlst_tr]

(* ****** ****** *)

fun s1exp_app_unwind (
  s1e: s1exp, s1ess: &s1explstlst
) : s1exp = begin
  case+ s1e.s1exp_node of
  | S1Eapp (s1e, _(*loc_arg*), s1es) => begin
      s1ess := s1es :: s1ess; s1exp_app_unwind (s1e, s1ess)
    end // end of [S1Eapp]
  | S1Eqid (q, id) => begin case+ q.s0taq_node of
    | $Syn.S0TAQnone () => let
      val ans = the_s2expenv_find id in case+ ans of
      | ~Some_vt s2i => begin case+ s2i of
        | S2ITEMe1xp e1xp => let
            val s1e_new = s1exp_make_e1xp (s1e.s1exp_loc, e1xp)
          in
            s1exp_app_unwind (s1e_new, s1ess)
          end (* end of [S2ITEMe1xp] *)
        | _ => s1e
        end // end of [Some_vt]
      | ~None_vt () => s1e
      end // end of [$Syn.S0TAQnone]
    | _ => s1e
    end (* end of [S1Eqid] *)
  | _ => s1e // end of [_]
end // end of [s1exp_app_unwind]

(* ****** ****** *)

fn s2rtlst_of_s2varlst
  (s2vs: s2varlst): s2rtlst = $Lst.list_map_fun (s2vs, s2var_get_srt)
// end of [s2rtlst_of_s2varlst]

(* ****** ****** *)

local

fun aux01 (
    i: int
  , npf: int
  , s1es: s1explst
  , lin: &int
  , prg: &int
  , res: labs2explst
  ) : labs2explst = begin case+ s1es of
  | list_cons (s1e, s1es) => let
      val lab = $Lab.label_make_int i
      val s2e = s1exp_tr_dn_impredicative s1e
      val s2t = s2e.s2exp_srt
      val () = if s2rt_is_linear s2t then (lin := lin+1)
      val () = begin
        if i >= npf then (if ~(s2rt_is_proof s2t) then (prg := prg+1))
      end // end of [val]
    in
      LABS2EXPLSTcons (lab, s2e, aux01 (i+1, npf, s1es, lin, prg, res))
    end (* end of [list_cons] *)
  | list_nil () => res
end // end of [aux01]

fun aux23 (
    s2t: s2rt, i: int, s1es: s1explst, res: labs2explst
  ) : labs2explst = begin case+ s1es of
  | list_cons (s1e, s1es) => let
      val lab = $Lab.label_make_int i
      val s2e = s1exp_tr_dn (s1e, s2t)
    in
      LABS2EXPLSTcons (lab, s2e, aux23 (s2t, i+1, s1es, res))
    end (* end of [list_cons] *)
  | list_nil () => res
end // end of [aux23]

in // in of [local]

fn s1exp_list_tr_up
  (loc0: loc_t, npf: int, s1es: s1explst): s2exp = let
  var lin: int = 0 and prg: int = 0
  val ls2es = aux01 (0, npf, s1es, lin, prg, LABS2EXPLSTnil ())
  val s2t_rec = begin
    s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, 0, npf, ls2es)
  end
in
  s2exp_tyrec_srt (s2t_rec, TYRECKINDflt0 (), npf, ls2es)
end // end of [s1exp_list_tr_up]

fn s1exp_tytup_tr_up
  (loc0: loc_t, tupknd: int, s1es: s1explst): s2exp = begin
  case+ tupknd of
  | _ when 0 <= tupknd andalso tupknd <= 1 => let
      var lin: int = 0 and prg: int = 0
      val ls2es = aux01 (0, 0, s1es, lin, prg, LABS2EXPLSTnil ())
      val boxed = (if tupknd > 0 then 1 else 0): int
      val s2t_rec = begin
        s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, boxed, 0, ls2es)
      end (* end of [s2t_rec] *)
      val tyrecknd = (
        if boxed > 0 then TYRECKINDbox () else TYRECKINDflt0 ()
      ) : tyreckind
    in
      s2exp_tyrec_srt (s2t_rec, tyrecknd, 0(*npf*), ls2es)
    end (* end of [_ when ...] *)
  | _ when 2 <= tupknd andalso tupknd <= 3 => let
      val s2t_elt: s2rt =
        if tupknd = 2 then s2rt_t0ype else s2rt_viewt0ype
      val ls2es = aux23 (s2t_elt, 0, s1es, LABS2EXPLSTnil ())
      val s2t_rec: s2rt =
        if tupknd = 2 then s2rt_type else s2rt_viewtype
    in
      s2exp_tyrec_srt (s2t_rec, TYRECKINDbox (), 0(*npf*), ls2es)
    end (* end of [_ when ...] *)
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": s1exp_tytup_tr_up"; prerr_newline ();
      $Err.abort {s2exp} ()
    end (* end of [_] *)
end // end of [s1exp_tytup_tr_up]

fn s1exp_tytup2_tr_up
  (loc0: loc_t, tupknd: int, s1es1: s1explst, s1es2: s1explst)
  : s2exp = begin case+ tupknd of
  | _ when 0 <= tupknd andalso tupknd <= 1 => let
      var lin: int = 0 and prg: int = 0
      val npf = $Lst.list_length s1es1        
      val ls2es = LABS2EXPLSTnil ()
      val ls2es2 = aux01 (npf, npf, s1es2, lin, prg, ls2es)
      val ls2es12 = aux01 (0, npf, s1es1, lin, prg, ls2es2)
      val boxed = (if tupknd > 0 then 1 else 0): int
      val s2t_rec = begin
        s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, boxed, 0, ls2es2)
      end
      val tyrecknd = (
        if boxed > 0 then TYRECKINDbox () else TYRECKINDflt0 ()
      ) : tyreckind
    in
      s2exp_tyrec_srt (s2t_rec, tyrecknd, npf, ls2es12)
    end
  | _ when 2 <= tupknd andalso tupknd <= 3 => let
      val npf = $Lst.list_length s1es1
      val s2t_elt1: s2rt =
        if tupknd = 2 then s2rt_prop else s2rt_view
      val s2t_elt2: s2rt =
        if tupknd = 2 then s2rt_t0ype else s2rt_viewt0ype
      val ls2es = aux23 (s2t_elt2, npf, s1es2, LABS2EXPLSTnil ())
      val ls2es = aux23 (s2t_elt1, 0, s1es1, ls2es)
      val s2t_rec: s2rt =
        if tupknd = 2 then s2rt_type else s2rt_viewtype
    in
      s2exp_tyrec_srt (s2t_rec, TYRECKINDbox (), npf, ls2es)
    end
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": s1exp_tytup2_tr_up"; prerr_newline ();
      $Err.abort {s2exp} ()
    end // end of [_]
end // end of [s1exp_tytup2_tr_up]

end // end of [local]

(* ****** ****** *)

local

fun aux01 (
  ls1es: labs1explst, lin: &int, prg: &int
) : labs2explst = begin
  case+ ls1es of
  | LABS1EXPLSTcons
      (lab, s1e, ls1es) => let
      val s2e = s1exp_tr_dn_impredicative (s1e)
      val s2t = s2e.s2exp_srt
      val () = if s2rt_is_linear (s2t) then (lin := lin+1)
      val () = if not (s2rt_is_proof s2t) then (prg := prg+1)
    in
      LABS2EXPLSTcons (lab, s2e, aux01 (ls1es, lin, prg))
    end // end of [LABS1EXPLSTcons]
  | LABS1EXPLSTnil () => LABS2EXPLSTnil ()
end // end of [aux01]

fun aux23 (
  s2t: s2rt, ls1es: labs1explst
) : labs2explst = begin
  case+ ls1es of
  | LABS1EXPLSTcons
      (lab, s1e, ls1es) => let
      val s2e = s1exp_tr_dn (s1e, s2t)
    in
      LABS2EXPLSTcons (lab, s2e, aux23 (s2t, ls1es))
    end // end of [LABS1EXPLSTcons]
  | LABS1EXPLSTnil () => LABS2EXPLSTnil ()
end // end of [aux23]

in // in of [local]

(*
// HX-2010-11-01: simplification
fn s1exp_struct_tr_up (
   loc0: loc_t, ls1es: labs1explst
  ) : s2exp = let
  var lin: int = 0 and prg: int = 0      
  val ls2es = aux01 (ls1es, lin, prg)
  val s2t_rec: s2rt = begin
    s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, 0(*boxed*), 0, ls2es)
  end // end of [val]
  val stamp = $Stamp.s2exp_struct_stamp_make ()
in
  s2exp_tyrec_srt (s2t_rec, TYRECKINDflt1 stamp, 0(*npf*), ls2es)
end // end of [s1exp_struct_tr_up]
*)

(* ****** ****** *)

fn s1exp_tmpid_tr (
    loc0: loc_t
  , q: $Syn.d0ynq
  , id: $Sym.symbol_t
  ) : s2cst_t = s2c where {
(*
  val () = begin
    $Loc.print_location loc0;
    print ": s1exp_tmpid_tr: id = "; $Sym.print_symbol id; print_newline ()
  end // end of [val]
*)
  fn err1
    (loc: loc_t, q: s0taq, id: sym_t): s2cst_t = begin
    prerr_loc_error2 loc;
    $Deb.debug_prerrf (": %s: s1exp_tmpid_tr: err1", @(THISFILENAME));
    prerr ": the static identifier [";
    $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
    prerr "] does not refer to a static constant";
    prerr_newline ();
    $Err.abort {s2cst_t} ()
  end // end of [err1]
//
  fn err2 (loc: loc_t, q: $Syn.s0taq, id: sym_t): s2cst_t = begin
    prerr_loc_error2 loc;
    $Deb.debug_prerrf (": %s: s1exp_tmpid_tr: err2", @(THISFILENAME));
    prerr ": the identifier [";
    $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
    prerr "] is unrecognized.";
    prerr_newline ();
    $Err.abort {s2cst_t} ()
  end // end of [err2]
//
  val q_loc = q.d0ynq_loc
  val q_node = (case+ q.d0ynq_node of
    | $Syn.D0YNQnone () => $Syn.S0TAQnone ()
    | $Syn.D0YNQfildot nam => $Syn.S0TAQfildot nam
    | $Syn.D0YNQsymcolon sym => $Syn.S0TAQsymcolon sym
    | $Syn.D0YNQsymdot sym => $Syn.S0TAQsymdot sym
    | _ => begin
        prerr_loc_error2 (q_loc);
        $Deb.debug_prerrf (": %s: s1exp_tmpid_tr", @(THISFILENAME));
        prerr ": the static qualifier ["; $Syn.prerr_d0ynq q; prerr "] is not supported.";
        prerr_newline ();
        $Err.abort {$Syn.s0taq_node} ()
      end // end of [_]
  ) : $Syn.s0taq_node // end of [val]
  val q = $Syn.s0taq_make (q_loc, q_node)
  val ans = the_s2expenv_find_qua (q, id)
  val s2c = (case+ ans of
    | ~Some_vt s2i => begin case+ s2i of
      | S2ITEMcst s2cs => begin case+ s2cs of
        | S2CSTLSTcons (s2c, _) => s2c where {
//
            val () = stacstuseloc_posmark (loc0, s2c)
//
          } // end of [S2CSTLSTcons]
        | S2CSTLSTnil () => err1 (loc0, q, id)
        end (* end of [S2ITEMcst] *)
      | _ => err1 (loc0, q, id)
      end // end of [Some_vt]
    | ~None_vt () => err2 (loc0, q, id)
  ) : s2cst_t
} // end of [s1exp_tmpid_tr]

(* ****** ****** *)

fn s1exp_tyrec_tr_up (
  loc0: loc_t, recknd: int, ls1es: labs1explst
) : s2exp = begin
  case+ recknd of
  | _ when 0 <= recknd andalso recknd <= 1 => let
      var lin: int = 0 and prg: int = 0
      val ls2es = aux01 (ls1es, lin, prg)
      val boxed = (if recknd > 0 then 1 else 0): int
      val s2t_rec: s2rt = begin
        s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, boxed, 0, ls2es)
      end
      val tyrecknd = (
        if boxed > 0 then TYRECKINDbox () else TYRECKINDflt0 ()
      ) : tyreckind
    in
      s2exp_tyrec_srt (s2t_rec, tyrecknd, 0(*npf*), ls2es)
    end
  | _ when 2 <= recknd andalso recknd <= 3 => let
      val s2t_rec: s2rt =
        if recknd = 2 then s2rt_type else s2rt_viewtype
      val s2t_elt: s2rt =
        if recknd = 2 then s2rt_t0ype else s2rt_viewt0ype
      val ls2es = aux23 (s2t_elt, ls1es)
    in
      s2exp_tyrec_srt (s2t_rec, TYRECKINDbox (), 0(*npf*), ls2es)
    end
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": s1exp_tyrec_tr_up"; prerr_newline ();
      $Err.abort {s2exp} ()
    end // end of [_]
end // end of [s1exp_tyrec_tr_up]

fn s1exp_tyrec_ext_tr_up
  (loc0: loc_t, name: string, ls1es: labs1explst): s2exp = let
  var lin: int = 0 and prg: int = 0      
  val ls2es = aux01 (ls1es, lin, prg)
  val s2t_rec: s2rt = begin
    s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, 0(*boxed*), 0, ls2es)
  end // end of [val]
in
  s2exp_tyrec_srt (s2t_rec, TYRECKINDflt_ext name, 0(*npf*), ls2es)
end // end of [s1exp_tyrec_ext_tr_up]

fn s1exp_union_tr_up (loc0: loc_t, s1e_ind: s1exp, ls1es: labs1explst)
  : s2exp = let
  val s2e_ind = s1exp_tr_dn_int s1e_ind
  var lin: int = 0 and prg: int = 0
  val ls2es = aux01 (ls1es, lin, prg)
  val s2t_rec = s2rt_lin_prg_boxed (lin, prg, 0(*boxed*))
  val stamp = $Stamp.s2exp_union_stamp_make ()
in
  s2exp_union_srt (s2t_rec, stamp, s2e_ind, ls2es)
end // end of [s1exp_union_tr_up]

end // end of [local]

(* ****** ****** *)

implement
s1exp_tr_up (s1e0) = let
(*
  val () = begin
    print "s1exp_tr_up: s1e0 = "; print s1e0; print_newline ()
  end // end of [val]
*)
in
  case+ s1e0.s1exp_node of
  | S1Eann (s1e, s1t) => let
      val s2t = s1rt_tr s1t
      val s2e = s1exp_tr_dn (s1e, s2t)
      val () = s2exp_set_srt (s2e, s2t)
    in
      s2e (* [s2e] is of the sort [s2t] *)
    end // end of [S1Eann]
  | S1Eany () => s1exp_any_tr_up (s1e0.s1exp_loc)
  | S1Eapp (s1e, _(*loc_arg*), s1es) => let
      var s1ess_arg: s1explstlst = '[s1es]
      val s1e_opr = s1exp_app_unwind (s1e, s1ess_arg)
    in
      case+ s1e_opr.s1exp_node of
      | S1Eqid (q, id) => begin case+ staspecid_of_qid (q, id) of
        | SPSIDarrow () => s1exp_arrow_tr_up
            (s1e0.s1exp_loc, None (), false, false, None (), s1ess_arg)
        | SPSIDnone () => let
          val ans = the_s2expenv_find_qua (q, id) in case+ ans of
          | ~Some_vt s2i => s1exp_qid_app_tr_up
              (s1e0.s1exp_loc, s1e_opr.s1exp_loc, q, id, s2i, s1ess_arg)
          | ~None_vt () => begin
              prerr_loc_error2 s1e.s1exp_loc;
              $Deb.debug_prerrf (": %s: s1exp_tr_up", @(THISFILENAME));
              prerr ": unrecognized static identifier [";
              $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
              prerr "].";
              prerr_newline ();
              $Err.abort {s2exp} ()
            end // end of [None_vt]
          end // end of [SPSIDnone]
        end // end of [S1Eqid]
      | S1Eimp (fc, lin, prf, oefc) => s1exp_arrow_tr_up 
          (s1e0.s1exp_loc, Some fc, lin>0, prf>0, oefc, '[s1es])
      | _ => let
          val s2e_opr = s1exp_tr_up s1e_opr
        in
          s1exp_app_tr_up (
            s1e0.s1exp_loc, s1e_opr.s1exp_loc, s2e_opr, s1ess_arg
          ) // end of [s1exp_app_tr_up]
        end // end of [_]
      // end of [case]
    end // end of [S1Eapp]
  | S1Echar c => s2exp_char c
  | S1Eexi (knd, s1qs, s1e_scope) => let
(*
      val () = begin
        print "s1exp_tr_up: S1Eexi: s1e0 = "; print s1e0; print_newline ()
      end // end of [val]
*)
//
      val () = if knd > 0 then let
        val () = prerr_loc_error2 (s1e0.s1exp_loc)
        val () = prerr (
          ": The existential quantifier #[...] is used incorrectly."
        ) // end of [val]
        val () = prerr_newline ()
      in
        $Err.abort {void} ()
      end // end of [val]
//
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val @(s2vs, s2ps) = s1qualst_tr (s1qs)
      val s2e_scope = s1exp_tr_dn_impredicative s1e_scope
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      s2exp_exi (s2vs, s2ps, s2e_scope)
    end // end of [S1Eexi]
  | S1Eextype (name, s1ess_arg) => let
      val s2ess_arg =
        s1explstlst_tr_dn_viewt0ype (s1ess_arg)
      // end of [val]
    in
      s2exp_extype_srt (s2rt_viewt0ype, name, s2ess_arg)
    end // end of [S1Eextype]
  | S1Eimp _ => begin
      prerr_loc_interror s1e0.s1exp_loc;
      prerr ": s1exp_tr_up: S1Eimp"; prerr_newline ();
      $Err.abort {s2exp} ()
    end // end of [S1Eimp]
  | S1Eint int(*string*) => s2exp_intinf ($IntInf.intinf_make_string(int))
  | S1Einvar (refval, s1e) => let
      val () = prerr_loc_error2 (s1e0.s1exp_loc)
      val () = prerr (
        ": an invariant type can only be assigned to the argument of a function."
      ) // end of [val]
      val () = prerr_newline ()
    in
      $Err.abort {s2exp} ()
    end // end of [S1Einvar]
  | S1Elam (s1as, os1t, s1e_body) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val s2vs = s1arglst_var_tr s1as; val s2e_body = (
        case+ os1t of
        | Some s1t => s1exp_tr_dn (s1e_body, s1rt_tr s1t)
        | None () => s1exp_tr_up s1e_body
      ) : s2exp // end of [val]
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
      val s2ts_arg = s2rtlst_of_s2varlst (s2vs)
      val s2t_res = s2e_body.s2exp_srt
    in
      s2exp_lam_srt (s2rt_fun (s2ts_arg, s2t_res), s2vs, s2e_body)
    end // end of [S1Elam]
  | S1Elist (npf, s1es) => begin
      s1exp_list_tr_up (s1e0.s1exp_loc, npf, s1es)
    end // end of [S1Elist]
(*
// HX-2010-12-04: simplification
  | S1Emod _ => let
      val () = prerr_loc_interror s1e0.s1exp_loc
      val () = prerr ": s1exp_tr_up: S1Emod: not implemented yet."
      val () = prerr_newline ()
    in
      $Err.abort {s2exp} ()
    end // end of [S1Emod]
*)
(*
// HX-2010-12-04: inadequate design
  | S1Enamed (name, s1e) => let
      val s2e = s1exp_tr_up (s1e) in
      s2exp_named (s2e.s2exp_srt, name, s2e)
    end // end of [S1Enamed]
*)
  | S1Eqid (q, id) => s1exp_qid_tr_up (s1e0.s1exp_loc, q, id)
  | S1Eread (_v, s1e) => s1exp_read_tr_up (_v, s1e)
(*
// HX-2010-11-01: simplification
  | S1Estruct (ls1es) => begin
      s1exp_struct_tr_up (s1e0.s1exp_loc, ls1es)
    end // end of [S1Estruct]
*)
  | S1Etop (knd, s1e) => s1exp_top_tr_up (knd, s1e)
  | S1Etrans _ => begin
      prerr_loc_error2 s1e0.s1exp_loc;
      prerr ": a transitional type can only be assigned to the argument of a function.";
      prerr_newline ();
      $Err.abort {s2exp} ()
    end // end of [S1Etrans]
  | S1Etyarr (s1e_elt, s1ess_dim) => let
      val s2e_elt = s1exp_tr_dn_viewt0ype s1e_elt
      val s2ess_dim = $Lst.list_map_fun (s1ess_dim, s1explst_tr_dn_int)
    in
      s2exp_tyarr (s2e_elt, s2ess_dim)
    end // end of [S1Etyarr]
  | S1Etyrec (recknd, ls1es) => begin
      s1exp_tyrec_tr_up (s1e0.s1exp_loc, recknd, ls1es)
    end // end of [S1Etyrec]
  | S1Etyrec_ext (name, ls1es) => begin
      s1exp_tyrec_ext_tr_up (s1e0.s1exp_loc, name, ls1es)
    end // end of [S1Etyrec_ext]
  | S1Etytup (tupknd, s1es) => begin
      s1exp_tytup_tr_up (s1e0.s1exp_loc, tupknd, s1es)
    end // end of [S1Etytup]
  | S1Etytup2 (tupknd, s1es1, s1es2) => begin
      s1exp_tytup2_tr_up (s1e0.s1exp_loc, tupknd, s1es1, s1es2)
    end // end of [S1Etytup2]
  | S1Euni (s1qs, s1e_scope) => let
      var s2vs: s2varlst = nil () and s2ps: s2explst = nil ()
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val @(s2vs, s2ps) = s1qualst_tr (s1qs)
      val s2e_scope = s1exp_tr_dn_impredicative s1e_scope
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      s2exp_uni (s2vs, s2ps, s2e_scope)
    end // end of [S1Euni]
  | S1Eunion (s2e_ind, ls2es) => begin
      s1exp_union_tr_up (s1e0.s1exp_loc, s2e_ind, ls2es)
    end // end of [S1Eunion]
(*
  | _ => begin
      prerr_loc_interror s1e0.s1exp_loc;
      prerr ": s1exp_tr: not available yet."; prerr_newine ();
      $Err.abort {s2exp} ()
    end // end of [_]
*)
end // end of [s1exp_tr_up]

implement
s1explst_tr_up (s1es) = $Lst.list_map_fun (s1es, s1exp_tr_up)
implement
s1explstlst_tr_up (s1ess) = $Lst.list_map_fun (s1ess, s1explst_tr_up)

(* ****** ****** *)

implement
tmps1explstlst_tr_up
  (ts1ess) = begin case+ ts1ess of
  | TMPS1EXPLSTLSTcons
      (loc, s1es, ts1ess) => let
      val s2e = s1explst_tr_up s1es
      val ts2ess = tmps1explstlst_tr_up ts1ess
    in
      TMPS2EXPLSTLSTcons (loc, s2e, ts2ess)
    end // end of [TMPS1EXPLSTLSTcons]
  | TMPS1EXPLSTLSTnil () => TMPS2EXPLSTLSTnil ()
end // end of [tmps1explstlst_tr]

(* ****** ****** *)

implement
s1exp_tr_dn (s1e0, s2t0) = begin
  case+ s1e0.s1exp_node of
  | S1Eextype (name, _arg) => let
      val _arg = s1explstlst_tr_dn_viewt0ype (_arg)
    in
      if s2rt_is_impredicative s2t0 then
        s2exp_extype_srt (s2t0, name, _arg) // [s2t0] can even be a view!
      else let
        val () = prerr_loc_error2 s1e0.s1exp_loc
        val () = $Deb.debug_prerrf (": %s: s1exp_tr_dn", @(THISFILENAME))
        val () = prerr ": the external type cannot be assigned the sort ["
        val () = prerr s2t0
        val () = prerr "]."
        val () = prerr_newline ()
      in
        $Err.abort ()
      end (* end of [if] *)
    end // end of [S1Eextype]
  | _ => let
      val s2e0 = s1exp_tr_up (s1e0)
      val s2t0_new = s2e0.s2exp_srt
    in
      if s2t0_new <= s2t0 then s2e0 else let
        val () = prerr_loc_error2 s1e0.s1exp_loc
        val () = $Deb.debug_prerrf (": %s: s1exp_tr_dn", @(THISFILENAME))
        val () = prerr ": the static expression is of sort ["
        val () = prerr_s2rt (s2t0_new)
        val () = prerr "] but it is expected to be of sort ["
        val () = prerr_s2rt (s2t0)
        val () = prerr "]."
        val () = prerr_newline ()
      in
        $Err.abort ()
      end (* end of [if] *)
    end // end of [_]
end (* end of [s1exp_tr_dn] *)

implement
s1explst_tr_dn (s1es, s2ts) = begin
  case+ s1es of
  | s1e :: s1es => let
      val+ s2t :: s2ts = s2ts
    in
      s1exp_tr_dn (s1e, s2t) :: s1explst_tr_dn (s1es, s2ts)
    end // end of [::]
  | nil () => nil ()
end // end of [s1explst_tr_dn]

(* ****** ****** *)

implement
s1exparg_tr (s1a) = begin
  case+ s1a.s1exparg_node of
  | S1EXPARGone () => s2exparg_one (s1a.s1exparg_loc)
  | S1EXPARGall () => s2exparg_all (s1a.s1exparg_loc)
  | S1EXPARGseq (s2es) => begin
      s2exparg_seq (s1a.s1exparg_loc, s1explst_tr_up s2es)
    end // end of [S1EXPARGseq]
end // end of [s1exparg_tr]

implement
s1exparglst_tr (s1as) = $Lst.list_map_fun (s1as, s1exparg_tr)

(* ****** ****** *)

fn s1rtdef_tr
  (d: s1rtdef): void = let
  val id = d.s1rtdef_sym and s2te = s1rtext_tr (d.s1rtdef_def)
in
  the_s2rtenv_add (id, s2te)
end // end of [s1rtdef_tr]

implement
s1rtdeflst_tr (ds): void = begin case+ ds of
  | cons (d, ds) => (s1rtdef_tr d; s1rtdeflst_tr ds) | nil () => ()
end // end of [s1rtdeflst_tr]

(* ****** ****** *)

fn d1atarg_tr (
  d1a: d1atarg
) : @(symopt_t, s2rt, int) = begin
  case+ d1a.d1atarg_node of
  | D1ATARGsrt s1tp => let
      val s2t = s1rt_tr (s1tp.s1rtpol_srt)
    in
      @(None (), s2t, s1tp.s1rtpol_pol)
    end // end of [D1ATARGsrt]
  | D1ATARGidsrt (id, s1tp) => let
      val s2t = s1rt_tr (s1tp.s1rtpol_srt)
    in
      @(Some id, s2t, s1tp.s1rtpol_pol)
    end // end of [D1ATARGidsrt]
end // end of [d1atarg_tr]

implement
d1atarglst_tr (d1as) = begin case+ d1as of
  | cons (d1a, d1as) => cons (d1atarg_tr d1a, d1atarglst_tr d1as)
  | nil () => nil ()
end // end of [d1atarglst_tr]

fn s1tacon_tr (
  s2t_res: s2rt, d: s1tacon
) : void = let
  val id = d.s1tacon_sym
  val fil = d.s1tacon_fil
  val loc = d.s1tacon_loc
  val argvar = (case+ d.s1tacon_arg of
    | Some d1as => Some (d1atarglst_tr d1as) | None () => None ()
  ) : Option (List @(symopt_t, s2rt, int))
  val s2t_fun = (
    case+ argvar of
    | Some xs => let
        fun aux (xs: List @(symopt_t, s2rt, int)): s2rtlst =
          case+ xs of
            | cons (x, xs) => cons (x.1, aux xs) | nil () => nil ()
        val s2ts_arg = aux xs
      in
        s2rt_fun (s2ts_arg, s2t_res)
      end
    | None => s2t_res
  ) : s2rt // end of [val]
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val s2vs_opt = let
    fun aux (
      xs: List @(symopt_t, s2rt, int)
    ) : s2varlst =
      case+ xs of
      | cons (x, xs) => let
          val s2v = case+ x.0 of
            | Some id => s2var_make_id_srt (id, x.1)
            | None () => s2var_make_srt (x.1)
        in
          the_s2expenv_add_svar s2v; cons (s2v, aux xs)
        end
      | nil () => nil ()
    // end of [aux]
  in
    case+ argvar of Some xs => Some (aux xs) | None () => None ()
  end : Option (s2varlst) // end of [val]
  val def = (
    case+ d.s1tacon_def of
    | Some s1e => let
        val s2e = s1exp_tr_dn (s1e, s2t_res)
        val s2e_def = case+ s2vs_opt of
          | Some s2vs => s2exp_lam_srt (s2t_fun, s2vs, s2e) | None => s2e
        // end of [s2e_def]
      in
        Some s2e_def
      end // end of [Some]
    | None () => None ()
  ) : s2expopt // end of [val]
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))
  val s2c = s2cst_make (
      id // sym
    , loc // location
    , s2t_fun // srt
    , Some def // isabs
    , true // iscon
    , false // isrec
    , false // isasp
    , None () // islst
    , argvar // argvar
    , None () // def
    ) // end of [s2cst_make]
  // end of [val]
  val () = s2cst_set_fil (s2c, Some (fil))
in
  the_s2expenv_add_scst (s2c)
end // end of [s1tacon_tr]

implement
s1taconlst_tr (absknd, ds) = let
  fun aux (
    s2t: s2rt, ds: s1taconlst
  ) : void = case+ ds of
    | cons (d, ds) => (s1tacon_tr (s2t, d); aux (s2t, ds)) | nil () => ()
  // end of [aux]
  val s2t = (case+ absknd of
    | $Syn.ABSKINDprop () => s2rt_prop
    | $Syn.ABSKINDtype () => s2rt_type
    | $Syn.ABSKINDt0ype () => s2rt_t0ype
    | $Syn.ABSKINDview () => s2rt_view
    | $Syn.ABSKINDviewtype () => s2rt_viewtype
    | $Syn.ABSKINDviewt0ype () => s2rt_viewt0ype
  ) : s2rt // end of [val]
in
  aux (s2t, ds)
end // end of [s1taconlst_tr]

(* ****** ****** *)

fn s1tacst_tr
  (d: s1tacst): void = let
  val id = d.s1tacst_sym
  val loc = d.s1tacst_loc
  val s2t_res = s1rt_tr (d.s1tacst_res)
  val s2t = (case+ d.s1tacst_arg of
    | Some s1ts => s2rt_fun (s1rtlst_tr s1ts, s2t_res)
    | None () => s2t_res
  ) : s2rt // end of [val]
  val s2c = s2cst_make (
      id // sym
    , loc // location
    , s2t // srt
    , None () // isabs
    , false // iscon
    , false // isrec
    , false // isasp
    , None () // islst
    , None () // argvar
    , None () // def
  ) // end of [s2cst_make]
in
  the_s2expenv_add_scst s2c
end // end of [s1tacst_tr]

implement
s1tacstlst_tr (ds) = begin case+ ds of
  | cons (d, ds) => (s1tacst_tr d; s1tacstlst_tr ds) | nil () => ()
end // end of [s1tacstlst_tr]

(* ****** ****** *)

fun s1tavar_tr
  (d: s1tavar): s2tavar = let
  val s2t = s1rt_tr (d.s1tavar_srt)
  val s2v = s2var_make_id_srt (d.s1tavar_sym, s2t)
  val () = the_s2expenv_add_svar s2v
in
  s2tavar_make (d.s1tavar_loc, s2v)
end // end of [s1tavar_tr]

implement
s1tavarlst_tr (ds) = $Lst.list_map_fun (ds, s1tavar_tr)

(* ****** ****** *)

fn d1atsrtdec_tr (
  res: s2rt, d1c: d1atsrtdec
) : s2cstlst = let
//
  fn aux (
    i: int, res: s2rt, d1c: d1atsrtcon
  ) : s2cst_t = let
    val id = d1c.d1atsrtcon_sym
    val loc = d1c.d1atsrtcon_loc
    val arg = s1rtlst_tr d1c.d1atsrtcon_arg
    val s2t = s2rt_fun (arg, res)
    val s2c = s2cst_make (
      id // sym
    , loc // location
    , s2t // srt
    , None () // isabs
    , true // iscon
    , false // isrec
    , false // isasp
    , None () // islst
    , None () // argvar
    , None () // def
    ) // end of [s2cst_make]
    val () = s2cst_set_tag (s2c, i)
  in
    the_s2expenv_add_scst s2c; s2c
  end // end of [aux]
//
  fun auxlst (i: int, res: s2rt, d1cs: d1atsrtconlst): s2cstlst =
    case+ d1cs of
    | cons (d1c, d1cs) => begin
        S2CSTLSTcons (aux (i, res, d1c), auxlst (i+1, res, d1cs))
      end // end of [cons]
    | nil () => S2CSTLSTnil ()
  // end of [auxlst]
//
in
  auxlst (0, res, d1c.d1atsrtdec_con)
end // end of [d1atsrtdec_tr]

implement
d1atsrtdeclst_tr (d1cs) = let
//
  viewtypedef VT = List_vt @(d1atsrtdec, s2rtdat_t, s2rt)
//
  fun loop1 (xs0: VT): void =
    case+ xs0 of
    | ~list_vt_cons (x, xs) => let
        val s2cs = d1atsrtdec_tr (x.2, x.0)
        val () = s2rtdat_set_conlst (x.1, s2cs)
      in
        loop1 xs
      end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  // end of [loop1]
//
  fun loop2 (
    d1cs: d1atsrtdeclst, res: VT
  ) : void =
    case+ d1cs of
    | list_cons (d1c, d1cs) => let
        val id = d1c.d1atsrtdec_sym
        val loc = d1c.d1atsrtdec_loc
        val s2td = s2rtdat_make id
        val s2t = S2RTbas (S2RTBASdef s2td)
        val s2t_eq = s2rt_fun ('[s2t, s2t], s2rt_bool)
        val s2c_eq = s2cst_make (
          $Sym.symbol_EQEQ // sym
        , loc // location
        , s2t_eq // srt
        , None () // isabs
        , false // iscon
        , false // isrec
        , false // isasp
        , None () // islst
        , None () // argvar 
        , None () // def
        ) // end of [val]
        val () = the_s2expenv_add_scst s2c_eq
        val () = the_s2rtenv_add (id, S2TEsrt s2t)
      in
        loop2 (d1cs, list_vt_cons (@(d1c, s2td, s2t), res))
      end // end of [list_cons]
    | list_nil () => loop1 res
  // end of [loop2]
//
in
  loop2 (d1cs, list_vt_nil ())
end // end of [d1atsrtdeclst_tr]

(* ****** ****** *)

fn s1expdef_s1aspdec_tr_main (
  loc0: loc_t
, s1ass: s1arglstlst, res: s2rtopt, body: s1exp
) : s2exp = let 
//
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val s2vss = (s1arglstlst_var_tr s1ass): s2varlstlst
  val body = case+ res of
    | Some s2t => s1exp_tr_dn (body, s2t) | _ => s1exp_tr_up body
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))
//
  fun aux (
    body: s2exp, s2vss: s2varlstlst
  ) : s2exp = begin
    case+ s2vss of
    | s2vs :: s2vss => let
        val body = aux (body, s2vss)
        val s2ts_arg = s2rtlst_of_s2varlst s2vs
        val s2t_fun = s2rt_fun (s2ts_arg, body.s2exp_srt)
      in
        s2exp_lam_srt (s2t_fun, s2vs, body)
      end // end of [::]
    | nil () => body
  end // end of [aux]
//
in
  aux (body, s2vss)
end // end of [s1expdef_s1aspdec_tr_main]

(* ****** ****** *)

implement
s1expdef_tr (res, d1c) = let
  fn err (d1c: s1expdef): void = begin
    prerr_loc_error2 d1c.s1expdef_loc;
    $Deb.debug_prerrf (": %s: s1expdef_tr", @(THISFILENAME));
    prerr ": the sort for the definition does not match";
    prerr " the sort assigned to the static constant [";
    $Sym.prerr_symbol d1c.s1expdef_sym;
    prerr "].";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [err]
  val res = (case+ d1c.s1expdef_res of
    | Some s1t => let
        val s2t1 = s1rt_tr s1t; val () = case+ res of
          | Some s2t => if (s2t1 <= s2t) then () else err (d1c)
          | None () => ()
        // end of [val]
      in
        Some s2t1
      end // end of [Some]
    | None () => res
  ) : s2rtopt
  val s2e = s1expdef_s1aspdec_tr_main
    (d1c.s1expdef_loc, d1c.s1expdef_arg, res, d1c.s1expdef_def)
  // end of [val]
in
  s2cst_make (
    d1c.s1expdef_sym // symbol
  , d1c.s1expdef_loc // location
  , s2e.s2exp_srt // srt
  , None () // isabs
  , false // iscon
  , false // isrec
  , false // isasp
  , None () // islst
  , None () // argvar
  , Some s2e // def
  ) // end of [s2cst_make]
end // end of [s1expdef_tr]

implement
s1expdeflst_tr (res, d1cs) = let
  val s2cs = aux (res, d1cs) where {
    fun aux
      (res: s2rtopt, d1cs: s1expdeflst)
      : List_vt (s2cst_t) = case+ d1cs of
      | list_cons (d1c, d1cs) => let
          val s2c = s1expdef_tr (res, d1c)
        in
          list_vt_cons (s2c, aux (res, d1cs))
        end // end of [list_cons]
      | list_nil () => list_vt_nil ()
    // end of [aux]
  } // end of [val]
  val () = aux s2cs where {
    fun aux (s2cs: List_vt s2cst_t): void =
      case+ s2cs of
      | ~list_vt_cons (s2c, s2cs) => let
          val () = the_s2expenv_add_scst s2c in aux s2cs
        end // end of [list_vt_cons]
      | ~list_vt_nil () => ()
    // end of [aux]
  } // end of [val]
in
  // empty
end // end of [s1expdeflst_tr]

(* ****** ****** *)

implement
s1aspdec_tr (d1c) = let
//
fn err1 (
  loc: loc_t
, q: $Syn.s0taq, id: sym_t,
  s2t_s2c: s2rt, s2t_s2e: s2rt
) : s2aspdec = begin
  prerr_loc_error2 loc;
  $Deb.debug_prerrf (": %s: s1aspdec_tr: err1", @(THISFILENAME));
  prerr ": sort mismatch";
  prerr ": the sort of the static constant [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] is [";
  prerr s2t_s2c;
  prerr "] while the sort of its definition is [";
  prerr s2t_s2e;
  prerr "].";
  prerr_newline ();
  $Err.abort {s2aspdec} ()
end // end of [err1]
//
(*
fn err2 (
  loc: loc_t
, q: $Syn.s0taq, id: sym_t
) : s2aspdec = begin
  prerr_loc_error2 loc;
  $Deb.debug_prerrf (": %s: s1aspdec_tr: err2", @(THISFILENAME));
  prerr ": the static constant referred to by [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] cannot be uniquely resolved.";
  prerr_newline ();
  $Err.abort {s2aspdec} ()
end // end of [err2]
*)
//
fn err3 (
  loc: loc_t
, q: $Syn.s0taq, id: sym_t
) : s2aspdec = begin
  prerr_loc_error2 loc;
  $Deb.debug_prerrf (": %s: s1aspdec_tr: err3", @(THISFILENAME));
  prerr ": the static constant [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] is not abstract.";
  prerr_newline ();
  $Err.abort {s2aspdec} ()
end // end of [err3]
//
fn err4 (
  loc: loc_t
, q: $Syn.s0taq, id: sym_t
) : s2aspdec = begin
  prerr_loc_error2 loc;
  $Deb.debug_prerrf (": %s: s1aspdec_tr: err4", @(THISFILENAME));
  prerr ": the identifier [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] does not refer to a static constant.";
  prerr_newline ();
  $Err.abort {s2aspdec} ()
end // end of [err4]
//
fn err5 (
  loc: loc_t
, q: $Syn.s0taq, id: sym_t
) : s2aspdec = begin
  prerr_loc_error2 loc;
  $Deb.debug_prerrf (": %s: s1aspdec_tr: err5", @(THISFILENAME));
  prerr ": the identifier [";
  $Syn.prerr_s0taq q; $Sym.prerr_symbol id;
  prerr "] is unrecognized.";
  prerr_newline ();
  $Err.abort {s2aspdec} ()
end // end of [err5]
//
  val fil = d1c.s1aspdec_fil
  val loc = d1c.s1aspdec_loc
  val qid = d1c.s1aspdec_qid
  val q = qid.sqi0de_qua and id = qid.sqi0de_sym
  val os2i = the_s2expenv_find_qua (q, id)
in
  case+ os2i of
  | ~Some_vt s2i => begin case+ s2i of
    | S2ITEMcst s2cs => let
        val s2cs = filter s2cs where {
          fun filter (s2cs: s2cstlst): s2cstlst =
            case+ s2cs of
            | S2CSTLSTcons (s2c, s2cs) => begin
              case+ 0 of
              | _ when s2cst_is_abstract s2c =>
                  S2CSTLSTcons (s2c, filter s2cs)
              | _ => filter s2cs
              end // end of [S2CSTLSTcons]
            | S2CSTLSTnil () => S2CSTLSTnil ()
        } // end of [val]
      in
        case+ s2cs of
        | S2CSTLSTcons (s2c, _) => let
            val res = s1rtopt_tr d1c.s1aspdec_res
            val s2e = s1expdef_s1aspdec_tr_main
              (loc, d1c.s1aspdec_arg, res, d1c.s1aspdec_def)
(*
            // definition binding is to be done in [ats_trans3_dec.dats]
*)
            val s2t_s2e = s2e.s2exp_srt
            val s2t_s2c = s2cst_get_srt (s2c)
          in
            if s2t_s2e <= s2t_s2c then begin
              s2aspdec_make (fil, loc, s2c, s2e)
            end else begin
              err1 (loc, q, id, s2t_s2c, s2t_s2e)
            end // end of [if]
          end // end of [S2CSTLSTcons]
        | S2CSTLSTnil () => begin
            err3 (loc, q, id) // [s2c] is not abstract!
          end // end of [if]
      end // end of [S2ITEMcst]
    | _ => err4 (loc, q, id)
    end // end of [Some_vt]
  | ~None_vt () => err5 (loc, q, id)
end // end of [s1aspdec_tr]

(* ****** ****** *)

fn d1atcon_tr (
    s2c: s2cst_t
  , islin: bool
  , isprf: bool
  , s2vs0: s2varlst
  , fil: fil_t
  , d1c: d1atcon
  ) : d2con_t = let

  fn err1 (loc: loc_t, id: sym_t): s2explstopt = begin
    prerr_loc_error2 loc;
    prerr ": fewer indexes are needed for the constructor [";
    $Sym.prerr_symbol id; prerr "]"; prerr_newline ();
    $Err.abort {s2explstopt} ()
  end // end of [err1]

  fn err2 (loc: loc_t, id: sym_t): s2explstopt = begin
    prerr_loc_error2 loc;
    prerr ": more indexes are needed for the constructor [";
    $Sym.prerr_symbol id; prerr "]"; prerr_newline ();
    $Err.abort {s2explstopt} ()
  end // end of [err2]

  fn err3 (loc: loc_t, id: sym_t): s2explstopt = begin
    prerr_loc_error2 loc;
    prerr ": no indexes are needed for the constructor [";
    $Sym.prerr_symbol id; prerr "]"; prerr_newline ();
    $Err.abort {s2explstopt} ()
  end // end of [err3]

  fn err4 (loc: loc_t, id: sym_t): s2explstopt = begin
    prerr_loc_error2 loc;
    prerr ": some indexes are needed for the constructor [";
    $Sym.prerr_symbol id; prerr "]"; prerr_newline ();
    $Err.abort {s2explstopt} ()
  end // end of [err4]

  val loc = d1c.d1atcon_loc and id = d1c.d1atcon_sym
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val () = the_s2expenv_add_svarlst s2vs0
  var s2vpslst: s2qualst = s1qualstlst_tr (d1c.d1atcon_qua)
  val () = case+ s2vs0 of
    | cons _ => s2vpslst := cons (@(s2vs0, nil ()), s2vpslst)
    | nil () => ()
  var os2ts_s2c_ind: s2rtlstopt = None ()
  val () = case+ s2cst_get_srt s2c of
    | S2RTfun (s2ts, s2t) => (os2ts_s2c_ind := Some s2ts) | s2t => ()
  val npf = d1c.d1atcon_npf and s1es_arg = d1c.d1atcon_arg
  val s2es_arg = let
    val s2t_pfarg = (
      if islin then s2rt_view else s2rt_prop
    ) : s2rt
    val s2t_arg = (
      if isprf then s2t_pfarg else begin
        if islin then s2rt_viewt0ype else s2rt_t0ype
      end // end of [if]
    ) : s2rt
    fun aux (i: int, s1es: s1explst):<cloref1> s2explst = begin
      case+ s1es of
      | cons (s1e, s1es) => let
          val s2t = (if i < npf then s2t_pfarg else s2t_arg): s2rt
        in
          cons (s1exp_tr_dn (s1e, s2t), aux (i+1, s1es))
        end // end of [cons]
      | nil () => nil () // end of [nil]
    end // end of [aux]
  in
    aux (0, s1es_arg)
  end // end of [val]
  val os2ts_s2c_ind = (os2ts_s2c_ind: s2rtlstopt)
  val os2es_ind = (
    case+ (d1c.d1atcon_ind, os2ts_s2c_ind) of
    | (Some s1es, Some s2ts) => let
        val n1 = $Lst.list_length (s1es)
        and n2 = $Lst.list_length (s2ts)
      in
        case+ compare (n1, n2) of
        | 0 => Some (s1explst_tr_dn (s1es, s2ts))
        | 1 => err1 (loc, id)
        | _ (*~1*) => err2 (loc, id)
      end
    | (None (), None ()) => None ()
    | (Some _, None _) => err3 (loc, id)
    | (None _, Some _) => err4 (loc, id)
  ) : s2explstopt
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))
  val vwtp = (if isprf then 0 else if islin then 1 else 0): int
  val d2c = d2con_make
    (loc, fil, id, s2c, vwtp, s2vpslst, npf, s2es_arg, os2es_ind)
  val () = the_d2expenv_add_dcon d2c; val () =
    if isprf then () else let
      val () = the_s2expenv_add_datcontyp d2c // struct
    in
      if islin then the_s2expenv_add_datconptr d2c // unfold
    end // end of [if]
  // end of [val]
in
  d2c
end // end of [d1atcon_tr]

fun d1atconlst_tr (
    s2c: s2cst_t
  , islin: bool
  , isprf: bool
  , s2vs0: s2varlst
  , fil: fil_t
  , d1cs: d1atconlst
  ) : d2conlst = begin case+ d1cs of
  | cons (d1c, d1cs) => let
      val d2c = d1atcon_tr (s2c, islin, isprf, s2vs0, fil, d1c)
    in
      D2CONLSTcons (d2c, d1atconlst_tr (s2c, islin, isprf, s2vs0, fil, d1cs))
    end // end of [cons]
  | nil () => D2CONLSTnil () // end of [nil]
end // end of [d1atconlst_tr]

(* ****** ****** *)

fn d1atdec_tr (
  s2c: s2cst_t, s2vs0: s2varlst, d1c: d1atdec
) : void = let
  val s2t_s2c = begin
    case+ s2cst_get_srt (s2c) of S2RTfun (s2ts, s2t) => s2t | s2t => s2t
  end // end of [val]
  val islin = s2rt_is_linear s2t_s2c and isprf = s2rt_is_proof s2t_s2c
  val d2cs = d1atconlst_tr
    (s2c, islin, isprf, s2vs0, d1c.d1atdec_fil, d1c.d1atdec_con)
  // end of [val]
  val () = let // assigning tags to dynamic constructors
    fun aux (i: int, d2cs: d2conlst): void = case+ d2cs of
      | D2CONLSTcons (d2c, d2cs) => (d2con_set_tag (d2c, i); aux (i+1, d2cs))
        // end of [D2CONLSTcons]
      | D2CONLSTnil () => ()
    // end of [aux]
  in
    aux (0, d2cs)
  end // end of [val]
  val islst = (case+ d2cs of
    | D2CONLSTcons (d2c1, D2CONLSTcons (d2c2, D2CONLSTnil ())) =>
        if d2con_get_arity_real (d2c1) = 0 then begin
          if d2con_get_arity_real (d2c2) > 0 then Some @(d2c1, d2c2)
          else None ()
        end else begin
          if d2con_get_arity_real (d2c2) = 0 then Some @(d2c2, d2c1)
          else None ()
        end
      // end of [D2CONLSTcons (_, D2CONSLSTcons (_, D2CONLSTnil))
    | _ => None ()
  ) : Option @(d2con_t, d2con_t)
  val () = s2cst_set_islst (s2c, islst)
  val () = s2cst_set_conlst (s2c, Some d2cs)
in
  // nothing
end // end of [d1atdec_tr]

implement
d1atdeclst_tr (
  datknd, d1cs_dat, d1cs_def
) = let
//
  val s2t_res = s2rt_datakind datknd
  typedef T = List @(d1atdec, s2cst_t, s2varlst)
//
  val d1cs2cs2vslst = let
//
    var res: T = list_nil ()
//
    fun aux .<>. (
      d1c: d1atdec, res: &T
    ) :<cloref1> void = let
      val argvar = (
        case+ d1c.d1atdec_arg of
        | Some d1as => Some (d1atarglst_tr d1as)
        | None () => None () 
      ) : Option (List @(symopt_t, s2rt, int))
      val s2vs = let
        fun aux
          (xs: List @(symopt_t, s2rt, int)): s2varlst =
          case+ xs of
          | list_cons (x, xs) => begin case+ x.0 of
            | Some id => begin
                list_cons (s2var_make_id_srt (id, x.1), aux xs)
              end // end of [Some]
            | None () => aux xs
            end // end of [list_cons]
          | list_nil () => list_nil ()
        // end of [aux]
      in
        case+ argvar of Some xs => aux xs | None () => nil ()
      end : s2varlst
//
      val os2ts_arg = let
        fun aux
          (xs: List @(symopt_t, s2rt, int)): s2rtlst =
          case+ xs of
          | list_cons (x, xs) => list_cons (x.1, aux xs)
          | list_nil () => list_nil ()
        // end of [aux]
      in
        case+ argvar of Some xs => Some (aux xs) | None () => None ()
      end : s2rtlstopt
//
      val s2c = s2cst_make_dat (
        d1c.d1atdec_sym, d1c.d1atdec_loc, os2ts_arg, s2t_res, argvar
      ) // end of [val]
      val () = the_s2expenv_add_scst s2c
//
    in
      res := cons (@(d1c, s2c, s2vs), res)
    end // end of [val]
//
    fun auxlst (
      d1cs: d1atdeclst, res: &T
    ) :<cloref1> void = case+ d1cs of
      | list_cons (d1c, d1cs) => (aux (d1c, res); auxlst (d1cs, res))
      | list_nil () => ()
    // end of [auxlst]
//
  in
    auxlst (d1cs_dat, res); res
  end : T // end of [d1cs2cs2vslst]
//
  val () = aux (d1cs_def) where {
    fun aux (
      d1cs: s1expdeflst
    ) : void = begin case+ d1cs of
      | list_cons (d1c, d1cs) => let
          val s2c = s1expdef_tr (None, d1c)
          val () = the_s2expenv_add_scst (s2c)
        in
          aux (d1cs)
        end // end of [cons]
      | list_nil () => () // end of [list_nil]
    end (* end of [aux] *)
  } // end of [val]
//
  fun aux (xs: T): s2cstlst = case+ xs of
    | list_cons (x, xs) => begin
        d1atdec_tr (x.1, x.2, x.0); S2CSTLSTcons (x.1, aux xs)
      end // end of [cons]
    | list_nil () => S2CSTLSTnil ()
  // end of [aux]
in
  aux (d1cs2cs2vslst)
end // end of [d1atdeclst_tr]

(* ****** ****** *)

(* [exn] is considered a viewtype constructor *)
fn e1xndec_tr
  (s2c: s2cst_t, d1c: e1xndec): d2con_t = let
  val loc = d1c.e1xndec_loc
  val fil = d1c.e1xndec_fil and id = d1c.e1xndec_sym
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val s2vpslst = s1qualstlst_tr (d1c.e1xndec_qua)
  val npf = d1c.e1xndec_npf
  val s1es_arg = d1c.e1xndec_arg
  val s2es_arg = s1explst_tr_dn_viewt0ype s1es_arg
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))
  val d2c = d2con_make
    (loc, fil, id, s2c, 1(*vwtp*), s2vpslst, npf, s2es_arg, None(*ind*))
  val () = d2con_set_tag (d2c, ~1)
in
  the_d2expenv_add_dcon d2c; d2c
end // end of [e1xndec_tr]

fun d2conlst_revapp
  (d2cs1: d2conlst, d2cs2: d2conlst): d2conlst = begin
  case+ d2cs1 of
  | D2CONLSTcons (d2c1, d2cs1) => begin
      d2conlst_revapp (d2cs1, D2CONLSTcons (d2c1, d2cs2))
    end (* end of [D2CONLSTcons] *)
  | D2CONLSTnil () => d2cs2
end // end of [d2conlst_revapp]

implement
e1xndeclst_tr (d1cs) = d2cs where {
  fun aux (s2c: s2cst_t, d1cs: e1xndeclst): d2conlst =
    case+ d1cs of
    | cons (d1c, d1cs) => let
        val d2c = e1xndec_tr (s2c, d1c)
      in
        D2CONLSTcons (d2c, aux (s2c, d1cs))
      end
    | nil () => D2CONLSTnil ()
  // end of [aux]
  val s2c = s2cstref_get_cst (Exception_viewtype)
  val d2cs = aux (s2c, d1cs)
  val d2cs0 = case+ s2cst_get_conlst (s2c) of
    | Some d2cs0 => d2conlst_revapp (d2cs, d2cs0) | None () => d2cs
  // end of [val]
  val () = s2cst_set_conlst (s2c, Some d2cs0)
} // end of [e1xndeclst_tr]

(* ****** ****** *)

(* end of [ats_trans2_sta.dats] *)
