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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2007

(* ****** ****** *)

staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload PM = "ats_posmark.sats"

(* ****** ****** *)

staload "ats_syntax.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef loc_t = $Loc.location_t

(* ****** ****** *)

fn externloc_posmark
  (loc: loc_t): void = let
  val loc_begoff = $Loc.location_begpos_toff loc
  val loc_endoff = $Loc.location_endpos_toff loc
in
  $PM.posmark_insert_extern_beg loc_begoff;
  $PM.posmark_insert_extern_end loc_endoff;
end // end of [externloc_posmark]

fn neuexploc_posmark
  (loc: loc_t): void = let
  val loc_begoff = $Loc.location_begpos_toff loc
  val loc_endoff = $Loc.location_endpos_toff loc
in
  $PM.posmark_insert_neuexp_beg loc_begoff;
  $PM.posmark_insert_neuexp_end loc_endoff;
end // end of [neuexploc_posmark]

fn staexploc_posmark
  (loc: loc_t): void = let
  val loc_begoff = $Loc.location_begpos_toff loc
  val loc_endoff = $Loc.location_endpos_toff loc
in
  $PM.posmark_insert_staexp_beg loc_begoff;
  $PM.posmark_insert_staexp_end loc_endoff;
end // end of [staexploc_posmark]

fn prfexploc_posmark
  (loc: loc_t): void = let
  val loc_begoff = $Loc.location_begpos_toff loc
  val loc_endoff = $Loc.location_endpos_toff loc
in
  $PM.posmark_insert_prfexp_beg loc_begoff;
  $PM.posmark_insert_prfexp_end loc_endoff;
end // end of [prfexploc_posmark]

(* ****** ****** *)

fn e0xp_posmark (e: e0xp): void =
  neuexploc_posmark (e.e0xp_loc)

fn s0exp_posmark (s0e: s0exp): void =
  staexploc_posmark (s0e.s0exp_loc)

fun s0explst_posmark (s0es: s0explst): void =
  $Lst.list_foreach_fun (s0es, s0exp_posmark) 

fn s0expopt_posmark (os0e: s0expopt): void =
  case+ os0e of Some s0e => s0exp_posmark s0e | None () => ()
// end of [s0expopt_posmark]

fn s0explstlst_posmark
  (s0ess: s0explstlst): void =
  $Lst.list_foreach_fun (s0ess, s0explst_posmark) 

fun labs0explst_posmark
  (ls0es: labs0explst): void =
  case+ ls0es of
  | LABS0EXPLSTcons (lab, s0e, ls0es) => let
      val loc1 = lab.l0ab_loc and loc2 = s0e.s0exp_loc
      val loc_begoff = $Loc.location_begpos_toff loc1
      val () = $PM.posmark_insert_staexp_beg loc_begoff
      val loc_endoff = $Loc.location_endpos_toff loc2
      val () = $PM.posmark_insert_staexp_end loc_endoff
    in
      labs0explst_posmark (ls0es)
    end // end of [LABS0EXPcons]
  | LABS0EXPLSTnil () => ()
// end of [labs0explst_posmark]

fun t1mps0explstlst_posmark
  (ts0ess: t1mps0explstlst): void =
  case+ ts0ess of
  | T1MPS0EXPLSTLSTcons (_(*loc*), s0es, ts0ess) => begin
      s0explst_posmark s0es; t1mps0explstlst_posmark ts0ess
    end // end of [T1MPS0EXPLSTLSTcons]
  | T1MPS0EXPLSTLSTnil () => ()
// end of [tmps0explstlst_posmark]

(* ****** ****** *)

fn s0arg_posmark (s0a: s0arg): void =
  staexploc_posmark (s0a.s0arg_loc)

fn s0arglst_posmark (s0as: s0arglst): void =
  $Lst.list_foreach_fun (s0as, s0arg_posmark)

fn s0arglstlst_posmark (s0ass: s0arglstlst): void =
  $Lst.list_foreach_fun (s0ass, s0arglst_posmark)

(* ****** ****** *)

fn s0qua_posmark (s0q: s0qua): void =
  staexploc_posmark (s0q.s0qua_loc)

fn s0qualst_posmark (s0qs: s0qualst): void =
 $Lst.list_foreach_fun (s0qs, s0qua_posmark)

fn s0qualstlst_posmark (s0qss: s0qualstlst): void =
 $Lst.list_foreach_fun (s0qss, s0qualst_posmark)

(* ****** ****** *)

fn e0fftag_posmark (tag: e0fftag): void =
  staexploc_posmark (tag.e0fftag_loc)

fn e0fftaglst_posmark (tags: e0fftaglst): void =
  $Lst.list_foreach_fun (tags, e0fftag_posmark) 

fn e0fftaglstopt_posmark
  (otags: e0fftaglstopt): void = case+ otags of
  | Some tags => e0fftaglst_posmark tags | None () => () 
// end of [e0fftaglstopt_posmark]

(* ****** ****** *)

fn p0at_prf_posmark (p0t: p0at): void = begin
  prfexploc_posmark p0t.p0at_loc; p0at_posmark p0t;
end // end of [p0at_prf_posmark]

fun p0atlst_prf_posmark (p0ts: p0atlst): void =
  $Lst.list_foreach_fun (p0ts, p0at_prf_posmark)

fn p0atopt_posmark (op0t: p0atopt): void =
  case+ op0t of Some p0t => p0at_posmark p0t | None () => ()
// end of [p0atopt_posmark]

fun labp0atlst_posmark (lp0ts: labp0atlst): void =
  case+ lp0ts of
  | LABP0ATLSTcons (_(*lab*), p0t, lp0ts) => begin
      p0at_posmark p0t; labp0atlst_posmark lp0ts
    end // end of [LABP0ATLSTcons]
  | _ => ()
// end of [labp0atlst_posmark]

implement
p0at_posmark (p0t) = case+ p0t.p0at_node of
  | P0Tann (p0t, s0e) => begin
      p0at_posmark p0t; staexploc_posmark (s0e.s0exp_loc);
    end
  | P0Tapp (p0t1, p0t2) => begin
      p0at_posmark p0t1; p0at_posmark p0t2;
    end
  | P0Tas (_(*id*), p0t) => p0at_posmark p0t
  | P0Texist s0as => s0arglst_posmark s0as
  | P0Tfree p0t => p0at_posmark p0t
  | P0Tlist (p0ts) => p0atlst_posmark p0ts
  | P0Tlist2 (p0ts1, p0ts2) => begin
      p0atlst_prf_posmark p0ts1; p0atlst_posmark p0ts2;
    end
  | P0Tlst p0ts => p0atlst_posmark p0ts
  | P0Trec (_(*recknd*), lp0ts) => labp0atlst_posmark lp0ts
  | P0Tsvararg s0vs => staexploc_posmark (p0t.p0at_loc)
  | P0Ttup (_(*tupknd*), p0ts) => p0atlst_posmark p0ts
  | P0Ttup2 (_(*tupknd*), p0ts1, p0ts2) => begin
      p0atlst_prf_posmark p0ts1; p0atlst_posmark p0ts2;
    end
  | _ => ()
// end of [p0at_posmark]

implement p0atlst_posmark (p0ts) =
  $Lst.list_foreach_fun (p0ts, p0at_posmark)

(* ****** ****** *)

fn p0arg_posmark (p0a: p0arg): void =
  s0expopt_posmark (p0a.p0arg_ann)

fn p0arglst_posmark (p0as: p0arglst) =
  $Lst.list_foreach_fun (p0as, p0arg_posmark)


fn p0arg_prf_posmark (p0a: p0arg): void = begin
  prfexploc_posmark (p0a.p0arg_loc); s0expopt_posmark (p0a.p0arg_ann)
end // end of [p0arg_prf_posmark]

fn p0arglst_prf_posmark (p0as: p0arglst) =
  $Lst.list_foreach_fun (p0as, p0arg_prf_posmark)

(* ****** ****** *)

fn d0arg_posmark (d0a: d0arg): void =
  case+ d0a.d0arg_node of
  | D0ARGsta _ => staexploc_posmark (d0a.d0arg_loc)
  | D0ARGdyn p0as => p0arglst_posmark p0as
  | D0ARGdyn2 (p0as1, p0as2) => begin
      p0arglst_prf_posmark p0as1; p0arglst_posmark p0as2
    end // end of [D0ARGdyn2]
// end of [d0arg_posmark]

fn d0arglst_posmark (d0as: d0arglst) =
  $Lst.list_foreach_fun (d0as, d0arg_posmark)

(* ****** ****** *)

fn f0arg_posmark (f0a: f0arg): void =
  case+ f0a.f0arg_node of
  | F0ARGsta1 _ => staexploc_posmark (f0a.f0arg_loc)
  | F0ARGsta2 _ => staexploc_posmark (f0a.f0arg_loc)
  | F0ARGdyn p0t => p0at_posmark p0t
  | F0ARGmet _ => staexploc_posmark (f0a.f0arg_loc)
// end of [f0arg_posmark]

fn f0arglst_posmark (f0as: f0arglst): void =
  $Lst.list_foreach_fun (f0as, f0arg_posmark)

(* ****** ****** *)

fun i0nvarglst_posmark
  (args: i0nvarglst): void = case+ args of
  | arg :: args => begin
      s0expopt_posmark arg.i0nvarg_typ; i0nvarglst_posmark args
    end // end of [::]
  | nil () => ()
// end of [i0nvarglst_posmark]

fn i0nvresstate_posmark
  (res: i0nvresstate): void = let
  val () = case+ res.i0nvresstate_qua of
    | Some s0qs => s0qualst_posmark s0qs | None () => ()
  // end of [val]
in
  i0nvarglst_posmark (res.i0nvresstate_arg)
end // end of [i0nvresstate_posmark]

fn loopi0nv_posmark (inv: loopi0nv): void = let
  val () = case+ inv.loopi0nv_qua of
    | Some s0qs => s0qualst_posmark s0qs | None () => ()
  // end of [val]
  val () = case+ inv.loopi0nv_met of
    | Some s0es => s0explst_posmark s0es | None () => ()
  // end of [val]
  val () = i0nvarglst_posmark inv.loopi0nv_arg
  val () = i0nvresstate_posmark inv.loopi0nv_res
in
  // empty
end // end of [loopi0nv_posmark]

fn loopi0nvopt_posmark (oinv: loopi0nvopt): void =
  case+ oinv of Some inv => loopi0nv_posmark inv | None () => ()
// end of [loopi0nvopt_posmark]

(* ****** ****** *)

fn d0exp_prf_posmark (d0e: d0exp): void = begin
  prfexploc_posmark d0e.d0exp_loc; d0exp_posmark d0e;
end // end of [d0exp_prf_posmark]

fn d0explst_prf_posmark (d0es: d0explst): void =
  $Lst.list_foreach_fun (d0es, d0exp_prf_posmark)

fn d0explstlst_posmark (d0ess: d0explstlst): void =
  $Lst.list_foreach_fun (d0ess, d0explst_prf_posmark)

fn d0expopt_posmark (od0e: d0expopt): void =
  case+ od0e of Some d0e => d0exp_posmark d0e | None () => ()

fn m0atch_posmark (m0at: m0atch): void = begin
  d0exp_posmark (m0at.m0atch_exp); p0atopt_posmark (m0at.m0atch_pat)
end // end of [m0atch_posmark]

fn m0atchlst_posmark (m0ats: m0atchlst): void =
  $Lst.list_foreach_fun (m0ats, m0atch_posmark)

fn guap0at_posmark (gp0t: guap0at): void = begin
  p0at_posmark gp0t.guap0at_pat; m0atchlst_posmark gp0t.guap0at_gua
end // end of [guap0at_posmark]

fn c0lau_posmark (c0l: c0lau): void = begin
  guap0at_posmark c0l.c0lau_pat; d0exp_posmark c0l.c0lau_body
end // end of [c0clau_posmark]

fn c0laulst_posmark (c0ls: c0laulst): void =
  $Lst.list_foreach_fun (c0ls, c0lau_posmark)

fun labd0explst_posmark (ld0es: labd0explst): void =
  case+ ld0es of
  | LABD0EXPLSTcons (_(*lab*), d0e, ld0es) => begin
      d0exp_posmark d0e; labd0explst_posmark ld0es
    end
  | LABD0EXPLSTnil () => ()
// end of [labd0explst_posmark]

implement d0exp_posmark (d0e0) = case+ d0e0.d0exp_node of
  | D0Eann (d0e, s0e) => begin
      d0exp_posmark d0e; s0exp_posmark (s0e);
    end
  | D0Eapp (d0e_fun, d0e_arg) => begin
      d0exp_posmark d0e_fun; d0exp_posmark d0e_arg;
    end
  | D0Earrinit (s0e_elt, od0e_asz, d0es_elt) => begin
      s0exp_posmark s0e_elt; d0expopt_posmark od0e_asz; d0explst_posmark d0es_elt;
    end // end of [D0Earrinit]
  | D0Earrsub (_(*id*), _(*loc_ind*), d0ess) => d0explstlst_posmark d0ess
  | D0Ecaseof (hd, d0e, c0ls) => begin
      d0exp_posmark d0e; c0laulst_posmark c0ls
    end // end of [D0Ecaseof]
  | D0Eexist (qualoc, _(*s0exparg*), d0e) => begin
      staexploc_posmark qualoc; d0exp_posmark d0e
    end // end of [D0Eexist]
  | D0Eextval (s0e, _(*code*)) => s0exp_posmark s0e
  | D0Efix (
      _(*knd*), _(*id*), f0as, os0e, otags, d0e_body
    ) => begin
      f0arglst_posmark f0as;
      s0expopt_posmark os0e; e0fftaglstopt_posmark otags;
      d0exp_posmark d0e_body;
    end // end of [D0Efix]
  | D0Efor (inv, loc_inv, d0e_ini, d0e_test, d0e_post, d0e_body) => begin
      loopi0nvopt_posmark inv;
      d0exp_posmark d0e_ini; d0exp_posmark d0e_test;
      d0exp_posmark d0e_post; d0exp_posmark d0e_body;
    end // end of [D0Efor]
  | D0Eif (hd, d0e_cond, d0e_then, od0e_else) => begin
      d0exp_posmark d0e_cond;
      d0exp_posmark d0e_then;
      d0expopt_posmark od0e_else;
    end // end of [D0Eif]
  | D0Elam (_(*lin*), f0as, os0e, otags, d0e_body) => begin
      f0arglst_posmark f0as;
      s0expopt_posmark os0e; e0fftaglstopt_posmark otags;
      d0exp_posmark d0e_body;
    end
  | D0Elet (d0cs, d0e) => begin
      d0eclst_posmark d0cs; d0exp_posmark d0e;
    end
  | D0Elist d0es => d0explst_posmark d0es
  | D0Elist2 (d0es1, d0es2) => begin
      d0explst_prf_posmark d0es1; d0explst_posmark d0es2;
    end
  | D0Elst (
      _(*lstknd*), os0e, d0e_elts
    ) => begin
      s0expopt_posmark os0e; d0exp_posmark d0e_elts;
    end // end of [D0Elst]
  | D0Emacsyn (_(*knd*), d0e) => d0exp_posmark d0e
  | D0Eraise (d0e) => d0exp_posmark d0e
  | D0Erec (_(*recknd*), ld0es) => begin
      labd0explst_posmark ld0es;
    end
  | D0Esel_ind (_(*ptr*), d0ess) => begin
      d0explstlst_posmark d0ess;
    end
  | D0Eseq d0es => d0explst_posmark d0es
  | D0Esexparg _(*s0exparg*) => begin
      staexploc_posmark (d0e0.d0exp_loc);
    end
  | D0Esif (hd, s0e_cond, d0e_then, d0e_else) => let
      // val () =  prfexploc_posmark (d0e0.d0exp_loc)
    in
      s0exp_posmark s0e_cond;
      d0exp_posmark d0e_then;
      d0exp_posmark d0e_else;
    end // end of [D0Esif]
  | D0Estruct ld0es => labd0explst_posmark ld0es
  | D0Etmpid (_(*id*), ts0ess) => t1mps0explstlst_posmark ts0ess
  | D0Etrywith (hd, d0e, c0ls) => begin
      d0exp_posmark d0e; c0laulst_posmark c0ls;
    end // end of [D0Etrywith]
  | D0Etup (_(*tupknd*), d0es) => d0explst_posmark d0es
  | D0Etup2 (_(*tupknd*), d0es1, d0es2) => begin
      d0explst_prf_posmark d0es1; d0explst_posmark d0es2;
    end
  | D0Ewhere (d0e, d0cs) => begin
      d0eclst_posmark d0cs; d0exp_posmark d0e;
    end
  | D0Ewhile (inv, loc_inv, d0e_test, d0e_body) => begin
      loopi0nvopt_posmark inv; d0exp_posmark d0e_test; d0exp_posmark d0e_body;
    end // end of [D0Ewhile]
  | _ => ()
// end of [d0exp_posmark]

implement d0explst_posmark (d0es) =
  $Lst.list_foreach_fun (d0es, d0exp_posmark)

implement d0explstopt_posmark (od0es) = begin
  case+ od0es of Some d0es => d0explst_posmark d0es | None () => ()
end // end of [d0explstopt_posmark]

(* ****** ****** *)

fn stacstdecloc_posmark (loc_id: loc_t): void = let
  val loc_begoff = $Loc.location_begpos_toff loc_id
  val () = $PM.posmark_insert_stacstdec_beg (loc_begoff, loc_id)
  val loc_endoff = $Loc.location_endpos_toff loc_id
  val () = $PM.posmark_insert_stacstdec_end (loc_endoff, loc_id)
in
  // empty
end // end of [stacstdecloc_posmark]

(* ****** ****** *)

fn s0expdef_posmark (d0c: s0expdef): void = let
  val loc = d0c.s0expdef_loc; val () = stacstdecloc_posmark (loc)
in
  staexploc_posmark (loc)
end // end of [s0expdef_posmark]

fn s0expdeflst_posmark (d0cs: s0expdeflst): void =
  $Lst.list_foreach_fun (d0cs, s0expdef_posmark)

(* ****** ****** *)

fn d0atcon_posmark (d0c: d0atcon): void = begin
  s0qualstlst_posmark d0c.d0atcon_qua;
  s0expopt_posmark d0c.d0atcon_arg;
  s0expopt_posmark d0c.d0atcon_ind;
end // end of [d0atcon_posmark]

fn d0atconlst_posmark (d0cs: d0atconlst): void =
  $Lst.list_foreach_fun (d0cs, d0atcon_posmark)

fn d0atdec_posmark
  (d0c: d0atdec): void = let
  val headloc = d0c.d0atdec_headloc
  val () = stacstdecloc_posmark (headloc)
  val () = staexploc_posmark (headloc)
  val () = d0atconlst_posmark (d0c.d0atdec_con)
in
  // empty
end // end of [d0atdec_posmark]

fn d0atdeclst_posmark (d0cs: d0atdeclst): void =
  $Lst.list_foreach_fun (d0cs, d0atdec_posmark)

(* ****** ****** *)

fn e0xndec_posmark (d0c: e0xndec): void = begin
  s0qualstlst_posmark (d0c.e0xndec_qua);
  s0expopt_posmark (d0c.e0xndec_arg);
end // end of [e0xndec_posmark]

fn e0xndeclst_posmark (d0cs: e0xndeclst): void =
  $Lst.list_foreach_fun (d0cs, e0xndec_posmark)

(* ****** ****** *)

fn dyncstdecloc_posmark (loc_id: loc_t): void = let
  val loc_begoff = $Loc.location_begpos_toff loc_id
  val () = $PM.posmark_insert_dyncstdec_beg (loc_begoff, loc_id)
  val loc_endoff = $Loc.location_endpos_toff loc_id
  val () = $PM.posmark_insert_dyncstdec_end (loc_endoff, loc_id)
in
  // empty
end // end of [dyncstdecloc_posmark]

fn d0cstdec_posmark (d0c: d0cstdec): void = let
  val loc = d0c.d0cstdec_loc
  val () = dyncstdecloc_posmark (loc)
  val () = d0arglst_posmark (d0c.d0cstdec_arg)
  val () = e0fftaglstopt_posmark (d0c.d0cstdec_eff)
  val () = s0exp_posmark (d0c.d0cstdec_res)
in
  // empty
end // end of [d0cstdec_posmark]

fn d0cstdeclst_posmark (d0cs: d0cstdeclst): void =
  $Lst.list_foreach_fun (d0cs, d0cstdec_posmark)

(* ****** ****** *)

fn v0aldec_posmark (d0c: v0aldec): void = begin
  p0at_posmark d0c.v0aldec_pat; d0exp_posmark d0c.v0aldec_def;
end // end of [v0aldec_posmark]

fn v0aldeclst_posmark (d0cs: v0aldeclst): void =
  $Lst.list_foreach_fun (d0cs, v0aldec_posmark)

(* ****** ****** *)

fn f0undec_posmark (d0c: f0undec): void = begin
  f0arglst_posmark d0c.f0undec_arg;
  e0fftaglstopt_posmark d0c.f0undec_eff;
  s0expopt_posmark d0c.f0undec_res;
  d0exp_posmark d0c.f0undec_def;
end // end of [f0undec_posmark]

fn f0undeclst_posmark (d0cs: f0undeclst): void =
  $Lst.list_foreach_fun (d0cs, f0undec_posmark)

(* ****** ****** *)

fn v0ardec_posmark
  (d0c: v0ardec): void = let
  val () = s0expopt_posmark d0c.v0ardec_typ
  val () = case+ d0c.v0ardec_wth of
    | Some id => prfexploc_posmark (id.i0de_loc)
    | None () => ()
  // end of [val]
  val () = d0expopt_posmark d0c.v0ardec_ini
in
  // empty
end // end of [v0ardec_posmark]

fn v0ardeclst_posmark (d0cs: v0ardeclst): void =
  $Lst.list_foreach_fun (d0cs, v0ardec_posmark)

(* ****** ****** *)

fn i0mpdec_posmark
  (d0c: i0mpdec): void = let
  val qid = d0c.i0mpdec_qid
  val () = t1mps0explstlst_posmark (qid.impqi0de_arg)
  val () = f0arglst_posmark (d0c.i0mpdec_arg)
  val () = s0expopt_posmark (d0c.i0mpdec_res)
  val () = d0exp_posmark (d0c.i0mpdec_def)
in
  // empty
end // end of [i0mpdec_posmark]

(* ****** ****** *)

fun guad0ec_node_posmark
  (gdn: guad0ec_node): void = begin case+ gdn of
  | GD0Cone (e0xp, d0cs) => begin
      e0xp_posmark e0xp; d0eclst_posmark d0cs;
    end // end of [GD0Cone]
  | GD0Ctwo (e0xp, d0cs1, d0cs2) => begin
      e0xp_posmark e0xp;
      d0eclst_posmark d0cs1; d0eclst_posmark d0cs2;
    end // end of [GD0Ctwo]
  | GD0Ccons (e0xp, d0cs, knd, gdn) => begin
      e0xp_posmark e0xp;
      d0eclst_posmark d0cs; guad0ec_node_posmark gdn;
    end // end of [GD0Ccons]
end // end of [guad0ec_node_posmark]

(* ****** ****** *)

implement d0ec_posmark (d0c0) =
  case+ d0c0.d0ec_node of
  | D0Cfixity _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Cnonfix _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Cinclude _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Csymintr _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Ce0xpdef _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Ce0xpundef _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Ce0xpact _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Cdatsrts _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Csrtdefs _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Cstacons _ => let
      val loc = d0c0.d0ec_loc; val () = stacstdecloc_posmark (loc)
    in
      staexploc_posmark (loc)
    end // end of [D0Cstacons]
  | D0Cstacsts _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Cstavars _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Csexpdefs (_, d0c, d0cs) => begin
      s0expdef_posmark (d0c); s0expdeflst_posmark (d0cs)
    end // end of [D0Csexpdefs]
  | D0Csaspdec _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Cdcstdecs (dk, s0qss, d0c, d0cs) => let
      val isprf = dcstkind_is_proof dk
      val () = if isprf then prfexploc_posmark (d0c0.d0ec_loc)
      val () = s0qualstlst_posmark s0qss
    in
      d0cstdec_posmark d0c; d0cstdeclst_posmark d0cs
    end // end of [D0Cdcstdecs]
  | D0Cdatdecs (dk, d0c1, d0cs1, d0cs2) => let
      val isprf = datakind_is_proof dk
      val () = if isprf then prfexploc_posmark (d0c0.d0ec_loc)
      val () = (d0atdec_posmark d0c1; d0atdeclst_posmark d0cs1)
      val () = s0expdeflst_posmark d0cs2
    in
      // empty
    end // end of [D0Cdatdecs]
  | D0Cexndecs (d0c, d0cs) => begin
      e0xndec_posmark d0c; e0xndeclst_posmark d0cs
    end // end of [val]
  | D0Cclassdec _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Coverload _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Cextype _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Cextval (_(*name*), d0e) => d0exp_posmark d0e
  | D0Cextcode (_, code) => begin
      externloc_posmark (d0c0.d0ec_loc)
    end // end of [D0Cextcode]
  | D0Cvaldecs (vk, d0c, d0cs) => begin
      if valkind_is_proof vk then
        prfexploc_posmark (d0c0.d0ec_loc);
      v0aldec_posmark d0c; v0aldeclst_posmark d0cs;
    end // end of [D0Cvaldecs]
  | D0Cvaldecs_par (d0c, d0cs) =>  begin
      v0aldec_posmark d0c; v0aldeclst_posmark d0cs
    end // end of [D0Cvaldecs_par]
  | D0Cvaldecs_rec (d0c, d0cs) =>  begin
      v0aldec_posmark d0c; v0aldeclst_posmark d0cs
    end // end of [D0Cvaldecs_rec]
  | D0Cfundecs (fk, decarg, d0c, d0cs) => let
      val isprf = funkind_is_proof fk
      val () = if isprf then prfexploc_posmark (d0c0.d0ec_loc)
      val () = s0qualstlst_posmark decarg
    in
      f0undec_posmark d0c; f0undeclst_posmark d0cs
    end // end of [D0Cfundecs]
  | D0Cvardecs (d0c, d0cs) => begin
      v0ardec_posmark d0c; v0ardeclst_posmark d0cs;
    end // end of [D0Cvardecs]
  | D0Cmacdefs _ => neuexploc_posmark (d0c0.d0ec_loc)
  | D0Cimpdec (decarg, d0c) => begin
      s0arglstlst_posmark decarg; i0mpdec_posmark d0c
    end // end of [D0Cimpdec]
  | D0Cdynload _ => ()
  | D0Cstaload _ => staexploc_posmark (d0c0.d0ec_loc)
  | D0Clocal (d0cs1, d0cs2) => begin
      d0eclst_posmark d0cs1; d0eclst_posmark d0cs2;
    end // end of [D0Clocal]
  | D0Cguadec (_(*knd*), gd0c) => begin
      guad0ec_node_posmark (gd0c.guad0ec_node)
    end // end of [D0Cguadec]
// end of [d0ec_posmark]

implement d0eclst_posmark (d0cs) =
  $Lst.list_foreach_fun (d0cs, d0ec_posmark)

(* ****** ****** *)

(* end of [ats_syntax_posmark.dats] *)
