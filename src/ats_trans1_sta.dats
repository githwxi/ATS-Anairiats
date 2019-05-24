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
// Time: August 2007
//
(* ****** ****** *)

(* 
** HX:
** The first translation mainly resolves the issue of operator fixity
*)
 
(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Fix = "ats_fixity.sats"
typedef fxty = $Fix.fxty and prec_t = $Fix.prec_t
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_syntax.sats"
staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_trans1_env.sats"
staload "ats_e1xp_eval.sats"

(* ****** ****** *)

staload "ats_trans1.sats"

(* ****** ****** *)

#define THISFILENAME "ats_trans1_sta.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef loc_t = $Loc.location_t
typedef fil_t = $Fil.filename_t

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol
overload prerr with $Sym.prerr_symbol

(* ****** ****** *)

fn prerr_loc_error1 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(1)")
// end of [prerr_loc_error1]

fn prerr_interror (): void = prerr "INTERNAL ERROR (ats_trans1_sta)"

(* ****** ****** *)

local

fn prec_tr_errmsg
  (opr: i0de): prec_t = begin
  prerr_loc_error1 opr.i0de_loc;
  prerr ": the operator [";
  prerr opr.i0de_sym;
  prerr "] is given no fixity";
  prerr_newline ();
  $Err.abort ()
end // end of [prec_tr_errmsg]

in // in of [local]

fn p0rec_tr (p0: p0rec): prec_t = let
  fun precfnd (id: i0de): prec_t = let
    val fxtyopt = the_fxtyenv_find id.i0de_sym
  in
    case+ fxtyopt of
    | ~Some_vt fxty => let
(*
        val () = begin
          print "p0rec_tr: Some: id = ";
          $Sym.print_symbol_code id.i0de_sym; print_newline ()
        end // end of [val]
*)
        val precopt = $Fix.fixity_get_prec (fxty)
      in
        case+ precopt of
        | ~Some_vt prec => prec | ~None_vt () => prec_tr_errmsg id
      end // end of [Some_vt]
    | ~None_vt () => prec_tr_errmsg id
  end // end of [precfnd]
in
  case+ p0 of
  | P0RECide id => precfnd id
  | P0RECint int => $Fix.prec_make_int int
  | P0RECinc (id, int) => $Fix.precedence_inc (precfnd id, int)
  | P0RECdec (id, int) => $Fix.precedence_dec (precfnd id, int)
end // end of [p0rec_tr]

end // end of [local]

(* ****** ****** *)

fn f0xty_tr
  (f0xty: f0xty): fxty = case+ f0xty of
  | F0XTYinf (p0, a) =>
      let val p = p0rec_tr p0 in $Fix.fxty_inf (p, a) end
  | F0XTYpre p0 => let val p = p0rec_tr p0 in $Fix.fxty_pre p end
  | F0XTYpos p0 => let val p = p0rec_tr p0 in $Fix.fxty_pos p end
// end of [f0xty_tr]

(* ****** ****** *)

typedef e1xpitm = $Fix.item (e1xp)
typedef e1xpitmlst = List e1xpitm

val e1xpitm_app : e1xpitm = let
//
fn f (e1: e1xp, e2: e1xp):<cloref1> e1xpitm = let
  val loc = $Loc.location_combine (e1.e1xp_loc, e2.e1xp_loc)
  val es2 = (
    case+ e2.e1xp_node of E1XPlist es => es | _ => '[e2]
  ) : e1xplst
  val e_app = e1xp_app (loc, e1, e2.e1xp_loc, es2)
(*
  val () = begin
    print "e1xpitm_app: f: e_app = "; print e_app; print_newline ()
  end // end of [val]
*)
in
  $Fix.ITEMatm (e_app)
end // end of [f]
//
in // in of [let]
  $Fix.item_app (f)
end // end of [e1xpitm_app]

fn e1xp_make_opr
  (e: e1xp, f: fxty): e1xpitm = begin
  $Fix.oper_make {e1xp} (
    lam x => x.e1xp_loc,
    lam (loc, x, loc_arg, xs) => e1xp_app (loc, x, loc_arg, xs), e, f
  ) // end of [oper_make]
end // end of [e1xpitm_opr]

val e1xpitm_backslash : e1xpitm = begin
  $Fix.oper_make_backslash {e1xp} (
    lam x => x.e1xp_loc,
    lam (loc, x, loc_arg, xs) => e1xp_app (loc, x, loc_arg, xs)
  ) // end of [oper_make_backslash]
end // end of [e1xpitm_backslash]

(* ****** ****** *)

local

fn e0xp_tr_errmsg_opr
  (loc: loc_t): e1xp = let
  val () = prerr_loc_error1 (loc)
  val () = prerr ": the operator needs to be applied."
  val () = prerr_newline ()
in
  $Err.abort {e1xp} ()
end // end of [e0xp_tr_errmsg_opr]

in // in of [local]
  
implement e0xp_tr (e0) = let
//
  fun aux_item (e0: e0xp): e1xpitm = let
    val loc = e0.e0xp_loc in case+ e0.e0xp_node of
    | E0XPapp _ => let
        val es_new = aux_itemlst e0
        val e0_new = $Fix.fixity_resolve (loc, e1xpitm_app, es_new)
      in
        $Fix.ITEMatm (e0_new)
      end
    | E0XPchar (c: char) => $Fix.ITEMatm (e1xp_char (loc, c))
    | E0XPeval (e: e0xp) => let
        val e = e0xp_tr (e)
        val v = e1xp_eval (e)
        val e = e1xp_make_v1al (loc, v)
      in
        $Fix.ITEMatm (e)
      end // end of [E0XPeval]
    | E0XPfloat (f: string) => $Fix.ITEMatm (e1xp_float (loc, f))
    | E0XPide id when id = $Sym.symbol_BACKSLASH => e1xpitm_backslash
    | E0XPide id => begin case+ the_fxtyenv_find id of
      | ~Some_vt f => begin
          let val e = e1xp_ide (loc, id) in e1xp_make_opr (e, f) end
        end
      | ~None_vt () => $Fix.ITEMatm (e1xp_ide (loc, id))
      end (* end of [E0XPide] *)
    | E0XPint (int: string) => $Fix.ITEMatm (e1xp_int (loc, int))
    | E0XPlist (es) => $Fix.ITEMatm (e1xp_list (loc, e0xplst_tr es))
    | E0XPstring (str, len) => $Fix.ITEMatm (e1xp_string (loc, str, len))
    | E0XPcstsp (cst) => $Fix.ITEMatm (e1xp_cstsp (loc, cst))
  end // end of [aux_item]
//
  and aux_itemlst (e0: e0xp): e1xpitmlst = let
    fun loop (res: e1xpitmlst, e0: e0xp): e1xpitmlst =
      case+ e0.e0xp_node of
      | E0XPapp (e1, e2) => begin
          let val res = aux_item e2 :: res in loop (res, e1) end
        end // end of [E0XPapp]
      | _ => aux_item e0 :: res
    // end of [loop]
  in
    loop (nil (), e0)
  end // end of [aux_itemlst]
//
in
  case+ aux_item e0 of
  | $Fix.ITEMatm (e) => e
  | $Fix.ITEMopr _ => e0xp_tr_errmsg_opr e0.e0xp_loc
  // end of [case]
end // end of [e0xp_tr]

end // end of [local]

implement e0xplst_tr (es) = $Lst.list_map_fun (es, e0xp_tr)

(* ****** ****** *)
//
// HX: translation of sorts
//
typedef s1rtitm = $Fix.item s1rt
typedef s1rtitmlst = List s1rtitm

val s1rtitm_app : s1rtitm = let
  fn f (s1t1: s1rt, s1t2: s1rt):<cloref1> s1rtitm = let
    val loc = $Loc.location_combine (s1t1.s1rt_loc, s1t2.s1rt_loc)
    val s1ts2 = (
      case+ s1t2.s1rt_node of
      | S1RTlist s1ts => s1ts | _ => cons (s1t2, nil ())
    ) : s1rtlst
    val s1t_app = s1rt_app (loc, s1t1, s1ts2)
  in
    $Fix.ITEMatm (s1t_app)
  end // end of [f]
in
  $Fix.item_app (f)
end // end of [app_s1rt_item]

fun s1rt_make_opr
  (s1t: s1rt, f: fxty): s1rtitm = begin
  $Fix.oper_make {s1rt} (
    lam x => x.s1rt_loc,
    lam (loc, x, _(*loc_arg*), xs) => s1rt_app (loc, x, xs), s1t, f
  ) // end of [oper_make]
end // end of [s1rt_make_opr]

val s1rtitm_backslash : s1rtitm = begin
  $Fix.oper_make_backslash {s1rt} (
    lam x => x.s1rt_loc,
    lam (loc, x, _(*loc_arg*), xs) => s1rt_app (loc, x, xs)
  ) // end of [oper_make_backslash]
end // end of [s1rtitm_backslash]

(* ****** ****** *)

local

fn s0rt_tr_errmsg_opr
  (loc: loc_t): s1rt = let
  val () = prerr_loc_error1 (loc)
  val () = prerr ": the operator needs to be applied."
  val () = prerr_newline ()
in
  $Err.abort {s1rt} ()
end // end of [s0rt_tr_errmsg_opr]

in // in of [local]
  
implement s0rt_tr (s0t0) = let
//
fun aux_item (s0t0: s0rt): s1rtitm = let
  val loc0 = s0t0.s0rt_loc in case+ s0t0.s0rt_node of
    | S0RTapp _ => let 
        val s1t0 =
          $Fix.fixity_resolve (loc0, s1rtitm_app, aux_itemlst s0t0)
        // end of [val]
      in
        $Fix.ITEMatm (s1t0)
      end // end of [S0RTapp]
    | S0RTide id when id = $Sym.symbol_BACKSLASH => s1rtitm_backslash
    | S0RTide id => begin case+ the_fxtyenv_find id of
      | ~Some_vt f => s1rt_make_opr (s1rt_ide (loc0, id), f)
      | ~None_vt () => $Fix.ITEMatm (s1rt_ide (loc0, id))
      end // end of [S0RTide]
    | S0RTlist (s0ts) => $Fix.ITEMatm (s1rt_list (loc0, s0rtlst_tr s0ts))
    | S0RTqid (q, id) => $Fix.ITEMatm (s1rt_qid (loc0, q, id))
    | S0RTtup (s0ts) => $Fix.ITEMatm (s1rt_tup (loc0, s0rtlst_tr s0ts))
end // end of [aux_item]
//
and aux_itemlst
  (s0t0: s0rt): s1rtitmlst = let
  fun loop (res: s1rtitmlst, s0t0: s0rt): s1rtitmlst =
    case+ s0t0.s0rt_node of
    | S0RTapp (s0t1, s0t2) => let
        val res = aux_item s0t2 :: res in loop (res, s0t1)
      end // end of [S0RTapp]
    | _ => aux_item s0t0 :: res // end of [_]
  // end of [loop]
in
  loop (nil (), s0t0)
end // end of [aux_itemlst]
//
in
  case+ aux_item s0t0 of
  | $Fix.ITEMatm (s1t) => s1t
  | $Fix.ITEMopr _ => s0rt_tr_errmsg_opr s0t0.s0rt_loc
  // end of [case]
end // end of [s0rt_tr]

end // end of [local]

implement
s0rtlst_tr (s0ts) = $Lst.list_map_fun (s0ts, s0rt_tr)

implement s0rtopt_tr (os0t) =
  case+ os0t of Some s0t => Some (s0rt_tr s0t) | None () => None ()
// end of [s0rtopt_tr]

(* ****** ****** *)

fn s0rtpol_tr (s0tp: s0rtpol): s1rtpol =
  s1rtpol_make (s0tp.s0rtpol_loc, s0rt_tr s0tp.s0rtpol_srt, s0tp.s0rtpol_pol)
// end of [s0rtpol_tr]

fn s0rtpol_srt_tr (s0tp: s0rtpol): s1rt =
  if s0tp.s0rtpol_pol = 0 then s0rt_tr s0tp.s0rtpol_srt
  else begin
    prerr_loc_error1 s0tp.s0rtpol_loc;
    prerr ": only a nonpolarized sort is allowed here";
    prerr_newline ();
    $Err.abort ()
  end // end of [if]
// end of [s0rtpol_srt_tr]

(* ****** ****** *)

fn d0atarg_tr
  (d0a: d0atarg): d1atarg = begin
  case+ d0a.d0atarg_node of
  | D0ATARGsrt s0tp => begin
      d1atarg_srt (d0a.d0atarg_loc, s0rtpol_tr s0tp)
    end
  | D0ATARGidsrt (id, s0tp) => begin
      d1atarg_idsrt (d0a.d0atarg_loc, id, s0rtpol_tr s0tp)
    end
end // end of [d0atarg_tr]

fun d0atarglst_tr
  (d0as: d0atarglst): d1atarglst =
  case+ d0as of
  | cons (d0a, d0as) => cons (d0atarg_tr d0a, d0atarglst_tr d0as)
  | nil () => nil ()
// end of [d0atarglst_tr]

fun d0atarglst_srtlst_tr
  (d0as: d0atarglst): s1rtlst = begin
  case+ d0as of
  | cons (d0a, d0as) => let
      val s0tp: s0rtpol = case+ d0a.d0atarg_node of
        | D0ATARGsrt s0tp => s0tp | D0ATARGidsrt (_(*id*), s0tp) => s0tp
      val s1t = s0rtpol_srt_tr s0tp
    in
      cons (s1t, d0atarglst_srtlst_tr d0as)
    end (* end of [cons] *)
  | nil () => nil ()
end // end of [d0atarglst_srtlst_tr]

(* ****** ****** *)

implement
d0ec_fixity_tr (f0xty, ids) = let
  fun loop (fxty: fxty, ids: i0delst): void =
    case+ ids of
    | cons (id, ids) => let
(*
        val () = begin
          print "d0ec_fixity_tr: loop: id = ";
          $Sym.print_symbol_code id.i0de_sym; print_newline ()
        end // end of [val]
        val () = begin
          print "the_fxtyenv_add: before: \n"; ats_fxtyenv_print ()
        end // end of [val]
*)
        val () = the_fxtyenv_add (id.i0de_sym, fxty)
(*
        val () = begin
          print "the_fxtyenv_add: after: \n"; ats_fxtyenv_print ()
        end // end of [val]
*)
      in
        loop (fxty, ids)
      end
    | nil () => ()
in
  loop (f0xty_tr f0xty, ids)
end // end of [d0ec_fixity_tr]

implement
d0ec_nonfix_tr (ids) = let
  fun loop (ids: i0delst): void = case+ ids of
    | cons (id, ids) => begin
        the_fxtyenv_add (id.i0de_sym, $Fix.fxty_non); loop ids
      end // end of [cons]
    | nil () => () // end of [nil]
  // end of [loop]
in
  loop ids
end // end of [d0ec_nonfix_tr]

(* ****** ****** *)

implement
do_e0xpact_assert (loc, v) = let
  val is_false = (case+ v of
    | V1ALchar c => c = '\0'
    | V1ALfloat f => f = 0.0 | V1ALint i => i = 0
    | V1ALstring s => let
        val s = string1_of_string s in string_is_empty s
      end // end of [V1ALstring]
    | V1ALcstsp _ => true // HX: always true
  ) : bool
in
  if is_false then begin
    prerr_loc_error1 loc;
    prerr ": [#assert] failed"; prerr_newline ();
    exit {void} (1)
  end // end of [if]
end // end of [do_e0xpact_assert]

implement
do_e0xpact_error (loc, v) = let
  val () = begin
    prerr_loc_error1 loc;
    prerr ": [#error] directive encountered: "
  end // end of [val]
  val () = case+ v of
    | V1ALchar c => prerr c
    | V1ALfloat f => prerr f
    | V1ALint i => prerr i
    | V1ALstring s => prerr s
    | V1ALcstsp (loc, cst) => (case+ cst of
        | CSTSPfilename () => prerr "#FILENAME"
        | CSTSPlocation () => prerr "#LOCATION"
      ) // end of [V1ALcstsp]
  // end of [val]
in
  exit {void} (1)
end // end of [do_e0xpact_error]

implement
do_e0xpact_prerr
  (v) = case+ v of
  | V1ALchar c => prerr c
  | V1ALfloat f => prerr f
  | V1ALint i => prerr i
  | V1ALstring s => prerr s
  | V1ALcstsp (loc, cst) => (
    case+ cst of
    | CSTSPfilename () => let
        val fil = $Loc.location_get_filename (loc)
      in
        $Fil.prerr_filename (fil)
      end
    | CSTSPlocation () => $Loc.prerr_location (loc)
    ) // end of [V1ALcstsp]
// end of [do_e0xpact_prerr]

(* ****** ****** *)

implement
s0tacon_tr (d) = let
  val fil = d.s0tacon_fil
  val loc = d.s0tacon_loc
  val arg = (case+ d.s0tacon_arg of
    | Some d0as => Some (d0atarglst_tr d0as) | None () => None ()
  ) : Option d1atarglst 
  val def = s0expopt_tr d.s0tacon_def
in
  s1tacon_make (fil, loc, d.s0tacon_sym, arg, def)
end // end of [s0tacon_tr]

implement
s0taconlst_tr (ds) = $Lst.list_map_fun (ds, s0tacon_tr)

(* ****** ****** *)

implement
s0tacst_tr (d) = let
  val fil = d.s0tacst_fil
  val loc = d.s0tacst_loc
  val os1ts_arg = (
    case+ d.s0tacst_arg of
    | Some arg => Some (d0atarglst_srtlst_tr arg) | None () => None ()
  ) : s1rtlstopt
  val s1t_res: s1rt = s0rt_tr d.s0tacst_res
in
  s1tacst_make (fil, loc, d.s0tacst_sym, os1ts_arg, s1t_res)
end // end of [s0tacst_tr]

implement
s0tacstlst_tr (ds) = $Lst.list_map_fun (ds, s0tacst_tr)

(* ****** ****** *)

implement
s0tavar_tr (d) = let
  val s1t: s1rt = s0rt_tr d.s0tavar_srt
in
  s1tavar_make (d.s0tavar_loc, d.s0tavar_sym, s1t)
end // end of [s0tavar_tr]

implement
s0tavarlst_tr (ds) = $Lst.list_map_fun (ds, s0tavar_tr)

(* ****** ****** *)

local

fn d0atsrtcon_tr
  (x: d0atsrtcon): d1atsrtcon = let
  val loc = x.d0atsrtcon_loc and nam = x.d0atsrtcon_sym
  val s1ts = (
    case+ x.d0atsrtcon_arg of
    | Some s0t => let
        val s1t = s0rt_tr s0t in
        case+ s1t.s1rt_node of
          | S1RTlist s1ts => s1ts | _ => cons (s1t, nil ())
        // end of [case]
      end // end of [Some]
    | None () => nil ()
  ) : s1rtlst // end of [val]
in
  d1atsrtcon_make (loc, nam, s1ts)
end // end of [d0atsrtcon_tr]

fn d0atsrtconlst_tr
  (xs: d0atsrtconlst): d1atsrtconlst =
  $Lst.list_map_fun (xs, d0atsrtcon_tr)

in // in of [local]

implement
d0atsrtdec_tr (d) = let
  val loc = d.d0atsrtdec_loc and nam = d.d0atsrtdec_sym
in
  d1atsrtdec_make (loc, nam, d0atsrtconlst_tr d.d0atsrtdec_con)
end // end of [d0atsrtdec_tr]

implement
d0atsrtdeclst_tr (ds) = $Lst.list_map_fun (ds, d0atsrtdec_tr)

end // end of [local]

(* ****** ****** *)

local

fn s0arg_tr
  (s0a: s0arg): s1arg = let
  val res = s0rtopt_tr s0a.s0arg_srt
in
  s1arg_make (s0a.s0arg_loc, s0a.s0arg_sym, res)
end // end of [s0arg_tr]

in // in of [local]

implement
s0arglst_tr (s0as) = $Lst.list_map_fun (s0as, s0arg_tr)

end // end of [local]

implement
s0arglstlst_tr (s0ass) = $Lst.list_map_fun (s0ass, s0arglst_tr)

(* ****** ****** *)

implement
sp0at_tr (sp0t) = begin
  case+ sp0t.sp0at_node of
  | SP0Tcon (qid, s0as) => let
      val s1as = s0arglst_tr s0as in
      sp1at_con (sp0t.sp0at_loc, qid.sqi0de_qua, qid.sqi0de_sym, s1as)
    end // end of [SP0Tcon]
end // end of [sp0at_tr]

(* ****** ****** *)
//
// HX: translation of static expressions
//
typedef s1expitm = $Fix.item s1exp
typedef s1expitmlst = List s1expitm

val s1expitm_app : s1expitm = let
//
fn f (s1e1: s1exp, s1e2: s1exp):<cloref1> s1expitm = let
  val loc = $Loc.location_combine (s1e1.s1exp_loc, s1e2.s1exp_loc)
  val s1es2 = (
    case+ s1e2.s1exp_node of
    | S1Elist (npf, s1es) => s1es // should [npf = 0] be enforced?
    | _ => cons (s1e2, nil ())
  ) : s1explst
  val s1e_app = s1exp_app (loc, s1e1, s1e2.s1exp_loc, s1es2)
(*
  val () = begin
    print "s1expitm_app: f: s1e_app = "; print s1e_app; print_newline ()
  end // end of [val]
*)
in
  $Fix.ITEMatm (s1e_app)
end // end of [f]
//
in
  $Fix.item_app (f)
end // end of [app_s1exp_item]

fn s1exp_make_opr 
  (s1e: s1exp, f: fxty): s1expitm = begin
  $Fix.oper_make {s1exp} (
    lam x => x.s1exp_loc,
    lam (loc, x, loc_arg, xs) => s1exp_app (loc, x, loc_arg, xs), s1e, f
  ) // end of[ oper_make]
end // end of [s1exp_make_opr]

val s1expitm_backslash : s1expitm = begin
  $Fix.oper_make_backslash {s1exp} (
    lam x => x.s1exp_loc,
    lam (loc, x1, loc_arg, x2) => s1exp_app (loc, x1, loc_arg, x2)
  ) // end of [oper_make_backslash]
end // end of [s1expitm_backslash]

(* ****** ****** *)

fn s0qua_tr (s0q: s0qua): s1qua = begin
  case+ s0q.s0qua_node of
  | S0QUAprop s0p => s1qua_prop (s0q.s0qua_loc, s0exp_tr s0p)
  | S0QUAvars (id, ids, s0te) => begin
      s1qua_vars (s0q.s0qua_loc, id :: ids, s0rtext_tr s0te)
    end // end of [S0QUAvars]
end // end of [s0qua_tr]

implement
s0qualst_tr (s0qs) = $Lst.list_map_fun (s0qs, s0qua_tr)
implement
s0qualstlst_tr (s0qss) = $Lst.list_map_fun (s0qss, s0qualst_tr)

(* ****** ****** *)

local

fn s0exp_tr_errmsg_opr
  (loc: loc_t): s1exp = let
  val () = prerr_loc_error1 (loc)
  val () = prerr ": the operator needs to be applied."
  val () = prerr_newline ()
in
  $Err.abort {s1exp} ()
end // end of [s0exp_tr_errmsg_opr]

in // in of [local]

implement
s0exp_tr s0e0 = let
  fun aux_item (s0e0: s0exp): s1expitm = let
    val loc0 = s0e0.s0exp_loc in case+ s0e0.s0exp_node of
    | S0Eann (s0e, s0t) => let
        val s1e = s0exp_tr s0e and s1t = s0rt_tr s0t
        val s1e_ann = s1exp_ann (loc0, s1e, s1t)
      in
        $Fix.ITEMatm (s1e_ann)
      end // end of [S0Eann]
    | S0Eapp _ => let 
        val s1e_app =
          $Fix.fixity_resolve (loc0, s1expitm_app, aux_itemlst s0e0)
        // end of [val]
      in
        $Fix.ITEMatm (s1e_app)
      end // end of [S0Eapp]
    | S0Echar c => $Fix.ITEMatm (s1exp_char (loc0, c))
//
    | S0Eexi (knd(*funres*), s0qs) => let
        val s1qs = s0qualst_tr s0qs
        fn f (body: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, body.s1exp_loc) in
            $Fix.ITEMatm (s1exp_exi (loc0, knd, s1qs, body))
          end // end of [let]
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.exi_prec_sta, f))
      end // end of [S0Eexi]
//
    | S0Eextype (name, s0es) => let
        val s1ess = loop (s0es, nil) where {
          fun loop (s0es: s0explst, res: s1explstlst): s1explstlst =
            case+ s0es of 
            | cons (s0e, s0es) => let
                val s1e = s0exp_tr (s0e)
                val s1es = (case+ s1e.s1exp_node of
                  | S1Elist (_(*npf*), s1es) => s1es | _ => cons (s1e, nil)
                ) : s1explst
              in
                loop (s0es, cons (s1es, res))
              end // end of [cons]
            | nil () => res
          // end of [loop]
        } // end of [val]
      in
        $Fix.ITEMatm (s1exp_extype (loc0, name, s1ess))
      end // end of [S0Eextype]
//
    | S0Eint int (*string*) => $Fix.ITEMatm (s1exp_int (loc0, int))
    | S0Eide id when id = $Sym.symbol_AMPERSAND => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, s1e.s1exp_loc) in
            $Fix.ITEMatm (s1exp_invar (loc0, 1(*ref*), s1e))
          end // end of [let]
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.invar_prec_sta, f))
      end // end of [S0Eide when ...]
    | S0Eide id when id = $Sym.symbol_BACKSLASH => s1expitm_backslash
    | S0Eide id when id = $Sym.symbol_BANG => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, s1e.s1exp_loc) in
            $Fix.ITEMatm (s1exp_invar (loc0, 0(*val*), s1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.invar_prec_sta, f))
      end // end of [S0Eide when ...]
    | S0Eide id when id = $Sym.symbol_QMARK => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (s1e.s1exp_loc, loc0) in
            $Fix.ITEMatm (s1exp_top (loc0, 0(*knd*), s1e))
          end // end of [let]
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.qmark_prec_sta, f))
      end // end of [S0Eide when ...]
    | S0Eide id when id = $Sym.symbol_QMARKBANG => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (s1e.s1exp_loc, loc0) in
            $Fix.ITEMatm (s1exp_top (loc0, 1(*knd*), s1e))
          end // end of [let]
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.qmarkbang_prec_sta, f))
      end // end of [S0Eide when ...]
    | S0Eide id when id = $Sym.symbol_GTGT => let
        fn f (s1e1: s1exp, s1e2: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (s1e1.s1exp_loc, s1e2.s1exp_loc) in
            $Fix.ITEMatm (s1exp_trans (loc0, s1e1, s1e2))
          end // end of [let]
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERinf ($Fix.trans_prec_sta, $Fix.ASSOCnon, f))
      end // end of [S0Eide when ...]
    | S0Eide id when id = $Sym.symbol_R0EAD => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, s1e.s1exp_loc) in
            $Fix.ITEMatm (s1exp_read (loc0, s1e))
          end // end of [let
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.r0ead_prec_sta, f))
      end // end of [S0Eide when ...]
    | S0Eide id => let
        // [e1xpdef] expansion is to be done in [ats_trans2.dats]
        // if it is done here, then it is only one level expansion
        val s1e = s1exp_ide (loc0, id)
      in
        case+ the_fxtyenv_find id of
          | ~Some_vt f => s1exp_make_opr (s1e, f) | ~None_vt () => $Fix.ITEMatm (s1e)
        // end of [case]
      end // end of [S0Eide]
    | S0Eimp tags => let
        val (ofc, lin, prf, efc) = $Eff.e0fftaglst_tr (tags)
        val fc = (case+ ofc of
          | Some fc => fc | None => $Syn.FUNCLOfun () // default is [function]
        ) : $Syn.funclo // end of [val]
(*
        val () = begin
          print "s0exp_tr: S0Eimp: efc = "; $Eff.print_effcst efc; print_newline ()
        end // end of [val]
*)
        val ans = the_fxtyenv_find ($Sym.symbol_MINUSGT)
      in
        case+ ans of
        | ~Some_vt f => let
            val s1e_imp = s1exp_imp (loc0, fc, lin, prf, Some efc)
          in
            s1exp_make_opr (s1e_imp, f)
          end // end of [Some_vt]
        | ~None_vt () => begin
            prerr_interror ();
            prerr ": s0exp_tr: the fixity of -> is unavailable."; prerr_newline ();
            $Err.abort ()
          end // end of [None_vt]
      end // end of [S0Eimp]
    | S0Elam (arg, res, body) => let
        val arg = s0arglst_tr arg
        val res = s0rtopt_tr res
        val body = s0exp_tr body
        val s1e_lam = s1exp_lam (loc0, arg, res, body)
(*
        val () = begin
          print "s0exp_tr: S0Elam: s1e_lam = "; print s1e_lam; print_newline ()
        end // end of [val]
*)
      in
        $Fix.ITEMatm (s1e_lam)
      end // end of [S0Elam]
    | S0Elist (s0es) => let
        val s1es = s0explst_tr s0es in $Fix.ITEMatm (s1exp_list (loc0, s1es))
      end // end of [S0Elist]
    | S0Elist2 (s0es1, s0es2) => let
        val s1es1 = s0explst_tr s0es1
        val s1es2 = s0explst_tr s0es2
      in
        $Fix.ITEMatm (s1exp_list2 (loc0, s1es1, s1es2))
      end // end of [S0Elist2]
(*
// HX-2010-12-04: inadequate design
    | S0Enamed (name, s0e) => let
        val s1e = s0exp_tr s0e in
        $Fix.ITEMatm (s1exp_named (loc0, name, s1e))
      end // end of [S0Enamed]
*)
    | S0Eopide id => $Fix.ITEMatm (s1exp_ide (loc0, id))
    | S0Eqid (q, id) => $Fix.ITEMatm (s1exp_qid (loc0, q, id))
(*
// HX-2010-11-01: simplification
    | S0Estruct (ls0es) => let
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_struct (loc0, ls1es))
      end // end of [S0Estruct]
*)
    | S0Etyarr (s0e_elt, s0ess_dim) => let
        val s1e_elt = s0exp_tr s0e_elt
        val s1ess_dim = s0explstlst_tr s0ess_dim
      in
        $Fix.ITEMatm (s1exp_tyarr (loc0, s1e_elt, s1ess_dim))
      end // end of [S0Etyarr]
    | S0Etyrec (flat, ls0es) => let
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_tyrec (loc0, flat, ls1es))
      end // end of [S0Etyrec]
    | S0Etyrec_ext (name, ls0es) => let
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_tyrec_ext (loc0, name, ls1es))
      end // end of [S0Etyrec_ext]
    | S0Etytup (flat, s0es) => let
        val s1es = s0explst_tr s0es
      in
        $Fix.ITEMatm (s1exp_tytup (loc0, flat, s1es))
      end // end of [S0Etytup]
    | S0Etytup2 (flat, s0es1, s0es2) => let
        val s1es1 = s0explst_tr s0es1
        val s1es2 = s0explst_tr s0es2
      in
        $Fix.ITEMatm (s1exp_tytup2 (loc0, flat, s1es1, s1es2))
      end // end of [S0Etytup2]
    | S0Euni (s0qs) => let
        val s1qs = s0qualst_tr s0qs
        fn f (body: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, body.s1exp_loc) in
            $Fix.ITEMatm (s1exp_uni (loc0, s1qs, body))
          end // end of [f]
        // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.uni_prec_sta, f))
      end // end of [S0Euni]
    | S0Eunion (s0e, ls0es) => let
        val s1e = s0exp_tr s0e
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_union (loc0, s1e, ls1es))
      end // end of [S0Eunion]
    | _ => begin
        prerr_loc_error1 loc0;
        $Deb.debug_prerrf (": %s: s0exp_tr", @(THISFILENAME));
        prerr ": not available yet"; prerr_newline ();
        $Err.abort {s1expitm} ()
      end // end of [_]
  end // end of [aux_item]
//
  and aux_itemlst
    (s0e0: s0exp): s1expitmlst = let
    fun loop (res: s1expitmlst, s0e0: s0exp): s1expitmlst =
      case+ s0e0.s0exp_node of
      | S0Eapp (s0e1, s0e2) => let
          val res = aux_item s0e2 :: res in loop (res, s0e1)
        end // end of [S0Eapp]
      | _ => aux_item s0e0 :: res
    // end of [loop]
  in
    loop (nil (), s0e0)
  end // end of [aux_itemlist]
//
in
  case+ aux_item s0e0 of
  | $Fix.ITEMatm (s1e) => s1e
  | $Fix.ITEMopr _ => s0exp_tr_errmsg_opr s0e0.s0exp_loc
end // end of [s0exp_tr]

end // end of [local]

implement
s0explst_tr (s0es) = $Lst.list_map_fun (s0es, s0exp_tr)
// end of [s0explst_tr]

implement
s0expopt_tr (os0e) = case+ os0e of
  | Some s0e => Some (s0exp_tr s0e) | None () => None ()
// end of [s0expopt_tr]

implement
s0explstlst_tr s0ess = $Lst.list_map_fun (s0ess, s0explst_tr)
// end of [s0explstlst_tr]

implement
labs0explst_tr ls0es = case+ ls0es of
  | LABS0EXPLSTcons (l, s0e, ls0es) =>
    LABS1EXPLSTcons (l.l0ab_lab, s0exp_tr s0e, labs0explst_tr ls0es)
  | LABS0EXPLSTnil () => LABS1EXPLSTnil ()
// end of [labs0explst_tr]

implement
s0rtext_tr s0te = let
  val loc = s0te.s0rtext_loc
in
  case+ s0te.s0rtext_node of
  | S0TEsrt s0t => s1rtext_srt (loc, s0rt_tr s0t)
  | S0TEsub (id, s0te, s0p, s0ps) => let
      val s1te = s0rtext_tr s0te
      val s1p = s0exp_tr s0p and s1ps = s0explst_tr s0ps
    in
      s1rtext_sub (loc, id.i0de_sym, s1te, s1p :: s1ps)
    end
end // end of [s0rtext_tr]

(* ****** ****** *)

implement
t1mps0explstlst_tr (ts0ess) = begin
  case+ ts0ess of
  | T1MPS0EXPLSTLSTnil () => TMPS1EXPLSTLSTnil ()
  | T1MPS0EXPLSTLSTcons (loc, s0es, ts0ess) => let
      val s1es = s0explst_tr (s0es)
      val ts1ess = t1mps0explstlst_tr ts0ess
    in
      TMPS1EXPLSTLSTcons (loc, s1es, ts1ess)
    end // end of [T1MPS0EXPLSTLSTcons]
end // end of [t1mps0explstlst_tr]

(* ****** ****** *)

implement
witht0ype_tr (w0t) = begin case+ w0t of
  | WITHT0YPEnone () => WITHT1YPEnone ()
  | WITHT0YPEprop s0e => WITHT1YPEprop (s0exp_tr s0e)
  | WITHT0YPEtype s0e => WITHT1YPEtype (s0exp_tr s0e)
  | WITHT0YPEview s0e => WITHT1YPEview (s0exp_tr s0e)
  | WITHT0YPEviewtype s0e => WITHT1YPEviewtype (s0exp_tr s0e)
end // end of [witht0ype_tr]

(* ****** ****** *)

implement
s0rtdef_tr (d) = let
  val s1te = s0rtext_tr d.s0rtdef_def
(*
  val () = print "s0rtdef_tr: s1te = "
  val (pf_stdout | ptr_stdout) = stdout_get ()
  val () = fprint (file_mode_lte_w_w | !ptr_stdout, s1te)
  val () = stdout_view_set (pf_stdout | (*none*))
  val () = print_newline ()
*)
in
  s1rtdef_make (d.s0rtdef_loc, d.s0rtdef_sym, s1te)
end // end of [s0rtdef_tr]

implement
s0rtdeflst_tr (ds) = $Lst.list_map_fun (ds, s0rtdef_tr)

(* ****** ****** *)

implement
s0expdef_tr (d) = let
  val loc = d.s0expdef_loc
  val arg = s0arglstlst_tr d.s0expdef_arg
  val id = d.s0expdef_sym
  val res = s0rtopt_tr d.s0expdef_res
  val def = s0exp_tr d.s0expdef_def
(*
  val () = begin
    print "s0expdef_tr: def = "; print def; print_newline ()
  end // end of [val]
*)
in
  s1expdef_make (loc, id, arg, res, def)
end // end of [s0expdef_tr]

implement
s0expdeflst_tr (ds) = $Lst.list_map_fun (ds, s0expdef_tr)

(* ****** ****** *)

implement
s0aspdec_tr (d) = let
  val arg = s0arglstlst_tr d.s0aspdec_arg
  val res = s0rtopt_tr d.s0aspdec_res
  val def = s0exp_tr d.s0aspdec_def
in
//
s1aspdec_make (
  d.s0aspdec_fil, d.s0aspdec_loc, d.s0aspdec_qid, arg, res, def
) // end of [s1aspdec_make]
end // end of [s0aspdec_tr]

(* ****** ****** *)

fn d0atcon_tr (d0c: d0atcon): d1atcon = let
//
val qua = s0qualstlst_tr (d0c.d0atcon_qua)
var npf_var: int = 0
val arg = (case+ d0c.d0atcon_arg of
  | Some s0e => let
      val s1e = s0exp_tr s0e
    in
      case+ s1e.s1exp_node of
      | S1Elist (npf, s1es) => (npf_var := npf; s1es)
      | _ => cons (s1e, nil ())
    end
  | None () => nil ()
) : s1explst
//
val ind = (case+ d0c.d0atcon_ind of
  | Some s0e => let
      val s1es = case+ s0e.s0exp_node of
      | S0Elist s0es => s0explst_tr s0es | _ => begin
          prerr_interror ();
          prerr ": d0atcon_tr: index is not a list."; prerr_newline ();
          $Err.abort ()
        end // end of [_]
    in
      Some s1es
    end // end of [Some]
  | None () => None () // end of [None]
) : s1explstopt
//
in
  d1atcon_make (d0c.d0atcon_loc, d0c.d0atcon_sym, qua, npf_var, arg, ind)
end // end of [d0atcon_tr]

fun d0atconlst_tr (ds: d0atconlst): d1atconlst = begin
  case+ ds of
  | cons (d, ds) => cons (d0atcon_tr d, d0atconlst_tr ds)
  | nil () => nil ()
end // end of [d0atconlst_tr]

implement
d0atdec_tr (d0c) = let
  val arg = (
    case+ d0c.d0atdec_arg of
    | Some d0as => Some (d0atarglst_tr d0as) | None () => None ()
  ) : d1atarglstopt

  val con = d0atconlst_tr d0c.d0atdec_con
in
  d1atdec_make (
    d0c.d0atdec_fil, d0c.d0atdec_loc, d0c.d0atdec_sym, arg, con
  ) // end of [d1atdec_make]
end // end of [d0atdec_tr]

implement
d0atdeclst_tr (ds) = begin
  case+ ds of
  | cons (d, ds) => cons (d0atdec_tr d, d0atdeclst_tr ds)
  | nil () => nil ()
end // end of [d0atdeclst_tr]

(* ****** ****** *)

implement
e0xndec_tr (d) = let
  val qua = s0qualstlst_tr (d.e0xndec_qua)
  var npf0: int = 0
  val arg = (case+ d.e0xndec_arg of
    | Some s0e => let
        val s1e = s0exp_tr s0e in
        case+ s1e.s1exp_node of
        | S1Elist (npf, s1es) => (npf0 := npf; s1es)
        | _ => cons (s1e, nil ())
      end // end of [Some]
    | None () => nil ()
  ) : s1explst // end of [val]
in
  e1xndec_make (
    d.e0xndec_fil, d.e0xndec_loc, d.e0xndec_sym, qua, npf0, arg
  ) // end of [e1xndec_make]
end // end of [e0xndec_tr]

implement
e0xndeclst_tr (ds) = $Lst.list_map_fun (ds, e0xndec_tr)

(* ****** ****** *)

(* end of [ats_trans1_sta.dats] *)
