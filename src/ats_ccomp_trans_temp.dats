(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
// Start Time: May 2008
//
(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%}

(* ****** ****** *)

staload "ats_reference.sats"

(* ****** ****** *)

staload CS = "ats_charlst.sats"
staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload HT = "ats_hashtbl.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Map = "ats_map_lin.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_reference.dats"
staload _(*anonymois*) = "ats_hashtbl.dats"
staload _(*anonymois*) = "ats_map_lin.dats"

(* ****** ****** *)

#define THISFILENAME "ats_ccomp_trans_temp.dats"

(* ****** ****** *)

absviewtype stactx_vt
absview stactx_token_v

extern fun print_the_stactx (): void

extern fun the_stactx_add (s2v: s2var_t, hit: hityp_t): void
extern fun the_stactx_free ():<> void // free the (toplevel) stactx
extern fun the_stactx_find (s2v: s2var_t): Option_vt (hityp_t)
extern fun the_stactx_push (): @(stactx_token_v | void)
extern fun the_stactx_pop (pf: stactx_token_v | (*none*)): void

(* ****** ****** *)

fn prerr_interror () =
  prerr "INTERNAL ERROR (ats_ccomp_trans_temp)"
fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_ccomp_trans_temp)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

local

viewtypedef stactx = $Map.map_vt (s2var_t, hityp_t)
viewtypedef stactxlst = List_vt (stactx)

assume stactx_vt = stactx
assume stactx_token_v = unit_v

fn stactx_nil ():<> stactx = $Map.map_make (compare_s2var_s2var)

val the_stactx = ref_make_elt<stactx> (stactx_nil ())
val the_stactxlst = ref_make_elt<stactxlst> (list_vt_nil ())

in // in of [local]

implement
print_the_stactx () = let
  val kis = $Map.map_list_inf (!p) where {
    val (vbox pf | p) = ref_get_view_ptr (the_stactx)
  } // end of [val]
  fun loop (
    kis: List_vt @(s2var_t, hityp_t)
  ) : void = case+ kis of
    | ~list_vt_cons (ki, kis) => let
        val () = print_s2var (ki.0)
        val () = print_string " -> "
        val () = print_hityp_t (ki.1)
        val () = print_newline ()
      in
        loop (kis)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => () // end of [list_vt_nil]
  // end of [loop]
in
  loop (kis)
end // end of [print_the_stactx]

implement
the_stactx_add (s2v, hit) = let
  val (vbox pf | p) = ref_get_view_ptr (the_stactx)
in
  $Map.map_insert<s2var_t,hityp_t> (!p, s2v, hit)
end // end of [the_stactx_add]

implement
the_stactx_find (s2v) = let
  val (vbox pf | p) = ref_get_view_ptr (the_stactx)
in
  $Map.map_search<s2var_t,hityp_t> (!p, s2v)
end // end of [the_stactx_find]

implement
the_stactx_push () = let
//
  val stactx = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactx)
    val stactx = !p
  in
    !p := stactx_nil (); stactx
  end // end of [val]
//
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactxlst)
  in
    !p := list_vt_cons (stactx, !p)
  end // end of [val]
//
in
  (unit_v () | ())
end // end of [the_stactx_push]

implement
the_stactx_pop (pf | (*none*)) = let
  prval unit_v () = pf
//
  var err: int = 0; val stactx = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactxlst)
    val stactx = (
      case+ !p of
      | ~list_vt_cons (x, xs) => (!p := (xs: stactxlst); x)
      | list_vt_nil () => begin
          fold@ (!p); err := 1; stactx_nil ()
        end
    ) : stactx
  in
    stactx
  end // end of [val]
//
  val () = if err > 0 then begin // error checking
    prerr_interror (); prerr ": the_stactx_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
//
  val stactx = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactx)
    val () = $Map.map_free (!p)
  in
    !p := stactx
  end // end of [val]
//
in
  // empty
end // end of [the_stactx_pop]

end // end of [local]

(* ****** ****** *)
//
// HX: declared in [ats_hiexp.sats]
//
implement
hityp_s2var_normalize (s2v) = let
(*
  val () = print "hityp_s2var_normalize: the_stactx =\n"
  val () = print_the_stactx ()
*)
in
  the_stactx_find (s2v)
end // end of [hityp_s2var_normalize]

(* ****** ****** *)

#define PTR_TYPE_NAME "ats_ptr_type"

(*
// HX: foo(bar)(baz1, baz2) -> foo;bar;baz1,baz2
*)

implement
template_name_make
  (basename, hitss0) = let
  viewtypedef T = $CS.Charlst_vt
//
  fun aux_char
    (cs: &T, c: char): void = (cs := $CS.CHARLSTcons (c, cs))
  (* end of [aux_char] *)
//
  fun aux_string {n,i:nat | i <= n}
     (cs: &T, s: string n, i: size_t i): void =
    if string_is_atend (s, i) then () else begin
      cs := $CS.CHARLSTcons (s[i], cs); aux_string (cs, s, i+1)
    end // end of [if]
  (* end of [aux_string] *)
//
  fun aux_hityp
    (cs: &T, hit: hityp): void =
    case+ hit.hityp_node of
    | HITextype (name, _arg) => let
        val name = string1_of_string name
        val () = aux_string (cs, name, 0)
      in
        aux_hityplstlst (cs, _arg, 1)
      end // end of [HITextype]
    | _ => let    
        val HITNAM (knd, name) = hit.hityp_name
        val name = (if knd > 0 then PTR_TYPE_NAME else name): string
        val name = string1_of_string name
      in
        aux_string (cs, name, 0)
      end // end of [_]
  (* end of [aux_hityp] *)
//
  and aux_hityplst (
    cs: &T, hits: hityplst, i: int
  ) : void = case+ hits of
    | list_cons (hit, hits) => let
        val () = if i > 0 then aux_char (cs, ',')
        val () = aux_hityp (cs, hit)
      in
        aux_hityplst (cs, hits, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  (* end of [aux_hityplst] *)
//
  and aux_hityplstlst (
    cs: &T, hitss: hityplstlst, i: int
  ) : void = case+ hitss of
    | list_cons (hits, hitss) => let
        val () = if i > 0 then aux_char (cs, ';')
        val () = aux_hityplst (cs, hits, 0)
      in
        aux_hityplstlst (cs, hitss, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  (* end of [aux_hityplstlst] *)
//
  fun aux1_hityplstlst (
    cs: &T, hitss: hityplstlst, i: int
  ) : void = case+ hitss of
    | list_cons (hits, hitss) => let
        val () = if i > 0 then aux_char (cs, '_')
        val () = aux_hityplst (cs, hits, 0)
      in
        aux1_hityplstlst (cs, hitss, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  (* end of [aux1_hityplstlst] *)
//
  var cs: T = $CS.CHARLSTnil ()
  val basename = string1_of_string (basename)
  val () = aux_string (cs, basename, 0)
  val hitss0 = hityplstlst_decode hitss0
  val () = aux1_hityplstlst (cs, hitss0, 1)
//
in
  $CS.string_make_charlst_rev (cs)
end // end of [template_name_make]

(* ****** ****** *)

datatype tmpcstvar =
  | TMPcst of d2cst_t | TMPvar of d2var_t
// end of [tmpcstvar]

fn fprint_tmpcstvar {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, tcv: tmpcstvar)
  : void = begin case+ tcv of
  | TMPcst d2c => fprint_d2cst (pf | out, d2c)
  | TMPvar d2v => fprint_d2var (pf | out, d2v)
end // end of [fprint_tmpcstvar]

fn print_tmpcstvar (tcv: tmpcstvar): void = print_mac (fprint_tmpcstvar, tcv)
fn prerr_tmpcstvar (tcv: tmpcstvar): void = prerr_mac (fprint_tmpcstvar, tcv)

(* ****** ****** *)

extern
fun ccomp_tmpdef
(
  loc0: loc_t
, res: &instrlst_vt
, hit0: hityp_t
, tcv: tmpcstvar
, hitss: hityplstlst_t
, fullname: string
, tmpdef: tmpdef_t
) : valprim // end of [ccomp_tmpdef]

(* ****** ****** *)

fn template_arg_match
(
    loc0: loc_t
  , tcv: tmpcstvar
  , tmparg: s2qualst
  , hitss: hityplstlst_t
  ) : void = let
//
  fun aux (
    s2v: s2var_t, hit: hityp
  ) :<cloptr1> void = let
    val hit = hityp_encode hit in the_stactx_add (s2v, hit)
  end // end of [aux]
//
  fun auxlst (
    s2vs: s2varlst
  , hits: hityplst
  ) :<cloptr1> void = begin
    case+ (s2vs, hits) of
    | (list_cons (s2v, s2vs),
       list_cons (hit, hits)) => let
       val () = aux (s2v, hit) in auxlst (s2vs, hits)
      end // end of [list_cons _, list_cons _]
    | (list_nil (), list_nil ()) => ()
    | (_, _) => let
        val () = $Loc.prerr_location (loc0)
        val () = prerr ": error(ccomp)"; val () = (
          prerr ": template argument mismatch for ["; prerr_tmpcstvar tcv; prerr "]."
        ) // end of [val]
        val () = prerr_newline ()
      in
        $Err.abort {void} ()
      end // end of [_, _]
  end // end of [auxlst]
//
  fun auxlstlst (
    s2qs: s2qualst
  , hitss: hityplstlst
  ) :<cloptr1> void = begin
    case+ (s2qs, hitss) of
    | (list_cons (s2q, s2qs),
       list_cons (hits, hitss)) => let
        val () = auxlst (s2q.0, hits) in auxlstlst (s2qs, hitss)
      end // end of [list_cons _, list_cons _]
    | (list_nil (), list_nil ()) => ()
    | (_, _) => let
        val () = $Loc.prerr_location (loc0)
        val () = prerr ": error(ccomp)"; val () = (
          prerr ": template argument mismatch for ["; prerr_tmpcstvar tcv; prerr "]."
        ) // end of [val]
        val () = prerr_newline ()
      in
        $Err.abort {void} ()
      end // end of [_, _]
  end // end of [auxlstlst]
//
in
  auxlstlst (tmparg, hityplstlst_decode hitss)
end // end of [template_arg_match]

(* ****** ****** *)

local

#define TMPNAMETBL_SIZE_HINT 1024

typedef tmpnamtbl = $HT.hashtbl_t (string, valprim)

val the_tmpnamtbl = begin
  $HT.hashtbl_str_make_hint {valprim} (TMPNAMETBL_SIZE_HINT)
end : tmpnamtbl // end of [the_tmpnamtbl]

in // in of [local]

implement
tmpnamtbl_add
(
  fullname, vp_funclo
) = let
//
val ans =
  $HT.hashtbl_insert (the_tmpnamtbl, fullname, vp_funclo)
//
in
//
case+ ans of
| ~None_vt () => ()
| ~Some_vt vp => begin
    prerr_interror ();
    prerr ": tmpnamtbl_add: fullname = "; prerr fullname; prerr_newline ();
    $Err.abort {void} ()
  end // end of [Some_vt]
//
end // end of [tmpnamtbl_add]

implement
tmpnamtbl_find (fullname) =
  $HT.hashtbl_search (the_tmpnamtbl, fullname)
// end of [tmpnamtbl_find]

end // end of [local]

(* ****** ****** *)

implement
ccomp_tmpdef
(
  loc0, res, hit0, tcv, hitss, fullname, tmpdef
) = let
//
  val fl = funlab_make_nam_typ (fullname, hit0)
  val vp_funclo = valprim_funclo_make (fl)
//
  val (pf_stactx_token | ()) = the_stactx_push ()
  val (pf_dynctx_token | ()) = the_dynctx_push ()
//
  val tmparg = tmpdef_get_arg tmpdef
  val () = template_arg_match (loc0, tcv, tmparg, hitss)
  val () = tmpnamtbl_add (fullname, vp_funclo)
//
(* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv *)
  val (pf_tailcalist_mark | ()) = the_tailcalist_mark ()
  val () = the_tailcalist_add (fl, list_nil ())
  val _(*funentry_t*) = let
    val ins = instr_funlab (fl); val prolog = '[ins]
    val hie = tmpdef_get_exp (tmpdef); val loc_fun = hie.hiexp_loc
  in
    case+ hie.hiexp_node of
    | HIElam (hips_arg, hie_body) => begin
        ccomp_exp_arg_body_funlab (loc_fun, prolog, hips_arg, hie_body, fl)
      end // end of [HIElam]
    | _ => begin
        prerr_loc_interror (loc_fun);
        prerr ": ccomp_tmpdef: hie = "; prerr_hiexp hie; prerr_newline ();
        $Err.abort {funentry_t} ()
      end // end of [_]
   end (* end of [val] *)
  val () = the_tailcalist_unmark (pf_tailcalist_mark | (*none*))
(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
//
  val () = the_stactx_pop (pf_stactx_token | (*none*))
  val () = the_dynctx_pop (pf_dynctx_token | (*none*))
//
in
  vp_funclo
end // end of [ccomp_tmpdef]

(* ****** ****** *)

implement
template_cst_name_make
  (d2c, hitss) = let
  val extdef = d2cst_get_extdef (d2c)
  val base = (case+ extdef of
    | $Syn.DCSTEXTDEFnone () => let
        val sym = d2cst_get_sym (d2c)
        and stamp = d2cst_get_stamp (d2c)
        val name = tostringf (
          "%s$%s", @($Sym.symbol_name sym, $Stamp.tostring_stamp stamp)
        ) // end of [tostringf]
      in
        string_of_strptr (name)
      end // end of [if]
    | $Syn.DCSTEXTDEFsome_ext name => name
    | $Syn.DCSTEXTDEFsome_sta name => name
    | $Syn.DCSTEXTDEFsome_mac name => let
        val () = prerr_interror (); val () =  (
          prerr ": tmpnamtbl_cst_name_make: d2c = "; prerr d2c
        ) // end of [val]
        val () = prerr_newline ()
      in
        $Err.abort {string} ()
      end // end of [DCSTEXTDEFsome_mac]
  ) : string // end of [val]
in
  template_name_make (base, hitss)
end // end of [template_cst_name_make]

implement
template_var_name_make
  (d2v, hitss) = let
  val sym = d2var_get_sym d2v
  val stamp = d2var_get_stamp d2v
  val basename = tostringf (
    "%s$%s", @($Sym.symbol_name sym, $Stamp.tostring_stamp stamp)
  ) // end of [tostringf]
  val basename = string_of_strptr (basename)
in
  template_name_make (basename, hitss)
end // end of [template_var_name_make]

(* ****** ****** *)

implement
ccomp_exp_template_cst
  (res, loc0, hit0, d2c, hitss) = let
  val hitss = hityplstlst_normalize (hitss)
  val fullname = template_cst_name_make (d2c, hitss)
(*
  val () = begin
    print "ccomp_exp_tmpcst: hit0 = "; print hit0; print_newline ();
    print "ccomp_exp_tmpcst: fullname = "; print fullname; print_newline ();
  end // end of [val]
*)
  val ovp = tmpnamtbl_find (fullname)
in
  case+ ovp of
  | ~None_vt () => let
      val tmpdef = (
      case+ tmpcstmap_find d2c of
      | ~Some_vt tmpdef => tmpdef
      | ~None_vt () => let
          val () = $Loc.prerr_location loc0
          val () = prerr ": error(ccomp)"
          val () = $Deb.debug_prerrf
            (": %s: ccomp_exp_template_cst", @(THISFILENAME))
          val () = prerr ": the template definition for ["
          val () = prerr d2c
          val () = prerr "] is unavailable at ["
          val () = prerr fullname
          val () = prerr "]."
          val () = prerr_newline ()
        in
          $Err.abort {tmpdef_t} ()
        end // end of [None_vt]
      ) : tmpdef_t
      val level0 = d2var_current_level_get ()
      val () = d2var_current_level_set (0)
      val vp = ccomp_tmpdef (loc0, res, hit0, TMPcst d2c, hitss, fullname, tmpdef)
      val level0 = d2var_current_level_set (level0)
    in
      vp // return value
    end (* end of [None_vt] *)
  | ~Some_vt vp => vp
end // end of [ccomp_exp_template_cst]

(* ****** ****** *)

implement
ccomp_exp_template_var
  (res, loc0, hit0, d2v, hitss) = let
  val hitss = hityplstlst_normalize (hitss)
  val fullname = template_var_name_make (d2v, hitss)
(*
  val () = begin
    print "ccomp_exp_tmpvar: hit0 = "; print hit0; print_newline ();
    print "ccomp_exp_tmpvar: fullname = "; print fullname; print_newline ();
  end // end of [val]
*)
  val ovp = tmpnamtbl_find (fullname)
in
  case+ ovp of
  | ~None_vt () => let
      val tmpdef = (
      case+ tmpvarmap_find d2v of
      | ~Some_vt tmpdef => tmpdef
      | ~None_vt () => let
          val () = $Loc.prerr_location loc0
          val () = prerr ": error(ccomp)"
          val () = $Deb.debug_prerrf
            (": %s: ccomp_exp_template_var", @(THISFILENAME))
          val () = prerr ": the template definition for ["
          val () = prerr d2v
          val () = prerr "] is unavailable at ["
          val () = prerr fullname
          val () = prerr "]."
          val () = prerr_newline ()
        in
          $Err.abort {tmpdef_t} ()
        end // end of [None_vt]
      ) : tmpdef_t
      val d2v_lev = d2var_get_lev (d2v)
      val level0 = d2var_current_level_get ()
(*
      val () = begin
        print "ccomp_exp_tmpvar: d2v_lev = "; print d2v_lev; print_newline ();
        print "ccomp_exp_tmpvar: level0 = "; print level0; print_newline ();
      end // end of [val]
*)
      val () = d2var_current_level_set (d2v_lev)
      val vp = ccomp_tmpdef (loc0, res, hit0, TMPvar d2v, hitss, fullname, tmpdef)
      val () = d2var_current_level_set (level0)
    in
      vp // return value
    end (* end of [None_vt] *)
  | ~Some_vt vp => vp
end // end of [ccomp_exp_template_var]

(* ****** ****** *)

(* end of [ats_ccomp_trans_temp.dats] *)
