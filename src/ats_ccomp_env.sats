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
// Time: April 2008
//
(* ****** ****** *)

staload Fil = "ats_filename.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Set = "ats_set_fun.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"

(* ****** ****** *)

sortdef vtype = viewtype

(* ****** ****** *)
//
// for accumulating type defintiions (rec/sum/uni)
//
dataviewtype
typdeflst =
  | TYPDEFLSTcons of (typkey, string(*name*), typdeflst)
  | TYPDEFLSTnil of ()
// end of [typdeflst]

fun typdeflst_get (): typdeflst

(* ****** ****** *)

viewtypedef
saspcstlst = List_vt (s2cst_t)

fun saspcstlst_free (xs: saspcstlst): void

fun the_saspcstlst_add (x: s2cst_t): void
fun the_saspcstlst_get (): saspcstlst

(* ****** ****** *)

dataviewtype
datcstlst =
  | DATCSTLSTcons of (s2cst_t, datcstlst) | DATCSTLSTnil of ()
// end of [datcstlst]

fun datcstlst_free (s2cs: datcstlst): void

fun the_datcstlst_add (s2c: s2cst_t): void
fun the_datcstlst_adds (s2cs: s2cstlst): void
fun the_datcstlst_get (): datcstlst

(* ****** ****** *)

dataviewtype
exnconlst =
  | EXNCONLSTcons of (d2con_t, exnconlst) | EXNCONLSTnil of ()
// end of [exnconlst]

fun exnconlst_free (d2cs: exnconlst): void

fun the_exnconlst_add (d2c: d2con_t): void
fun the_exnconlst_adds (d2cs: d2conlst): void
fun the_exnconlst_get (): exnconlst

(* ****** ****** *)
//
// HX: implemented in [ats_ccomp_trans.dats]
//
absviewtype dynctx_vt

fun the_dynctx_add (d2v: d2var_t, vp: valprim): void

absview dynctx_mark_token
fun the_dynctx_mark (): @(dynctx_mark_token | void)
fun the_dynctx_unmark (pf: dynctx_mark_token | (*none*)): void

fun the_dynctx_free (): void // free the (toplevel) dynctx

fun the_dynctx_find (d2v: d2var_t): valprim

absview dynctx_push_token
fun the_dynctx_pop (pf: dynctx_push_token | (*none*)): void
fun the_dynctx_push (): @(dynctx_push_token | void)

fun dynctx_foreach_main
  {v:view} {vt:vtype} {f:eff} (
    pf: !v
  | m: !dynctx_vt
  , f: (!v | d2var_t, valprim, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [dynctx_foreach_main]

(* ****** ****** *)

typedef vartypset = $Set.set_t (vartyp_t)
fun the_vartypset_add (vtp: vartyp_t): void
fun the_vartypset_pop (): vartypset and the_vartypset_push (): void

fun vartypset_d2varlst_make (vtps: vartypset): d2varlst_vt

fun vartypset_foreach_main
  {v:view} {vt:vtype} {f:eff} (
    pf: !v
  | vtps: vartypset
  , f: (!v | vartyp_t, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [vartypset_foreach_main]

fun vartypset_union
  (vtps1: vartypset, vtps2: vartypset): vartypset
fun vartypset_foreach_cloptr {f:eff}
  (vtps: vartypset, f: !vartyp_t -<cloptr,f> void):<f> void

fun print_vartypset (vtps: vartypset): void
fun prerr_vartypset (vtps: vartypset): void

(* ****** ****** *)

typedef funlabset = $Set.set_t (funlab_t)

fun the_funlabset_add (fl: funlab_t): void
fun the_funlabset_mem (fl: funlab_t): bool
fun the_funlabset_pop (): funlabset and the_funlabset_push (): void

fun funlabset_foreach_main
  {v:view} {vt:vtype} {f:eff} (
    pf: !v
  | fls: funlabset
  , f: (!v | funlab_t, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [funlabset_foreach_main]

fun funlabset_foreach_cloptr {f:eff}
  (fls: funlabset, f: !funlab_t -<cloptr,f> void):<f> void

fun print_funlabset (fls: funlabset): void
fun prerr_funlabset (fls: funlabset): void

(* ****** ****** *)

// [dyncstcon] is in [ats_hiexp.sats]

fun dynconset_foreach_main
  {v:view} {vt:vtype} {f:eff} (
  pf: !v
| d2cs: dynconset
, f: (!v | d2con_t, !vt) -<f> void
, env: !vt
) :<f> void // endfun

fun the_dynconset_get (): dynconset
fun the_dynconset_add (d2c: d2con_t): void

(* ****** ****** *)
//
// HX: [dyncstset] is in [ats_hiexp.sats]
//
fun dyncstset_foreach_main
  {v:view} {vt:vtype} {f:eff} (
  pf: !v
| d2cs: dyncstset
, f: (!v | d2cst_t, !vt) -<f> void
, env: !vt
) :<f> void // endfun

fun the_dyncstset_get
  (): dyncstset = "atsopt_the_dyncstset_get"
// end of [the_dyncstset_get]

//
// HX: [d2c] is added only if it has not been
//
fun the_dyncstset_add_if
  (d2c: d2cst_t): void = "atsopt_the_dyncstset_add_if"
// end of [the_dyncstset_add_if]

fun the_dyncstsetlst_pop
  (): dyncstset = "atsopt_the_dyncstsetlst_pop"
// end of [the_dyncstsetlst_pop]

fun the_dyncstsetlst_push
  ((*void*)): void = "atsopt_the_dyncstsetlst_push"
// end of [the_dyncstsetlst_push]

(* ****** ****** *)

dataviewtype
extypelst =
  | EXTYPELSTcons of (string (*name*), hityp_t, extypelst)
  | EXTYPELSTnil of ()
// end of [extypelst]  

fun the_extypelst_get (): extypelst
fun the_extypelst_add (name: string, hit: hityp_t): void

(* ****** ****** *)

dataviewtype
extvalist =
  | EXTVALLSTnil of ()
  | EXTVALLSTcons of (string (*name*), valprim, extvalist)
// end of [extvalist]

fun extvalist_free (exts: extvalist): void

fun the_extvalist_get (): extvalist
fun the_extvalist_add (name: string, vp: valprim): void

(* ****** ****** *)

dataviewtype
extcodelst =
  | EXTCODELSTcons of
      (loc_t, int(*position*), string (*code*), extcodelst)
  | EXTCODELSTnil of ()
// end of [extcodelst]

fun extcodelst_free (codes: extcodelst): void

fun the_extcodelst_get (): extcodelst
fun the_extcodelst_add (loc: loc_t, pos: int, code: string): void

(* ****** ****** *)

dataviewtype
stafilelst =
  | STAFILELSTcons of ($Fil.filename_t, int(*loadflag*), stafilelst)
  | STAFILELSTnil of ()
// end of [stafilelst]

fun stafilelst_free (fils: stafilelst): void

fun the_stafilelst_get (): stafilelst
fun the_stafilelst_add (fil: $Fil.filename_t, loadflag: int): void

(* ****** ****** *)

dataviewtype
dynfilelst =
  | DYNFILELSTcons of ($Fil.filename_t, dynfilelst)
  | DYNFILELSTnil of ()
// end of [dynfilelst]

fun dynfilelst_free (fils: dynfilelst): void

fun the_dynfilelst_get (): dynfilelst
fun the_dynfilelst_add (fil: $Fil.filename_t): void

(* ****** ****** *)

absview funlab_token
fun funlab_pop (pf: funlab_token | (*none*)): void
fun funlab_push (fl: funlab_t): (funlab_token | void)
fun funlab_top (): funlab_t

(* ****** ****** *)

fun funentry_make (
    loc: loc_t
  , fl: funlab_t
  , level: int
  , fls: funlabset
  , vtps: vartypset
  , _ret: tmpvar_t
  , inss: instrlst
  ) : funentry_t

fun funentry_get_loc (entry: funentry_t): loc_t
fun funentry_get_lab (entry: funentry_t): funlab_t
fun funentry_get_lev (entry: funentry_t): int
fun funentry_get_vtps (entry: funentry_t): vartypset
fun funentry_set_vtps
  (entry: funentry_t, vtps: vartypset): void = "atsopt_funentry_set_vtps"
// end of [funentry_set_vtps]

fun funentry_get_vtps_flag (entry: funentry_t): int
fun funentry_set_vtps_flag // set to 1
  (entry: funentry_t): void = "atsopt_funentry_set_vtps_flag"
// end of [funentry_set_vtps_flag]

fun funentry_get_labset (entry: funentry_t): funlabset
fun funentry_get_ret (entry: funentry_t): tmpvar_t
fun funentry_get_body (entry: funentry_t): instrlst

fun funentry_get_tailjoin (entry: funentry_t): tailjoinlst
fun funentry_set_tailjoin
  (entry: funentry_t, tjs: tailjoinlst): void = "atsopt_funentry_set_tailjoin"
// end of [funentry_set_tailjoin]

 
fun funentry_associate (entry: funentry_t): void
fun funentry_get_vtps_all (entry: funentry_t): vartypset

//

fun varindmap_find (d2v: d2var_t): Option_vt int
fun varindmap_find_some (d2v: d2var_t): int

fun funentry_varindmap_reset (): void
fun funentry_varindmap_set (vtps: vartypset): void

(* ****** ****** *)

fun funentry_get_lablst (): funlablst_vt
fun funentry_add_lablst (fl: funlab_t): void

(* ****** ****** *)

fun loopexnlablst_pop (): void
fun loopexnlablst_push
  (tl_init: tmplab_t, tl_fini: tmplab_t, tl_cont: tmplab_t): void
fun loopexnlablst_get (i: int): tmplab_t

(* ****** ****** *)

dataviewtype
glocstlst =
  | GLOCSTLSTcons_clo of (d2cst_t, glocstlst)
  | GLOCSTLSTcons_fun of (d2cst_t, glocstlst)
  | GLOCSTLSTcons_val of (d2cst_t, valprim, glocstlst)
  | GLOCSTLSTnil of ()
// end of [glocstlst]

fun the_glocstlst_get (): glocstlst

fun the_glocstlst_add_clo (d2c: d2cst_t): void
fun the_glocstlst_add_fun (d2c: d2cst_t): void

fun the_glocstlst_add_val (d2c: d2cst_t, vp: valprim): void

(* ****** ****** *)

dataviewtype
partvalst =
  | PARTVALSTcons of (string(*name*), valprim, partvalst)
  | PARTVALSTnil of ()
// end of [partvalst]

fun the_partvalst_get (): partvalst
fun the_partvalst_add (name: string, vp: valprim): void

(* ****** ****** *)

fun the_topcstctx_add (d2c: d2cst_t, vp: valprim): void
fun the_topcstctx_find (d2c: d2cst_t): Option_vt (valprim)

(* ****** ****** *)

fun the_valprimlst_get_free (): valprimlst_vt
fun the_valprimlst_add_free (vp: valprim): void

(* ****** ****** *)
//
// HX: for tailcall optimization
//
dataviewtype
tailcalist =
  | TAILCALLSTnil of ()
  | TAILCALLSTmark of tailcalist
  | TAILCALLSTcons of (funlab_t, tmpvarlst, tailcalist)
// end of [tailcalist]

absview tailcalist_token

fun the_tailcalist_add (fl: funlab_t, tmps: tmpvarlst): void
fun the_tailcalist_mark (): (tailcalist_token | void)
fun the_tailcalist_unmark (pf: tailcalist_token | (*none*)): void
fun the_tailcalist_find (fl: funlab_t): Option_vt (tmpvarlst)

(* ****** ****** *)

(* end of [ats_ccomp_env.sats] *)
