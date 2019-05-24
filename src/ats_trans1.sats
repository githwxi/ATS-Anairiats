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
// Time: August 2007

(* ****** ****** *)

(* The first translation mainly resolves the issue of operator fixity *)

(* ****** ****** *)

staload Loc = "ats_location.sats"
staload Eff = "ats_effect.sats"
staload Syn = "ats_syntax.sats"
staload SEXP = "ats_staexp1.sats"
staload DEXP = "ats_dynexp1.sats"

(* ****** ****** *)

fun do_e0xpact_assert
  (loc: $Loc.location_t, v: $SEXP.v1al): void
fun do_e0xpact_error
  (loc: $Loc.location_t, v: $SEXP.v1al): void
fun do_e0xpact_prerr (v: $SEXP.v1al): void

(* ****** ****** *)

fun e0xp_tr (_: $Syn.e0xp): $SEXP.e1xp
fun e0xplst_tr (_: $Syn.e0xplst): $SEXP.e1xplst

(* ****** ****** *)

fun s0rt_tr (_: $Syn.s0rt): $SEXP.s1rt
fun s0rtlst_tr (_: $Syn.s0rtlst): $SEXP.s1rtlst
fun s0rtopt_tr (_: $Syn.s0rtopt): $SEXP.s1rtopt

fun s0arglst_tr (s0as: $Syn.s0arglst): $SEXP.s1arglst
fun s0arglstlst_tr (s0ass: $Syn.s0arglstlst): $SEXP.s1arglstlst

fun sp0at_tr (sp0t: $Syn.sp0at): $SEXP.sp1at

fun s0exp_tr (_: $Syn.s0exp): $SEXP.s1exp
fun s0explst_tr (_: $Syn.s0explst): $SEXP.s1explst
fun s0expopt_tr (_: $Syn.s0expopt): $SEXP.s1expopt
fun s0explstlst_tr (_: $Syn.s0explstlst): $SEXP.s1explstlst
fun labs0explst_tr (_: $Syn.labs0explst): $SEXP.labs1explst

fun s0qualst_tr (s0qs: $Syn.s0qualst): $SEXP.s1qualst
fun s0qualstlst_tr (s0qss: $Syn.s0qualstlst): $SEXP.s1qualstlst

fun s0rtext_tr (_: $Syn.s0rtext): $SEXP.s1rtext

fun t1mps0explstlst_tr
  (ts0ess: $Syn.t1mps0explstlst): $SEXP.tmps1explstlst

fun witht0ype_tr (w0t: $Syn.witht0ype): $SEXP.witht1ype

(* ****** ****** *)

fun p0at_tr (_: $Syn.p0at): $DEXP.p1at
fun p0atlst_tr (_: $Syn.p0atlst): $DEXP.p1atlst
fun labp0atlst_tr (_: $Syn.labp0atlst): $DEXP.labp1atlst

fun d0exp_tr (_: $Syn.d0exp): $DEXP.d1exp
fun d0explst_tr (_: $Syn.d0explst): $DEXP.d1explst
fun d0explstlst_tr (_: $Syn.d0explstlst): $DEXP.d1explstlst
fun labd0explst_tr (_: $Syn.labd0explst): $DEXP.labd1explst
fun d0expopt_tr (_: $Syn.d0expopt): $DEXP.d1expopt

fun d0exp_lams_dyn_tr (
    knd  : $Syn.lamkind
  , oloc : Option $Loc.location_t
  , ofc  : Option $Syn.funclo
  , lin  : int
  , args : $Syn.f0arglst
  , res  : $Syn.s0expopt
  , oefc : Option ($Eff.effcst)
  , body : $Syn.d0exp
  ) : $DEXP.d1exp
// end of [d0exp_lams_dyn_tr]

(* ****** ****** *)

fun d0ec_fixity_tr
  (f0xty: $Syn.f0xty, ids: $Syn.i0delst): void
fun d0ec_nonfix_tr (ids: $Syn.i0delst): void

(* ****** ****** *)

fun s0rtdef_tr (d: $Syn.s0rtdef): $DEXP.s1rtdef
fun s0rtdeflst_tr (ds: $Syn.s0rtdeflst): $DEXP.s1rtdeflst

fun s0tacon_tr (d: $Syn.s0tacon): $DEXP.s1tacon
fun s0taconlst_tr (ds: $Syn.s0taconlst): $DEXP.s1taconlst
fun s0tacst_tr (d: $Syn.s0tacst): $DEXP.s1tacst
fun s0tacstlst_tr (ds: $Syn.s0tacstlst): $DEXP.s1tacstlst

fun s0tavar_tr (d: $Syn.s0tavar): $DEXP.s1tavar
fun s0tavarlst_tr (ds: $Syn.s0tavarlst): $DEXP.s1tavarlst

fun s0expdef_tr (d: $Syn.s0expdef): $DEXP.s1expdef
fun s0expdeflst_tr (ds: $Syn.s0expdeflst): $DEXP.s1expdeflst

fun s0aspdec_tr (d: $Syn.s0aspdec): $DEXP.s1aspdec

fun d0atdec_tr (d0c: $Syn.d0atdec): $DEXP.d1atdec
fun d0atdeclst_tr (ds: $Syn.d0atdeclst): $DEXP.d1atdeclst

fun e0xndec_tr (d: $Syn.e0xndec): $DEXP.e1xndec
fun e0xndeclst_tr (ds: $Syn.e0xndeclst): $DEXP.e1xndeclst

(* ****** ****** *)

fun d0atsrtdec_tr (d: $Syn.d0atsrtdec): $DEXP.d1atsrtdec
fun d0atsrtdeclst_tr (ds: $Syn.d0atsrtdeclst): $DEXP.d1atsrtdeclst

(* ****** ****** *)

fun d0ec_tr (_: $Syn.d0ec): $DEXP.d1ec
fun d0eclst_tr (_: $Syn.d0eclst): $DEXP.d1eclst

(* ****** ****** *)

fun initize((*void*)): void and finalize((*void*)): void

(* ****** ****** *)

(* end of [ats_trans1.sats] *)
