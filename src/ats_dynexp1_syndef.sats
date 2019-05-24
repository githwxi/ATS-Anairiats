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
// Time: November 2010
//
(* ****** ****** *)

staload
Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
staload  Syn = "ats_syntax.sats"
typedef tmpqi0de = $Syn.tmpqi0de

(* ****** ****** *)

staload  "ats_staexp1.sats"
staload  "ats_dynexp1.sats"

(* ****** ****** *)

fun tmpqi0de_make_qid
  (loc: loc_t, q: d0ynq, id: sym_t): tmpqi0de
// end of [tmpqi0de_make_qid]

(* ****** ****** *)

fun un_d1exp_ann_type (d1e: d1exp): (d1exp, s1exp)

(* ****** ****** *)

fun un_d1exp_qid (d1e: d1exp): (d0ynq, sym_t)
fun un_d1exp_qid_sym (d1e: d1exp, id: sym_t): void

(* ****** ****** *)

fun un_d1exp_idext (d1e: d1exp): sym_t
fun un_d1exp_idext_sym (d1e: d1exp, id: sym_t): void

(* ****** ****** *)

fun un_d1exp_sexparg (d1e: d1exp): s1exparg

(* ****** ****** *)

fun un_d1exp_decseq (d1e: d1exp): d1eclst

(* ****** ****** *)

typedef intlst = List (int)
typedef fsyndef = (loc_t, d1explst) -<fun1> d1exp
viewtypedef fsyndefopt = Option_vt (fsyndef)

(* ****** ****** *)

fun fprint_intlst (out: FILEref, ns: intlst): void

(* ****** ****** *)

fun match_intlst_intlst (ns1: intlst, ns2: intlst): bool

(* ****** ****** *)

fun d1exp_idextapp_resolve (loc0: loc_t, d1e: d1exp): d1exp

(* ****** ****** *)
//
// HX: for resolving external ids loaded with syndef
//
fun d1exp_app_syndef (
  loc: loc_t, d1e_fun: d1exp, d1e_arg: d1exp
) : d1exp // end of [d1exp_app_syndef]

(* ****** ****** *)

fun atsyndef_search_all_default (id: sym_t, ns: intlst): fsyndefopt

(* ****** ****** *)

(* end of [ats_dynexp1_syndef.sats] *)
