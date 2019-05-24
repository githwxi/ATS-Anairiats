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
// Time: October 2007
//
(* ****** ****** *)

staload Cnt = "ats_counter.sats"
staload Eff = "ats_effect.sats"
staload Fil = "ats_filename.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats" // for [e1xp]

(* ****** ****** *)

typedef count_t = $Cnt.count_t
typedef fil_t = $Fil.filename_t
typedef intinf_t = $IntInf.intinf_t
typedef lab_t = $Lab.label_t
typedef loc_t = $Loc.location_t
typedef stamp_t = $Stamp.stamp_t
typedef sym_t = $Sym.symbol_t
typedef symopt_t = Option (sym_t)

(* ****** ****** *)

abstype s2rtdat_t // boxed type

abstype s2cst_t // assumed in [ats_staexp2_scst.dats]
abstype s2var_t // assumed in [ats_staexp2_svVar.dats]
abstype s2varset_t // assumed in [ats_staexp2_svVar.dats]

abstype s2Var_t // assumed in [ats_staexp2_svVar.dats]
abstype s2Varset_t // assumed in [ats_staexp2_svVar.dats]
abstype s2Varbound_t // assumed in [ats_staexp2_svVar.dats]

abstype d2con_t // assumed in [ats_staexp2_dcon.dats]

typedef s2varlst = List s2var_t
typedef s2varopt = Option s2var_t
typedef s2varlstlst = List s2varlst

typedef s2Varlst = List s2Var_t
typedef s2Varboundlst = List s2Varbound_t

datatype s2cstopt =
  | S2CSTOPTsome of s2cst_t | S2CSTOPTnone 
// end of [s2cstopt]

datatype s2cstlst =
  | S2CSTLSTcons of (s2cst_t, s2cstlst) | S2CSTLSTnil 
// end of [s2cstlst]

datatype d2conlst =
  | D2CONLSTcons of (d2con_t, d2conlst) | D2CONLSTnil
// end of [d2conlst]

(* ****** ****** *)

datatype s2item =
  (* static items *)
  | S2ITEMcst of s2cstlst
  | S2ITEMdatconptr of d2con_t
  | S2ITEMdatcontyp of d2con_t
  | S2ITEMe1xp of e1xp
  | S2ITEMfil of fil_t
  | S2ITEMvar of s2var_t
// end of [s2item]

where s2itemlst = List s2item
and s2itemopt_vt = Option_vt s2item

(* ****** ****** *)

fun s2cstlst_length (_: s2cstlst): Nat
fun s2cstlst_append (_: s2cstlst, _: s2cstlst): s2cstlst
fun s2cstlst_reverse (_: s2cstlst): s2cstlst

(* ****** ****** *)

datatype tyreckind =
  | TYRECKINDbox (* boxed *)
  | TYRECKINDflt0
  | TYRECKINDflt1 of stamp_t (* flat *)
  | TYRECKINDflt_ext of string  (* flat *)
// end of [tyreckind]

fun eq_tyreckind_tyreckind (_: tyreckind, _: tyreckind): bool
overload = with eq_tyreckind_tyreckind

(* ****** ****** *)

datatype s2rtbas =
  | S2RTBASpre of (* predicative sorts *)
      sym_t // bool, char, int, ...
  | S2RTBASimp of (* impredicative sorts *)
      (sym_t, int (*prf*), int (*lin*))
  | S2RTBASdef of (* user-defined datasorts *)
      s2rtdat_t
// end of [s2rtbas]

and s2rt =
  | S2RTbas of s2rtbas (* base sort *)
  | S2RTfun of (s2rtlst, s2rt) // function sort
  | S2RTtup of s2rtlst (* tuple sort *)
// end of [s2rt]

and s2rtext = (* extended sort *)
  | S2TEsrt of s2rt
  | S2TEsub of (s2var_t, s2rt, s2explst)
// end of [s2rtext]

and sp2at_node =
  | SP2Tcon of (s2cst_t, s2varlst)
// end of [sp2at_node]

and s2kexp =
  | S2KEany
  | S2KEapp of (s2kexp, s2kexplst)
  | S2KEcst of s2cst_t
  | S2KEfun of ($Syn.funclo, s2kexplst, s2kexp)
  | S2KEtyarr
  | S2KEtyrec of (tyreckind, labs2kexplst)
  | S2KEunion of s2kexplst // union
  | S2KEvar of s2var_t
// end of [s2kexp]

and labs2kexplst =
  | LABS2KEXPLSTnil
  | LABS2KEXPLSTcons of (lab_t, s2kexp, labs2kexplst)
// end of [labs2kexplst]

and s2zexp =
  | S2ZEapp of (s2zexp, s2zexplst)
  | S2ZEbot
  | S2ZEcst of s2cst_t
  | S2ZEextype of string (* external type *)
  | S2ZEptr of () (* pointer size *)
  | S2ZEtyarr of // array size
      (s2zexp (*element size*), s2explstlst (*dimension*))
  | S2ZEtyrec of (tyreckind, labs2zexplst)
  | S2ZEunion of (stamp_t, labs2zexplst)
  | S2ZEvar of s2var_t
// end of [s2zexp]

and labs2zexplst =
  | LABS2ZEXPLSTnil
  | LABS2ZEXPLSTcons of (lab_t, s2zexp, labs2zexplst)
// end of [labs2zexplst]

and s2eff =
  | S2EFFall
  | S2EFFnil
  | S2EFFset of ($Eff.effset_t, s2explst)
// end of [s2eff]

and s2lab = 
  | S2LAB0lab of lab_t
  | S2LAB0ind of s2explstlst
  | S2LAB1lab of (* selection label *)
      (lab_t, s2exp) (* record/union type *)
  | S2LAB1ind of (* array index *)
      (s2explstlst, s2exp(*element*))
// end of [s2lab]

and s2exp_node =
  | S2Eapp of (* static application *)
      (s2exp, s2explst)
  | S2Echar of char
  | S2Eclo of (int(*knd*), s2exp) (* knd: -1/0/1: ref/clo/ptr *)
  | S2Ecrypt of s2exp
  | S2Ecst of (* static constant *)
      s2cst_t
  | S2Edatconptr of (* unfolded datatype *)
      (d2con_t, s2explst) (* constructor and addrs of arguments *)
  | S2Edatcontyp of (* unfolded datatype *)
      (d2con_t, s2explst) (* constructor and types of arguments *)
  | S2Eeff of (* effects *)
      s2eff
  | S2Eeqeq of (* generic equality relation *)
      (s2exp, s2exp)
  | S2Eexi of (* existential quantifed expression *)
      (s2varlst, s2explst, s2exp)
  | S2Eextype of (* external name *)
      (string, s2explstlst)
  | S2Efun of (* function type *) (
      $Syn.funclo
    , int(*lin*)
    , s2eff(*effects*)
    , int (*pfarity*)
    , s2explst (*arguments*)
    , s2exp (*result*)
    ) // end of S2Efun
  | S2Eint of (* static integer *)
      int
  | S2Eintinf of (* static integer *)
      intinf_t
  | S2Elam of (* static abstraction *)
      (s2varlst, s2exp)
  | S2Emetfn of (* metriked function *)
      (Option stamp_t, s2explst, s2exp)
  | {n:nat} S2Emetlt of (* strict metric ordering *)
      (s2explst n, s2explst n)
(*
// HX-2010-12-04: inadequate design
  | S2Enamed of (sym_t, s2exp) // named types
*)
  | S2Eout of (* taken out *)
      s2exp
  | S2Eproj of (s2exp (*addr*), s2lab)
  | S2Eread of (s2exp (*view*), s2exp (*viewt@ype*))
  | S2Erefarg of (* reference argument type *)
      (int(*1:ref/0:val*), s2exp) (* &/!: call-by-ref/val *)
  | S2Esel of (* static selection *)
      (s2exp, int)
  | S2Esize of (* size *)
      s2zexp
  | S2Esizeof of (* size of a type *)
      s2exp
  | S2Etop of (* 0/1: topization/typization *)
      (int(*knd*), s2exp)
  | S2Etup of (* tuple *)
      s2explst
  | S2Etyarr of (* array type *)
      (s2exp (*elt type*), s2explstlst (*dimension*))
  | S2Etyleq of (* dynamic subprop/subtype/subview/subviewtype relation *)
      (int(*knd*), s2exp, s2exp) // knd=0: already tried; knd=1+: not tried
  | S2Etylst of (* type list *)
      s2explst
  | S2Etyrec of (* record expression *)
      (tyreckind, int (*pfarity*), labs2explst)
  | S2Euni of (* universal quantified expression *)
      (s2varlst, s2explst, s2exp)
  | S2Eunion of (* union type *)
      (stamp_t, s2exp (*index*), labs2explst)
  | S2Evar of (* static variable *)
      s2var_t
  | S2EVar of (* static existential variable *)
      s2Var_t
  | S2Evararg of (* variadic argument type *)
      s2exp
  | S2Ewth of (* the result part of a function type *)
      (s2exp, wths2explst (* for restoration *))
// end of [s2exp_node]

and labs2explst =
  | LABS2EXPLSTnil
  | LABS2EXPLSTcons of (lab_t, s2exp, labs2explst)
// end of [labs2explst]

and tmps2explstlst =
  | TMPS2EXPLSTLSTnil
  | TMPS2EXPLSTLSTcons of (loc_t, s2explst, tmps2explstlst)
// end of [tmps2explstlst]

and wths2explst = // needed in [ats_trans2_sta.dats]
  | WTHS2EXPLSTnil
  | WTHS2EXPLSTcons_some of (int(*refval*), s2exp, wths2explst)
  | WTHS2EXPLSTcons_none of wths2explst
// end of [wths2explst]

where s2rtlst = List s2rt
and s2rtopt = Option s2rt
and s2rtlstlst = List s2rtlst
and s2rtlstopt = Option s2rtlst

and s2rtextopt_vt = Option_vt s2rtext

and s2arg = '{
  s2arg_loc= loc_t, s2arg_sym= sym_t, s2arg_srt= s2rtopt
} // end of [s2arg]

and s2arglst = List s2arg

and s2zexplst = List s2zexp
and s2zexpopt = Option s2zexp
and s2zexpopt_vt = Option_vt s2zexp

and s2kexplst = List s2kexp

and s2lablst = List s2lab
and s2lablst_vt = List_vt s2lab

(* ****** ****** *)

and s2exp = '{
  s2exp_srt= s2rt, s2exp_node= s2exp_node
} // end of [s2exp]

and s2explst (n:int) = list (s2exp, n)
and s2explst = [n:nat] s2explst n
and s2expopt = Option s2exp
and s2expopt_vt = Option_vt s2exp
and s2explstlst = List s2explst
and s2explstopt = Option s2explst

(* ****** ****** *)

and sp2at = '{
  sp2at_loc= loc_t, sp2at_exp= s2exp, sp2at_node= sp2at_node
} // end of [sp2at]

(* ****** ****** *)

datatype s2exparg_node =
  | S2EXPARGone (* {..} *)
  | S2EXPARGall (* {...} *)
  | S2EXPARGseq of s2explst
// end of [s2exparg_node]

typedef s2exparg = '{
  s2exparg_loc= loc_t, s2exparg_node= s2exparg_node
} // end of [s2exparg]

typedef s2exparglst = List s2exparg

(* ****** ****** *)

typedef
s2qua = (s2varlst, s2explst)
typedef s2qualst = List s2qua

(* ****** ****** *)

val s2rt_addr : s2rt
val s2rt_bool : s2rt
val s2rt_char : s2rt
val s2rt_cls : s2rt
val s2rt_eff : s2rt
val s2rt_int : s2rt

(*

val s2rt_rat : s2rt
val s2rt_reg : s2rt

*)

val s2rt_prop : s2rt
val s2rt_type : s2rt
val s2rt_t0ype : s2rt
val s2rt_view : s2rt
val s2rt_viewtype : s2rt
val s2rt_viewt0ype : s2rt
val s2rt_types : s2rt

(* ****** ****** *)

fun s2rt_is_cls (s2t: s2rt): bool

fun s2rt_is_dat (s2t: s2rt): bool
fun s2rt_is_int (s2t: s2rt): bool

fun s2rt_is_fun (s2t: s2rt): bool

fun s2rt_is_prop (s2t: s2rt): bool
fun s2rt_is_type (s2t: s2rt): bool
fun s2rt_is_t0ype (s2t: s2rt): bool
fun s2rt_is_view (s2t: s2rt): bool
fun s2rt_is_viewtype (s2t: s2rt): bool
fun s2rt_is_viewtype_fun (s2t: s2rt): bool
fun s2rt_is_viewt0ype (s2t: s2rt): bool
fun s2rt_is_types (s2t: s2rt): bool

(* ****** ****** *)

fun s2rt_is_linear (s2t: s2rt): bool
fun s2rt_is_linear_fun (s2t: s2rt): bool
fun s2rt_is_proof (s2t: s2rt): bool
fun s2rt_is_proof_fun (s2t: s2rt): bool
fun s2rt_is_program (s2t: s2rt): bool
fun s2rt_is_program_fun (s2t: s2rt): bool
fun s2rt_is_impredicative (s2t: s2rt): bool
fun s2rt_is_impredicative_fun (s2t: s2rt): bool
fun s2rt_is_boxed (s2t: s2rt): bool
fun s2rt_is_boxed_fun (s2t: s2rt): bool

(* ****** ****** *)

fun s2rt_base_fun (s2t: s2rt): s2rt
fun s2rt_datakind (k: $Syn.datakind): s2rt
fun s2rt_readize (s2t: s2rt): s2rt
fun s2rt_linearize (s2t: s2rt): s2rt

(* ****** ****** *)

// implemented in [ats_staexp2_util1.dats]
fun s2rt_prf_lin_fc
  (loc0: loc_t, isprf: bool, islin: bool, fc: $Syn.funclo): s2rt
// end of [s2rt_prf_lin_fc]

(* ****** ****** *)

fun fprint_s2rt {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2t: s2rt): void
overload fprint with fprint_s2rt

fun fprint_s2rtlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2ts: s2rtlst): void
overload fprint with fprint_s2rtlst

fun fprint_s2rtlstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2tss: s2rtlstlst): void
overload fprint with fprint_s2rtlstlst

fun fprint_s2rtext {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2te: s2rtext): void
overload fprint with fprint_s2rtext

//

fun print_s2rt (_: s2rt): void
fun prerr_s2rt (_: s2rt): void

overload print with print_s2rt
overload prerr with prerr_s2rt

(* ****** ****** *)

fun lte_s2rt_s2rt (_: s2rt, _: s2rt): bool
overload <= with lte_s2rt_s2rt

fun lte_s2rtlst_s2rtlst (_: s2rtlst, _: s2rtlst): bool
overload <= with lte_s2rtlst_s2rtlst

(* ****** ****** *)

fun s2rt_fun (s2ts: s2rtlst, s2t: s2rt): s2rt
fun s2rt_tup (s2ts: s2rtlst): s2rt

fun un_s2rt_fun (s2t: s2rt): Option_vt @(s2rtlst, s2rt)
fun un_s2rt_tup (s2t: s2rt): Option_vt (s2rtlst)

(* ****** ****** *)
//
// HX: [s2rtdat_t] is assumed in [ats_staexp2.dats]
//
fun s2rtdat_make (id: sym_t): s2rtdat_t

fun s2rtdat_get_sym (s2td: s2rtdat_t): sym_t
fun s2rtdat_get_conlst (s2td: s2rtdat_t): s2cstlst
fun s2rtdat_set_conlst (s2td: s2rtdat_t, s2cs: s2cstlst): void
fun s2rtdat_get_stamp (s2td: s2rtdat_t): stamp_t

fun eq_s2rtdat_s2rtdat (s2td1: s2rtdat_t, s2td2: s2rtdat_t): bool
overload = with eq_s2rtdat_s2rtdat

(* ****** ****** *)
//
// HX: [s2cst_t] is assumed in [ats_staexp2_scst.dats]
//
fun s2cst_make (
  id: sym_t // the name
, loc: loc_t // the location of introduction
, s2t: s2rt // the sort
, isabs: Option (s2expopt)
, iscon: bool
, isrec: bool
, isasp: bool
, islst: Option @(d2con_t (*nil*), d2con_t (*cons*))
, argvar: Option (List @(symopt_t, s2rt, int))
, def: s2expopt
) : s2cst_t

fun s2cst_make_dat (
  id: sym_t
, loc: loc_t // the location of introduction
, os2ts_arg: s2rtlstopt
, s2t_res: s2rt
, argvar: Option (List @(symopt_t, s2rt, int))
) : s2cst_t

fun s2cst_make_cls (
  id: sym_t, loc: loc_t, s2vss: s2varlstlst
) : s2cst_t // end of [s2cst_make_cls]

(* ****** ****** *)

fun s2cst_get_sym (_: s2cst_t): sym_t
fun s2cst_get_loc (_: s2cst_t): loc_t
fun s2cst_get_fil (_: s2cst_t): Option (fil_t)
fun s2cst_set_fil (_: s2cst_t, opt: Option (fil_t)): void
fun s2cst_get_srt (_: s2cst_t): s2rt
fun s2cst_get_isabs (_: s2cst_t): Option (s2expopt)
fun s2cst_get_iscon (_: s2cst_t): bool
fun s2cst_get_isrec (_: s2cst_t): bool
fun s2cst_get_isasp (_: s2cst_t): bool
fun s2cst_set_isasp (_: s2cst_t, _: bool): void
fun s2cst_get_iscpy (_: s2cst_t): s2cstopt
fun s2cst_set_iscpy (_: s2cst_t, _: s2cstopt): void
fun s2cst_get_islst (_: s2cst_t): Option @(d2con_t, d2con_t)
fun s2cst_set_islst (_: s2cst_t, _: Option @(d2con_t, d2con_t)): void
fun s2cst_get_arilst (_: s2cst_t): List int // arity list
fun s2cst_get_argvar (_: s2cst_t): Option (List @(symopt_t, s2rt, int))
fun s2cst_get_conlst (_: s2cst_t): Option d2conlst
fun s2cst_set_conlst (_: s2cst_t, _: Option d2conlst): void
fun s2cst_get_def (_: s2cst_t): s2expopt
fun s2cst_set_def (_: s2cst_t, _: s2expopt): void
//
fun s2cst_get_sup (self: s2cst_t): s2cstlst
fun s2cst_add_sup (self: s2cst_t, sup: s2cst_t): void
fun s2cst_get_supcls (_: s2cst_t): s2explst
fun s2cst_add_supcls (_: s2cst_t, sup: s2exp): void
//
fun s2cst_get_sVarset (_: s2cst_t): s2Varset_t
fun s2cst_set_sVarset (_: s2cst_t, _: s2Varset_t): void
fun s2cst_get_stamp (_: s2cst_t): stamp_t
fun s2cst_set_stamp (_: s2cst_t, _: stamp_t): void
fun s2cst_get_tag (s2c: s2cst_t): int
fun s2cst_set_tag (s2c: s2cst_t, tag: int): void

(* ****** ****** *)

fun lt_s2cst_s2cst (_: s2cst_t, _: s2cst_t):<> bool
overload < with lt_s2cst_s2cst

fun lte_s2cst_s2cst (_: s2cst_t, _: s2cst_t):<> bool
overload <= with lte_s2cst_s2cst

fun eq_s2cst_s2cst (_: s2cst_t, _: s2cst_t):<> bool
overload = with eq_s2cst_s2cst

fun neq_s2cst_s2cst (_: s2cst_t, _: s2cst_t):<> bool
overload <> with eq_s2cst_s2cst

fun compare_s2cst_s2cst (_: s2cst_t, _: s2cst_t):<> Sgn
overload compare with compare_s2cst_s2cst

(* ****** ****** *)

fun s2cst_is_abstract (s2c: s2cst_t): bool
fun s2cst_is_data (s2c: s2cst_t): bool
fun s2cst_is_eqsup (s2c1: s2cst_t, s2c2: s2cst_t): bool
fun s2cst_is_listlike (s2c: s2cst_t): bool
fun s2cst_is_singular (s2c: s2cst_t): bool

(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_scst.dats]
//
fun fprint_s2cst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2c: s2cst_t): void
overload fprint with fprint_s2cst

fun fprint_s2cstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2cs: s2cstlst): void
overload fprint with fprint_s2cstlst

fun print_s2cst (_: s2cst_t): void
fun prerr_s2cst (_: s2cst_t): void

overload print with print_s2cst
overload prerr with prerr_s2cst

fun print_s2cstlst (_: s2cstlst): void
fun prerr_s2cstlst (_: s2cstlst): void

overload print with print_s2cstlst
overload prerr with prerr_s2cstlst

(* ****** ****** *)
//
// HX: [s2var_t] is assumed in [ats_staexp2_svVar.dats]
//
fun s2var_make_srt (s2t: s2rt): s2var_t
fun s2var_make_id_srt (id: sym_t, s2t: s2rt): s2var_t
fun s2var_copy (s2v: s2var_t): s2var_t

(* ****** ****** *)

fun s2var_get_sym (s2v: s2var_t): sym_t
fun s2var_get_srt (s2v: s2var_t): s2rt
fun s2var_get_tmplev (s2v: s2var_t): int
fun s2var_set_tmplev (s2v: s2var_t, lev: int): void
fun s2var_get_sVarset (_: s2var_t): s2Varset_t
fun s2var_set_sVarset (_: s2var_t, _: s2Varset_t): void
fun s2varlst_set_sVarset (_: s2varlst, _: s2Varset_t): void
fun s2var_get_stamp (s2v: s2var_t): stamp_t

(* ****** ****** *)

fun lt_s2var_s2var (_: s2var_t, _: s2var_t):<> bool
overload < with lt_s2var_s2var

fun lte_s2var_s2var (_: s2var_t, _: s2var_t):<> bool
overload <= with lte_s2var_s2var

fun eq_s2var_s2var (_: s2var_t, _: s2var_t):<> bool
overload = with eq_s2var_s2var

fun neq_s2var_s2var (_: s2var_t, _: s2var_t):<> bool
overload <> with eq_s2var_s2var

fun compare_s2var_s2var (_: s2var_t, _: s2var_t):<> Sgn
overload compare with compare_s2var_s2var

(* ****** ****** *)

fun s2var_is_boxed (s2v: s2var_t): bool
fun s2var_is_unboxed (s2v: s2var_t): bool

(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_dcon.dats]
//
fun fprint_s2var {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2v: s2var_t): void
overload fprint with fprint_s2var

fun fprint_s2varlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2vs: s2varlst): void
overload fprint with fprint_s2varlst

fun print_s2var (_: s2var_t): void
fun prerr_s2var (_: s2var_t): void

overload print with print_s2var
overload prerr with prerr_s2var

fun print_s2varlst (_: s2varlst): void
fun prerr_s2varlst (_: s2varlst): void

overload print with print_s2varlst
overload prerr with prerr_s2varlst

(* ****** ****** *)

val s2varset_nil : s2varset_t

fun fprint_s2varset {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, svs: s2varset_t): void
overload fprint with fprint_s2varset

fun s2varset_add (_: s2varset_t, _: s2var_t): s2varset_t
fun s2varset_adds (svs: s2varset_t, s2vs: s2varlst): s2varset_t
fun s2varset_del (svs: s2varset_t, s2v: s2var_t): s2varset_t
fun s2varset_dels (svs: s2varset_t, s2vs: s2varlst): s2varset_t
fun s2varset_union (svs1: s2varset_t, svs2: s2varset_t): s2varset_t

fun s2varset_ismem (svs: s2varset_t, s2v: s2var_t): bool

(* ****** ****** *)
//
// HX: [s2Var_t] is assumed in [ats_staexp2_svVar.dats]
//
fun s2Var_make_srt (_: loc_t, s2t: s2rt): s2Var_t
fun s2Var_make_var (_: loc_t, s2v: s2var_t): s2Var_t

(* ****** ****** *)

fun s2Var_get_loc (_: s2Var_t): loc_t
fun s2Var_get_cnt (_: s2Var_t): count_t
fun s2Var_get_srt (_: s2Var_t): s2rt
fun s2Var_set_srt (_: s2Var_t, _: s2rt): void
fun s2Var_get_link (_: s2Var_t): Option s2exp
fun s2Var_set_link (_: s2Var_t, _: s2expopt): void
fun s2Var_get_svar (_: s2Var_t): Option s2var_t
//
fun s2Var_get_lbs (_: s2Var_t): s2Varboundlst
fun s2Var_set_lbs (_: s2Var_t, lbs: s2Varboundlst): void
fun s2Var_get_ubs (_: s2Var_t): s2Varboundlst
fun s2Var_set_ubs (_: s2Var_t, ubs: s2Varboundlst): void
//
fun s2Var_get_sVarset (_: s2Var_t): s2Varset_t
fun s2Var_set_sVarset (_: s2Var_t, sVs: s2Varset_t): void
fun s2Var_get_stamp (_: s2Var_t): stamp_t

(* ****** ****** *)

fun s2Varbound_make (loc: loc_t, s2e: s2exp): s2Varbound_t
fun s2Varbound_get_loc (s2Vb: s2Varbound_t): loc_t
fun s2Varbound_get_val (s2Vb: s2Varbound_t): s2exp

(* ****** ****** *)

fun lt_s2Var_s2Var (_: s2Var_t, _: s2Var_t): bool
overload < with lt_s2Var_s2Var

fun lte_s2Var_s2Var (_: s2Var_t, _: s2Var_t): bool
overload <= with lte_s2Var_s2Var

fun eq_s2Var_s2Var (_: s2Var_t, _: s2Var_t): bool
overload = with eq_s2Var_s2Var

fun neq_s2Var_s2Var (_: s2Var_t, _: s2Var_t): bool
overload <> with eq_s2Var_s2Var

fun compare_s2Var_s2Var (_: s2Var_t, _: s2Var_t): Sgn
overload compare with compare_s2Var_s2Var

(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_dcon.dats]
//
fun fprint_s2Var {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2V: s2Var_t): void
overload fprint with fprint_s2Var

fun fprint_s2Varlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2Vs: s2Varlst): void
overload fprint with fprint_s2Varlst

fun print_s2Var (_: s2Var_t): void
fun prerr_s2Var (_: s2Var_t): void

overload print with print_s2Var
overload prerr with prerr_s2Var

fun print_s2Varlst (_: s2Varlst): void
fun prerr_s2Varlst (_: s2Varlst): void

overload print with print_s2Varlst
overload prerr with prerr_s2Varlst

(* ****** ****** *)

val s2Varset_nil : s2Varset_t

fun fprint_s2Varset {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, sVs: s2Varset_t): void
overload fprint with fprint_s2Varset

fun s2Varset_add (sVs: s2Varset_t, s2V: s2Var_t): s2Varset_t
fun s2Varset_adds (sVs: s2Varset_t, s2Vs: s2Varlst): s2Varset_t
fun s2Varset_del (sVs: s2Varset_t, s2V: s2Var_t): s2Varset_t
fun s2Varset_dels (sVs: s2Varset_t, s2Vs: s2Varlst): s2Varset_t
fun s2Varset_union (sVs1: s2Varset_t, sVs2: s2Varset_t): s2Varset_t

fun s2Varset_ismem (sVs: s2Varset_t, s2V: s2Var_t): bool

(* ****** ****** *)

fun s2qualst_reverse (xs: s2qualst): s2qualst

fun fprint_s2qua {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2q: s2qua): void

fun fprint_s2qualst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2qs: s2qualst): void

fun print_s2qualst (s2qs: s2qualst): void
fun prerr_s2qualst (s2qs: s2qualst): void

(* ****** ****** *)
//
// HX: [d2con_t] is assumed in [ats_staexp2_dcon.dats]
//
fun d2con_make (
  loc: loc_t // location
, fil: fil_t // filename
, id: sym_t // the name
, s2c: s2cst_t // the type constructor
, vwtp: int
, qua: s2qualst
, npf: int // pfarity
, arg: s2explst // arguments
, ind: s2explstopt // indexes
) : d2con_t

(* ****** ****** *)

fun d2con_make_list_nil (): d2con_t
fun d2con_make_list_cons (): d2con_t

(* ****** ****** *)

fun d2con_get_fil (_: d2con_t): fil_t
fun d2con_get_sym (_: d2con_t): sym_t
fun d2con_get_scst (_: d2con_t): s2cst_t
fun d2con_get_vwtp (_: d2con_t): int
fun d2con_get_qua (_: d2con_t): s2qualst
fun d2con_get_npf (_: d2con_t): int
fun d2con_get_arg (_: d2con_t): s2explst
fun d2con_get_arity_full (_: d2con_t): int
fun d2con_get_arity_real (_: d2con_t): int
fun d2con_get_ind (_: d2con_t): s2explstopt
fun d2con_get_typ (_: d2con_t): s2exp
fun d2con_get_tag (_: d2con_t): int
fun d2con_set_tag (_: d2con_t, _: int): void
fun d2con_get_stamp (_: d2con_t): stamp_t

(* ****** ****** *)

fun lt_d2con_d2con (_: d2con_t, _: d2con_t): bool
overload < with lt_d2con_d2con

fun lte_d2con_d2con (_: d2con_t, _: d2con_t): bool
overload <= with lte_d2con_d2con

fun eq_d2con_d2con (_: d2con_t, _: d2con_t): bool
overload = with eq_d2con_d2con

fun neq_d2con_d2con (_: d2con_t, _: d2con_t): bool
overload <> with neq_d2con_d2con

fun compare_d2con_d2con (_: d2con_t, _: d2con_t):<> Sgn
overload compare with compare_d2con_d2con

(* ****** ****** *)

fun d2con_is_exn (d2c: d2con_t): bool // exn constructor
fun d2con_is_msg (d2c: d2con_t): bool // msg constructor
fun d2con_is_proof (d2c: d2con_t): bool // proof constructor

(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_dcon.dats]
//
fun fprint_d2con {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2c: d2con_t): void

and fprint_d2conlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2cs: d2conlst): void

overload fprint with fprint_d2con
overload fprint with fprint_d2conlst

fun print_d2con (_: d2con_t): void
fun prerr_d2con (_: d2con_t): void

overload print with print_d2con
overload prerr with prerr_d2con

fun print_d2conlst (_: d2conlst): void
fun prerr_d2conlst (_: d2conlst): void

overload print with print_d2conlst
overload prerr with prerr_d2conlst

(* ****** ****** *)

fun fprint_s2item {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2i: s2item): void
overload fprint with fprint_s2item

fun print_s2item (s2i: s2item): void
fun prerr_s2item (s2i: s2item): void

overload print with print_s2item
overload prerr with prerr_s2item

(* ****** ****** *)

fun s2arg_make (_: loc_t, id: sym_t, res: s2rtopt): s2arg

(* ****** ****** *)

fun fprint_s2eff {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2fe: s2eff): void
overload fprint with fprint_s2eff

fun print_s2eff (s2fe: s2eff): void
fun prerr_s2eff (s2fe: s2eff): void

overload print with print_s2eff
overload prerr with prerr_s2eff

(* ****** ****** *)

fun s2eff_union_eff (_: s2eff, _: $Syn.effect_t): s2eff
fun s2eff_union_s2eff (_: s2eff, _: s2eff): s2eff

fun s2eff_contain_eff (_: s2eff, _: $Syn.effect_t): bool
fun s2eff_contain_effset (_: s2eff, _: $Eff.effset_t): bool
fun s2eff_contain_effvar (_: s2eff, _: s2var_t): bool
fun s2eff_contain_s2eff (_: s2eff, _: s2eff): bool

(* ****** ****** *)

fun s2lab_syneq (_: s2lab, _: s2lab): bool
fun s2lablst_trim_s2lablst_s2lablst
  (_: s2lablst, _: s2lablst, _: s2lablst): s2lablst

(* ****** ****** *)

fun fprint_s2lab {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2l: s2lab): void
overload fprint with fprint_s2lab

fun print_s2lab (s2l: s2lab): void
fun prerr_s2lab (s2l: s2lab): void

fun fprint_s2lablst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2ls: s2lablst): void
overload fprint with fprint_s2lablst

fun print_s2lablst (s2ls: s2lablst): void
fun prerr_s2lablst (s2ls: s2lablst): void

(* ****** ****** *)

fun fprint_s2kexp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2ke: s2kexp): void
overload fprint with fprint_s2kexp

fun fprint_s2kexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2kes: s2kexplst): void
overload fprint with fprint_s2kexplst

fun fprint_labs2kexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ls2kes: labs2kexplst): void
overload fprint with fprint_labs2kexplst


fun print_s2kexp (s2ke: s2kexp): void
overload print with print_s2kexp
fun prerr_s2kexp (s2ke: s2kexp): void
overload prerr with prerr_s2kexp

(* ****** ****** *)

fun fprint_s2zexp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2ze: s2zexp): void
fun print_s2zexp (s2ze: s2zexp): void
fun prerr_s2zexp (s2ze: s2zexp): void

fun fprint_s2zexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2zes: s2zexplst): void

fun fprint_labs2zexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ls2zes: labs2zexplst): void

(* ****** ****** *)

fun s2exp_is_proof (s2e: s2exp): bool
fun s2exp_is_proof_fun (s2e: s2exp): bool
fun s2exp_is_linear (s2e: s2exp): bool
fun s2exp_is_nonlin (s2e: s2exp): bool
fun s2exp_is_impredicative (s2e: s2exp): bool
fun s2exp_is_types (s2e: s2exp): bool

fun s2exp_is_abscon (s2e: s2exp): bool

fun s2exp_is_non_fun (s2e: s2exp): bool
fun s2exp_is_non_tyrec (s2e: s2exp): bool

fun s2exp_is_wth (s2e: s2exp): bool

(* ****** ****** *)

fun s2exp_set_srt
  (s2e: s2exp, s2t: s2rt): void = "atsopt_s2exp_set_srt"
// end of [s2exp_set_srt]

(* ****** ****** *)

fun fprint_s2exp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2e: s2exp): void
overload fprint with fprint_s2exp

fun fprint_s2explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2es: s2explst): void
overload fprint with fprint_s2explst

fun fprint_s2explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2ess: s2explstlst): void
overload fprint with fprint_s2explstlst

fun fprint_s2expopt {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2es: s2expopt): void
overload fprint with fprint_s2expopt

fun print_s2exp (s2e: s2exp): void
fun prerr_s2exp (s2e: s2exp): void

overload print with print_s2exp
overload prerr with prerr_s2exp

fun print_s2explst (s2es: s2explst): void
fun prerr_s2explst (s2es: s2explst): void

overload print with print_s2explst
overload prerr with prerr_s2explst

fun print_labs2explst (ls2es: labs2explst): void
fun prerr_labs2explst (ls2es: labs2explst): void

overload print with print_labs2explst
overload prerr with prerr_labs2explst

(* ****** ****** *)

fun fprint_labs2explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ls2es: labs2explst): void
overload fprint with fprint_labs2explst

(* ****** ****** *)

fun fprint_tmps2explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ts2ess: tmps2explstlst): void
overload fprint with fprint_tmps2explstlst

fun print_tmps2explstlst (ts2ess: tmps2explstlst): void
fun prerr_tmps2explstlst (ts2ess: tmps2explstlst): void

(* ****** ****** *)

fun fprint_wths2explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, wths2es: wths2explst): void
overload fprint with fprint_wths2explst

fun print_wths2explst (wths2es: wths2explst): void
fun prerr_wths2explst (wths2es: wths2explst): void

(* ****** ****** *)

fun fprint_s2exparg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2a: s2exparg): void
overload fprint with fprint_s2exparg

fun fprint_s2exparglst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2as: s2exparglst): void
overload fprint with fprint_s2exparglst

fun print_s2exparglst (s2as: s2exparglst): void
fun prerr_s2exparglst (s2as: s2exparglst): void

overload print with print_s2exparglst
overload prerr with prerr_s2exparglst

(* ****** ****** *)

fun sp2at_con (loc: loc_t, s2c: s2cst_t, s2vs: s2varlst): sp2at

(* ****** ****** *)

fun s2exp_app_srt
  (s2t: s2rt, s2e_fun: s2exp, s2es_arg: s2explst): s2exp
fun s2exp_app_wind (s2e_fun: s2exp, s2ess_arg: s2explstlst): s2exp
fun s2exp_char (chr: char): s2exp
fun s2exp_clo_srt (s2t: s2rt, knd: int, s2e: s2exp): s2exp
fun s2exp_confun (npf: int, s2es: s2explst, s2e: s2exp): s2exp
fun s2exp_crypt (s2e: s2exp): s2exp
fun s2exp_cst (s2c: s2cst_t): s2exp
fun s2exp_cstapp (s2c: s2cst_t, s2es: s2explst): s2exp
fun s2exp_datconptr (d2c: d2con_t, s2es: s2explst): s2exp
fun s2exp_datcontyp (d2c: d2con_t, s2es: s2explst): s2exp
fun s2exp_eff (s2fe: s2eff): s2exp
fun s2exp_eqeq (s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_exi (s2vs: s2varlst, s2ps: s2explst, s2e: s2exp): s2exp

fun s2exp_extype_srt
  (s2t: s2rt, name: string, arglst: s2explstlst): s2exp
// end of [s2exp_extype_srt]

fun s2exp_fun_srt (
  s2t: s2rt
, fc: $Syn.funclo, lin: int, s2fe: s2eff, npf: int
, s2es_arg: s2explst, s2e_res: s2exp
) : s2exp // end of [s2exp_fun_srt]

fun s2exp_int (i: int): s2exp
val s2exp_int_0 : s2exp and s2exp_int_1 : s2exp
fun s2exp_intinf (i: intinf_t): s2exp

fun s2exp_lam_srt (s2t: s2rt, s2vs: s2varlst, s2e: s2exp): s2exp
fun s2exp_metfn
  (d2vopt: Option stamp_t, met: s2explst, s2e_fun: s2exp): s2exp
fun s2exp_metlt {n:nat} (met1: s2explst n, met2: s2explst n): s2exp

(*
// HX-2010-12-04: inadequate design
fun s2exp_named (s2t: s2rt, name: sym_t, s2e: s2exp): s2exp
*)

fun s2exp_out (s2e: s2exp): s2exp
fun s2exp_proj (ptr: s2exp, lab: s2lab): s2exp

fun s2exp_read (s2e_v: s2exp, s2e_vt: s2exp): s2exp
fun s2exp_read_srt (s2t: s2rt, s2e_v: s2exp, s2e_vt: s2exp): s2exp
fun un_s2exp_read (s2e: s2exp): Option_vt @(s2exp, s2exp)

fun s2exp_refarg (refval: int, s2e: s2exp): s2exp
fun un_s2exp_refarg_arg (s2e: s2exp): s2exp

fun s2exp_sel_srt (s2t: s2rt, s2e: s2exp, i: int): s2exp
fun s2exp_size (s2ze: s2zexp): s2exp
fun s2exp_sizeof (s2e: s2exp): s2exp

fun s2exp_top_srt (s2t: s2rt, knd: int, s2e: s2exp): s2exp
fun s2exp_tup_srt (s2t: s2rt, s2es: s2explst): s2exp
fun s2exp_tyarr (elt: s2exp, dim: s2explstlst): s2exp
fun s2exp_tyleq (knd: int, s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_tylst (s2es: s2explst): s2exp
fun s2exp_tyrec (recknd: int, npf: int, ls2es: labs2explst): s2exp
fun s2exp_tyrec_srt
  (s2t: s2rt, k: tyreckind, npf: int, ls2es: labs2explst): s2exp
fun s2exp_uni (s2vs: s2varlst, s2ps: s2explst, s2e: s2exp): s2exp
fun s2exp_union
  (isbox: bool, stamp: stamp_t, s2i: s2exp, ls2es: labs2explst): s2exp
fun s2exp_union_srt
  (s2t: s2rt, stamp: stamp_t, s2i: s2exp, ls2es: labs2explst): s2exp
fun s2exp_var (s2v: s2var_t): s2exp
fun s2exp_vararg (arg: s2exp): s2exp
fun s2exp_Var (s2V: s2Var_t): s2exp
fun s2exp_wth (_res: s2exp, _with: wths2explst): s2exp

(* ****** ****** *)

fun s2exparg_one (loc: loc_t): s2exparg
fun s2exparg_all (loc: loc_t): s2exparg
fun s2exparg_seq (loc: loc_t, s2es: s2explst): s2exparg

(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_util1.dats]
//
fun s2exp_get_head (_: s2exp): s2exp

fun s2cst_select_s2explstlst (_: s2cstlst, _: s2explstlst): s2cstlst

fun s2rt_lin_prg_boxed (lin: int, prg: int, boxed: int): s2rt
fun s2rt_lin_prg_boxed_npf_labs2explst
  (lin: int, prg: int, boxed: int, npf: int, ls2es: labs2explst): s2rt
// end of [s2rt_lin_prg_boxed_npf_labs2explst]

(* ****** ****** *)

fun s2kexp_make_s2exp (s2e: s2exp): s2kexp

fun s2kexp_match_approx
  (pol: int, _: s2kexp, _: s2kexp, approx: &int): bool

fun s2kexplst_match_approx
  (pol: int, _: s2kexplst, _: s2kexplst, approx: &int): bool
// end of [s2kexplst_match_approx]

fun labs2kexplst_match_approx
  (pol: int, _: labs2kexplst, _: labs2kexplst, approx: &int): bool
// end of [labs2kexplst_match_approx]

fun s2kexp_match_fun_arg
  (s2ke_fun: s2kexp, s2kes_arg: s2kexplst): Option_vt @(s2kexp, int)
// end of [s2kexp_match_fun_arg]

(* ****** ****** *)

// substitution functions

abstype stasub_t // boxed type

val stasub_nil : stasub_t
fun stasub_add (_: stasub_t, _: s2var_t, _: s2exp): stasub_t
fun stasub_addlst (_: stasub_t, _: s2varlst, _: s2explst): stasub_t

fun stasub_get_domain (_: stasub_t): s2varlst
fun stasub_get_codomain_whnf (_: stasub_t): s2explst

fun stasub_extend_svarlst
  (sub: stasub_t, s2vs: s2varlst): @(stasub_t, s2varlst)

fun stasub_extend_sarglst_svarlst
  (loc0: loc_t, sub: stasub_t, s2as: s2arglst, s2vs: s2varlst)
  : @(stasub_t, s2varlst)

fun s2exp_subst (sub: stasub_t, s2e: s2exp): s2exp
fun s2explst_subst {n:nat} (sub: stasub_t, s2es: s2explst n): s2explst n
fun s2expopt_subst (sub: stasub_t, os2e: s2expopt): s2expopt

fun s2explstlst_subst (_: stasub_t, _: s2explstlst): s2explstlst

(* ****** ****** *)

fun s2exp_alpha 
  (s2v: s2var_t, s2v1: s2var_t, s2e: s2exp): s2exp
// end of [s2exp_alpha]

fun s2explst_alpha
  (s2v: s2var_t, s2v1: s2var_t, s2es: s2explst): s2explst
// end of [s2explst_alpha]

(* ****** ****** *)

fun s2exp_freevars (_: s2exp): s2varset_t
fun s2Var_s2exp_occurs
  (_: s2Var_t, _: s2exp, _: &s2cstlst, _: &s2varlst): int
fun s2exp_link_remove (root: s2exp): s2exp

(* ****** ****** *)

fun eqref_s2exp_s2exp
  (s2e1: s2exp, s2e2: s2exp): bool
  = "atsopt_eqref_s2exp_s2exp"
// end of [eqref_s2exp_s2exp]

fun s2exp_syneq (_: s2exp, _: s2exp): bool
fun s2explst_syneq (_: s2explst, _: s2explst): bool
fun s2explstlst_syneq (_: s2explstlst, _: s2explstlst): bool
fun s2zexp_syneq (_: s2zexp, _: s2zexp): bool
fun s2zexp_make_s2exp (_: s2exp): s2zexp

fun s2exp_projlst (_root: s2exp, _path: s2lablst): s2exp
fun s2exp_addr_normalize (_: s2exp): @(s2exp, s2lablst)

fun s2exp_readize (_v: s2exp, _vt: s2exp): s2exp
fun s2expopt_readize (_v: s2exp, _vt: s2expopt): s2expopt

fun s2exp_topize (knd: int, s2e: s2exp): s2exp
fun s2exp_topize_0 (s2e: s2exp): s2exp // = s2exp_topize (0, s2e)
fun s2exp_topize_1 (s2e: s2exp): s2exp // = s2exp_topize (1, s2e)

(* ****** ****** *)
//
// HX: weak-head normalization
//
fun s2exp_whnf (s2e: s2exp): s2exp
fun s2explst_whnf {n:nat} (s2es: s2explst n): s2explst n
//
(* ****** ****** *)
//
// HX: application normalization
//
fun s2exp_nfapp (s2e: s2exp): s2exp
fun s2explst_nfapp {n:nat} (s2es: s2explst n): s2explst n
//
(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_util2.dats]
//
fun s2exp_absuni (s2e: s2exp): @(s2varlst, s2explst, s2exp)
fun s2exp_opnexi (s2e: s2exp): @(s2varlst, s2explst, s2exp)
fun s2explst_opnexi (s2es: s2explst): @(s2varlst, s2explst, s2explst)
//
(* ****** ****** *)
//
// HX: implemented in [ats_staexp2_util2.dats]
//
fun labs2explst_get_lab
  (_: labs2explst, l0: lab_t): s2expopt_vt
fun labs2explst_set_lab
  (_: labs2explst, l0: lab_t, s2e0: s2exp): Option_vt labs2explst
// end of [labs2explst_set_lab]

fun labs2zexplst_get_lab (_: labs2zexplst, l0: lab_t): s2zexpopt_vt

fun s2exp_get_lab_restlin_cstr
  (loc0: loc_t, s2e0: s2exp, l0: lab_t, restlin: &int, cstr: &s2explst): s2exp

fun s2exp_get_slablst_restlin_cstr {n:nat}
  (loc0: loc_t, s2e0: s2exp, s2ls: list (s2lab, n), restlin: &int, cstr: &s2explst)
  : @(s2exp, list (s2lab, n))
// end of [s2exp_get_slablst_restlin_cstr]

fun s2exp_linget_lab_cstr
  (loc0: loc_t, s2e0: s2exp, l0: lab_t, cstr: &s2explst): s2exp(*result*)
// end of [s2exp_linget_lab_cstr]

fun s2exp_linget_ind_cstr
  (loc0: loc_t, s2e_arr: s2exp, s2ess_ind: s2explstlst, cstr: &s2explst)
  : s2exp(*element*)
// end of [s2exp_linget_ind_cstr]

fun s2exp_linget_slab_cstr
  (loc0: loc_t, s2e0: s2exp, s2l: s2lab, cstr: &s2explst)
  : @(s2exp(*result*), s2lab(*updated label*))
// end of [s2exp_linget_slab_cstr]

fun s2exp_linset_lab
  (loc0: loc_t, s2e0: s2exp, l0: lab_t, s2e_new: s2exp): s2exp
// end of [s2exp_linset_lab]

(* ****** ****** *)

fun s2exp_lintry_slablst_cstr {n:nat}
  (loc0: loc_t, s2e0: s2exp, s2ls: list (s2lab, n), cstr: &s2explst)
  : list (s2lab, n)
// end of [s2exp_lintry_slablst_cstr]

fun s2exp_linget_slablst_cstr {n:nat}
  (loc0: loc_t, s2e0: s2exp, s2ls: list (s2lab, n), cstr: &s2explst)
  : @(s2exp(*part*), s2exp(*whole*), list (s2lab, n))
// end of [s2exp_linget_slablst_cstr]

fun s2exp_linset_slablst_cstr {n:nat}
  (loc0: loc_t, s2e0: s2exp, s2ls: list (s2lab, n), s2e_new: s2exp, cstr: &s2explst)
  : @(s2exp(*part*), s2exp(*whole*), list (s2lab, n))
// end of [s2exp_linset_slablst_cstr]

fun s2exp_lindel_slablst_cstr {n:nat}
  (loc0: loc_t, s2e0: s2exp, s2ls: list (s2lab, n), cstr: &s2explst)
  : @(s2exp(*part*), s2exp(*whole*), list (s2lab, n))
// end of [s2exp_lindel_slablst_cstr]

(* ****** ****** *)
//
// HX-2010-04-07:
// this functions yields a definite answer
// if both [s2e1] and [s2e2] are constants
//
// positive:  1
// negative: ~1
// undecided: 0
//
fun s2exp_subclass_test (s2e1: s2exp, s2e2: s2exp): Sgn

(* ****** ****** *)

(* end of [ats_staexp2.sats] *)
