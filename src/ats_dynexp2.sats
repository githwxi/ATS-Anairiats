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

(* The second translation resolves binding as well as sort assignment *)

(* ****** ****** *)

staload Fil = "ats_filename.sats"
typedef fil_t = $Fil.filename_t

staload Lab = "ats_label.sats"
typedef lab_t = $Lab.label_t

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

staload IntInf = "ats_intinf.sats"
typedef intinf_t = $IntInf.intinf_t

staload SEXP1 = "ats_staexp1.sats" // for [e1xp]
typedef e1xp = $SEXP1.e1xp

staload Stamp = "ats_stamp.sats"
typedef stamp_t = $Stamp.stamp_t

staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

staload SymEnv = "ats_symenv.sats"
stadef symmapref = $SymEnv.symmapref

staload Syn = "ats_syntax.sats"
typedef dcstextdef = $Syn.dcstextdef

(* ****** ****** *)

staload Syn = "ats_syntax.sats"
typedef l0ab = $Syn.l0ab
typedef d0ynq = $Syn.d0ynq
typedef dqi0de = $Syn.dqi0de
typedef sqi0de = $Syn.sqi0de
typedef i0delstlst = $Syn.i0delstlst
typedef dcstkind = $Syn.dcstkind
typedef funkind = $Syn.funkind
typedef intkind = $Syn.intkind
typedef valkind = $Syn.valkind

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

abstype d2cst_t // boxed type
abstype d2mac_abs_t (int(*curry arity*))// boxed type
abstype d2var_t // boxed type
abstype d2varset_t // boxed type

typedef d2mac_t (narg:int) = d2mac_abs_t (narg)
typedef d2mac_t = [narg:nat] d2mac_abs_t (narg)

typedef d2cstlst = List d2cst_t
datatype d2cstopt = D2CSTOPTsome of d2cst_t | D2CSTOPTnone

typedef d2varlst (n:int) = list (d2var_t, n)
typedef d2varlst = [n:nat] d2varlst n

viewtypedef d2varlst_vt (n:int) = list_vt (d2var_t, n)
viewtypedef d2varlst_vt = [n:nat] d2varlst_vt n

datatype d2varopt = D2VAROPTsome of d2var_t | D2VAROPTnone

(* ****** ****** *)

abstype s2varlstord_t
abstype d2varlstord_t

fun s2varlst_of_s2varlstord (_: s2varlstord_t): s2varlst
fun d2varlst_of_d2varlstord (_: d2varlstord_t): d2varlst

(* ****** ****** *)

datatype d2item =
  | D2ITEMcon of d2conlst
  | D2ITEMcst of d2cst_t
  | D2ITEMe1xp of e1xp
  | D2ITEMmacdef of d2mac_t
  | D2ITEMmacvar of d2var_t
  | D2ITEMsymdef of List d2item (* overloaded symbol *)
  | D2ITEMvar of d2var_t
// end of [d2item]

typedef d2itemlst = List d2item
viewtypedef d2itemopt_vt = Option_vt d2item

(* ****** ****** *)

typedef d2sym = '{
  d2sym_loc= loc_t
, d2sym_qua= $Syn.d0ynq, d2sym_sym= sym_t
, d2sym_itm= d2itemlst
} // end of [d2sym]

fun fprint_d2sym {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2s: d2sym): void
overload fprint with fprint_d2sym

fun print_d2sym (_: d2sym): void
overload print with print_d2sym

fun prerr_d2sym (_: d2sym): void
overload prerr with prerr_d2sym

(* ****** ****** *)

fun d2cst_make (
  id: sym_t
, fil: fil_t
, loc: loc_t
, dck: $Syn.dcstkind
, decarg: s2qualst
, arilst: List int
, typ: s2exp
, extdef: dcstextdef
) : d2cst_t

(* ****** ****** *)

fun d2cst_get_loc (_: d2cst_t): loc_t
fun d2cst_get_fil (_: d2cst_t): fil_t
fun d2cst_get_sym (_: d2cst_t): sym_t
fun d2cst_get_name (_: d2cst_t): string
fun d2cst_get_kind (_: d2cst_t): $Syn.dcstkind
fun d2cst_get_arilst (_: d2cst_t): List int
fun d2cst_get_decarg (_: d2cst_t): s2qualst
fun d2cst_set_decarg (_: d2cst_t, _: s2qualst): void
fun d2cst_get_typ (_: d2cst_t): s2exp
fun d2cst_get_extdef (_: d2cst_t): dcstextdef
fun d2cst_get_stamp (_: d2cst_t): stamp_t

(* ****** ****** *)

fun lt_d2cst_d2cst (_: d2cst_t, _: d2cst_t):<> bool
overload < with lt_d2cst_d2cst

fun lte_d2cst_d2cst (_: d2cst_t, _: d2cst_t):<> bool
overload <= with lte_d2cst_d2cst

fun eq_d2cst_d2cst (_: d2cst_t, _: d2cst_t):<> bool
overload = with eq_d2cst_d2cst

fun neq_d2cst_d2cst (_: d2cst_t, _: d2cst_t):<> bool
overload <> with eq_d2cst_d2cst

fun compare_d2cst_d2cst (_: d2cst_t, _: d2cst_t):<> Sgn
overload compare with compare_d2cst_d2cst

(* ****** ****** *)

fun d2cst_is_fun (d2c: d2cst_t):<> bool
fun d2cst_is_castfn (d2c: d2cst_t):<> bool
fun d2cst_is_extmac (d2c: d2cst_t):<> bool
fun d2cst_is_extsta (d2c: d2cst_t):<> bool
fun d2cst_is_praxi (d2c: d2cst_t):<> bool
fun d2cst_is_prfun (d2c: d2cst_t):<> bool
fun d2cst_is_prval (d2c: d2cst_t):<> bool
fun d2cst_is_proof (d2c: d2cst_t):<> bool
fun d2cst_is_temp (d2c: d2cst_t):<> bool

(* ****** ****** *)
//
// HX: implemented in [ats_dynexp2_dcst.dats]
//
fun fprint_d2cst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2c: d2cst_t): void
overload fprint with fprint_d2cst

fun fprint_d2cstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2cs: d2cstlst): void
overload fprint with fprint_d2cstlst

fun print_d2cst (_: d2cst_t): void
fun prerr_d2cst (_: d2cst_t): void

overload print with print_d2cst
overload prerr with prerr_d2cst

fun print_d2cstlst (_: d2cstlst): void
fun prerr_d2cstlst (_: d2cstlst): void

overload print with print_d2cstlst
overload prerr with prerr_d2cstlst

(* ****** ****** *)

fun fprint_d2mac {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2m: d2mac_t): void
overload fprint with fprint_d2mac

fun print_d2mac (_: d2mac_t): void
fun prerr_d2mac (_: d2mac_t): void

overload print with print_d2mac
overload prerr with prerr_d2mac

(* ****** ****** *)

fun d2var_make (_: loc_t, id: sym_t): d2var_t
fun d2var_make_any (_: loc_t): d2var_t // for wildcard pattern

(* ****** ****** *)

datatype d2var_fin =
  | D2VARFINdone
  | D2VARFINnone
  | D2VARFINsome of s2exp
  | D2VARFINvbox of s2exp
// end of [d2var_fin]

(* ****** ****** *)

fun d2var_get_loc (_: d2var_t): loc_t
fun d2var_get_sym (_: d2var_t): sym_t
fun d2var_get_isfix (_: d2var_t): bool
fun d2var_set_isfix (_: d2var_t, _: bool): void
fun d2var_get_isprf (_: d2var_t): bool
fun d2var_set_isprf (_: d2var_t, _: bool): void
fun d2var_get_lev (_: d2var_t): int
fun d2var_set_lev (_: d2var_t, _: int): void
fun d2var_get_lin (_: d2var_t): int
fun d2var_inc_lin (_: d2var_t): void
fun d2var_set_lin (_: d2var_t, _: int): void
fun d2var_get_decarg (_: d2var_t): s2qualst
fun d2var_set_decarg (_: d2var_t, _: s2qualst): void
fun d2var_get_addr (_: d2var_t): s2expopt
fun d2var_set_addr (_: d2var_t, _: s2expopt): void
fun d2var_get_view (_: d2var_t): d2varopt
fun d2var_set_view (_: d2var_t, _: d2varopt): void
fun d2var_get_fin (_: d2var_t): d2var_fin
fun d2var_set_fin (_: d2var_t, _: d2var_fin): void
fun d2var_get_typ (_: d2var_t): s2expopt
fun d2var_set_typ (_: d2var_t, _: s2expopt): void
fun d2var_get_mastyp (_: d2var_t): s2expopt
fun d2var_set_mastyp (_: d2var_t, _: s2expopt): void
fun d2var_get_count (_: d2var_t): int
fun d2var_inc_count (_: d2var_t): void
fun d2var_get_stamp (_: d2var_t): stamp_t

fun d2var_get_typ_some (_: loc_t, _: d2var_t): s2exp
fun d2var_get_mastyp_some (_: loc_t, _: d2var_t): s2exp
fun d2var_get_addr_some (_: loc_t, _: d2var_t): s2exp
fun d2var_get_view_some (_: loc_t, _: d2var_t): d2var_t

(* ****** ****** *)

fun lt_d2var_d2var (_: d2var_t, _: d2var_t):<> bool
overload < with lt_d2var_d2var

fun lte_d2var_d2var (_: d2var_t, _: d2var_t):<> bool
overload <= with lte_d2var_d2var

fun eq_d2var_d2var (_: d2var_t, _: d2var_t):<> bool
overload = with eq_d2var_d2var

fun neq_d2var_d2var (_: d2var_t, _: d2var_t):<> bool
overload <> with eq_d2var_d2var

fun compare_d2var_d2var (_: d2var_t, _: d2var_t):<> Sgn
overload compare with compare_d2var_d2var

(* ****** ****** *)
//
// HX: implemented in [ats_dynexp2_dvar.dats]
//
fun fprint_d2var {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2c: d2var_t): void
overload fprint with fprint_d2var

fun fprint_d2varlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2cs: d2varlst): void
overload fprint with fprint_d2varlst

fun print_d2var (_: d2var_t): void
fun prerr_d2var (_: d2var_t): void

overload print with print_d2var
overload prerr with prerr_d2var

fun print_d2varlst (_: d2varlst): void
fun prerr_d2varlst (_: d2varlst): void

overload print with print_d2varlst
overload prerr with prerr_d2varlst

(* ****** ****** *)

fun d2var_is_linear (d2v: d2var_t): bool
fun d2var_is_mutable (d2v: d2var_t): bool

fun d2var_reset_typ
  (d2v: d2var_t, s2e: s2exp): void

fun d2var_reset_typ_at
  (d2v: d2var_t, s2e: s2exp, s2l: s2exp): void

fun d2var_ptr_viewat_make
  (d2v_ptr: d2var_t, od2v_view: d2varopt): d2var_t

fun d2var_ptr_viewat_make_none (d2v_ptr: d2var_t): d2var_t

(* ****** ****** *)

fun d2var_readize (s2e_v: s2exp, d2v: d2var_t): void
fun d2varlst_readize (s2e_v: s2exp, d2v: d2varlst): void

(* ****** ****** *)

val d2varset_nil : d2varset_t

fun fprint_d2varset {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, dvs: d2varset_t): void
overload fprint with fprint_d2varset

fun print_d2varset (dvs: d2varset_t): void
overload print with print_d2varset

fun prerr_d2varset (dvs: d2varset_t): void
overload prerr with prerr_d2varset

fun d2varset_add (_: d2varset_t, _: d2var_t): d2varset_t
fun d2varset_adds (dvs: d2varset_t, d2vs: d2varlst): d2varset_t

fun d2varset_del (dvs: d2varset_t, d2v: d2var_t): d2varset_t
fun d2varset_dels (dvs: d2varset_t, d2vs: d2varlst): d2varset_t

fun d2varset_union (dvs1: d2varset_t, dvs2: d2varset_t): d2varset_t

fun d2varset_ismem (dvs: d2varset_t, d2v: d2var_t): bool

fun d2varset_foreach_main {v:view} {vt:viewtype} (
    pf: !v | dvs: d2varset_t, f: (!v | d2var_t, !vt) -<1> void, env: !vt
  ) : void

fun d2varset_foreach_cloptr
  (dvs: d2varset_t, f: !d2var_t -<cloptr1> void): void

(* ****** ****** *)

fun d2sym_make
  (_: loc_t, q: d0ynq, id: sym_t, d2is: d2itemlst): d2sym
// end of [d2sym_make]

(* ****** ****** *)

fun fprint_d2item {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2i: d2item): void
overload fprint with fprint_d2item

fun print_d2item (d2i: d2item): void
fun prerr_d2item (d2i: d2item): void

overload print with print_d2item
overload prerr with prerr_d2item

fun fprint_d2itemlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2i: d2itemlst): void
overload fprint with fprint_d2item

fun print_d2itemlst (d2is: d2itemlst): void
fun prerr_d2itemlst (d2is: d2itemlst): void

overload print with print_d2itemlst
overload prerr with prerr_d2itemlst

(* ****** ****** *)

datatype p2at_node =
  | P2Tann of // ascribed pattern
      (p2at, s2exp)
  | P2Tany // wild card
  | P2Tas of // referenced pattern
      (int(*refknd*), d2var_t, p2at)
  | P2Tbool of bool // boolean pattern
  | P2Tchar of char // character pattern
  | P2Tcon of // constructor pattern
      (int(*freeknd*), d2con_t, s2qualst,
       s2exp(*con*), int(*npf*), p2atlst)
  | P2Tempty // empty pattern
  | P2Texist of // existentially qualified
      (s2varlst, p2at)
  | P2Tfloat of string // float pattern
  | P2Tint of (string, intinf_t) // integer pattern
  | P2Tlist of // (temporary) pattern list
      (int(*npf*), p2atlst)
  | P2Tlst of p2atlst // list pattern
  | P2Trec of // tuple pattern
      (int(*recknd*), int(*npf*), labp2atlst)
  | P2Tstring of string // string pattern
  | P2Tvar of // variable pattern
      (int(*refknd*), d2var_t)
  | P2Tvbox of // vbox pattern
      d2var_t
// end of [p2at_node]

and labp2atlst =
  | LABP2ATLSTnil
  | LABP2ATLSTdot
  | LABP2ATLSTcons of (lab_t, p2at, labp2atlst)
// end of [labp2atlst]

where p2at = '{
  p2at_loc= loc_t
, p2at_svs= s2varlstord_t
, p2at_dvs= d2varlstord_t
, p2at_typ= s2expopt
, p2at_node= p2at_node
} // end of [p2at]

and p2atlst (n:int) = list (p2at, n)
and p2atlst = [n:nat] p2atlst n
and p2atopt = Option p2at

(* ****** ****** *)

fun p2at_set_typ
  (p2t: p2at, os2e: s2expopt): void = "atsopt_p2at_set_typ"
// end of [p2at_set_typ]

fun p2atlst_svs_union (_: p2atlst): s2varlstord_t
fun p2atlst_dvs_union (_: p2atlst): d2varlstord_t

fun labp2atlst_svs_union (_: labp2atlst): s2varlstord_t
fun labp2atlst_dvs_union (_: labp2atlst): d2varlstord_t

fun s2varlstord_linearity_test (_: loc_t, _: s2varlstord_t): void
fun d2varlstord_linearity_test (_: loc_t, _: d2varlstord_t): void

(* ****** ****** *)

fun fprint_p2at {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, p2t: p2at): void
overload fprint with fprint_p2at

fun fprint_p2atlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, p2ts: p2atlst): void
overload fprint with fprint_p2atlst

fun fprint_labp2atlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, lp2ts: labp2atlst): void
overload fprint with fprint_labp2atlst

fun print_p2at (p2t: p2at): void
fun prerr_p2at (p2t: p2at): void

overload print with print_p2at
overload prerr with prerr_p2at

fun print_p2atlst (p2ts: p2atlst): void
fun prerr_p2atlst (p2ts: p2atlst): void

overload print with print_p2atlst
overload prerr with prerr_p2atlst

(* ****** ****** *)

fun p2at_ann (_: loc_t, _: p2at, _: s2exp): p2at
fun p2at_any (_: loc_t): p2at
fun p2at_as (_: loc_t, refknd: int, _: d2var_t, _: p2at): p2at
fun p2at_bool (_: loc_t, _: bool): p2at
fun p2at_char (_: loc_t, _: char): p2at

fun p2at_con
  (loc: loc_t,
   freeknd: int,
   d2c: d2con_t,
   qua: s2qualst,
   res: s2exp,
   npf: int,
   arg: p2atlst)
  : p2at

fun p2at_empty (_: loc_t): p2at
fun p2at_exist (_: loc_t, _: s2varlst, _: p2at): p2at
fun p2at_float (_: loc_t, f: string): p2at
fun p2at_int (_: loc_t, s: string, i: intinf_t): p2at
fun p2at_list (_: loc_t, npf: int, _: p2atlst): p2at
fun p2at_lst (_: loc_t, _: p2atlst): p2at
fun p2at_rec (_: loc_t, kind: int, npf: int, _: labp2atlst): p2at
fun p2at_string (_: loc_t, _: string): p2at
fun p2at_tup (_: loc_t, kind: int, npf: int, _: p2atlst): p2at
fun p2at_var (_: loc_t, refknd: int, d2v: d2var_t): p2at
fun p2at_vbox (_: loc_t, d2v: d2var_t): p2at

(* ****** ****** *)

datatype d2ec_node =
  | D2Cnone
  | D2Clist of d2eclst
  | D2Cinclude of d2eclst (* inclusion *)
  | D2Csymintr of (* symbol intr *) // for temporary use
      $Syn.i0delst
  | D2Csymelim of (* symbol elim *) // for temporary use
      $Syn.i0delst
  | D2Cstavars of s2tavarlst
  | D2Csaspdec of s2aspdec
  | D2Cdcstdec of ($Syn.dcstkind, d2cstlst)
  | D2Cdatdec of ($Syn.datakind, s2cstlst)
  | D2Cexndec of d2conlst
  | D2Coverload of (* overloading *) // for temporary use
      ($Syn.i0de, d2item)
  | D2Cextype of // external type
      (string(*name*), s2exp(*definition*))
  | D2Cextval of (* external value *)
      (string(*name*), d2exp(*definition*))
  | D2Cextcode of (* external code *)
      (int (*position: 0/1/2 : top/?/end*), string (*code*))
  | D2Cvaldecs of (* value declaration *)
      ($Syn.valkind, v2aldeclst)
  | D2Cvaldecs_par of (* parallel value declaration *)
      v2aldeclst // HX: this one is no longer supported
  | D2Cvaldecs_rec of (* recursive value declaration *)
      v2aldeclst
  | D2Cfundecs of (* function declaration *)
      (s2qualst(*decarg*), $Syn.funkind, f2undeclst)
  | D2Cvardecs of (* variable declaration *)
      v2ardeclst
  | D2Cimpdec of (* implementation *)
      i2mpdec
  | D2Clocal of (* local declaration *)
      (d2eclst, d2eclst)
  | D2Cdynload of (* dynamic load *)
      fil_t
  | D2Cstaload of (* static load *)
      (int(*qua*), fil_t, int(*loaded*), int(*loadflag*), d2eclst)
    // end of [D2Cstaload]
// end of [d2ec_node]

and d2exp_node =
  | D2Eann_funclo of (* ascribed with funclo kind *)
      (d2exp, $Syn.funclo)
  | D2Eann_seff of (* ascribed with effects *)
      (d2exp, s2eff)
  | D2Eann_type of (* ascribed dynamic expressions *)
      (d2exp, s2exp)
  | D2Eapps of (d2exp, d2exparglst)
  | D2Earrinit of (* array initialization *)
      (s2exp (*eltyp*), d2expopt (*asz*), d2explst (*elt*))
  | D2Earrpsz of (* array expression *)
      (s2expopt (*element type*), d2explst (*elements*))
  | D2Earrsub of (* array subscription *)
      (d2sym (*[] overloading*), d2exp, loc_t(*ind*), d2explstlst)
  | D2Eassgn of (* assignment *)
      (d2exp(*left*), d2exp(*right*))
  | D2Ebool of bool (* boolean values *)
  | {n:nat} D2Ecaseof of ( // dynamic caseof-expression
      int(*kind*), i2nvresstate, int n, d2explst n, c2laulst n
    ) // end of [D2Ecaseof]
  | D2Echar of char // dynamic character
  | D2Econ of (* dynamic constructor *)
      (d2con_t, s2exparglst, int (*pfarity*), d2explst)
  | D2Ecst of d2cst_t // dynamic constant
  | D2Ecstsp of $Syn.cstsp // special dynamic constant
  | D2Ecrypt of (* cryption *)
      (int, d2exp) (* 1/-1: encrypt/decrypt *)
  | D2Ederef of (* left-value derefence *)
      d2exp
  | D2Edynload of (* dynamic loading *)
      fil_t
  | D2Eeffmask of (* effect masking *)
      ($Syn.effectlst, d2exp)
  | D2Eempty (* empty expression *)
  | D2Eexist of (* existential sum *)
      (s2exparg, d2exp)
  | D2Eextval of (* external value *)
      (s2exp, string(*code*))
  | D2Efix of // dynamic fixed-point expression
      (int(*knd: 0/1: flat/boxed*), d2var_t, d2exp)
  | D2Efloat of (* dynamic float constant *)
      string
  | D2Efloatsp of (* dynamic specified float constant *)
      string
  | D2Efoldat of (* folding at a given address *)
      (s2exparglst, d2exp)
  | D2Efor of ( // for-loop
      loopi2nv, d2exp(*ini*), d2exp(*test*), d2exp(*post*), d2exp(*body*)
    ) // end of [D2Efor]
  | D2Efreeat of (* freeing at a given address *)
      (s2exparglst, d2exp)
  | D2Eif of (* dynamic conditional *)
      (i2nvresstate, d2exp, d2exp, d2expopt)
  | D2Eint of (* dynamic integer constant *)
      (string, intinf_t)
  | D2Eintsp of (* dynamic specified integer constant *)
      (string, intinf_t)
  | D2Elam_dyn of (* dynamic abstraction: boxed *)
      (int(*lin*), int(*npf*), p2atlst, d2exp)
  | D2Elaminit_dyn of (* dynamic abstraction: unboxed *)
      (int(*lin*), int(*npf*), p2atlst, d2exp)
  | D2Elam_met of (* metric abstraction *)
      (ref d2varlst, s2explst, d2exp)
  | D2Elam_sta of (* static abstraction *)
      (s2varlst, s2explst, d2exp)
  | D2Elazy_delay of (* delayed computation *)
      d2exp (*eval*)
  | D2Elazy_ldelay of (* delayed computation *)
      (d2exp (*eval*), d2exp (*free*))
  | D2Elet of (* dynamic let-expression *)
      (d2eclst, d2exp)
  | D2Elist of (int(*npf*), d2explst)
  | D2Eloopexn of (* break: 0 and continue: 1 *)
      int
  | D2Elst of ( // list expression
      int(*lin*), s2expopt(*element type*), d2explst(*elements*)
    ) // end of [D2Elst]
  | D2Emac of (* macro expression *)
      d2mac_t
  | D2Emacsyn of (* macro encoding *)
      ($Syn.macsynkind, d2exp)
  | D2Eptrof of (* taking the address of *)
      d2exp
  | D2Eraise of (* raised exception *)
      d2exp
  | D2Erec of (* dynamic record expression *)
      (int (*recknd*), int(*npf*), labd2explst)
  | D2Escaseof of ( // static caseof-expression
      i2nvresstate, s2exp, sc2laulst
    ) // end of [D2Escaseof]
  | D2Esel of (* record selection *)
      (d2exp, d2lablst)
  | D2Eseq of (* dynamic expression sequence *)
      d2explst
  | D2Eshowtype of (* $showtype: debugging *)
      d2exp
  | D2Esif of (* static conditional *)
      (i2nvresstate, s2exp, d2exp, d2exp)
  | D2Estruct of (* dynamic structure *)
      labd2explst
  | D2Estring of (* dynamic string *)
      (string, int(*length*))
  | D2Esym of (* overloaded dynamic symbol *)
      d2sym
  | D2Etmpid of (* template instantiation *)
      (d2exp, tmps2explstlst)
  | D2Etop (* uninitiated value *)
  | D2Etrywith of (* dynamic trywith expression *)
      (i2nvresstate, d2exp, c2laulst 1)
  | D2Evar of (* dynamic variable *)
      d2var_t
  | D2Eviewat of (* taking view at a given address *)
      d2exp
  | D2Ewhere of (* dynamic where-expression *)
      (d2exp, d2eclst)
  | D2Ewhile of (* while-loop *)
      (loopi2nv, d2exp(*test*), d2exp(*body*))
// end of [d2exp_node]

and d2exparg =
  | D2EXPARGsta of s2exparglst
  | D2EXPARGdyn of (loc_t(*arg*), int (*pfarity*), d2explst)
// end of [d2exparg]

and labd2explst =
  | LABD2EXPLSTnil
  | LABD2EXPLSTcons of (lab_t, d2exp, labd2explst)
// end of [labd2explst]

and d2lab_node =
  | D2LABlab of lab_t
  | D2LABind of d2explstlst
// end of [d2lab_node]

where d2ec = '{
  d2ec_loc= loc_t, d2ec_node= d2ec_node
} // end of [d2ec]

and d2eclst = List d2ec

and d2exp = '{
  d2exp_loc= loc_t, d2exp_node= d2exp_node, d2exp_typ= s2expopt
} // end of [d2exp]

and d2explst (n:int) = list (d2exp, n)
and d2explst = [n:nat] d2explst n
and d2expopt = Option d2exp
and d2explstlst = List d2explst
and d2explstopt = Option d2explst

(* ****** ****** *)

and d2exparglst = List d2exparg

(* ****** ****** *)

and d2lab = '{
  d2lab_loc= loc_t, d2lab_node= d2lab_node
} // end of [d2lab]

and d2lablst = List d2lab

(* ****** ****** *)

and i2nvarg = '{
  i2nvarg_var= d2var_t
, i2nvarg_typ= s2expopt
} // end of [i2nvarg]

and i2nvarglst = List i2nvarg

and i2nvresstate = '{
  i2nvresstate_svs= s2varlst
, i2nvresstate_gua= s2explst
, i2nvresstate_arg= i2nvarglst
, i2nvresstate_met= s2explstopt
} // end of [i2nvresstate]

and loopi2nv = '{
  loopi2nv_loc= loc_t
, loopi2nv_svs= s2varlst
, loopi2nv_gua= s2explst
, loopi2nv_met= s2explstopt (* metric *)
, loopi2nv_arg= i2nvarglst (* argument *)
, loopi2nv_res= i2nvresstate (* result *)
} // end of [loopi2nv]

(* ****** ****** *)

and m2atch = '{
  m2atch_loc= loc_t, m2atch_exp= d2exp, m2atch_pat= p2atopt
} // end of [m2atch]

and m2atchlst = List m2atch

(* ****** ****** *)

and c2lau (n:int) = '{
  c2lau_loc= loc_t
, c2lau_pat= p2atlst n
, c2lau_gua= m2atchlst
, c2lau_seq= int
, c2lau_neg= int
, c2lau_exp= d2exp
} // end of [c2lau]

and c2lau = [n:nat] c2lau n

and c2laulst (n:int) = List (c2lau n)

and c2laulst = [n:nat] c2laulst n

and sc2lau = '{
  sc2lau_loc= loc_t
, sc2lau_pat= sp2at
, sc2lau_exp= d2exp
} // end of [sc2lau]

and sc2laulst = List (sc2lau)

(* ****** ****** *)

and s2tavar = '{
  s2tavar_loc= loc_t
, s2tavar_var= s2var_t
} // end of [s2tavar]

and s2tavarlst = List s2tavar

(* ****** ****** *)

and s2aspdec = '{
  s2aspdec_fil= fil_t
, s2aspdec_loc= loc_t
, s2aspdec_cst= s2cst_t
, s2aspdec_def= s2exp
} // end of [s2aspdec]

(* ****** ****** *)

and v2aldec = '{
  v2aldec_loc= loc_t
, v2aldec_pat= p2at
, v2aldec_def= d2exp
, v2aldec_ann= s2expopt
} // end of [v2aldec]

and v2aldeclst = List v2aldec

(* ****** ****** *)

and f2undec = '{
  f2undec_loc= loc_t
, f2undec_var= d2var_t
, f2undec_def= d2exp
, f2undec_ann= s2expopt
} // end of [f2undec]

and f2undeclst = List f2undec

(* ****** ****** *)

and v2ardec = '{
  v2ardec_loc= loc_t
, v2ardec_knd= int (* BANG: knd = 1 *)
, v2ardec_dvar= d2var_t // dynamic address
, v2ardec_svar= s2var_t // static address
, v2ardec_typ= s2expopt
, v2ardec_wth= d2varopt // proof of @-view
, v2ardec_ini= d2expopt
} // end of [v2ardec]

and v2ardeclst = List v2ardec

(* ****** ****** *)

and i2mpdec = '{
  i2mpdec_loc= loc_t
, i2mpdec_loc_id= loc_t
, i2mpdec_cst= d2cst_t
, i2mpdec_decarg= s2qualst
, i2mpdec_tmparg= s2explstlst, i2mpdec_tmpgua= s2explstlst
, i2mpdec_def= d2exp
} // end of [i2mpdec]

(* ****** ****** *)

fun d2cst_get_def (_: d2cst_t): d2expopt
fun d2cst_set_def (_: d2cst_t, def: d2expopt): void

(* ****** ****** *)

datatype macarg =
  MACARGone of d2var_t | {n:nat} MACARGlst of (int n, d2varlst n)
// end of [macarg]

typedef macarglst (narg:int) = list (macarg, narg)
typedef macarglst = [narg:nat] list (macarg, narg)

fun d2mac_make {narg:nat} (
    _: loc_t
  , name: sym_t
  , knd: int
  , args: macarglst narg
  , def: d2exp
  ) : d2mac_t narg
// end of [d2mac_make]

fun d2mac_get_loc (_: d2mac_t): loc_t
fun d2mac_get_sym (_: d2mac_t): sym_t
fun d2mac_get_kind (_: d2mac_t): int (* 1/0: long/short form *)
fun d2mac_get_narg {narg:nat} (_: d2mac_t narg): int narg
fun d2mac_get_arglst {narg:nat} (_: d2mac_t narg): macarglst narg
fun d2mac_get_def (_: d2mac_t): d2exp
fun d2mac_set_def (_: d2mac_t, _: d2exp): void
fun d2mac_get_stamp (_: d2mac_t): stamp_t

(* ****** ****** *)

fun d2exp_is_raised (_: d2exp): bool
fun c2lau_is_raised (_: c2lau): bool

(* ****** ****** *)

fun d2exp_is_varlamcst (d2e: d2exp): bool
fun d2exp_var_cst_is_ptr (d2e: d2exp): bool

(* ****** ****** *)

fun d2exp_set_typ
  (_: d2exp, _: s2expopt): void = "atsopt_d2exp_set_typ"
// end of [d2exp_set_typ]

(* ****** ****** *)

fun fprint_i2nvarg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, i2nv: i2nvarg): void
overload fprint with fprint_i2nvarg

fun fprint_i2nvarglst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, i2nvs: i2nvarglst): void
overload fprint with fprint_i2nvarglst

fun print_i2nvarglst (i2nv: i2nvarglst): void
overload print with print_i2nvarglst

fun prerr_i2nvarglst (i2nv: i2nvarglst): void
overload prerr with prerr_i2nvarglst

(* ****** ****** *)

fun fprint_i2nvresstate {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, res: i2nvresstate): void
overload fprint with fprint_i2nvresstate

fun print_i2nvresstate (res: i2nvresstate): void
overload print with print_i2nvresstate

fun prerr_i2nvresstate (res: i2nvresstate): void
overload prerr with prerr_i2nvresstate

(* ****** ****** *)

fun fprint_d2exp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2e: d2exp): void
overload fprint with fprint_d2exp

fun print_d2exp (d2e: d2exp): void
overload print with print_d2exp

fun prerr_d2exp (d2e: d2exp): void
overload prerr with prerr_d2exp

(* ****** ****** *)

fun fprint_d2explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2es: d2explst): void
overload fprint with fprint_d2explst

fun print_d2explst (d2es: d2explst): void
overload print with print_d2explst

fun prerr_d2explst (d2es: d2explst): void
overload prerr with prerr_d2explst

(* ****** ****** *)

fun fprint_d2explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2ess: d2explstlst): void
overload fprint with fprint_d2explstlst

fun print_d2explstlst (d2ess: d2explstlst): void
overload print with print_d2explstlst

fun prerr_d2explstlst (d2ess: d2explstlst): void
overload prerr with prerr_d2explstlst

(* ****** ****** *)

fun fprint_labd2explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ld2es: labd2explst): void
overload fprint with fprint_labd2explst

fun print_labd2explst (ld2es: labd2explst): void
overload print with print_labd2explst

fun prerr_labd2explst (ld2es: labd2explst): void
overload prerr with prerr_labd2explst

(* ****** ****** *)

fun fprint_d2lab {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2l: d2lab): void
fun print_d2lab (d2l: d2lab): void
fun prerr_d2lab (d2l: d2lab): void

fun fprint_d2lablst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2ls: d2lablst): void
fun print_d2lablst (d2ls: d2lablst): void
fun prerr_d2lablst (d2ls: d2lablst): void

(* ****** ****** *)

fun fprint_d2exparg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2a: d2exparg): void
fun print_d2exparg (d2a: d2exparg): void
fun prerr_d2exparg (d2a: d2exparg): void

fun fprint_d2exparglst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d2as: d2exparglst): void
fun print_d2exparglst (d2as: d2exparglst): void
fun prerr_d2exparglst (d2as: d2exparglst): void

(* ****** ****** *)

fun d2exp_ann_type (_: loc_t, _: d2exp, _: s2exp): d2exp
fun d2exp_ann_seff (_: loc_t, _: d2exp, _: s2eff): d2exp
fun d2exp_ann_funclo (_: loc_t, _: d2exp, _: $Syn.funclo): d2exp

//

fun d2exp_app_sta (_: loc_t, _fun: d2exp, _arg: s2exparglst)
  : d2exp

fun d2exp_app_dyn
  (loc: loc_t, _fun: d2exp, loc_arg: loc_t, npf: int, _arg: d2explst)
  : d2exp

fun d2exp_app_sta_dyn
  (loc_dap: loc_t, loc_sap: loc_t,
   _fun: d2exp, _sarg: s2exparglst,
   loc_arg: loc_t, npf: int, _darg: d2explst)
  : d2exp

fun d2exp_apps (_: loc_t, _fun: d2exp, _arg: d2exparglst): d2exp

(* ****** ****** *)

fun d2exp_arrinit
  (_: loc_t, eltyp: s2exp, asz: d2expopt, elts: d2explst): d2exp

fun d2exp_arrpsz (_: loc_t, eltyp: s2expopt, elts: d2explst): d2exp

fun d2exp_arrsub (
  loc: loc_t, d2s: d2sym, arr: d2exp, locind: loc_t, ind: d2explstlst
) : d2exp // end of [d2exp_arrsub]

(* ****** ****** *)

fun d2exp_assgn (_: loc_t, _lval: d2exp, _val: d2exp): d2exp

fun d2exp_bool (_: loc_t, _: bool): d2exp

fun d2exp_caseof {n:nat}
  (_: loc_t,
   casknd: int,
   res: i2nvresstate,
   n: int n, d2es: d2explst n,
   c2ls: c2laulst n): d2exp

fun d2exp_char (_: loc_t, _: char): d2exp

fun d2exp_con
  (_: loc_t, d2c: d2con_t, sarg: s2exparglst, npf: int, darg: d2explst)
  : d2exp

fun d2exp_cst (_: loc_t, d2c: d2cst_t): d2exp
fun d2exp_cstsp (_: loc_t, _: $Syn.cstsp): d2exp

fun d2exp_crypt (_: loc_t, knd: int, _: d2exp): d2exp
fun d2exp_deref (_: loc_t, _: d2exp): d2exp
fun d2exp_dynload (_: loc_t, _: fil_t): d2exp
fun d2exp_effmask (_: loc_t, effs: $Syn.effectlst, d2e: d2exp): d2exp
fun d2exp_empty (_: loc_t): d2exp
fun d2exp_exist (_: loc_t, s2a: s2exparg, d2e: d2exp): d2exp
fun d2exp_extval (_: loc_t, type: s2exp, code: string): d2exp

fun d2exp_fix (_: loc_t, knd: int, _fun: d2var_t, _body: d2exp): d2exp

fun d2exp_float (_: loc_t, _: string): d2exp
fun d2exp_floatsp (_: loc_t, _: string): d2exp

fun d2exp_foldat (_: loc_t, _: s2exparglst, _: d2exp): d2exp

fun d2exp_for
  (_: loc_t, inv: loopi2nv, ini: d2exp, test: d2exp, post: d2exp, body: d2exp)
  : d2exp

fun d2exp_freeat (_: loc_t, _: s2exparglst, _: d2exp): d2exp

fun d2exp_if
  (_: loc_t, res: i2nvresstate, _cond: d2exp, _then: d2exp, _else: d2expopt)
  : d2exp

fun d2exp_int (_: loc_t, str: string, int: intinf_t): d2exp
fun d2exp_intsp (_: loc_t, str: string, int: intinf_t): d2exp


(* ****** ****** *)

fun d2exp_lam_dyn
  (_: loc_t, lin: int, npf: int, arg: p2atlst, body: d2exp): d2exp
fun d2exp_laminit_dyn
  (_: loc_t, lin: int, npf: int, arg: p2atlst, body: d2exp): d2exp

(* ****** ****** *)

fun d2exp_lam_met
  (_: loc_t, r: ref d2varlst, met: s2explst, body: d2exp): d2exp

fun d2exp_lam_met_new (_: loc_t, met: s2explst, body: d2exp): d2exp

fun d2exp_lam_sta
  (_: loc_t, _: s2varlst, _: s2explst, body: d2exp): d2exp

fun d2exp_lam_sta_para
  (_: loc_t, _: s2varlst, _: s2explst, body: d2exp): d2exp

//

fun d2exp_lazy_delay (_: loc_t, _: d2exp): d2exp
fun d2exp_lazy_ldelay (_: loc_t, _: d2exp, _: d2exp): d2exp

//

fun d2exp_let (_: loc_t, _: d2eclst, _: d2exp): d2exp

fun d2exp_list (_: loc_t, npf: int, d2es: d2explst): d2exp

fun d2exp_loopexn (_: loc_t, kind: int (*break/continue*)): d2exp

fun d2exp_lst (_: loc_t, lin: int, elt: s2expopt, d2es: d2explst): d2exp

fun d2exp_mac (_: loc_t, d2m: d2mac_t): d2exp

fun d2exp_macsyn (_: loc_t, knd: $Syn.macsynkind, _: d2exp): d2exp

fun d2exp_ptrof (_: loc_t, _: d2exp): d2exp

fun d2exp_raise (_: loc_t, _: d2exp): d2exp

fun d2exp_rec (_: loc_t, kind: int, npf: int, _: labd2explst): d2exp

fun d2exp_scaseof
  (_: loc_t, res: i2nvresstate, s2e: s2exp, sc2ls: sc2laulst): d2exp

fun d2exp_sel (_: loc_t, root: d2exp, path: d2lablst): d2exp
fun d2exp_sel_ptr (_: loc_t, root: d2exp, lab: d2lab): d2exp

fun d2exp_seq (_: loc_t, _: d2explst): d2exp

fun d2exp_showtype (_: loc_t, _: d2exp): d2exp

fun d2exp_sif (
    _: loc_t
  , res: i2nvresstate
  , _cond: s2exp
  , _then: d2exp
  , _else: d2exp
  ) : d2exp
// end of [d2exp_sif]

fun d2exp_string (_: loc_t, _: string, _: int): d2exp
fun d2exp_struct (_: loc_t, _: labd2explst): d2exp
fun d2exp_sym (_: loc_t, d2s: d2sym): d2exp
fun d2exp_tmpid (_: loc_t, _: d2exp, _: tmps2explstlst): d2exp
fun d2exp_top (_: loc_t): d2exp
fun d2exp_trywith (_: loc_t, _: i2nvresstate, _: d2exp, _: c2laulst 1): d2exp
fun d2exp_tup (_: loc_t, knd: int, npf: int, _: d2explst): d2exp
fun d2exp_var (_: loc_t, d2v: d2var_t): d2exp
fun d2exp_viewat (_: loc_t, d2e: d2exp): d2exp
fun d2exp_where (_: loc_t, _: d2exp, _: d2eclst): d2exp
fun d2exp_while (_: loc_t, _: loopi2nv, test: d2exp, body: d2exp): d2exp

(* ****** ****** *)

fun d2lab_lab (_: loc_t, lab: lab_t): d2lab
fun d2lab_ind (_: loc_t, ind: d2explstlst): d2lab

(* ****** ****** *)

fun i2nvarg_make (_: d2var_t, _: s2expopt): i2nvarg

val i2nvresstate_nil : i2nvresstate

fun i2nvresstate_make (
  svs: s2varlst, gua: s2explst, arg: i2nvarglst
) : i2nvresstate // end of [i2nvresstate_make]
fun i2nvresstate_make_met (
  svs: s2varlst, gua: s2explst, arg: i2nvarglst, met: s2explstopt
) : i2nvresstate // end of [i2nvresstate_make_met]

fun i2nvresstate_update (res: i2nvresstate): i2nvresstate

(* ****** ****** *)

fun loopi2nv_make (
  loc: loc_t
, svs: s2varlst
, gua: s2explst
, met: s2explstopt
, arg: i2nvarglst
, res: i2nvresstate
) : loopi2nv // end of [loopi2nv_make]

fun loopi2nv_update (i2nv: loopi2nv): loopi2nv

(* ****** ****** *)

fun m2atch_make (_: loc_t, _: d2exp, _: p2atopt): m2atch

fun c2lau_make {n:nat}
  (_: loc_t, _: p2atlst n, gua: m2atchlst, seq: int, neg: int, exp: d2exp)
  : c2lau n

fun sc2lau_make (_: loc_t, sp2t: sp2at, exp: d2exp): sc2lau

(* ****** ****** *)

fun s2tavar_make (_: loc_t, s2v: s2var_t): s2tavar
fun s2aspdec_make
  (fil: fil_t, _: loc_t, s2c: s2cst_t, def: s2exp): s2aspdec
// end of [s2aspdec_make]

(* ****** ****** *)

fun v2aldec_make
  (_: loc_t, _: p2at, def: d2exp, ann: s2expopt): v2aldec
// end of [v2aldec_make]

fun f2undec_make
  (_: loc_t, _: d2var_t, def: d2exp, ann: s2expopt): f2undec
// end of [f2undec_make]

(* ****** ****** *)

fun v2ardec_make (
  _: loc_t
, knd: int
, _: d2var_t
, _: s2var_t
, typ: s2expopt
, wth: d2varopt
, ini: d2expopt
) : v2ardec // end of [v2ardec_make]

(* ****** ****** *)

fun i2mpdec_make (
  loc: loc_t
, loc_id: loc_t
, _: d2cst_t
, decarg: s2qualst
, tmparg: s2explstlst, tmpgua: s2explstlst
, def: d2exp
) : i2mpdec // end of [i2mpdec_make]

(* ****** ****** *)

fun d2ec_none (_: loc_t): d2ec
fun d2ec_list (_: loc_t, d2cs: d2eclst): d2ec
fun d2ec_include (_: loc_t, d2cs: d2eclst): d2ec
fun d2ec_symintr (_: loc_t, ids: $Syn.i0delst): d2ec
fun d2ec_symelim (_: loc_t, ids: $Syn.i0delst): d2ec
fun d2ec_stavars (_: loc_t, ds: s2tavarlst): d2ec
fun d2ec_saspdec (_: loc_t, d: s2aspdec): d2ec
fun d2ec_dcstdec (_: loc_t, _: $Syn.dcstkind, ds: d2cstlst): d2ec
fun d2ec_datdec (_: loc_t, k: $Syn.datakind, ds: s2cstlst): d2ec
fun d2ec_overload (_: loc_t, id: $Syn.i0de, d2i: d2item): d2ec
fun d2ec_exndec (_: loc_t, con: d2conlst): d2ec
fun d2ec_extype (_: loc_t, name: string, def: s2exp): d2ec
fun d2ec_extval (_: loc_t, name: string, def: d2exp): d2ec
fun d2ec_extcode (_: loc_t, position: int, code: string): d2ec
fun d2ec_valdecs (_: loc_t, _: $Syn.valkind, ds: v2aldeclst): d2ec
fun d2ec_valdecs_par (_: loc_t, ds: v2aldeclst): d2ec
fun d2ec_valdecs_rec (_: loc_t, ds: v2aldeclst): d2ec

fun d2ec_fundecs
  (_: loc_t, decarg: s2qualst, _: $Syn.funkind, ds: f2undeclst): d2ec

fun d2ec_vardecs (_: loc_t, ds: v2ardeclst): d2ec

fun d2ec_impdec (_: loc_t, d: i2mpdec): d2ec

fun d2ec_local (_: loc_t, head: d2eclst, body: d2eclst): d2ec

fun d2ec_dynload (_: loc_t, _: fil_t): d2ec
fun d2ec_staload
  (_: loc_t, qua: int, _: fil_t, loaded: int, loadflag: int, _: d2eclst): d2ec
// end of [d2ec_staload]

(* ****** ****** *)

datatype l2val = // type for left-values
  | L2VALarrsub of (* array subscription *)
      (d2sym (*brackets*), d2exp, loc_t(*ind*), d2explstlst)
  | L2VALptr of (* pointer path selection *)
      (d2exp(*pointer*), d2lablst)
  | L2VALvar_lin of (* variable path selection *)
      (d2var_t, d2lablst)
  | L2VALvar_mut of (* variable path selection *)
      (d2var_t, d2lablst)
  | L2VALnone of d2exp (* non-left-values *)
// end of [l2val]

fun l2val_make_d2exp (d2e0: d2exp): l2val

fun fprint_l2val {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, l2v: l2val): void
fun print_l2val (l2v: l2val): void
fun prerr_l2val (l2v: l2val): void

(* ****** ****** *)

(*
** implemented in [ats_trans3_exp_up.dats]
*)
fun p2at_typ_syn (_: p2at): s2exp
fun p2atlst_typ_syn {n:nat} (_: p2atlst n): s2explst n
fun d2exp_typ_syn (_: d2exp): s2exp

(* ****** ****** *)

(* end of [ats_dynexp2.sats] *)
