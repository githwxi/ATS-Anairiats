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
// Start Time: March 2008
//
(* ****** ****** *)

(* high-level intermediate representation *)

(* ****** ****** *)

staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)
//
// HX: implemented in [ats_ccomp.dats]
//
abstype funlab_t // boxed type
typedef funlablst = List funlab_t
viewtypedef funlablst_vt = List_vt (funlab_t)

(* ****** ****** *)

datatype hityp_node =
  | HITcltype of (* closure type *)
      funlab_t
  | HITextype of (* externally named type *)
      (string(*extname*), hityplstlst(*arglst*))
  | HITfun of (* function type *)
      ($Syn.funclo, hityplst, hityp)
  | HITrefarg of (* reference argument *)
      (int(*refval*), hityp)
  | HITs2var of s2var_t
  | HITtyarr of (* array type *)
      (hityp (*element*), s2explstlst(*dimension*))
  | HITtyrec of (* boxed record type *)
      (int(*fltboxknd*), labhityplst) (* knd: flt/box: 0/1 *)
  | HITtyrectemp of (* boxed record type in template *)
      (int(*fltboxknd*), labhityplst) (* knd: flt/box: 0/1 *)
  | HITtyrecsin of (* flat singluar record type *)
      hityp
  | HITtysum of (* constructor type *)
      (d2con_t, hityplst)
  | HITtysumtemp of (* constructor type in template *)
      (d2con_t, hityplst)
  | HITunion of (* union type *)
      labhityplst
  | HITvararg (* variadic function argument *)
// end of [hityp_node]

and labhityplst =
  | LABHITYPLSTcons of (lab_t, hityp, labhityplst)
  | LABHITYPLSTnil
// end of [labhityplst]

and hityp_name = HITNAM of (int(*1/0: ptr/non*), string)

where hityp = '{
  hityp_name= hityp_name, hityp_node= hityp_node
} // end of [hityp]

and hityplst = List hityp
and hityplstlst = List hityplst

(* ****** ****** *)

fun fprint_hityp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hit: hityp): void
fun print_hityp (hit: hityp): void
fun prerr_hityp (hit: hityp): void

fun fprint_hityplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hits: hityplst): void
fun print_hityplst (hits: hityplst): void
fun prerr_hityplst (hits: hityplst): void

fun fprint_hityplstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hitss: hityplstlst): void
// end of [fprint_hityplstlst]

(* ****** ****** *)

val hityp_abs : hityp
val hityp_bool : hityp
val hityp_char : hityp
val hityp_clo : hityp
val hityp_clo_ptr : hityp
val hityp_clo_ref : hityp
val hityp_double : hityp
val hityp_float : hityp
val hityp_int : hityp
val hityp_proof : hityp
val hityp_ptr : hityp
val hityp_string : hityp
val hityp_tysum_ptr : hityp
(*
val hityp_var : hityp
val hityp_varet : hityp
*)
val hityp_vararg : hityp
val hityp_void : hityp

(* ****** ****** *)

fun hityp_cltype
  (fl: funlab_t): hityp // for stack-allocated closures
// end of [hityp_cltype]

fun hityp_extype
  (name: string, _arg: hityplstlst): hityp
fun hityp_extype_nil (name: string): hityp

fun hityp_fun (fc: $Syn.funclo, _arg: hityplst, _res: hityp): hityp
fun hityp_refarg (refvar: int, _arg: hityp): hityp
fun hityp_s2var (s2v: s2var_t): hityp

fun hityp_tyarr (hit_elt: hityp, s2ess_dim: s2explstlst): hityp

fun hityp_tyrec (fltboxknd: int, name: string, lhits: labhityplst): hityp
fun hityp_tyrectemp (fltboxknd: int, lhits: labhityplst): hityp
fun hityp_tyrecsin (hit: hityp): hityp

fun hityp_tysum (name: string, d2c: d2con_t, _arg: hityplst): hityp
fun hityp_tysumtemp (d2c: d2con_t, _arg: hityplst): hityp

fun hityp_union (name: string, lhits: labhityplst): hityp

fun hityp_varetize (hit: hityp): hityp

(* ****** ****** *)

fun hityp_is_void (hit: hityp): bool
fun hityp_fun_is_void (hit: hityp): bool

fun hityp_is_vararg (hit: hityp): bool
fun hityp_fun_is_vararg (hit: hityp): bool

fun hityp_is_tyarr (hit: hityp): bool // (flat) array

fun hityp_is_tyrecbox (hit: hityp): bool // boxed record
fun hityp_is_tyrecext (hit: hityp): bool // external (flat) record
fun hityp_is_tyrecsin (hit: hityp): bool // singular (flat) record

(* ****** ****** *)

fun label_is_tyarr (hit_rec: hityp, lab: lab_t): bool

(* ****** ****** *)
//
// HX: implemented in [ats_ccomp.dats]
//
abstype tmpvar_t
typedef tmpvarlst = List (tmpvar_t)
datatype tmpvaropt =
  | TMPVAROPTsome of tmpvar_t | TMPVAROPTnone
// end of [tmpvaropt]

(* ****** ****** *)

datatype hipat_node =
  | HIPann of (* pattern with type ascription *)
      (hipat, hityp)
  | HIPany (* wildcard *)
  | HIPas of (* referenced pattern *)
      (int(*refkind*), d2var_t, hipat)
  | HIPbool of (* boolean pattern *)
      bool
  | HIPchar of (* character pattern *)
      char
  | HIPcon of (* constructor pattern *)
      (int (*freeknd*), d2con_t, hipatlst, hityp(*sum*))
  | HIPcon_any of (* constructor pattern with unused arg *)
      (int(*freeknd*), d2con_t)
  | HIPempty (* empty pattern *)
  | HIPfloat of string (* float point pattern *)
  | HIPint of (* integer pattern *)
      (string, intinf_t)
  | HIPlst of (* list pattern *)
      (hityp(*element*), hipatlst)
  | HIPrec of (* record pattern *)
      (int (*knd*), labhipatlst, hityp(*rec*))
  | HIPstring of (* string pattern *)
      string 
  | HIPvar of (* variable pattern *)
      (int(*refknd*), d2var_t)
// end of [hipat_node]

and labhipatlst =
  | LABHIPATLSTcons of (lab_t, hipat, labhipatlst)
  | LABHIPATLSTdot
  | LABHIPATLSTnil
// end of [labhipatlst]

where hipat = '{
  hipat_loc= loc_t
, hipat_node= hipat_node
, hipat_typ= hityp
// a variable for storing the value that matches the pattern
, hipat_asvar= d2varopt
} // end of [hipat]

and hipatlst = List hipat
and hipatopt = Option hipat

(* ****** ****** *)

fun fprint_hipat {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hip: hipat): void
fun print_hipat (hip: hipat): void
fun prerr_hipat (hip: hipat): void

fun fprint_hipatlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hips: hipatlst): void
fun print_hipatlst (hips: hipatlst): void
fun prerr_hipatlst (hips: hipatlst): void

fun fprint_labhipatlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, lhips: labhipatlst): void
// end of [fprint_labhipatlst]

(* ****** ****** *)

fun hipat_ann (_: loc_t, _: hityp, _: hipat, ann: hityp): hipat
fun hipat_any (_: loc_t, _: hityp): hipat
fun hipat_as (_: loc_t, _: hityp, refknd: int, _: d2var_t, _: hipat): hipat
fun hipat_bool (_: loc_t, _: hityp, _: bool): hipat
fun hipat_char (_: loc_t, _: hityp, _: char): hipat

fun hipat_con (
  _: loc_t, _: hityp, freeknd: int, _: d2con_t, _arg: hipatlst, _sum: hityp)
  : hipat
// end of [hipat_con]

fun hipat_con_any (_: loc_t, _: hityp, freeknd: int, _: d2con_t): hipat

fun hipat_empty (_: loc_t, _: hityp): hipat
fun hipat_int (_: loc_t, _: hityp, str: string, int: intinf_t): hipat
fun hipat_lst (_: loc_t, _lst: hityp, _elt: hityp, _: hipatlst): hipat

fun hipat_rec
  (_: loc_t, _: hityp, knd: int, _: labhipatlst, _rec: hityp): hipat
// end of [hipat_rec]

fun hipat_string (_: loc_t, _: hityp, _: string): hipat
fun hipat_var (_: loc_t, _: hityp, refknd: int, d2v: d2var_t): hipat

(* ****** ****** *)

fun hipatlst_is_unused (hips: hipatlst): bool

(* ****** ****** *)

fun hipat_set_asvar
  (hip: hipat, od2v: d2varopt): void = "atsopt_hipat_set_asvar"
// end of [hipat_set_asvar]

(* ****** ****** *)
//
// HX-2013-03:
// assumed in [ats_ccomp_env.dats]
//
abstype dynconset_type
typedef dynconset = dynconset_type
abstype dyncstset_type
typedef dyncstset = dyncstset_type
//
(* ****** ****** *)

datatype hidec_node =
  | HIDlist of hideclst
  | HIDsaspdec of s2aspdec
  | HIDdcstdec of (* dynamic constant *)
      ($Syn.dcstkind, d2cstlst)
  | HIDdatdec of (* datatype declaration *)
      ($Syn.datakind, s2cstlst)
  | HIDexndec of (* exception constructor *)
      d2conlst
  | HIDextype of (* external type *)
      (string (*name*), hityp (*definition*))
  | HIDextval of (* external value *)
      (string (*name*), hiexp (*definition*))
  | HIDextern of (* external code *)
      (int (*position: 0/1/2 : top/?/end*), string (*code*))
  | HIDfundecs of (* function *)
      (s2qualst(*decarg*), $Syn.funkind, hifundeclst)
  | HIDvaldecs of (* value *)
      ($Syn.valkind, hivaldeclst)
  | HIDvaldecs_par of (* parallel value declaration *)
      hivaldeclst
  | HIDvaldecs_rec of (* recursive value declaration *)
      hivaldeclst
  | HIDvardecs of (* variable *)
      hivardeclst
  | HIDimpdec of (* implementation *)
      hiimpdec
  | HIDimpdec_prf of (* proof implementation *)
      hiimpdec_prf
  | HIDlocal of (* local declaration *)
      (hideclst (*head*), hideclst (*body*))
  | HIDstaload of (* static loading *)
      (fil_t, int(*loadflag*))
  | HIDdynload of (* dynamic loading *)
      fil_t
// end of [hidec_node]

and hiexp_node =
  | HIEapp of (* dynamic application *)
      (hityp, hiexp, hiexplst)
  | HIEarrinit of (* array construction *)
      (hityp(*eltyp*), hiexpopt(*asz*), hiexplst(*elt*))
  | HIEarrpsz of (* arraysize construction *)
      (hityp(*eltyp*), hiexplst(*elt*))
  | HIEassgn_ptr of (* assignment to a pointer with offsets *)
      (hiexp, hilablst, hiexp)
  | HIEassgn_var of (* assignment to a variable with ofsets *)
      (d2var_t, hilablst, hiexp)
  | HIEbool of (* boolean constant *)
      bool
  | HIEcaseof of (* case expression *)
      (int(*casknd*), hiexplst, hiclaulst)
  | HIEcastfn of (* cast expression *)
      (d2cst_t, hiexp)
  | HIEchar of (* character constant *)
      char
  | HIEcon of (* constructor *)
      (hityp, d2con_t, hiexplst)
  | HIEcst of d2cst_t // dynamic constant
  | HIEcstsp of $Syn.cstsp // special dynamic constant
  | HIEdynload of (* dynamic loading *)
      fil_t (* filename *)
  | HIEempty (* no operation *)
  | HIEextval of (* external value *)
      string
  | HIEfix of // dynamic fixed-point expression
      (int(*knd: 0/1: flat/boxed*), d2var_t, hiexp)
  | HIEfloat of (* double precison floating point *)
      string
  | HIEfloatsp of (* specified floating point *)
      string
  | HIEfreeat of hiexp // memory deallocation
  | HIEif of (* conditional *)
      (hiexp, hiexp, hiexp)
  | HIEint of (* integer constant *)
      (string, intinf_t)
  | HIEintsp of (* specified integer constant *)
      (string, intinf_t)
  | HIElam of (* lambda-abstraction: boxed *)
      (hipatlst, hiexp)
  | HIElaminit of (* lambda-abstraction: unboxed *)
      (hipatlst, hiexp)
  | HIElazy_delay of (* delayed computation *)
      hiexp (*eval*)
  | HIElazy_ldelay of (* delayed linear computation *)
      (hiexp (*eval*), hiexp (*free*))
  | HIElazy_force of (* lazy value evaluation *)
      (int(*linearity*), hiexp)
  | HIElet of (* let-expression *)
      (hideclst, hiexp)
  | HIEloop of (* for-loop *)
      (hiexpopt(*init*), hiexp(*test*), hiexpopt(*post*), hiexp(*body*))
  | HIEloopexn of (* local jump *)
      int (* break: 0 and continue: 1 *)
  | HIElst of (* list expression *)
      (int(*lin*), hityp(*element*), hiexplst)
  | HIEptrof_ptr of (* address-of *)
      (hiexp, hilablst)
  | HIEptrof_var of (* address-of *)
      (d2var_t, hilablst)
  | HIEraise of (* raising exception *)
      hiexp
  | HIErec of (* record construction *)
      (int(*knd*), hityp, labhiexplst)
  | HIErefarg of (* call-by-refval argument *)
      (int(*refval*), int(*freeknd*), hiexp)
  | HIEsel of (* path selection *)
      (hiexp, hilablst)
  | HIEsel_ptr of (* path selection for pointer *)
      (hiexp, hilablst)
  | HIEsel_var of (* path selection for variable *)
      (d2var_t, hilablst)
  | HIEseq of (* sequencing *)
      hiexplst
  | HIEsif of (* static conditional expression *)
      (hiexp(*then*), hiexp(*else*))
  | HIEsizeof of (* size of type *)
      hityp
  | HIEstring of (* string constant *)
      (string, int(*length*))
  | HIEtmpcst of (* template constant *)
      (d2cst_t, hityplstlst)
  | HIEtmpvar of (* template variable *)
      (d2var_t, hityplstlst)
  | HIEtop (* uninitialized value *)
  | HIEtrywith of (* exception handling *)
      (hiexp, hiclaulst)
  | HIEvar of (* variable *)
      d2var_t
// end of [hiexp_node]

and labhiexplst =
  | LABHIEXPLSTcons of (lab_t, hiexp, labhiexplst)
  | LABHIEXPLSTnil
// end of [labhiexplst]

and hilab_node =
  | HILlab of (* record selection *)
      (lab_t, hityp (*record*))
  | HILind of (* array subscription *)
      (hiexplstlst (*index*), hityp (*element*))
// end of [hilab_node]

(* ****** ****** *)

where hidec = '{
  hidec_loc= loc_t, hidec_node= hidec_node
} // end of [hidec]

and hideclst = List hidec

and hiexp = '{ 
  hiexp_loc= loc_t, hiexp_node= hiexp_node, hiexp_typ= hityp
} // end of [hiexp]

and hiexplst = List hiexp
and hiexpopt = Option hiexp
and hiexplstlst = List hiexplst

and hilab = '{
  hilab_loc= loc_t, hilab_node= hilab_node
} // end of [hilab]

and hilablst = List hilab

and himat = '{
  himat_loc= loc_t, himat_exp= hiexp, himat_pat= Option (hipat)
} // end of [himat]

and himatlst = List himat

and hiclau = '{ (* type for clauses *)
  hiclau_loc= loc_t (* location information *)
, hiclau_pat= hipatlst (* pattern list *)
, hiclau_gua= himatlst (* clause guard *)
, hiclau_exp= hiexp (* expression body *)
} // end of [hiclau]

and hiclaulst = List hiclau

(* ****** ****** *)

and hifundec = '{
  hifundec_loc= loc_t
, hifundec_var= d2var_t
, hifundec_def= hiexp
} // end of [hifundec]

and hifundeclst = List hifundec

and hivaldec = '{
  hivaldec_loc= loc_t
, hivaldec_pat= hipat
, hivaldec_def= hiexp
} // end of [hivaldec]

and hivaldeclst = List hivaldec

and hivardec = '{
  hivardec_loc= loc_t
, hivardec_knd= int
, hivardec_ptr= d2var_t
, hivardec_ini= hiexpopt
} // end of [hivardec]

and hivardeclst = List hivardec

and hiimpdec = '{ (* implementation *)
  hiimpdec_loc= loc_t
, hiimpdec_cst= d2cst_t
, hiimpdec_tmp= int
, hiimpdec_decarg= s2qualst, hiimpdec_tmparg= hityplstlst
, hiimpdec_def= hiexp
, hiimpdec_cstset= dyncstset
} // end of [hiimpdec]

and hiimpdec_prf = '{ (* proof implementation *)
  hiimpdec_prf_loc= loc_t
, hiimpdec_prf_cst= d2cst_t
, hiimpdec_prf_cstset= dyncstset
} // end of [hiimpdec_prf]

(* ****** ****** *)

fun fprint_hilab {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hil: hilab): void

fun fprint_hilablst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hils: hilablst): void

//

fun fprint_hiexp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hie: hiexp): void
fun print_hiexp (hie: hiexp): void
fun prerr_hiexp (hie: hiexp): void

fun fprint_hiexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hies: hiexplst): void
fun print_hiexplst (hies: hiexplst): void
fun prerr_hiexplst (hies: hiexplst): void

fun fprint_hiexplstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, hiess: hiexplstlst): void
// end of [fprint_hiexplstlst]

fun fprint_labhiexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, lhies: labhiexplst): void
// end of [fprint_labhiexplst]

(* ****** ****** *)

fun hiexp_is_empty (hie: hiexp): bool

fun hiexp_is_value (hie: hiexp): bool

fun hiexp_let_simplify
  (_: loc_t, _: hityp, _: hideclst, _: hiexp): hiexp

fun hiexp_seq_simplify
  (_: loc_t, _: hityp, _: hiexplst): hiexp

(* ****** ****** *)
 
fun hiexp_app
  (_: loc_t, _app: hityp, _fun: hityp, hie: hiexp, hies: hiexplst)
  : hiexp

fun hiexp_arrinit
  (_: loc_t, _: hityp, hit_elt: hityp, ohie_asz: hiexpopt, hies_elt: hiexplst)
  : hiexp

fun hiexp_arrpsz
  (_: loc_t, _: hityp, hit_elt: hityp, hies: hiexplst): hiexp

fun hiexp_assgn_ptr
  (_: loc_t, _: hityp, _ptr: hiexp, hils: hilablst, _val: hiexp)
  : hiexp

fun hiexp_assgn_var
  (_: loc_t, _: hityp, _ptr: d2var_t, hils: hilablst, _val: hiexp)
  : hiexp

fun hiexp_bool (_: loc_t, _: hityp, _: bool): hiexp

(* ****** ****** *)

fun hiexp_caseof
  (_: loc_t, _: hityp, knd: int, hies: hiexplst, hicls: hiclaulst)
  : hiexp

fun hiexp_caseof_if
  (loc0: loc_t, hit0: hityp, knd: int, hies: hiexplst, hicls: hiclaulst)
  : hiexp

(* ****** ****** *)

fun hiexp_castfn (_: loc_t, _: hityp, d2c: d2cst_t, hie: hiexp): hiexp

(* ****** ****** *)

fun hiexp_char (_: loc_t, _: hityp, _: char): hiexp

fun hiexp_con
  (_: loc_t, _: hityp, _sum: hityp, _: d2con_t, _arg: hiexplst)
  : hiexp

fun hiexp_cst (_: loc_t, _: hityp, d2c: d2cst_t): hiexp
fun hiexp_cstsp (_: loc_t, _: hityp, cst: $Syn.cstsp): hiexp

fun hiexp_dynload (_: loc_t, _: hityp, _: fil_t): hiexp

fun hiexp_empty (_: loc_t, _: hityp): hiexp

fun hiexp_extval (_: loc_t, _: hityp, code: string): hiexp

fun hiexp_fix (
  _: loc_t, _: hityp, knd: int, _fun: d2var_t, _body: hiexp
) : hiexp // end of [hiexp_fix]

fun hiexp_float (_: loc_t, _: hityp, _: string): hiexp
fun hiexp_floatsp (_: loc_t, _: hityp, _: string): hiexp

fun hiexp_freeat (_: loc_t, _: hityp, _: hiexp): hiexp

fun hiexp_if
  (_: loc_t, _: hityp, _cond: hiexp, _then: hiexp, _else: hiexp)
  : hiexp

fun hiexp_int
  (_: loc_t, _: hityp, str: string, int: intinf_t): hiexp

fun hiexp_intsp
  (_: loc_t, _: hityp, str: string, int: intinf_t): hiexp

(* ****** ****** *)

fun hiexp_is_lam (hie: hiexp): bool

fun hiexp_lam
  (_: loc_t, _: hityp, _arg: hipatlst, _body: hiexp): hiexp
// end of [hiexp_lam]

fun hiexp_laminit
  (_: loc_t, _: hityp, _arg: hipatlst, _body: hiexp): hiexp
// end of [hiexp_laminit]

(* ****** ****** *)

fun hiexp_lazy_delay
  (_: loc_t, _body: hityp, _eval: hiexp): hiexp

fun hiexp_lazy_ldelay
  (_: loc_t, _body: hityp, _eval: hiexp, _free: hiexp): hiexp

fun hiexp_lazy_force
  (_: loc_t, _val: hityp, lin: int, _lazyval: hiexp): hiexp

(* ****** ****** *)

fun hiexp_let (_: loc_t, _: hityp, _: hideclst, _: hiexp): hiexp

(* ****** ****** *)

fun hiexp_loop (
    _: loc_t
  , _: hityp
  , _init: hiexpopt
  , _test: hiexp
  , _post: hiexpopt
  , _body: hiexp
  ) : hiexp

fun hiexp_loopexn (_: loc_t, _: hityp, i: int): hiexp

(* ****** ****** *)

fun hiexp_lst
  (_: loc_t, _lst: hityp, lin: int, _elt: hityp, _: hiexplst)
  : hiexp

fun hiexp_ptrof_ptr
  (_: loc_t, _: hityp, _ptr: hiexp, hils: hilablst): hiexp

fun hiexp_ptrof_var
  (_: loc_t, _: hityp, _ptr: d2var_t, hils: hilablst): hiexp

fun hiexp_raise (_: loc_t, _: hityp, _: hiexp): hiexp

fun hiexp_rec
  (_: loc_t, _: hityp, knd: int, _rec: hityp, _: labhiexplst)
  : hiexp

fun hiexp_refarg
  (_: loc_t, hit: hityp, refval: int, freeknd: int, _: hiexp): hiexp

fun hiexp_sel
  (_: loc_t, _: hityp, hie: hiexp, hils: hilablst): hiexp

fun hiexp_sel_ptr
  (_: loc_t, _: hityp, _ptr: hiexp, hils: hilablst): hiexp

fun hiexp_sel_var
  (_: loc_t, _: hityp, _ptr: d2var_t, hils: hilablst): hiexp

fun hiexp_seq (_: loc_t, _: hityp, _: hiexplst): hiexp

fun hiexp_sif
  (_: loc_t, _: hityp, _: hiexp(*then*), _: hiexp(*else*)): hiexp

fun hiexp_sizeof (_: loc_t, _: hityp, _arg: hityp): hiexp

fun hiexp_string (_: loc_t, _: hityp, _: string, _: int): hiexp

fun hiexp_tmpcst
  (_: loc_t, _: hityp, d2c: d2cst_t, _: hityplstlst): hiexp

fun hiexp_tmpvar
  (_: loc_t, _: hityp, d2v: d2var_t, _: hityplstlst): hiexp

fun hiexp_top (_: loc_t, _: hityp): hiexp

fun hiexp_trywith
  (_: loc_t, _: hityp, _: hiexp, _: hiclaulst): hiexp

fun hiexp_var (_: loc_t, _: hityp, _: d2var_t): hiexp

(* ****** ****** *)

fun hilab_lab (_: loc_t, _lab: lab_t, _rec: hityp): hilab
fun hilab_ind (_: loc_t, _ind: hiexplstlst, _elt: hityp): hilab

(* ****** ****** *)

fun himat_make (_: loc_t, _: hiexp, _: hipatopt): himat

fun hiclau_make
  (_: loc_t, hips: hipatlst, gua: himatlst, body: hiexp): hiclau

(* ****** ****** *)

fun hidec_list (_: loc_t, _: hideclst): hidec

fun hidec_saspdec (_: loc_t, _: s2aspdec): hidec

fun hidec_dcstdec (_: loc_t, _: $Syn.dcstkind, _: d2cstlst): hidec

fun hidec_datdec (_: loc_t, _: $Syn.datakind, _: s2cstlst): hidec
fun hidec_exndec (_: loc_t, _: d2conlst): hidec

fun hidec_extern (_: loc_t, position: int, code: string): hidec
fun hidec_extype (_: loc_t, name: string, _def: hityp): hidec
fun hidec_extval (_: loc_t, name: string, _def: hiexp): hidec

fun hifundec_make (_: loc_t, d2v: d2var_t, hie: hiexp): hifundec
fun hidec_fundecs
  (_: loc_t, decarg: s2qualst, knd: $Syn.funkind, hids: hifundeclst)
  : hidec

fun hivaldec_make (_: loc_t, hip: hipat, hie: hiexp): hivaldec
fun hidec_valdecs
  (_: loc_t, knd: $Syn.valkind, hids: hivaldeclst): hidec
fun hidec_valdecs_par (_: loc_t, hids: hivaldeclst): hidec
fun hidec_valdecs_rec (_: loc_t, hids: hivaldeclst): hidec

fun hivardec_make
  (_: loc_t, knd: int, d2v: d2var_t, ini: hiexpopt): hivardec
fun hidec_vardecs (_: loc_t, hids: hivardeclst): hidec

(* ****** ****** *)

fun hiimpdec_make (
  loc: loc_t
, d2c: d2cst_t, tmp: int
, decarg: s2qualst, tmparg: hityplstlst, def: hiexp
, d2cs: dyncstset
) : hiimpdec // end of [hiimpdec_make]

fun hidec_impdec (_: loc_t, hid: hiimpdec): hidec

fun hiimpdec_prf_make
  (_: loc_t, d2c: d2cst_t, d2cs: dyncstset) : hiimpdec_prf
// end of [hiimpdec_prf_make]

fun hidec_impdec_prf (_: loc_t, hid: hiimpdec_prf): hidec

(* ****** ****** *)

fun hidec_local (_: loc_t, _head: hideclst, _body: hideclst): hidec

fun hidec_staload (_: loc_t, _: fil_t, loadflag: int): hidec
fun hidec_dynload (_: loc_t, _: fil_t): hidec

(* ****** ****** *)

abstype hityp_t // boxed type
abstype hityplst_t // boxed type
abstype hityplstlst_t // boxed type

fun hityp_encode (hit: hityp): hityp_t
fun hityp_decode (hit: hityp_t): hityp

val hityp_t_ptr: hityp_t
val hityp_t_void: hityp_t
fun hityp_t_s2var (s2v: s2var_t): hityp_t
fun hityp_t_get_name (hit: hityp_t): hityp_name

fun hityp_t_is_void (hit: hityp_t): bool
fun hityp_t_fun_is_void (hit: hityp_t): bool
fun hityp_t_is_tyrecbox (hit: hityp_t): bool
fun hityp_t_is_tyrecext (hit: hityp_t): bool
fun hityp_t_is_tyrecsin (hit: hityp_t): bool

fun hityplst_encode (hits: hityplst): hityplst_t
fun hityplst_decode (hits: hityplst_t): hityplst

fun hityplst_is_nil (hits: hityplst_t): bool
fun hityplst_is_cons (hits: hityplst_t): bool

fun hityplstlst_encode (hits: hityplstlst): hityplstlst_t
fun hityplstlst_decode (hits: hityplstlst_t): hityplstlst

fun hityplstlst_is_nil (hitss: hityplstlst_t): bool
fun hityplstlst_is_cons (hitss: hityplstlst_t): bool

//

fun print_hityp_t (hit: hityp_t): void
fun prerr_hityp_t (hit: hityp_t): void

(* ****** ****** *)

fun d2cst_get_hityp
  (_: d2cst_t): Option (hityp_t)
fun d2cst_get_hityp_some (_: d2cst_t): hityp_t
//
// HX: implemented in [ats_dynexp2_dcst.dats]
//
fun d2cst_set_hityp
  (_: d2cst_t, _: Option hityp_t): void = "atsopt_d2cst_set_hityp"
// end of [d2cst_set_hityp]

(* ****** ****** *)

abstype vartyp_t // boxed type

fun vartyp_make (d2v: d2var_t, hit: hityp_t): vartyp_t

fun vartyp_get_typ (vtp: vartyp_t):<> hityp_t
fun vartyp_get_var (vtp: vartyp_t):<> d2var_t

fun eq_vartyp_vartyp (_: vartyp_t, _: vartyp_t):<> bool
overload = with eq_vartyp_vartyp

fun compare_vartyp_vartyp (_: vartyp_t, _: vartyp_t):<> Sgn
overload compare with compare_vartyp_vartyp

fun fprint_vartyp {m:file_mode}
   (pf: file_mode_lte (m, w) | out: &FILE m, vtp: vartyp_t): void
fun print_vartyp (vtp: vartyp_t): void
fun prerr_vartyp (vtp: vartyp_t): void

(* ****** ****** *)

typedef strlst = List string

datatype labstrlst =
  | LABSTRLSTcons of (lab_t, string, labstrlst) | LABSTRLSTnil
// end of [labstrlst]

datatype typkey =
  | TYPKEYrec of labstrlst // record
  | TYPKEYsum of (int, strlst) // sum
  | TYPKEYuni of labstrlst // union
// end of [typkey]

// implemented in [ats_ccomp_env.dats]
fun typdefmap_find (tk: typkey): string

// implemented in [ats_hiexp_util.dats]
fun hityp_tyrec_make (fltboxknd: int, lhits: labhityplst): hityp_t
fun hityp_tysum_make (d2c: d2con_t, hits_arg: hityplst): hityp_t

fun hityp_normalize (hit: hityp): hityp_t
fun hityplst_normalize (hits: hityplst): hityplst_t
fun hityplstlst_normalize (hitss: hityplstlst): hityplstlst_t

// implemented in [ats_ccomp_trans_temp.dats]
fun hityp_s2var_normalize (s2v: s2var_t): Option_vt (hityp_t)

(* ****** ****** *)

abstype tmpdef_t

// implemented in [ats_hiexp_util.dats]
fun tmpdef_make (decarg: s2qualst, def: hiexp): tmpdef_t
fun tmpdef_get_arg (def: tmpdef_t): s2qualst
fun tmpdef_get_exp (def: tmpdef_t): hiexp

// implemented in [ats_hiexp_util.dats]
fun tmpcstmap_add (d2c: d2cst_t, decarg: s2qualst, def: hiexp): void
fun tmpcstmap_find (d2c: d2cst_t): Option_vt tmpdef_t

// implemented in [ats_hiexp_util.dats]
fun tmpvarmap_add (d2v: d2var_t, decarg: s2qualst, def: hiexp): void
fun tmpvarmap_find (d2v: d2var_t): Option_vt tmpdef_t

(* ****** ****** *)

(* end of [ats_hiexp.sats] *)
