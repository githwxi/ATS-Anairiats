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
// Time: December 2007

(* ****** ****** *)

(* The third translation does type-checking *)

(* ****** ****** *)

staload Fil = "ats_filename.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_patcst2.sats"

(* ****** ****** *)

datatype p3at_node =
  | P3Tann of (p3at, s2exp) // ascribed pattern
  | P3Tany of d2var_t // wildcard
  | P3Tas of (* referenced pattern *)
      (int(*refknd*), d2var_t, p3at)
  | P3Tbool of bool // boolean pattern
  | P3Tchar of char // character pattern
  | P3Tcon of (* constructor pattern *)
      (int(*refknd*), d2con_t, int(*npf*), p3atlst)
  | P3Tempty (* empty pattern *)
  | P3Texist of // existentially qualified
      (s2varlst, p3at)
  | P3Tfloat of string // float pattern
  | P3Tint of // integer pattern
      (string, intinf_t)
  | P3Tlst of // list pattern
      (s2exp(*elt*), p3atlst)
  | P3Trec of // record pattern
      (int(*recknd*), int(*npf*), labp3atlst)
  | P3Tstring of string // string pattern
  | P3Tvar of // variable pattern
      (int(*refknd*), d2var_t)
  | P3Tvbox of // vbox pattern
      d2var_t
// end of [p3at_node]

and labp3atlst = 
  | LABP3ATLSTnil
  | LABP3ATLSTdot
  | LABP3ATLSTcons of (lab_t, p3at, labp3atlst)
// end of [labp3atlst]

where p3at = '{
  p3at_loc= loc_t
, p3at_node= p3at_node
, p3at_typ= s2exp
, p3at_typ_lft= s2expopt
} // end of [p3at]

and p3atlst (n:int) = list (p3at, n)
and p3atlst = [n:nat] p3atlst n

and p3atopt = Option p3at

(* ****** ****** *)

fun fprint_p3at {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, p3t: p3at): void
overload fprint with fprint_p3at

fun fprint_p3atlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, p3ts: p3atlst): void
overload fprint with fprint_p3atlst

fun fprint_labp3atlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, lp3ts: labp3atlst): void
overload fprint with fprint_labp3atlst

fun print_p3at (p3t: p3at): void
fun prerr_p3at (p3t: p3at): void

overload print with print_p3at
overload prerr with prerr_p3at

fun print_p3atlst (p3ts: p3atlst): void
fun prerr_p3atlst (p3ts: p3atlst): void

overload print with print_p3atlst
overload prerr with prerr_p3atlst

(* ****** ****** *)

fun p3at_ann (_: loc_t, _: s2exp, p3t: p3at, ann: s2exp): p3at
fun p3at_any (_: loc_t, _: s2exp, _: d2var_t): p3at
fun p3at_as (_: loc_t, _: s2exp, refknd: int, _: d2var_t, _: p3at): p3at
fun p3at_bool (_: loc_t, _: s2exp, _: bool): p3at
fun p3at_char (_: loc_t, _: s2exp, _: char): p3at

fun p3at_con
  (_: loc_t, _: s2exp, freeknd: int, _: d2con_t, npf: int, arg: p3atlst): p3at
// end of [p3at_con]

fun p3at_empty (_: loc_t, _: s2exp): p3at
fun p3at_exist (_: loc_t, _: s2exp, _: s2varlst, _: p3at): p3at
fun p3at_float (_: loc_t, _: s2exp, f: string): p3at
fun p3at_int (_: loc_t, _: s2exp, str: string, int: intinf_t): p3at

fun p3at_lst (_: loc_t, lst: s2exp, elt: s2exp, _: p3atlst): p3at

fun p3at_rec
  (_: loc_t, _: s2exp, reckind: int, npf: int, _: labp3atlst): p3at
// end of [p3at_rec]

fun p3at_string (_: loc_t, _: s2exp, str: string): p3at
fun p3at_var (_: loc_t, _: s2exp, refknd: int, _: d2var_t): p3at
fun p3at_vbox (_: loc_t, _: s2exp, _: d2var_t): p3at

(* ****** ****** *)

fun p3at_set_typ (_: p3at, _: s2exp): void = "atsopt_p3at_set_typ"
fun p3at_set_typ_lft (_: p3at, _: s2expopt): void = "atsopt_p3at_set_typ_lft"

(* ****** ****** *)

datatype d3ec_node =
  | D3Cnone
  | D3Clist of d3eclst
  | D3Csaspdec of s2aspdec
  | D3Cdcstdec of // dynamic constants
      ($Syn.dcstkind, d2cstlst)
  | D3Cdatdec of // datatype declarations
      ($Syn.datakind, s2cstlst)
  | D3Cexndec of d2conlst
  | D3Cextype of // external type
      (string(*name*), s2exp(*def*))
  | D3Cextval of // external value
      (string(*name*), d3exp(*def*))
  | D3Cextcode of (* external code *)
      (int (*position: 0/1/2 : top/?/end*), string (*code*))
  | D3Cvaldecs of (* value declaration *)
      ($Syn.valkind, v3aldeclst)
  | D3Cvaldecs_par of (* parallel value declaration *)
      v3aldeclst
  | D3Cvaldecs_rec of (* recursive value declaration *)
      v3aldeclst
  | D3Cfundecs of (* function declaration *)
      (s2qualst(*decarg*), $Syn.funkind, f3undeclst)
  | D3Cvardecs of (* variable declaration *)
      v3ardeclst
  | D3Cimpdec of (* implementation *)
      i3mpdec
  | D3Clocal of (* local declaration *)
      (d3eclst, d3eclst)
  | D3Cstaload of (* static load *)
      (fil_t, int(*loadflag*), Option d3eclst) // 1: staloading at run-time
  | D3Cdynload of (* dynamic load *)
      fil_t
// end of [d3ec_node]

and d3exp_node =
  | D3Eann_type of (* ascribed expression *)
      (d3exp, s2exp)
  | D3Eapp_dyn of (* dynamic application *)
      (d3exp, int(*npf*), d3explst)
  | D3Eapp_sta of (* static application *)
      d3exp
  | D3Earrinit of (* arraysize expression *)
      (s2exp(*eltyp*), d3expopt(*asz*), d3explst(*elt*))
  | D3Earrpsz of (* arraysize expression *)
      (s2exp(*eltyp*), d3explst(*elements*))
  | D3Eassgn_ptr of (* assignment to a pointer *)
      (d3exp, d3lab1lst, d3exp)
  | D3Eassgn_var of (* assignment to a variable *)
      (d2var_t, d3lab1lst, d3exp)
  | D3Ebool of bool (* boolean values *)
  | {n:nat} D3Ecaseof of (* dynamic caseof-expression *)
      (int(*kind*), d3explst n, c3laulst n)
  | D3Echar of char (* dynamic character *)
  | D3Econ of (* dynamic constructor *)
      (d2con_t, int(*npf*), d3explst)
  | D3Ecst of d2cst_t // dynamic constant
  | D3Ecstsp of $Syn.cstsp // special dynamic constant
  | D3Ecrypt of (* cryption *)
      (int, d3exp) (* 1/-1: encrypt/decrypt *)
  | D3Edynload of (* dynamic loading *)
      $Fil.filename_t
  | D3Eeffmask of (* masking effects *)
      ($Syn.effectlst, d3exp)
  | D3Eempty (* empty expression *)
  | D3Eextval of (* external code *)
      string
  | D3Efix of // dynamic fixed-point expression
      (int(*knd: 0/1: flat/boxed*), d2var_t, d3exp)
  | D3Efloat of string (* dynamic float *)
  | D3Efloatsp of string (* dynamic float *)
  | D3Efoldat of d3exp (* linear datatype folding *)
  | D3Efreeat of d3exp (* linear datatype freeing *)
  | D3Eif of (* conditional expression *)
      (d3exp(*cond*), d3exp(*then*), d3exp(*else*))
  | D3Eint of (* dynamic integer *)
      (string, intinf_t)
  | D3Eintsp of (* dynamic specified integer *)
      (string, intinf_t)
  | D3Elam_dyn of (* dynamic abstraction: boxed *)
      (int(*lin*), int(*npf*), p3atlst, d3exp)
  | D3Elaminit_dyn of (* dynamic abstraction: unboxed *)
      (int(*lin*), int(*npf*), p3atlst, d3exp)
  | D3Elam_met of (* metric abstraction *)
      (s2explst(*metric*), d3exp)
  | D3Elam_sta of (* static abstraction *)
      (s2varlst, s2explst, d3exp)
  | D3Elazy_delay of (* delayed computation *)
      d3exp (*eval*)
  | D3Elazy_ldelay of (* delayed linear computation *)
      (d3exp (*eval*), d3exp (*free*))
  | D3Elazy_force of (* lazy value evaluation *)
      (int(*linearity*), d3exp)
  | D3Elet of // dynamic let-expression
      (d3eclst, d3exp)
  | D3Eloop of (* for-loop *)
      (d3expopt(*init*), d3exp(*test*), d3expopt(*post*), d3exp(*body*))
  | D3Eloopexn of (* loop exception: 0/1: break/continue *)
      int
  | D3Elst of (* list expression *)
      (int(*lin*), s2exp (*element type*), d3explst (*elements*))
  | D3Eptrof_ptr of (* address of a pointer selection *)
      (d3exp, d3lab1lst)
  | D3Eptrof_var of (* address of a variable selection *)
      (d2var_t, d3lab1lst)
  | D3Eraise of (* raised exception *)
      d3exp
  | D3Erec of (* record expression *)
      (int(*recknd*), int(*npf*), labd3explst)
  | D3Erefarg of
      // refval=1/0: call-by-ref/val argument
      // freeknd=1/0: to be freed or not after call
      (int(*refval*), int(*freeknd*), d3exp) 
  | D3Escaseof of (* static caseof-expression *)
      (s2exp, sc3laulst)
  | D3Esel of (* dynamic record selection *)
      (d3exp, d3lab1lst)
  | D3Esel_ptr of (* dynamic linear record ptr selection *)
      (d3exp, d3lab1lst)
  | D3Esel_var of (* dynamic linear record var selection *) 
      (d2var_t, d3lab1lst)
  | D3Eseq of (* dynamic expression sequence *)
      d3explst
  | D3Esif of (* static conditional dynamic expression *)
      (s2exp, d3exp, d3exp)
  | D3Estring of (* dynamic string *)
      (string, int(*length*))
  | D3Estruct of labd3explst (* dynamic structure *)
  | D3Etmpcst of (d2cst_t, s2explstlst)
  | D3Etmpvar of (d2var_t, s2explstlst)
  | D3Etop (* uninitialized value *)
  | D3Etrywith of (* exception handling *)
      (d3exp, c3laulst)
  | D3Evar of (* dynamic variable *)
      d2var_t
  | D3Eviewat_assgn_ptr of (* view@ assignment through a pointer *)
      (d3exp, d3lab1lst, d3exp)
  | D3Eviewat_assgn_var of (* view@ assignment through a variable *)
      (d2var_t, d3lab1lst, d3exp)
  | D3Eviewat_ptr of (* viewat access through a pointer *)
      (d3exp, d3lab1lst, d2var_t(*viewroot*), s2lablst(*viewpath*))
  | D3Eviewat_var of (* viewat access through a variable *)
      (d2var_t, d3lab1lst, d2var_t(*viewroot*), s2lablst(*viewpath*))
  | D3Ewhere of (d3exp, d3eclst)
(* end of [d3exp_node] *)

and labd3explst =
  | LABD3EXPLSTnil
  | LABD3EXPLSTcons of (lab_t, d3exp, labd3explst)
// end of [labd3explst]

and d3lab0_node = D3LAB0lab of lab_t | D3LAB0ind of d3explstlst

and d3lab1_node =
  D3LAB1lab of (lab_t, s2exp) | D3LAB1ind of (d3explstlst, s2exp)
// end of [d3lab1_node]

where d3ec = '{
  d3ec_loc= loc_t, d3ec_node= d3ec_node
} // end of [d3ec]

and d3eclst = List d3ec

and d3exp = '{
  d3exp_loc= loc_t
, d3exp_eff= s2eff
, d3exp_typ= s2exp
, d3exp_node= d3exp_node
} // end of [d3exp]

and d3explst (n:int) = list (d3exp, n)
and d3explst = [n:nat] d3explst n
and d3expopt = Option d3exp
and d3explstlst = List d3explst
and d3explstopt = Option d3explst

(* ****** ****** *)

and d3lab0 = '{
  d3lab0_loc= loc_t, d3lab0_node= d3lab0_node
} // end of [d3lab0]

and d3lab0lst = List d3lab0

and d3lab1 = '{
  d3lab1_loc= loc_t, d3lab1_node= d3lab1_node
} // end of [d3lab1]

and d3lab1lst = List d3lab1

(* ****** ****** *)

and m3atch = '{
  m3atch_loc= loc_t, m3atch_exp= d3exp, m3atch_pat= p3atopt
} // end of [m3atch]

and m3atchlst = List m3atch

and c3lau
  (n:int) = '{ // for clauses
  c3lau_loc= loc_t // location
, c3lau_pat= p3atlst n // pattern list
, c3lau_gua= m3atchlst // clause guard
, c3lau_seq= int // sequentiality
, c3lau_neg= int // negativativity
, c3lau_exp= d3exp // expression body
} // end of [c3lau]

and c3lau = [n:nat] c3lau (n)

and c3laulst (n:int) = List (c3lau n)
and c3laulst = [n:nat] c3laulst (n)

and sc3lau = '{ (* type for static clauses *)
  sc3lau_loc= loc_t
, sc3lau_pat= sp2at // static pattern
, sc3lau_exp= d3exp
} // end of [sc3lau]

and sc3laulst = List (sc3lau)

(* ****** ****** *)

and v3aldec = '{
  v3aldec_loc= loc_t
, v3aldec_pat= p3at
, v3aldec_def= d3exp
} // end of [v3aldec]

and v3aldeclst = List v3aldec

(* ****** ****** *)

and f3undec = '{
  f3undec_loc= loc_t
, f3undec_var= d2var_t
, f3undec_def= d3exp
} // end of [f3undec]

and f3undeclst = List f3undec

(* ****** ****** *)

and v3ardec = '{
  v3ardec_loc= loc_t
, v3ardec_knd= int
, v3ardec_dvar_ptr= d2var_t
, v3ardec_dvar_viw= d2var_t
, v3ardec_typ= s2exp
, v3ardec_ini= d3expopt
} // end of [v3ardec]

and v3ardeclst = List v3ardec

(* ****** ****** *)

and i3mpdec = '{
  i3mpdec_loc= loc_t
, i3mpdec_cst= d2cst_t
, i3mpdec_decarg= s2qualst, i3mpdec_tmparg= s2explstlst // one must be nil
, i3mpdec_def= d3exp
} // end of [i3mpdec]

(* ****** ****** *)

fun d3exp_set_typ (d3e: d3exp, s2e: s2exp): void
  = "ats_dynexp3_d3exp_set_typ"

fun d3explst_get_typ {n:nat} (d3es: d3explst n): s2explst n
fun labd3explst_get_typ (ld3es: labd3explst): labs2explst

(* ****** ****** *)

fun fprint_d3exp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3e: d3exp): void
overload fprint with fprint_d3exp

fun fprint_d3explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3es: d3explst): void
overload fprint with fprint_d3explst

fun fprint_d3explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3ess: d3explstlst): void
overload fprint with fprint_d3explstlst

fun fprint_labd3explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ld3es: labd3explst): void
overload fprint with fprint_labd3explst

fun fprint_d3lab0 {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3l: d3lab0): void
overload fprint with fprint_d3lab0

fun fprint_d3lab0lst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3ls: d3lab0lst): void
overload fprint with fprint_d3lab0lst

fun fprint_d3lab1 {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3l: d3lab1): void
overload fprint with fprint_d3lab1

fun fprint_d3lab1lst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d3ls: d3lab1lst): void
overload fprint with fprint_d3lab1lst

fun print_d3exp (d3e: d3exp): void
fun prerr_d3exp (d3e: d3exp): void

overload print with print_d3exp
overload prerr with prerr_d3exp

fun print_d3explst (d3es: d3explst): void
fun prerr_d3explst (d3es: d3explst): void

overload print with print_d3explst
overload prerr with prerr_d3explst

fun print_d3explstlst (d3ess: d3explstlst): void
fun prerr_d3explstlst (d3ess: d3explstlst): void

overload print with print_d3explstlst
overload prerr with prerr_d3explstlst

fun print_labd3explst (ld3es: labd3explst): void
fun prerr_labd3explst (ld3es: labd3explst): void

overload print with print_labd3explst
overload prerr with prerr_labd3explst

(* ****** ****** *)

fun d3exp_ann_type (_: loc_t, _: d3exp, _: s2exp): d3exp

fun d3exp_app_sta (_: loc_t, _: s2exp, _: d3exp): d3exp

fun d3exp_app_dyn
  (_: loc_t, _: s2exp, _: s2eff, _fun: d3exp, npf: int, _arg: d3explst)
  : d3exp

fun d3exp_arrinit
  (_: loc_t, arr: s2exp, elt: s2exp, asz: d3expopt, elts: d3explst): d3exp

fun d3exp_arrpsz
  (_: loc_t, arr: s2exp, elt: s2exp, elts: d3explst): d3exp

fun d3exp_assgn_ptr
  (_: loc_t, d3e_ptr: d3exp, d3ls: d3lab1lst, d3e_val: d3exp): d3exp

fun d3exp_assgn_var
  (_: loc_t, d2v: d2var_t, d3ls: d3lab1lst, d3e: d3exp): d3exp

fun d3exp_bool (_: loc_t, _: s2exp, _: bool): d3exp

fun d3exp_caseof {n:nat}
  (_: loc_t, _: s2exp, casknd: int, _: d3explst n, _: c3laulst n): d3exp
// end of [d3exp_caseof]

fun d3exp_char (_: loc_t, _: s2exp, _: char): d3exp

fun d3exp_con
  (_: loc_t, _: s2exp, _fun: d2con_t, npf: int, _arg: d3explst): d3exp
// end of [d3exp_con]

fun d3exp_cst (_: loc_t, d2c: d2cst_t): d3exp
fun d3exp_cstsp (_: loc_t, _: s2exp, cst: $Syn.cstsp): d3exp

fun d3exp_crypt (_: loc_t, _: s2exp, knd: int, _: d3exp): d3exp

fun d3exp_dynload (_: loc_t, _: $Fil.filename_t): d3exp

fun d3exp_effmask (_: loc_t, effs: $Syn.effectlst, d3e: d3exp): d3exp

fun d3exp_empty (_: loc_t, _: s2exp): d3exp

fun d3exp_fix (
  _: loc_t, _: s2exp, knd: int, d2v: d2var_t, _def: d3exp
) : d3exp // end of [d3exp_fix]

fun d3exp_float (_: loc_t, _: s2exp, f: string): d3exp
fun d3exp_floatsp (_: loc_t, _: s2exp, f: string): d3exp

fun d3exp_foldat (_: loc_t, _: d3exp): d3exp

fun d3exp_freeat (_: loc_t, _: d3exp): d3exp

fun d3exp_extval (_: loc_t, _: s2exp, code: string): d3exp

fun d3exp_if
  (_: loc_t, _: s2exp, _cond: d3exp, _then: d3exp, _else: d3exp): d3exp
// end of [d3exp_if]

fun d3exp_int (_: loc_t, _: s2exp, str: string, int: intinf_t): d3exp
fun d3exp_intsp (_: loc_t, _: s2exp, str: string, int: intinf_t): d3exp

(* ****** ****** *)

fun d3exp_lam_dyn
  (_: loc_t, _: s2exp, lin: int, npf: int, _arg: p3atlst, _body: d3exp)
  : d3exp

fun d3exp_laminit_dyn
  (_: loc_t, _: s2exp, lin: int, npf: int, _arg: p3atlst, _body: d3exp)
  : d3exp

(* ****** ****** *)

fun d3exp_lam_met (_: loc_t, met: s2explst, _body: d3exp): d3exp

fun d3exp_lam_sta
  (_: loc_t, _: s2exp, s2vs: s2varlst, s2ps: s2explst, _body: d3exp)
  : d3exp

(* ****** ****** *)

fun d3exp_lazy_delay (_: loc_t, _: s2exp, _: d3exp): d3exp
fun d3exp_lazy_ldelay (_: loc_t, _: s2exp, _: d3exp, _: d3exp): d3exp

fun d3exp_lazy_force (_: loc_t, _: s2exp, lin: int, _: d3exp): d3exp

(* ****** ****** *)

fun d3exp_let (_: loc_t, _: d3eclst, _: d3exp): d3exp

(* ****** ****** *)

fun d3exp_loop
  (_: loc_t, init: d3expopt, test: d3exp, post: d3expopt, body: d3exp): d3exp
// end of [d3exp_loop]

fun d3exp_loopexn (_: loc_t, knd: int): d3exp

(* ****** ****** *)

fun d3exp_lst
  (_: loc_t, _lst: s2exp, lin: int, elt: s2exp, elts: d3explst): d3exp

fun d3exp_ptrof_ptr
  (_: loc_t, _ptr: s2exp, _root: d3exp, d3ls: d3lab1lst): d3exp

fun d3exp_ptrof_var
  (_: loc_t, _ptr: s2exp, _root: d2var_t, d3ls: d3lab1lst): d3exp

fun d3exp_raise (_: loc_t, _: s2exp, _: d3exp): d3exp

fun d3exp_rec
  (_: loc_t, _: s2exp, recknd: int, npf: int, _: labd3explst): d3exp

fun d3exp_refarg
  (_: loc_t, _: s2exp, refval: int, freeknd: int, _: d3exp): d3exp

fun d3exp_scaseof
  (_: loc_t, _: s2exp, _val: s2exp, _: sc3laulst): d3exp

fun d3exp_sel (_: loc_t, _: s2exp, root: d3exp, path: d3lab1lst): d3exp

fun d3exp_sel_ptr
  (_: loc_t, _: s2exp, root: d3exp, path: d3lab1lst): d3exp
fun d3exp_sel_var
  (_: loc_t, _: s2exp, root: d2var_t, path: d3lab1lst): d3exp

fun d3exp_seq (_: loc_t, _: s2exp, _: d3explst): d3exp

fun d3exp_sif
  (_: loc_t, _: s2exp, _cond: s2exp, _then: d3exp, _else: d3exp): d3exp

fun d3exp_string (_: loc_t, _: s2exp, _: string, _: int): d3exp

fun d3exp_struct (_: loc_t, _: s2exp, _: labd3explst): d3exp

fun d3exp_tmpcst
  (_: loc_t, _: s2exp, d2c: d2cst_t, s2ess: s2explstlst): d3exp
fun d3exp_tmpvar
  (_: loc_t, _: s2exp, d2v: d2var_t, s2ess: s2explstlst): d3exp

fun d3exp_top (_: loc_t, _: s2exp): d3exp
fun d3exp_trywith (_: loc_t, _: d3exp, _: c3laulst): d3exp

fun d3exp_var (_: loc_t, _: s2exp, _: d2var_t): d3exp

//

fun d3exp_viewat_ptr
  (_: loc_t, _at: s2exp, _: d3exp, _: d3lab1lst,
   _viewroot: d2var_t, _viewpath: s2lablst): d3exp

fun d3exp_viewat_var
  (_: loc_t, _at: s2exp, _: d2var_t, _: d3lab1lst,
   _viewroot: d2var_t, _viewpath: s2lablst): d3exp

fun d3exp_viewat_assgn_ptr
  (_: loc_t, _left: d3exp, d3ls: d3lab1lst, _right: d3exp): d3exp

fun d3exp_viewat_assgn_var
  (_: loc_t, _left: d2var_t, d3ls: d3lab1lst, _right: d3exp): d3exp

//

fun d3exp_where (_: loc_t, _: d3exp, _: d3eclst): d3exp

(* ****** ****** *)

fun d3lab0_lab (_: loc_t, lab: lab_t): d3lab0
fun d3lab0_ind (_: loc_t, ind: d3explstlst): d3lab0

fun d3lab1_lab (_: loc_t, lab: lab_t, s2e: s2exp): d3lab1
fun d3lab1_ind (_: loc_t, ind: d3explstlst, elt: s2exp): d3lab1

(* ****** ****** *)

fun m3atch_make (_: loc_t, _: d3exp, _: p3atopt): m3atch

fun c3lau_make
  {n:nat} (
  loc: loc_t
, pat: p3atlst n
, gua: m3atchlst
, seq: int, neg: int
, exp: d3exp
) : c3lau n // end of [c3lau_make]

fun sc3lau_make (_: loc_t, sp2t: sp2at, exp: d3exp): sc3lau

(* ****** ****** *)

fun v3aldec_make (_: loc_t, pat: p3at, def: d3exp): v3aldec

fun f3undec_make (_: loc_t, d2v: d2var_t, def: d3exp): f3undec

fun v3ardec_make
  (_: loc_t, knd: int, ptr: d2var_t, viw: d2var_t, typ: s2exp, ini: d3expopt)
  : v3ardec

(* ****** ****** *)

fun i3mpdec_make (
    _: loc_t
  , d2c: d2cst_t
  , decarg: s2qualst, tmparg: s2explstlst (* one of decarg/tmparg must be nil *)
  , def: d3exp
  ) : i3mpdec

(* ****** ****** *)

fun d3ec_none (_: loc_t): d3ec
fun d3ec_list (_: loc_t, _: d3eclst): d3ec
fun d3ec_saspdec (_: loc_t, _: s2aspdec): d3ec
fun d3ec_dcstdec (_: loc_t, k: $Syn.dcstkind, _: d2cstlst): d3ec
fun d3ec_datdec (_: loc_t, k: $Syn.datakind, _: s2cstlst): d3ec
fun d3ec_exndec (_: loc_t, _: d2conlst): d3ec
fun d3ec_extype (_: loc_t, name: string, def: s2exp): d3ec
fun d3ec_extval (_: loc_t, name: string, def: d3exp): d3ec
fun d3ec_extcode (_: loc_t, position: int, code: string): d3ec
fun d3ec_valdecs (_: loc_t, _: $Syn.valkind, ds: v3aldeclst): d3ec
fun d3ec_valdecs_par (_: loc_t, ds: v3aldeclst): d3ec
fun d3ec_valdecs_rec (_: loc_t, ds: v3aldeclst): d3ec
fun d3ec_fundecs
  (_: loc_t, decarg: s2qualst, _: $Syn.funkind, ds: f3undeclst): d3ec
// end of [d3ec_fundecs]
fun d3ec_vardecs (_: loc_t, ds: v3ardeclst): d3ec
fun d3ec_impdec (_: loc_t, d: i3mpdec): d3ec
fun d3ec_local (_: loc_t, head: d3eclst, body: d3eclst): d3ec
fun d3ec_staload
  (_: loc_t, _: fil_t, loadflag: int, _: Option (d3eclst)): d3ec
// end of [d3ec_staload]
fun d3ec_dynload (_: loc_t, _: fil_t): d3ec

(* ****** ****** *)

(* end of [ats_dynexp3.sats] *)
