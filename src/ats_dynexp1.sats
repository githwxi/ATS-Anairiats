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

(* The first translation mainly resolves the issue of operator fixity *)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Fil = "ats_filename.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"

(* ****** ****** *)

typedef intlst = List (int)

typedef fil_t = $Fil.filename_t
typedef lab_t = $Lab.label_t
typedef loc_t = $Loc.location_t
typedef sym_t = $Sym.symbol_t

typedef i0de = $Syn.i0de
typedef l0ab = $Syn.l0ab
typedef d0ynq = $Syn.d0ynq
typedef dqi0de = $Syn.dqi0de
typedef sqi0de = $Syn.sqi0de

typedef i0deopt = $Syn.i0deopt
typedef i0delstlst = $Syn.i0delstlst

typedef abskind = $Syn.abskind
typedef dcstkind = $Syn.dcstkind
typedef datakind = $Syn.datakind
typedef funkind = $Syn.funkind
typedef intkind = $Syn.intkind
typedef valkind = $Syn.valkind

typedef dcstextdef = $Syn.dcstextdef

(* ****** ****** *)

datatype p1at_node = 
  | P1Tann of // ascribed pattern
      (p1at, s1exp) 
  | P1Tany // wildcards: _
  | P1Tany2 // wildcard: (_)
  | P1Tapp_dyn of // constructor
      (p1at, loc_t(*arg*), int, p1atlst)
  | P1Tapp_sta of // static application
      (p1at, s1vararglst)
  | P1Tas of // [as] pattern
      (i0de, p1at)
  | P1Tchar of // char constant
      char
  | P1Tempty // empty pattern
  | P1Texist of // existentially qualified
      (s1arglst, p1at)
  | P1Tfloat of // float constant
      string
  | P1Tfree of (* freed constructor *)
      p1at
  | P1Tint of // constant integer 
      string
  | P1Tlist of // pattern list
      (int (*pfarity*), p1atlst)
  | P1Tlst of // list pattern
      p1atlst
  | P1Tqid of // constructor (qualified) / variable (unqualified)
      (d0ynq, sym_t)
  | P1Trec of // boxed/unboxed records
      (int (*recknd*), labp1atlst)
  | P1Tref of // refvar pattern
      i0de
  | P1Trefas of // refvar [as] pattern
      (i0de, p1at)
  | P1Tstring of // string constant
      string
  | P1Tsvararg of (* static argument *)
      s1vararg
  | P1Ttup of (* boxed/unboxed tuples *)
      (int (*tupknd*), int (*pfarity*), p1atlst)
// end of [p1at_node]

and labp1atlst =
  | LABP1ATLSTnil
  | LABP1ATLSTdot
  | LABP1ATLSTcons of (l0ab, p1at, labp1atlst)
// end of [labp1atlst]

where p1at = '{ p1at_loc= loc_t, p1at_node= p1at_node }

and p1atlst: type = List p1at
and p1atopt: type = Option p1at

(* ****** ****** *)

fun fprint_p1at {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, p1t: p1at): void

and fprint_p1atlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, p1ts: p1atlst): void

and fprint_labp1atlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, lp1ts: labp1atlst): void

overload fprint with fprint_p1at
overload fprint with fprint_p1atlst
overload fprint with fprint_labp1atlst

fun print_p1at (p1t: p1at): void
fun prerr_p1at (p1t: p1at): void

overload print with print_p1at
overload prerr with prerr_p1at

(* ****** ****** *)

fun p1at_ann (_: loc_t, p1t: p1at, s1e: s1exp): p1at

fun p1at_any (_: loc_t): p1at
fun p1at_any2 (_: loc_t): p1at

fun p1at_app_dyn
  (loc: loc_t, p1t: p1at, loc_arg: loc_t, npf: int, p1ts: p1atlst): p1at
fun p1at_app_sta
  (_: loc_t, p1t: p1at, s1as: s1vararglst): p1at

fun p1at_as (_: loc_t, id: i0de, p1t: p1at): p1at
fun p1at_char (_: loc_t, c: char): p1at
fun p1at_empty (_: loc_t): p1at
fun p1at_exist (_: loc_t, s1as: s1arglst, p1t: p1at): p1at
fun p1at_float (_: loc_t, _: string): p1at
fun p1at_free (_: loc_t, p1t: p1at): p1at

fun p1at_ide (_: loc_t, id: sym_t): p1at
fun p1at_int (_: loc_t, str: string): p1at

fun p1at_list (_: loc_t, p1ts: p1atlst): p1at
fun p1at_list2
  (_: loc_t, p1ts1: p1atlst, p1ts2: p1atlst): p1at

fun p1at_lst (_: loc_t, p1ts: p1atlst): p1at

fun p1at_qid (_: loc_t, d0q: d0ynq, id: sym_t): p1at
fun p1at_rec (_: loc_t, recknd: int, lp1ts: labp1atlst): p1at
fun p1at_ref (_: loc_t, id: i0de): p1at
fun p1at_refas (_: loc_t, id: i0de, p1t: p1at): p1at
fun p1at_string (_: loc_t, str: string): p1at
fun p1at_svararg (_: loc_t, s1arg: s1vararg): p1at

fun p1at_tup
  (_: loc_t, tupknd: int, p1ts: p1atlst): p1at
fun p1at_tup2
  (_: loc_t, tupknd: int, p1ts1: p1atlst, p1ts2: p1atlst): p1at

(* ****** ****** *)

fun p1at_make_e1xp (_: loc_t, e: e1xp): p1at

(* ****** ****** *)

datatype d1ec_node =
  | D1Cnone
  | D1Clist of d1eclst
  | D1Cinclude of d1eclst (* inclusion *)
  | D1Csymintr of (* overloaded symbol intr *)
      i0delst
  | D1Csymelim of (* overloaded symbol elim *)
      i0delst
  | D1Ce1xpdef of (sym_t, e1xp)
  | D1Cdatsrts of (* datasort declaration *)
      (int(*para: 0/1*), d1atsrtdeclst)
  | D1Csrtdefs of (* sort definition *)
      s1rtdeflst
  | D1Cstacons of (* static constructor *)
      (abskind, s1taconlst)
  | D1Cstacsts of (* static constant *)
      s1tacstlst
  | D1Cstavars of (* static variable *)
      s1tavarlst
  | D1Csexpdefs of (* static definition *)
      (s1rtopt, s1expdeflst)
  | D1Csaspdec of (* static assumption *)
      s1aspdec
  | D1Cdcstdecs of (* dynamic constant *)
      (dcstkind, s1qualstlst, d1cstdeclst)
  | D1Cdatdecs of (* datatype declaration *)
      (datakind, d1atdeclst, s1expdeflst)
  | D1Cexndecs of (* exception declaration *)
      e1xndeclst
  | D1Cclassdec of (i0de, s1expopt)
  | D1Coverload of (i0de, dqi0de) // overloading declaration
  | D1Cextype of (* external type *)
      (string (* extype name *), s1exp (* extype definition *))
  | D1Cextval of (* external type *)
      (string (* extval name *), d1exp (* extval definition *))
  | D1Cextcode of (* external code *)
      (int (*position: 0/1/2 : top/?/end*), string (*code*))
  | D1Cvaldecs of (* value declaration *)
      (valkind, v1aldeclst)
  | D1Cvaldecs_par of (* parallel value declaration *)
      v1aldeclst
  | D1Cvaldecs_rec of (* recursive value declaration *)
      v1aldeclst
  | D1Cfundecs of (* function declaration *)
      (funkind, s1qualstlst, f1undeclst)
  | D1Cvardecs of (* variable declaration *)
      v1ardeclst
  | D1Cmacdefs of (* macro declaration *)
      (int (*long/short*), m1acdeflst)
  | D1Cimpdec of (* implementation *)
      (s1arglstlst, i1mpdec)
  | D1Clocal of (* local declaration *)
      (d1eclst, d1eclst)
  | D1Cdynload of (* dynamic load *)
      fil_t
  | D1Cstaload of (* static load *)
      (Option sym_t, fil_t, int (*loadflag*), d1eclst)
// end of [d1ec_node]

and d1exp_node =
  | D1Eann_effc of (* ascribed with effects *)
      (d1exp, $Eff.effcst)
  | D1Eann_funclo of (* ascribed with funtype *)
      (d1exp, funclo)
  | D1Eann_type of (* ascribed dynamic expressions *)
      (d1exp, s1exp)
  | D1Eapp_dyn of (* dynamic application *)
      (d1exp, loc_t(*arg*), int (*pfarity*), d1explst)
  | D1Eapp_sta of (* static application *)
      (d1exp, s1exparglst)
  | D1Earrinit of (* array initialization *)
      (s1exp (*eltyp*), d1expopt (*asz*), d1explst (*elt*))
  | D1Earrpsz of (* arraysize expression *)
      (s1expopt (*element type*), d1explst (*elements*))
  | D1Earrsub of (* array subscription *)
      (d1exp, loc_t(*ind*), d1explstlst)
  | D1Ebool of bool // boolean constant
  | D1Ecaseof of (* dynamic caseof-expression *)
      (int(*kind*), i1nvresstate, d1explst, c1laulst)
  | D1Echar of char // dynamic character
  | D1Ecstsp of $Syn.cstsp // special constants
  | D1Ecrypt of (* cryption *)
      (int, d1exp) (* 1/-1: encrypt/decrypt *)
  | D1Edecseq of // decseq as exp
      d1eclst (* HX: note that there is no [D2Edecseq] *)
  | D1Edynload of (* dynamic loading *)
      fil_t
  | D1Eeffmask of (* effect masking *)
      ($Syn.effectlst, d1exp)
  | D1Eempty (* empty expression *)
  | D1Eexist of (* existential sum *)
      (s1exparg, d1exp)
  | D1Eextval of (* external code *)
      (s1exp (*type*), string (*code*))
  | D1Efix of // dynamic fixed-point expression
      (int(*knd: 0/1: flat/boxed*), $Syn.i0de, d1exp)
  | D1Efloat of (* dynamic floats *)
      string 
  | D1Efloatsp of (* dynamic specified floats *)
      string 
  | D1Efoldat of (* fold at a given address *)
      (s1exparglst, d1exp)
  | D1Efor of ( // for-loop
      loopi1nv
    , d1exp(*ini*)
    , d1exp(*test*)
    , d1exp(*post*)
    , d1exp(*body*)
    ) // end of [D1Efor]
  | D1Efreeat of (* free at a given address *)
      (s1exparglst, d1exp)
  | D1Eidextapp of (* idext application for syndef *)
      (sym_t, intlst(*ns*), d1explst) // ns: arity list
  | D1Eif of (* conditional dynamic expression *)
      (i1nvresstate, d1exp, d1exp, d1expopt)
  | D1Eint of (* dynamic integer constant *)
      string
  | D1Eintsp of (* dynamic specified integer constant *)
      string
  | D1Elam_dyn of (* dynamic abstraction: alloc / init *)
      (int (*lin*), p1at, d1exp)
  | D1Elaminit_dyn of (* dynamic abstraction initialization *)
      (int (*lin*), p1at, d1exp)
  | D1Elam_met of (* metric abstraction *)
      (loc_t (*loc_arg*), s1explst, d1exp)
  | D1Elam_sta_ana of (* static abstraction: analysis *)
      (loc_t (*loc_arg*), s1arglst, d1exp)
  | D1Elam_sta_syn of (* static abstraction: synthesis *)
      (loc_t (*loc_arg*), s1qualst, d1exp)
  | D1Elazy_delay of (* delayed computation *)
      (int(*lin*), d1exp)
  | D1Elet of (* dynamic let-expression *)
      (d1eclst, d1exp)
  | D1Elist of (* dynamic expression list: temporary *)
      (int(*pfarity*), d1explst)
  | D1Eloopexn of (* break: 0 and continue: 1 *)
      int
  | D1Elst of (* dynamic list expression *)
      (int (*lin*), s1expopt, d1explst)
  | D1Emacsyn of (* macro syntax *)
      ($Syn.macsynkind, d1exp)
  | D1Eptrof of (* taking the address of *)
      d1exp
  | D1Eqid of (* identifier: either a constructor or variable *)
      (d0ynq, sym_t)
  | D1Eraise of (* raised exception *)
      d1exp
  | D1Erec of (* dynamic record expression *)
      (int (*recknd*), labd1explst)
  | D1Escaseof of (* static caseof-expression *)
      (i1nvresstate, s1exp, sc1laulst)
  | D1Esel of (* dynamic selection *)
      (int (*ptr*), d1exp, d1lab)
  | D1Eseq of (* dynamic sequencing *)
      d1explst
  | D1Esexparg of (* for temporary use *)
      s1exparg
  | D1Eshowtype of (* $showtype: debugging *)
      d1exp
  | D1Esif of (* conditional proof expression *)
      (i1nvresstate, s1exp, d1exp, d1exp)
  | D1Estring of (* dynamic string *)
      (string, int(*length*))
  | D1Estruct of (* dynamic structure *)
      labd1explst
  | D1Etmpid of (* template instantiation *)
      ($Syn.tmpqi0de, tmps1explstlst)
  | D1Etop (* uninitialized value *)
  | D1Etrywith of (* dynamic trywith expression *)
      (i1nvresstate, d1exp, c1laulst)
  | D1Etup of (* dynamic tuple expression *)
      (int (*tupknd*), int (*pfarity*), d1explst)
  | D1Eviewat of (* taking view at a given address *)
      d1exp
  | D1Ewhere of (* where clauses *)
      (d1exp, d1eclst)
  | D1Ewhile of (* while-loop *)
      (loopi1nv, d1exp, d1exp)
(*
  | D1Efold of (* folding recursive type *)
      squal_opt_id * d1exp
  | D1Emod of (* module declaration item *)
      moditemdec1 list
  | D1Eunfold of (* unfolding recursive type *)
      squal_opt_id * dexp1
*)
// end of [d1exp_node]

and labd1explst =
  | LABD1EXPLSTnil | LABD1EXPLSTcons of (l0ab, d1exp, labd1explst)
// end of [labd1explst]

and d1lab_node =
  | D1LABlab of lab_t | D1LABind of d1explstlst
// end of [d1lab_node]

(* ****** ****** *)

where d1ec = '{
  d1ec_loc= loc_t, d1ec_node= d1ec_node
} // end of [d1ec]

and d1eclst = List d1ec

(* ****** ****** *)

and d1exp = '{ d1exp_loc= loc_t, d1exp_node= d1exp_node }
and d1explst = List d1exp
and d1expopt = Option d1exp
and d1explstlst = List d1explst

(* ****** ****** *)

and d1lab = '{
  d1lab_loc= loc_t, d1lab_node= d1lab_node
} // end of [d1lab]

(* ****** ****** *)

and m1atch = '{
  m1atch_loc= loc_t, m1atch_exp= d1exp, m1atch_pat= p1atopt
} // end of [m1atch]

and m1atchlst = List m1atch

(* ****** ****** *)

and c1lau = '{
  c1lau_loc= loc_t
, c1lau_pat= p1at
, c1lau_gua= m1atchlst
, c1lau_seq= int
, c1lau_neg= int
, c1lau_exp= d1exp
} // end of [c1lau]

and c1laulst = List c1lau

(* ****** ****** *)

and sc1lau = '{
  sc1lau_loc= loc_t
, sc1lau_pat= sp1at
, sc1lau_exp= d1exp
} // end of [sc1lau]

and sc1laulst = List sc1lau

(* ****** ****** *)

and i1nvarg = '{
  i1nvarg_loc= loc_t
, i1nvarg_sym= sym_t
, i1nvarg_typ= s1expopt
} // end of [i1nvarg]

and i1nvarglst = List i1nvarg

and i1nvresstate = '{
 i1nvresstate_qua= s1qualst, i1nvresstate_arg= i1nvarglst
} // end of [i1nvresstate]

and loopi1nv = '{
  loopi1nv_loc= loc_t
, loopi1nv_qua= s1qualst (* quantifier *)
, loopi1nv_met= s1explstopt (* metric *)
, loopi1nv_arg= i1nvarglst (* argument *)
, loopi1nv_res= i1nvresstate (* result *)
} // end of [loopi1nv]

(* ****** ****** *)

and s1rtdef = '{ // (extended) sort definition
  s1rtdef_loc= loc_t
, s1rtdef_sym= sym_t
, s1rtdef_def= s1rtext
} // end of [s1rtdef]

and s1rtdeflst = List s1rtdef

(* ****** ****** *)

and d1atsrtcon = '{
  d1atsrtcon_loc= loc_t
, d1atsrtcon_sym= sym_t
, d1atsrtcon_arg= s1rtlst
} // end of [d1atsrtcon]

and d1atsrtconlst = List d1atsrtcon

and d1atsrtdec = '{
  d1atsrtdec_loc= loc_t
, d1atsrtdec_sym= sym_t
, d1atsrtdec_con= d1atsrtconlst
} // end of [d1atsrtdec]

and d1atsrtdeclst = List d1atsrtdec

(* ****** ****** *)

and s1tacon = '{ // static constructor declaration
  s1tacon_fil= fil_t
, s1tacon_loc= loc_t
, s1tacon_sym= sym_t
, s1tacon_arg= d1atarglstopt
, s1tacon_def= s1expopt
} // end of [s1tacon]

and s1taconlst = List s1tacon

and s1tacst = '{ // static constant declaration
  s1tacst_fil= fil_t
, s1tacst_loc= loc_t
, s1tacst_sym= sym_t
, s1tacst_arg= s1rtlstopt
, s1tacst_res= s1rt
} // end of [s1tacst]

and s1tacstlst = List s1tacst

and s1tavar = '{ // static variable declaration
  s1tavar_loc= loc_t
, s1tavar_sym= sym_t
, s1tavar_srt= s1rt
} // end of [s1tavar]

and s1tavarlst = List s1tavar

(* ****** ****** *)

and s1expdef = '{
  s1expdef_loc= loc_t
, s1expdef_sym= sym_t
, s1expdef_arg= s1arglstlst
, s1expdef_res= s1rtopt
, s1expdef_def= s1exp
} // end of [s1expdef]

and s1expdeflst = List s1expdef

and s1aspdec = '{
  s1aspdec_fil= fil_t
, s1aspdec_loc= loc_t
, s1aspdec_qid= sqi0de
, s1aspdec_arg= s1arglstlst
, s1aspdec_res= s1rtopt
, s1aspdec_def= s1exp
} // end of [s1aspdec]

and s1aspdeclst = List s1aspdec

(* ****** ****** *)

and d1cstdec = '{
  d1cstdec_fil= fil_t
, d1cstdec_loc= loc_t
, d1cstdec_sym= sym_t
, d1cstdec_typ= s1exp
, d1cstdec_extdef= dcstextdef
} // end of [d1cstdec]

and d1cstdeclst = List d1cstdec

(* ****** ****** *)

and d1atcon = '{
  d1atcon_loc= loc_t
, d1atcon_sym= sym_t
, d1atcon_qua= s1qualstlst
, d1atcon_npf= int
, d1atcon_arg= s1explst
, d1atcon_ind= s1explstopt
} // end of [d1atcon]

and d1atconlst = List d1atcon

and d1atdec = '{
  d1atdec_fil= fil_t
, d1atdec_loc= loc_t
, d1atdec_sym= sym_t
, d1atdec_arg= d1atarglstopt
, d1atdec_con= d1atconlst
} // end of [d1atdec]

and d1atdeclst = List d1atdec

(* ****** ****** *)

and e1xndec = '{
  e1xndec_fil= fil_t
, e1xndec_loc= loc_t
, e1xndec_sym= sym_t
, e1xndec_qua= s1qualstlst
, e1xndec_npf= int
, e1xndec_arg= s1explst
} // end of [e1xndec]

and e1xndeclst = List e1xndec

(* ****** ****** *)

and v1aldec = '{
  v1aldec_loc= loc_t
, v1aldec_pat= p1at
, v1aldec_def= d1exp
, v1aldec_ann= witht1ype
} // end of [v1aldec]

and v1aldeclst = List v1aldec

(* ****** ****** *)

and f1undec = '{
  f1undec_loc= loc_t
, f1undec_sym= sym_t
, f1undec_sym_loc= loc_t
, f1undec_def= d1exp
, f1undec_ann= witht1ype
} // end of [f1undec]

and f1undeclst = List f1undec

(* ****** ****** *)

and v1ardec = '{
  v1ardec_loc= loc_t
, v1ardec_knd= int (* BANG: knd = 1 *)
, v1ardec_sym= sym_t
, v1ardec_sym_loc= loc_t
, v1ardec_typ= s1expopt
, v1ardec_wth= i0deopt
, v1ardec_ini= d1expopt
} // end of [v1ardec]

and v1ardeclst = List v1ardec

(* ****** ****** *)

and m1acdef = '{
  m1acdef_loc= loc_t
, m1acdef_sym= sym_t
, m1acdef_arg= $Syn.m0acarglst
, m1acdef_def= d1exp
} // end of [m1acdef]

and m1acdeflst = List m1acdef

(* ****** ****** *)

and i1mpdec = '{
  i1mpdec_loc= loc_t
, i1mpdec_qid= $Syn.impqi0de
, i1mpdec_tmparg= s1explstlst
, i1mpdec_def= d1exp
} // end of [i1mpdec]

(* ****** ****** *)

fun fprint_d1exp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d1e: d1exp): void

and fprint_d1explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d1es: d1explst): void

and fprint_d1explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d1ess: d1explstlst): void

and fprint_labd1explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, ld1es: labd1explst): void

overload fprint with fprint_d1exp
overload fprint with fprint_d1explst
overload fprint with fprint_d1explstlst
overload fprint with fprint_labd1explst

fun print_d1exp (d1e: d1exp): void
fun prerr_d1exp (d1e: d1exp): void

overload print with print_d1exp
overload prerr with prerr_d1exp

fun fprint_d1lab {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, d1l: d1lab): void

overload fprint with fprint_d1lab

(* ****** ****** *)

fun d1exp_ann_effc (_: loc_t, d1e: d1exp, efc: $Eff.effcst): d1exp

fun d1exp_ann_funclo (_: loc_t, d1e: d1exp, fc: funclo): d1exp
fun d1exp_ann_funclo_opt (_: loc_t, d1e: d1exp, fc: funclo): d1exp

fun d1exp_ann_type (_: loc_t, d1e: d1exp, s1e: s1exp): d1exp

(* ****** ****** *)

fun d1exp_app_dyn (
  loc: loc_t, d1e: d1exp, loc_arg: loc_t, npf: int, d1es: d1explst
) : d1exp // end of [d1exp_app_dyn]

(* ****** ****** *)

fun d1exp_app_sta (_: loc_t, d1e: d1exp, s1as: s1exparglst): d1exp

(* ****** ****** *)

fun d1exp_arrinit (
  _: loc_t, s1e_elt: s1exp, od1e_asz: d1expopt, d1es_elt: d1explst
) : d1exp // end of [d1exp_arrinit]

fun d1exp_arrpsz
  (_: loc_t, os1e_elt: s1expopt, d1es_elt: d1explst): d1exp

fun d1exp_arrsub
  (_: loc_t, arr: d1exp, ind: loc_t, ind: d1explstlst): d1exp

(* ****** ****** *)

fun d1exp_bool (loc: loc_t, tf: bool): d1exp

(* ****** ****** *)

fun d1exp_caseof (
  _: loc_t, k: int, res: i1nvresstate, d1es: d1explst, c1ls: c1laulst
) : d1exp // end of [d1exp_caseof]

fun d1exp_char (_: loc_t, c: char): d1exp

fun d1exp_cstsp (_: loc_t, _: $Syn.cstsp): d1exp

fun d1exp_crypt (_: loc_t, knd: int, _: d1exp): d1exp

fun d1exp_decseq (_: loc_t, _: d1eclst): d1exp

fun d1exp_dynload (_: loc_t, _: fil_t): d1exp

fun d1exp_effmask
  (_: loc_t, effs: $Syn.effectlst, d1e: d1exp): d1exp
// end of [d1exp_effmask]

fun d1exp_empty (_: loc_t): d1exp

fun d1exp_exist (_: loc_t, s1a: s1exparg, d1e: d1exp): d1exp

fun d1exp_extval (_: loc_t, s1e: s1exp, code: string): d1exp

fun d1exp_fix
  (_: loc_t, knd: int, id: $Syn.i0de, d1e: d1exp): d1exp
// end of [d1exp_fix]

fun d1exp_float (_: loc_t, f: string): d1exp
fun d1exp_floatsp (_: loc_t, f: string): d1exp

fun d1exp_foldat (_: loc_t, _: s1exparglst, _: d1exp): d1exp

fun d1exp_for (
  loc: loc_t
, inv: loopi1nv
, init: d1exp
, test: d1exp
, post: d1exp
, body: d1exp
) : d1exp // end of [d1exp_for]

fun d1exp_freeat (_: loc_t, _: s1exparglst, _: d1exp): d1exp

(* ****** ****** *)

fun d1exp_ide (_: loc_t, _: sym_t): d1exp
fun d1exp_idextapp (
  _: loc_t, _: sym_t, ns: intlst, d1es: d1explst
) : d1exp // end of [d1exp_idextapp]

(* ****** ****** *)

fun d1exp_if (
  loc: loc_t
, inv: i1nvresstate
, _cond: d1exp
, _then: d1exp
, _else: d1expopt
) : d1exp // end of [d1exp_if]

(* ****** ****** *)

fun d1exp_int (_: loc_t, int: string): d1exp
fun d1exp_intsp (_: loc_t, int: string): d1exp

(* ****** ****** *)

fun d1exp_lam_dyn
  (_: loc_t, lin: int, arg: p1at, _: d1exp): d1exp
fun d1exp_laminit_dyn
  (_: loc_t, lin: int, arg: p1at, _: d1exp): d1exp

(* ****** ****** *)

fun d1exp_lam_met
  (_: loc_t, _arg: loc_t, _: s1explst, _: d1exp): d1exp
fun d1exp_lam_sta_ana
  (_: loc_t, _arg: loc_t, _: s1arglst, _: d1exp): d1exp
fun d1exp_lam_sta_syn
  (_: loc_t, _arg: loc_t, _: s1qualst, _: d1exp): d1exp

(* ****** ****** *)

fun d1exp_lazy_delay (_: loc_t, lin: int, _: d1exp): d1exp

fun d1exp_let (_: loc_t, _: d1eclst, _: d1exp): d1exp

fun d1exp_list (_: loc_t, _: d1explst): d1exp
fun d1exp_list2 (_: loc_t, _1: d1explst, _2: d1explst): d1exp

fun d1exp_loopexn (_: loc_t, kind: int (*break/continue*)): d1exp

fun d1exp_lst (_: loc_t, lin: int, elt: s1expopt, elts: d1explst): d1exp

fun d1exp_macsyn (_: loc_t, knd: $Syn.macsynkind, d1e: d1exp): d1exp

fun d1exp_ptrof (_: loc_t, _: d1exp): d1exp

fun d1exp_qid (_: loc_t, q: d0ynq, id: sym_t): d1exp

fun d1exp_raise (_: loc_t, _: d1exp): d1exp

fun d1exp_rec (_: loc_t, kind: int, _: labd1explst): d1exp

fun d1exp_scaseof
  (_: loc_t, res: i1nvresstate, s1e: s1exp, sc1ls: sc1laulst): d1exp

fun d1exp_sel (_: loc_t, kind: int, root: d1exp, lab: d1lab): d1exp

fun d1exp_seq (_: loc_t, seq: d1explst): d1exp

fun d1exp_sexparg (_: loc_t, _: s1exparg): d1exp

fun d1exp_showtype (_: loc_t, _: d1exp): d1exp

fun d1exp_sif
  (_: loc_t, res: i1nvresstate, _cond: s1exp, _then: d1exp, _else: d1exp)
  : d1exp

fun d1exp_string (_: loc_t, _: string, _: int): d1exp

fun d1exp_struct (_: loc_t, _: labd1explst): d1exp

fun d1exp_tmpid
  (_: loc_t, qid: $Syn.tmpqi0de, decarg: tmps1explstlst): d1exp

fun d1exp_top (_: loc_t): d1exp

fun d1exp_trywith (_: loc_t, _: i1nvresstate, _: d1exp, _: c1laulst): d1exp

fun d1exp_tup (_: loc_t, kind: int, _: d1explst): d1exp
fun d1exp_tup2 (_: loc_t, kind: int, _1: d1explst, _2: d1explst): d1exp
fun d1exp_tup_npf (_: loc_t, kind: int, npf: int, _: d1explst): d1exp

fun d1exp_viewat (_: loc_t, _: d1exp): d1exp

fun d1exp_where (_: loc_t, _: d1exp, _: d1eclst): d1exp

fun d1exp_while (_: loc_t, _: loopi1nv, test: d1exp, body: d1exp): d1exp

(* ****** ****** *)

fun d1exp_is_metric (_: d1exp): bool

(* ****** ****** *)

fun d1exp_make_e1xp (_: loc_t, _: e1xp): d1exp

(* ****** ****** *)

fun d1lab_lab (_: loc_t, lab: lab_t): d1lab
fun d1lab_ind (_: loc_t, ind: d1explstlst): d1lab

(* ****** ****** *)

fun m1atch_make (_: loc_t, d1e: d1exp, op1t: p1atopt): m1atch

fun c1lau_make (
  _: loc_t, _: p1at, gua: m1atchlst, seq: int, neg: int, body: d1exp
) : c1lau // end of [c1lau_make]

fun sc1lau_make (_: loc_t, _: sp1at, body: d1exp): sc1lau

(* ****** ****** *)

fun i1nvarg_make
  (_: loc_t, id: sym_t, os1e: s1expopt): i1nvarg

fun i1nvresstate_make (s1qs: s1qualst, arg: i1nvarglst): i1nvresstate
val i1nvresstate_nil: i1nvresstate

fun loopi1nv_make (
  _: loc_t, _: s1qualst, met: s1explstopt, _: i1nvarglst, _: i1nvresstate
) : loopi1nv // end of [loopi1nv_make]

fun loopi1nv_nil (loc0: loc_t): loopi1nv

(* ****** ****** *)

fun d1ec_none (_: loc_t): d1ec

fun d1ec_list (_: loc_t, ds: d1eclst): d1ec

fun d1ec_include (_: loc_t, ds: d1eclst): d1ec

fun d1ec_symelim (_: loc_t, ids: i0delst): d1ec

fun d1ec_symintr (_: loc_t, ids: i0delst): d1ec

fun d1ec_e1xpdef (_: loc_t, id: sym_t, def: e1xp): d1ec

fun d1ec_datsrts (_: loc_t, para: int, ds: d1atsrtdeclst): d1ec

fun d1ec_srtdefs (_: loc_t, ds: s1rtdeflst): d1ec

fun d1ec_stacons (_: loc_t, _: abskind, ds: s1taconlst): d1ec

fun d1ec_stacsts (_: loc_t, ds: s1tacstlst): d1ec

fun d1ec_stavars (_: loc_t, ds: s1tavarlst): d1ec

fun d1ec_sexpdefs (_: loc_t, res: s1rtopt, ds: s1expdeflst): d1ec

fun d1ec_saspdec (_: loc_t, d: s1aspdec): d1ec

fun d1ec_dcstdecs
  (_: loc_t, _: dcstkind, decarg: s1qualstlst, ds: d1cstdeclst): d1ec
// end of [d1ec_dcstdecs]

fun d1ec_datdecs
  (_: loc_t, _: datakind, ds_dat: d1atdeclst, ds_def: s1expdeflst): d1ec
// end of [d1ec_datdecs]

fun d1ec_exndecs (_: loc_t, ds: e1xndeclst): d1ec

fun d1ec_classdec (_: loc_t, id: i0de, sup: s1expopt): d1ec

fun d1ec_overload (_: loc_t, id: i0de, qid: dqi0de): d1ec

fun d1ec_extype (_: loc_t, name: string, def: s1exp): d1ec

fun d1ec_extval (_: loc_t, name: string, def: d1exp): d1ec

fun d1ec_extcode (_: loc_t, position: int, code: string): d1ec

fun d1ec_valdecs (_: loc_t, _: valkind, ds: v1aldeclst): d1ec

fun d1ec_valdecs_par (_: loc_t, ds: v1aldeclst): d1ec

fun d1ec_valdecs_rec (_: loc_t, ds: v1aldeclst): d1ec

fun d1ec_fundecs
  (_: loc_t, _: funkind, decarg: s1qualstlst, ds: f1undeclst): d1ec
// end of [d1ec_fundecs]

fun d1ec_vardecs (_: loc_t, ds: v1ardeclst): d1ec

fun d1ec_macdefs (_: loc_t, kind: int, ds: m1acdeflst): d1ec

fun d1ec_impdec (_: loc_t, decarg: s1arglstlst, d: i1mpdec): d1ec

fun d1ec_local (_: loc_t, head: d1eclst, body: d1eclst): d1ec

fun d1ec_dynload (_: loc_t, _: fil_t): d1ec

fun d1ec_staload (
  loc: loc_t
, id: Option sym_t
, fil: fil_t
, loadflag: int
, d1cs: d1eclst
) : d1ec // end of [d1ec_staload]

(* ****** ****** *)

fun d1atsrtcon_make
  (_: loc_t, id: sym_t, arg: s1rtlst): d1atsrtcon
// end of [d1atsrtcon_make]

fun d1atsrtdec_make
  (_: loc_t, id: sym_t, con: d1atsrtconlst): d1atsrtdec
// end of [d1atsrtdec_make]

fun s1rtdef_make (_: loc_t, id: sym_t, def: s1rtext): s1rtdef

fun s1tacon_make (
  _: fil_t, _: loc_t, id: sym_t, arg: d1atarglstopt, def: s1expopt
) : s1tacon // end of [s1tacon_make]

fun s1tacst_make
  (_: fil_t, _: loc_t, id: sym_t, arg: s1rtlstopt, res: s1rt): s1tacst
// end of [s1tacst_make]

fun s1tavar_make (_: loc_t, id: sym_t, s1t: s1rt): s1tavar

fun s1expdef_make (
    loc: loc_t
  , id: sym_t
  , arg: s1arglstlst
  , res: s1rtopt
  , def: s1exp
  ) : s1expdef
// end of [s1expdef_make]

fun s1aspdec_make (
  fil: fil_t, loc: loc_t
, qid: sqi0de, arg: s1arglstlst, res: s1rtopt, def: s1exp
) : s1aspdec // end of [s1aspdec_make]

fun d1cstdec_make
  (fil: fil_t, loc: loc_t, id: sym_t, typ: s1exp, extdef: dcstextdef)
  : d1cstdec
// end of [d1cstdec_make]

fun d1atcon_make
  (_: loc_t, id: sym_t,
   qua: s1qualstlst, npf: int, arg: s1explst, ind: s1explstopt)
  : d1atcon
// end of [d1atcon_make]

fun d1atdec_make
  (fil: fil_t, _: loc_t, id: sym_t, _: d1atarglstopt, _: d1atconlst)
  : d1atdec
// end of [d1atdec_make]

fun e1xndec_make
  (fil: fil_t, _: loc_t, id: sym_t, qua: s1qualstlst, npf: int, arg: s1explst)
  : e1xndec
// end of [e1xndec_make]

fun v1aldec_make
  (_: loc_t, pat: p1at, def: d1exp, typ: witht1ype): v1aldec
// end of [v1aldec_make]

fun f1undec_make
  (_: loc_t, id: sym_t, loc_id: loc_t, def: d1exp, typ: witht1ype)
  : f1undec
// end of [f1undec_make]

fun v1ardec_make (
    _: loc_t
  , knd: int
  , id: sym_t
  , loc_id: loc_t
  , typ: s1expopt
  , wth: i0deopt
  , def: d1expopt
  ) : v1ardec
// end of [v1ardec_make]

fun m1acdef_make
  (_: loc_t, id: sym_t, arg: $Syn.m0acarglst, def: d1exp): m1acdef
// end of [m1acdef_make]

fun i1mpdec_make
  (_: loc_t, qid: $Syn.impqi0de, _: s1explstlst, _: d1exp): i1mpdec
// end of [i1mpdec_make]

(* ****** ****** *)

(* end of [ats_dynexp1.sats] *)
