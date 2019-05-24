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

// Time: August 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

typedef efc = $Eff.effcst
typedef efcopt = Option efc
typedef lab_t = $Lab.label_t
typedef loc_t = $Loc.location_t
typedef sym_t = $Sym.symbol_t
typedef funclo = $Syn.funclo
typedef s0rtq = $Syn.s0rtq
typedef s0taq = $Syn.s0taq
typedef i0delst = $Syn.i0delst
typedef cstsp = $Syn.cstsp

(* ****** ****** *)

datatype e1xp_node =
  | E1XPapp of (e1xp, loc_t(*arg*), e1xplst)
  | E1XPchar of char
  | E1XPfloat of string
  | E1XPide of sym_t
  | E1XPint of string
  | E1XPlist of e1xplst
  | E1XPstring of (string, int(*length*))
  | E1XPundef of () // a special value for marking undefinition
  | E1XPcstsp of $Syn.cstsp // special constants
  | E1XPnone of ()
// end of [e1xp_node]

where e1xp: type = '{
  e1xp_loc= loc_t, e1xp_node= e1xp_node
}
and e1xplst: type = List e1xp

fun fprint_e1xp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: e1xp): void
overload fprint with fprint_e1xp

fun fprint_e1xplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: e1xplst): void
overload fprint with fprint_e1xplst

fun print_e1xp (_: e1xp): void
fun prerr_e1xp (_: e1xp): void
overload print with print_e1xp
overload prerr with prerr_e1xp

fun print_e1xplst (_: e1xplst): void
fun prerr_e1xplst (_: e1xplst): void
overload print with print_e1xplst
overload prerr with prerr_e1xplst

(* ****** ****** *)

fun e1xp_app (
  loc: loc_t, _fun: e1xp, loc_arg: loc_t, _arg: e1xplst
) : e1xp // end of [e1xp_app]
//
fun e1xp_char (_: loc_t, _:char): e1xp
fun e1xp_float (_: loc_t, _:string): e1xp
fun e1xp_ide (_: loc_t, _: sym_t): e1xp
fun e1xp_int (_: loc_t, _: string): e1xp
fun e1xp_list (_: loc_t, _: e1xplst): e1xp
fun e1xp_string (_: loc_t, _: string, _: int): e1xp
fun e1xp_undef (_: loc_t): e1xp
fun e1xp_cstsp (_: loc_t, cst: cstsp): e1xp
//
fun e1xp_none (_: loc_t): e1xp
//
fun e1xp_true (): e1xp and e1xp_false (): e1xp
//
(* ****** ****** *)

datatype v1al =
  | V1ALchar of char
  | V1ALfloat of double
  | V1ALint of int
  | V1ALstring of string
  | V1ALcstsp of (loc_t, cstsp)
// end of [v1al]

val v1al_true : v1al and v1al_false : v1al

(* ****** ****** *)

datatype s1rt_node =
  | S1RTapp of (s1rt, s1rtlst)
  | S1RTlist of s1rtlst
  | S1RTqid of (s0rtq, sym_t)
  | S1RTtup of s1rtlst
// end of [s1rt_node]

where s1rt: type = '{
  s1rt_loc= loc_t, s1rt_node= s1rt_node
}

and s1rtlst: type = List s1rt
and s1rtopt: type = Option s1rt
and s1rtlstlst: type = List s1rtlst
and s1rtlstopt: type = Option s1rtlst

typedef s1rtpol = '{
  s1rtpol_loc= loc_t, s1rtpol_srt= s1rt, s1rtpol_pol= int
} // end of [s1rtpol]

(* ****** ****** *)

fun fprint_s1rt {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1rt): void
overload fprint with fprint_s1rt

fun fprint_s1rtlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1rtlst): void
overload fprint with fprint_s1rtlst

fun fprint_s1rtopt {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1rtopt): void
overload fprint with fprint_s1rtopt

fun print_s1rt (_: s1rt): void
fun prerr_s1rt (_: s1rt): void

overload print with print_s1rt
overload prerr with prerr_s1rt

fun print_s1rtlst (_: s1rtlst): void
fun prerr_s1rtlst (_: s1rtlst): void

overload print with print_s1rtlst
overload prerr with prerr_s1rtlst

(* ****** ****** *)

(* functions for constructing sorts *)

fun s1rt_arrow (_: loc_t): s1rt

(* '->' is a special sort constructor *)
fun s1rt_is_arrow (s1t: s1rt): bool

fun s1rt_app (_: loc_t, _fun: s1rt, _arg: s1rtlst): s1rt
fun s1rt_fun (_: loc_t, arg: s1rt, res: s1rt): s1rt
fun s1rt_ide (_: loc_t, _: sym_t): s1rt
fun s1rt_list (_: loc_t, _: s1rtlst): s1rt
fun s1rt_qid (_: loc_t, q: s0rtq, id: sym_t): s1rt
fun s1rt_tup (_: loc_t, _: s1rtlst): s1rt

(* ****** ****** *)

fun s1rtpol_make (_: loc_t, _: s1rt, pol: int): s1rtpol

(* ****** ****** *)

datatype
d1atarg_node =
  | D1ATARGsrt of s1rtpol | D1ATARGidsrt of (sym_t, s1rtpol)
// end of [d1atarg_node]

typedef d1atarg = '{
  d1atarg_loc= loc_t, d1atarg_node= d1atarg_node
}

typedef d1atarglst = List d1atarg
typedef d1atarglstopt = Option d1atarglst

fun d1atarg_srt (_: loc_t, _: s1rtpol): d1atarg
fun d1atarg_idsrt (_: loc_t, _: sym_t, _: s1rtpol): d1atarg

(* ****** ****** *)

typedef s1arg = '{
  s1arg_loc= loc_t, s1arg_sym= sym_t, s1arg_srt= s1rtopt
}

typedef s1arglst = List s1arg
typedef s1arglstlst = List s1arglst

typedef s1var = '{
  s1var_loc= loc_t, s1var_sym= sym_t, s1var_srt= s1rt
}

typedef s1varlst = List s1var

(* ****** ****** *)

datatype sp1at_node =
  | SP1Tcon of (s0taq, sym_t, s1arglst)

where sp1at = '{
  sp1at_loc= loc_t, sp1at_node= sp1at_node
}

(* ****** ****** *)

datatype s1exp_node =
  | S1Eann of // sort-ascribed expression
      (s1exp, s1rt)
  | S1Eany of (* omitted static expression *)
      ()
  | S1Eapp of (* static application *)
      (s1exp, loc_t(*arg*), s1explst)
  | S1Echar of (* static character *)
      char
  | S1Eexi of (* existentially quantifed expression *)
      (int(*funres*), s1qualst, s1exp)
  | S1Eextype of (* external type *)
      (string(*extname*), s1explstlst(*arglst*))
  | S1Eimp of (* annotated implication *)
      (funclo, int (*lin*), int (*prf*), efcopt)
  | S1Eint of (* static integer *)
      string
  | S1Einvar of (* invariant view or viewtype *)
      (int(*1:ref/0:val*), s1exp) (* &/!: call-by-ref/val *)
  | S1Elam of (* static abstraction *)
      (s1arglst, s1rtopt, s1exp)
(*
// HX-2010-12-04: simplification
  | S1Emod of (s0taq, sym_t, labs1explst) // module types
*)
(*
// HX-2010-12-04: inadequate design
  | S1Enamed of (* named type (for template instantiation) *)
      (sym_t, s1exp)
*)
  | S1Elist of (* static expression list: temoprary *)
      (int (*pfarity*), s1explst)
  | S1Eqid of (* (qualified) static identifier *)
      (s0taq, sym_t)
  | S1Eread of (* read-only type *)
      (s1exp(*view*), s1exp(*viewtype*))
(*
// HX-2010-11-01: simplification
  | S1Estruct of (* struct type *)
      labs1explst
*)
  | S1Etop of (*0/1: topization/typization *)
      (int(*knd*), s1exp)
  | S1Etrans of (* view or viewtype transform *)
      (s1exp, s1exp)
  | S1Etyarr of (* array type *)
      (s1exp (*element*), s1explstlst (*dimension*))
  | S1Etyrec of (* record type *)
      (int (*recknd*), labs1explst)
  | S1Etyrec_ext of (* external record type *)
      (string (*name*), labs1explst) // it is assumed to be flat
  | S1Etytup of (* tuple type *)
      (int (*tupknd*), s1explst)
  | S1Etytup2 of (* tuple type *)
      (int (*tupknd*), s1explst, s1explst)
  | S1Euni of (* universal quantified expression *)
      (s1qualst, s1exp)
  | S1Eunion of (* union type *)
      (s1exp (*index*), labs1explst)
// end of [s1exp_node]

and labs1explst =
  | LABS1EXPLSTnil | LABS1EXPLSTcons of (lab_t, s1exp, labs1explst)
// end of [labs1explst]

and tmps1explstlst =
  | TMPS1EXPLSTLSTnil
  | TMPS1EXPLSTLSTcons of (loc_t, s1explst, tmps1explstlst)
// end of [tmps1explstlst]

and wths1explst = // needed in [ats_trans2_sta.dats]
  | WTHS1EXPLSTnil
  | WTHS1EXPLSTcons_some of (int(*refval*), s1exp, wths1explst)
  | WTHS1EXPLSTcons_none of wths1explst
// end of [wths1explst]

and s1rtext_node =
  | S1TEsrt of s1rt
  | S1TEsub of (sym_t, s1rtext, s1explst)
(*
  | S1TElam of (s1arglst, s1rtext)
  | S1TEapp of (s1rtext, s1explst)
*)
// end of [s1rtext_node]

and s1qua_node =
  | S1Qprop of s1exp | S1Qvars of (i0delst, s1rtext)
// end of [s1qua_node]

where s1exp : type = '{
  s1exp_loc= loc_t, s1exp_node= s1exp_node
} // end of [s1exp]

and s1explst = List s1exp
and s1expopt = Option s1exp
and s1explstlst = List s1explst
and s1explstopt = Option s1explst

and s1rtext = '{ (* type for extended sorts *)
  s1rtext_loc= loc_t, s1rtext_node= s1rtext_node
} // end of [s1rtext]

and s1qua = '{
  s1qua_loc= loc_t, s1qua_node= s1qua_node
} // end of [s1qua]

and s1qualst = List s1qua
and s1qualstlst = List s1qualst

(* ****** ****** *)

fun fprint_s1exp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1exp): void

and fprint_s1explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1explst): void

and fprint_s1expopt {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1expopt): void

and fprint_s1explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1explstlst): void

overload fprint with fprint_s1exp
overload fprint with fprint_s1explst
overload fprint with fprint_s1expopt
overload fprint with fprint_s1explstlst

fun fprint_labs1explst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: labs1explst): void
overload fprint with fprint_labs1explst

fun fprint_tmps1explstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: tmps1explstlst): void
overload fprint with fprint_tmps1explstlst

fun fprint_s1rtext {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s1rtext): void
overload fprint with fprint_s1rtext

fun print_s1exp (_: s1exp): void
fun prerr_s1exp (_: s1exp): void

overload print with print_s1exp
overload prerr with prerr_s1exp

fun print_s1explst (_: s1explst): void
fun prerr_s1explst (_: s1explst): void

overload print with print_s1explst
overload prerr with prerr_s1explst

(* ****** ****** *)

datatype s1vararg =
  | S1VARARGone (* {..} *)
  | S1VARARGall (* {...} *)
  | S1VARARGseq of s1arglst
// end of [s1vararg]

typedef s1vararglst = List s1vararg

datatype s1exparg_node =
  | S1EXPARGone (* {..} *)
  | S1EXPARGall (* {...} *)
  | S1EXPARGseq of s1explst
// end of [s1exparg_node]

typedef s1exparg = '{
  s1exparg_loc= loc_t, s1exparg_node= s1exparg_node
}

typedef s1exparglst = List s1exparg

(* ****** ****** *)

fun s1arg_make (_: loc_t, _: sym_t, _: s1rtopt): s1arg
fun sp1at_con (_: loc_t, q: s0taq, id: sym_t, args: s1arglst): sp1at

(* ****** ****** *)

fun s1exp_ann (_: loc_t, _: s1exp, _: s1rt): s1exp
fun s1exp_any (_: loc_t): s1exp

fun s1exp_app
  (loc: loc_t, _fun: s1exp, loc_arg: loc_t, _arg: s1explst): s1exp
// end of [s1exp_app]

fun s1exp_char (_: loc_t, _: char): s1exp
fun s1exp_exi (_: loc_t, knd: int, qua: s1qualst, body: s1exp): s1exp

fun s1exp_extype (_: loc_t, name: string, arg: s1explstlst): s1exp

fun s1exp_ide (_: loc_t, _: sym_t): s1exp
fun s1exp_imp
  (_: loc_t, fc: funclo, lin: int, prf: int, _: efcopt): s1exp
fun s1exp_int (_: loc_t, int: string): s1exp
fun s1exp_invar (_: loc_t, refval: int, arg: s1exp): s1exp

fun s1exp_lam
  (_: loc_t, arg: s1arglst, res: s1rtopt, body: s1exp): s1exp
// end of [s1exp_lam]

fun s1exp_list (_: loc_t, _: s1explst): s1exp
fun s1exp_list2 (_: loc_t, _1: s1explst, _2: s1explst): s1exp

(*
// HX-2010-12-04: simplification
fun s1exp_mod (_: loc_t, q: s0taq, id: sym_t, _: labs1explst): s1exp
*)

(*
// HX-2010-12-04: inadequate design
fun s1exp_named (_: loc_t, name: sym_t, s1e: s1exp): s1exp
*)

fun s1exp_qid (_: loc_t, q: s0taq, id: sym_t): s1exp
fun s1exp_read (_: loc_t, s1e: s1exp(*list*)): s1exp

(*
// HX-2010-11-01: simplification
fun s1exp_struct (_: loc_t, _: labs1explst): s1exp
*)

fun s1exp_top (_: loc_t, knd: int, arg: s1exp): s1exp
fun s1exp_trans (_: loc_t, arg1: s1exp, arg2: s1exp): s1exp
fun s1exp_tyarr (_: loc_t, elt: s1exp, dim: s1explstlst): s1exp
fun s1exp_tyrec (_: loc_t, kind: int, _: labs1explst): s1exp
fun s1exp_tyrec_ext (_: loc_t, name: string, _: labs1explst): s1exp
fun s1exp_tytup (_: loc_t, kind: int, _: s1explst): s1exp
fun s1exp_tytup2
  (_: loc_t, kind: int, _1: s1explst, _2: s1explst): s1exp
fun s1exp_uni (_: loc_t, qua: s1qualst, body: s1exp): s1exp
fun s1exp_union (_: loc_t, ind: s1exp, _: labs1explst): s1exp

//

fun s1exparg_one (_: loc_t): s1exparg
fun s1exparg_all (_: loc_t): s1exparg
fun s1exparg_seq (_: loc_t, seq: s1explst): s1exparg

(* ****** ****** *)

fun s1rtext_srt (_: loc_t, _: s1rt): s1rtext
fun s1rtext_sub
  (_: loc_t, _: sym_t, _: s1rtext, s1ps: s1explst)
  : s1rtext

(* ****** ****** *)

fun s1qua_prop (_: loc_t, _: s1exp): s1qua
fun s1qua_vars (_: loc_t, _: i0delst, _: s1rtext): s1qua

//

fun s1exp_make_e1xp (_: loc_t, _: e1xp): s1exp

//

fun wths1explst_is_none (_: wths1explst): bool
fun wths1explst_reverse (_: wths1explst): wths1explst

(* ****** ****** *)

datatype witht1ype =
  | WITHT1YPEnone
  | WITHT1YPEprop of s1exp
  | WITHT1YPEtype of s1exp
  | WITHT1YPEview of s1exp
  | WITHT1YPEviewtype of s1exp
// end of [witht1ype]

(* ****** ****** *)

(* end of [ats_staexp1.sats] *)
