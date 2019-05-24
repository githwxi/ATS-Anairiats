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
// Time: July 2007
//
(* ****** ****** *)

(* ats_syntax: AST for source programs in ATS/Anairiats *)

(* ****** ****** *)

staload Fil = "ats_filename.sats"
typedef fil_t = $Fil.filename_t
staload Fix = "ats_fixity.sats"
typedef assoc = $Fix.assoc
staload Lab = "ats_label.sats"
typedef lab_t = $Lab.label_t
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)
//
// HX:
// Note that [t0kn] is still boxed!
//
typedef t0kn = @{ t0kn_loc= loc_t }
//
(* ****** ****** *)

datatype abskind = 
  | ABSKINDprop | ABSKINDtype | ABSKINDt0ype
  | ABSKINDview | ABSKINDviewtype | ABSKINDviewt0ype
// end of [abskind]

fun abskind_prop ():<> abskind = "abskind_prop"
fun abskind_type ():<> abskind = "abskind_type"
fun abskind_t0ype ():<> abskind = "abskind_t0ype"
fun abskind_view ():<> abskind = "abskind_view"
fun abskind_viewtype ():<> abskind = "abskind_viewtype"
fun abskind_viewt0ype ():<> abskind = "abskind_viewt0ype"

(* ****** ****** *)

datatype dcstkind =
  | DCSTKINDfun | DCSTKINDval | DCSTKINDcastfn
  | DCSTKINDpraxi | DCSTKINDprfun | DCSTKINDprval
// end of [dcstkind]

fun dcstkind_fun ():<> dcstkind = "dcstkind_fun"
fun dcstkind_val ():<> dcstkind = "dcstkind_val"
fun dcstkind_castfn ():<> dcstkind = "dcstkind_castfn"
fun dcstkind_praxi ():<> dcstkind = "dcstkind_praxi"
fun dcstkind_prfun ():<> dcstkind = "dcstkind_prfun"
fun dcstkind_prval ():<> dcstkind = "dcstkind_prval"

fun dcstkind_is_fun (dck: dcstkind):<> bool
fun dcstkind_is_castfn (dck: dcstkind):<> bool
fun dcstkind_is_praxi (dck: dcstkind):<> bool
fun dcstkind_is_prfun (dck: dcstkind):<> bool
fun dcstkind_is_prval (dck: dcstkind):<> bool
fun dcstkind_is_proof (dck: dcstkind):<> bool

fun fprint_dcstkind (out: FILEref, knd: dcstkind): void

(* ****** ****** *)

datatype datakind =
  | DATAKINDprop | DATAKINDtype | DATAKINDview | DATAKINDviewtype
// end of [datakind]

fun datakind_prop ():<> datakind = "datakind_prop"
and datakind_type ():<> datakind = "datakind_type"
and datakind_view ():<> datakind = "datakind_view"
and datakind_viewtype ():<> datakind = "datakind_viewtype"

fun datakind_is_proof (dtk: datakind):<> bool

(* ****** ****** *)

datatype stadefkind =
  | STADEFKINDgeneric
  | STADEFKINDprop of t0kn
  | STADEFKINDtype of t0kn
  | STADEFKINDview of t0kn
  | STADEFKINDviewtype of t0kn
// end of [stadefkind]

fun stadefkind_generic ():<> stadefkind = "stadefkind_generic"
and stadefkind_prop (_: t0kn):<> stadefkind = "stadefkind_prop"
and stadefkind_type (_: t0kn):<> stadefkind = "stadefkind_type"
and stadefkind_view (_: t0kn):<> stadefkind = "stadefkind_view"
and stadefkind_viewtype (_: t0kn):<> stadefkind = "stadefkind_viewtype"

(* ****** ****** *)

(*
// HX-2010-05-12: the OOP plan is permanently abandoned
datatype clskind =
  | CLSKINDmod of t0kn | CLSKINDobj of t0kn
// end of [clskind]
fun clskind_mod (_: t0kn):<> clskind = "clskind_mod"
fun clskind_obj (_: t0kn):<> clskind = "clskind_obj"
*)

(* ****** ****** *)

(*
// HX-2010-05-12: the OOP plan is permanently abandoned
datatype objkind =
  | OBJKINDobj_t of t0kn
  | OBJKINDobj_vt of t0kn
  | OBJKINDobjmod of t0kn
// end of [objkind]
fun objkind_obj_t (_: t0kn):<> objkind = "objkind_obj_t"
fun objkind_obj_vt (_: t0kn):<> objkind = "objkind_obj_vt"
fun objkind_objmod (_: t0kn):<> objkind = "objkind_objmod"
*)

(* ****** ****** *)

datatype valkind =
  | VALKINDval | VALKINDvalminus | VALKINDvalplus | VALKINDprval
// end of [valkind]

fun valkind_val ():<> valkind = "valkind_val"
fun valkind_valminus ():<> valkind = "valkind_valminus"
fun valkind_valplus ():<> valkind = "valkind_valplus"
fun valkind_prval ():<> valkind = "valkind_prval"

fun valkind_is_proof (vk: valkind):<> bool

datatype funkind =
  | FUNKINDfn | FUNKINDfnstar | FUNKINDfun
  | FUNKINDprfn | FUNKINDprfun | FUNKINDcastfn
// end of [funkind]

fun funkind_fn ():<> funkind = "funkind_fn"
fun funkind_fnstar ():<> funkind = "funkind_fnstar"
fun funkind_fun ():<> funkind = "funkind_fun"
fun funkind_castfn ():<> funkind = "funkind_castfn"
fun funkind_prfn ():<> funkind = "funkind_prfn"
fun funkind_prfun ():<> funkind = "funkind_prfun"

fun funkind_is_proof (_: funkind):<> bool // proof
fun funkind_is_recursive (_: funkind):<> bool // recursive
fun funkind_is_tailrecur (_: funkind):<> bool // tail-recursive

(* ****** ****** *)

datatype macsynkind =
  | MACSYNKINDcross  // decode(lift(.))
  | MACSYNKINDdecode
  | MACSYNKINDencode
// end of [macsynkind]

(* ****** ****** *)

datatype lamkind =
  | LAMKINDlam of (t0kn)
  | LAMKINDatlam of (t0kn)
  | LAMKINDllam of (t0kn)
  | LAMKINDatllam of (t0kn)
  | LAMKINDfix of (t0kn)
  | LAMKINDatfix of (t0kn)
  | LAMKINDifix of (loc_t) // HX: implicit FIX
// end of [lamkind]
fun lamkind_lam (t: t0kn): lamkind = "lamkind_lam"
and lamkind_atlam (t: t0kn): lamkind = "lamkind_atlam"
and lamkind_llam (t: t0kn): lamkind = "lamkind_llam"
and lamkind_atllam (t: t0kn): lamkind = "lamkind_atllam"

typedef fixkind = lamkind
fun fixkind_fix (t: t0kn): fixkind = "fixkind_fix"
fun fixkind_atfix (t: t0kn): fixkind = "fixkind_atfix"

(* ****** ****** *)

datatype srpifkind =
  | SRPIFKINDif | SRPIFKINDifdef | SRPIFKINDifndef
// end of [srpifkind]

fun srpifkind_if (): srpifkind = "srpifkind_if"
and srpifkind_ifdef (): srpifkind = "srpifkind_ifdef"
and srpifkind_ifndef (): srpifkind = "srpifkind_ifndef"

datatype srpifkindtok = SRPIFKINDTOK of (srpifkind, t0kn)

fun srpifkindtok_if (t: t0kn): srpifkindtok = "srpifkindtok_if"
and srpifkindtok_ifdef (t: t0kn): srpifkindtok = "srpifkindtok_ifdef"
and srpifkindtok_ifndef (t: t0kn): srpifkindtok = "srpifkindtok_ifndef"

(* ****** ****** *)

datatype cstsp = // special constants
  | CSTSPfilename (* the filename where #FILENAME appears *)
  | CSTSPlocation (* the location where #LOCATION appears *)
(*
  | CSTSPcharcount of int
  | CSTSPlinecount of int
*)
// end of [cstsp]

fun fprint_cstsp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: cstsp): void
overload fprint with fprint_cstsp

(* ****** ****** *)

typedef c0har = '{
  c0har_loc= loc_t, c0har_val= char
} // end of [c0har]

typedef e0xtcode = '{
  e0xtcode_loc= loc_t, e0xtcode_pos= int, e0xtcode_cod= string
} // end of [e0xtcode]

typedef f0loat = '{
  f0loat_loc= loc_t, f0loat_val= string
}

typedef f0loatsp = '{
  f0loatsp_loc= loc_t, f0loatsp_val= string
}

typedef i0nt = '{
  i0nt_loc= loc_t, i0nt_val= string
}

typedef i0ntsp = '{
  i0ntsp_loc= loc_t, i0ntsp_val= string
}

typedef s0tring = '{
  s0tring_loc= loc_t, s0tring_val= string, s0tring_len= int
}

(* ****** ****** *)

fun c0har_make (_: loc_t, _: char): c0har = "c0har_make"
fun e0xtcode_make (_: loc_t, pos: int, code: string): e0xtcode
  = "e0xtcode_make"
fun f0loat_make (_: loc_t, _: string): f0loat = "f0loat_make"
fun f0loatsp_make (_: loc_t, _: string): f0loatsp = "f0loatsp_make"
fun i0nt_make (_: loc_t, _: string): i0nt = "i0nt_make"
fun i0ntsp_make (_: loc_t, _: string): i0ntsp = "i0ntsp_make"
fun s0tring_make (_: loc_t, _: string, _: int): s0tring = "s0tring_make"
fun t0kn_make (_: loc_t): t0kn = "t0kn_make"

(* ****** ****** *)

typedef i0de = '{
  i0de_loc= loc_t, i0de_sym= sym_t
} // end of [i0de]
typedef i0dext = i0de

typedef i0delst = List i0de
typedef i0delstlst = List i0delst

typedef i0deopt = Option i0de

fun fprint_i0de {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: i0de): void
overload fprint with fprint_i0de

fun print_i0de (_: i0de): void
fun prerr_i0de (_: i0de): void

fun fprint_i0delst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: i0delst): void
overload fprint with fprint_i0delst

(* ****** ****** *)

fun i0de_make (_: loc_t, _: string): i0de = "i0de_make"
fun i0de_make_ampersand (t: t0kn): i0de = "i0de_make_ampersand"
fun i0de_make_backslash (t: t0kn): i0de = "i0de_make_backslash"
fun i0de_make_bang (t: t0kn): i0de = "i0de_make_bang"
fun i0de_make_eq (t: t0kn): i0de = "i0de_make_eq"
fun i0de_make_gt (t: t0kn): i0de = "i0de_make_gt"
fun i0de_make_gtlt (t: t0kn): i0de = "i0de_make_gtlt"
fun i0de_make_lt (t: t0kn): i0de = "i0de_make_lt"
fun i0de_make_minusgt (t: t0kn): i0de = "i0de_make_minusgt"
fun i0de_make_minusltgt (t: t0kn): i0de = "i0de_make_minusltgt"
fun i0de_make_r0ead (t: t0kn): i0de = "i0de_make_r0ead"
fun i0de_make_tilde (t: t0kn): i0de = "i0de_make_tilde"
fun i0de_make_t0ype (t: t0kn): i0de = "i0de_make_t0ype"
fun i0de_make_viewt0ype (t: t0kn): i0de = "i0de_make_viewt0ype"

//

fun i0de_make_lrbrackets
  (t_l: t0kn, t_r: t0kn): i0de = "i0de_make_lrbrackets"
// end of [i0de_make_lrbrackets]

//

fun i0de_make_DO (t: t0kn): i0de = "i0de_make_DO"
fun i0de_make_IN (t: t0kn): i0de = "i0de_make_IN"
fun i0de_make_WHILE (t: t0kn): i0de = "i0de_make_WHILE"

(* ****** ****** *)

fun i0delst_nil (): i0delst = "i0delst_nil"
fun i0delst_sing (x: i0de): i0delst = "i0delst_sing"
fun i0delst_cons (x: i0de, xs: i0delst): i0delst = "i0delst_cons"

fun i0delstlst_nil (): i0delstlst = "i0delstlst_nil"
fun i0delstlst_cons
  (x: i0delst, xs: i0delstlst): i0delstlst = "i0delstlst_cons"
// end of [i0delstlst_cons]

(* ****** ****** *)

typedef l0ab = '{
  l0ab_loc= loc_t, l0ab_lab= lab_t
} // end of [l0ab]

fun l0ab_ide (ide: i0de): l0ab = "l0ab_ide"
fun l0ab_int (int: i0nt): l0ab = "l0ab_int"

(* ****** ****** *)

fun stai0de_make (ide: i0de): i0de = "stai0de_make"

(* ****** ****** *)

datatype p0rec =
  | P0RECint of int
  | P0RECide of i0de
  | P0RECinc of (i0de, int)
  | P0RECdec of (i0de, int)
// end of [p0rec]

fun p0rec_emp (): p0rec = "p0rec_emp"
fun p0rec_ide (ide: i0de): p0rec = "p0rec_ide"
fun p0rec_int (int: i0nt): p0rec = "p0rec_int"
fun p0rec_opr (ide: i0de, opr: i0de, int: i0nt): p0rec = "p0rec_opr"

(* ****** ****** *)
//
// HX: assumed in [ats_effect.dats]
//
abst@ype effect_t = int
//
typedef effectlst = List (effect_t)
//
(* ****** ****** *)

datatype e0xp_node =
  | E0XPapp of (e0xp, e0xp)
  | E0XPchar of char
  | E0XPeval of e0xp
  | E0XPfloat of string
  | E0XPide of sym_t
  | E0XPint of string
  | E0XPlist of e0xplst
  | E0XPstring of (string, int(*length*))
  | E0XPcstsp of cstsp // for special constants
// end of [e0xp_node]

where e0xp = '{
  e0xp_loc= loc_t, e0xp_node= e0xp_node
} // end of [e0xp]

and e0xplst: type = List e0xp
and e0xpopt: type = Option e0xp

(* ****** ****** *)

fun e0xplst_nil (): e0xplst = "e0xplst_nil"
fun e0xplst_cons (x: e0xp, xs: e0xplst): e0xplst = "e0xplst_cons"

fun e0xpopt_none (): e0xpopt = "e0xpopt_none"
fun e0xpopt_some (x: e0xp): e0xpopt = "e0xpopt_some"

(* ****** ****** *)

fun e0xp_app (_fun: e0xp, _arg: e0xp): e0xp = "e0xp_app"
fun e0xp_char (_: c0har): e0xp = "e0xp_char"

fun e0xp_eval
  (t_beg: t0kn, e: e0xp, t_end: t0kn): e0xp = "e0xp_eval"
// end of [e0xp_eval]

fun e0xp_float (_: f0loat): e0xp = "e0xp_float"
fun e0xp_ide (_: i0de): e0xp = "e0xp_ide"
fun e0xp_int (_: i0nt): e0xp = "e0xp_int"

fun e0xp_list
  (t_beg: t0kn, es: e0xplst, t_end: t0kn): e0xp = "e0xp_list"
// end of [e0xp_list]

fun e0xp_string (s: s0tring): e0xp = "e0xp_string"

fun e0xp_FILENAME (tok: t0kn): e0xp = "e0xp_FILENAME"
fun e0xp_LOCATION (tok: t0kn): e0xp = "e0xp_LOCATION"

(* ****** ****** *)
//
// HX: sort qualifier
//
datatype s0rtq_node =
  | S0RTQnone
  | S0RTQstr of string (* filename *)
  | S0RTQsym of sym_t (* fileid *)
// end of [s0rtq_node]

typedef s0rtq = '{
  s0rtq_loc= loc_t, s0rtq_node= s0rtq_node
} // end of [s0rtq]

fun fprint_s0rtq {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s0rtq): void
overload fprint with fprint_s0rtq

fun print_s0rtq (_: s0rtq): void
fun prerr_s0rtq (_: s0rtq): void

fun s0rtq_none (): s0rtq = "s0rtq_none"
fun s0rtq_str (_: s0tring): s0rtq = "s0rtq_str"
fun s0rtq_sym (_: i0de): s0rtq = "s0rtq_sym"

(* ****** ****** *)

datatype s0rt_node =
  | S0RTapp of (s0rt, s0rt)
  | S0RTide of sym_t (* sort identifier *)
  | S0RTqid of (s0rtq, sym_t) (* qualified sort identifier *)
  | S0RTlist of s0rtlst
  | S0RTtup of s0rtlst
// end of [s0rt_node]

where s0rt = '{ 
  s0rt_loc= loc_t, s0rt_node= s0rt_node
} // end of [s0rt]

and s0rtlst: type = List s0rt
and s0rtopt: type = Option s0rt

(* sorts with polarity *)
typedef s0rtpol = '{
  s0rtpol_loc= loc_t, s0rtpol_srt= s0rt, s0rtpol_pol= int
} // end of [s0rtpol]

(* ****** ****** *)

fun fprint_s0rt {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, s0t: s0rt
) : void = "fprint_s0rt" // end of [fprint_s0rt]

(* ****** ****** *)

fun s0rtlst_nil (): s0rtlst = "s0rtlst_nil"
fun s0rtlst_cons (x: s0rt, xs: s0rtlst): s0rtlst = "s0rtlst_cons"

fun s0rtopt_none (): s0rtopt = "s0rtopt_none"
fun s0rtopt_some (x: s0rt): s0rtopt = "s0rtopt_some"

(* ****** ****** *)

fun s0rt_prop (t: t0kn): s0rt = "s0rt_prop"
fun s0rt_type (t: t0kn): s0rt = "s0rt_type"
fun s0rt_t0ype (t: t0kn): s0rt = "s0rt_t0ype"
fun s0rt_view (t: t0kn): s0rt = "s0rt_view"
fun s0rt_viewtype (t: t0kn): s0rt = "s0rt_viewtype"
fun s0rt_viewt0ype (t: t0kn): s0rt = "s0rt_viewt0ype"

//

fun s0rt_app
  (_fun: s0rt, _arg: s0rt): s0rt = "s0rt_app"

fun s0rt_ide (_: i0de): s0rt = "s0rt_ide"

fun s0rt_qid (q: s0rtq, id: i0de): s0rt = "s0rt_qid"

fun s0rt_list
  (t_beg: t0kn, _: s0rtlst, t_end: t0kn): s0rt = "s0rt_list"
// end of [s0rt_list]

fun s0rt_tup (
  t_beg: t0kn, _: s0rtlst, t_end: t0kn
) : s0rt = "s0rt_tup" // end of [s0rt_tup]

fun s0rtpol_make (s0t: s0rt, pol: int): s0rtpol = "s0rtpol_make"

(* ****** ****** *)

typedef d0atsrtcon = '{
  d0atsrtcon_loc= loc_t
, d0atsrtcon_sym= sym_t
, d0atsrtcon_arg= s0rtopt
} // end of [d0atsrtcon]

fun d0atsrtcon_make_none
  (id: i0de): d0atsrtcon = "d0atsrtcon_make_none"
fun d0atsrtcon_make_some
  (id: i0de, s0t: s0rt): d0atsrtcon = "d0atsrtcon_make_some"

typedef d0atsrtconlst = List d0atsrtcon

fun d0atsrtconlst_nil (): d0atsrtconlst = "d0atsrtconlst_nil"
fun d0atsrtconlst_cons
  (x: d0atsrtcon, xs: d0atsrtconlst): d0atsrtconlst = "d0atsrtconlst_cons"
// end of [d0atsrtconlst_cons]

(* ****** ****** *)

typedef d0atsrtdec = '{
  d0atsrtdec_loc= loc_t
, d0atsrtdec_sym= sym_t
, d0atsrtdec_con= d0atsrtconlst
} // end of [d0atsrtdec]

typedef d0atsrtdeclst = List d0atsrtdec

fun d0atsrtdec_make
  (id: i0de, xs: d0atsrtconlst): d0atsrtdec = "d0atsrtdec_make"
// end of [d0atsrtdec_make]

fun d0atsrtdeclst_nil (): d0atsrtdeclst = "d0atsrtdeclst_nil"
fun d0atsrtdeclst_cons
  (x: d0atsrtdec, xs: d0atsrtdeclst): d0atsrtdeclst = "d0atsrtdeclst_cons"
// end of [d0atsrtdeclst_cons]

(* ****** ****** *)

datatype funclo = (* function or closure *)
  | FUNCLOclo of int(*knd*) (* ATS closure: knd=1/0/~1: ptr/clo/ref *)
  | FUNCLOfun (* ATS function *)
typedef funcloopt = Option funclo

fun fprint_funclo {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: funclo): void
overload fprint with fprint_funclo

fun print_funclo (_: funclo): void
fun prerr_funclo (_: funclo): void

fun eq_funclo_funclo (fc1: funclo, fc2: funclo): bool 
overload = with eq_funclo_funclo

(* ****** ****** *)

datatype e0fftag_node =
  | E0FFTAGcst of (int(*neg*), string) // [0/1]: pos/neg
  | E0FFTAGvar of i0de
  | E0FFTAGprf
  | E0FFTAGlin of int(*non/lin*)
  | E0FFTAGfun of (
      int(*non/lin*), int(*nil/all*)
    ) // E0FFTAGfun
  | E0FFTAGclo of (
      int(*non/lin*), int(*1/~1:ptr/ref*), int(*nil/all*)
    ) // E0FFTAGclo
// end of [e0fftag_node]

typedef e0fftag = '{
  e0fftag_loc= loc_t, e0fftag_node= e0fftag_node
} // end of [e0fftag]

fun e0fftag_cst (i: int, _: i0de): e0fftag = "e0fftag_cst"
fun e0fftag_var (_: i0de): e0fftag = "e0fftag_var"
fun e0fftag_var_fun (t_fun: t0kn): e0fftag = "e0fftag_var_fun"
fun e0fftag_int (_: i0nt): e0fftag = "e0fftag_int"

typedef e0fftaglst = List e0fftag

fun e0fftaglst_nil (): e0fftaglst = "e0fftaglst_nil"
fun e0fftaglst_cons (x: e0fftag, xs: e0fftaglst): e0fftaglst
  = "e0fftaglst_cons"

typedef e0fftaglstopt = Option e0fftaglst

fun e0fftaglstopt_none (): e0fftaglstopt
  = "e0fftaglstopt_none"
fun e0fftaglstopt_some (x: e0fftaglst): e0fftaglstopt
  = "e0fftaglstopt_some"

(* ****** ****** *)

datatype s0taq_node =
  | S0TAQnone
  | S0TAQfildot of string (* filename *)
  | S0TAQsymcolon of sym_t
  | S0TAQsymdot of sym_t
// end of [s0taq_node]

typedef s0taq = '{ s0taq_loc= loc_t, s0taq_node= s0taq_node }

//

fun fprint_s0taq {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: s0taq): void
overload fprint with fprint_s0taq

fun print_s0taq (_: s0taq): void
fun prerr_s0taq (_: s0taq): void

//

fun s0taq_make (loc: loc_t, node: s0taq_node): s0taq
fun s0taq_none (): s0taq = "s0taq_none"
fun s0taq_fildot (name: s0tring): s0taq = "s0taq_fildot"
fun s0taq_symcolon (id: i0de): s0taq = "s0taq_symcolon"
fun s0taq_symdot (id: i0de): s0taq = "s0taq_symdot"

(* ****** ****** *)

datatype d0ynq_node =
  | D0YNQnone
  | D0YNQfildot of string (* filename *)
  | D0YNQfildot_symcolon of (string (* filename *), sym_t)
  | D0YNQsymcolon of sym_t
  | D0YNQsymdot of sym_t
  | D0YNQsymdot_symcolon of (sym_t, sym_t)
// end of [d0ynq_node]

typedef d0ynq = '{
  d0ynq_loc= loc_t, d0ynq_node= d0ynq_node
} // end of [d0ynq]

typedef d0ynqopt = Option d0ynq

//

fun fprint_d0ynq {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, q: d0ynq): void
overload fprint with fprint_d0ynq
fun print_d0ynq (q: d0ynq): void
overload print with print_d0ynq
fun prerr_d0ynq (q: d0ynq): void
overload prerr with prerr_d0ynq

//

fun d0ynq_none (): d0ynq = "d0ynq_none"
fun d0ynq_fildot (name: s0tring): d0ynq = "d0ynq_fildot"
fun d0ynq_fildot_symcolon (name: s0tring, id: i0de): d0ynq
  = "d0ynq_fildot_symcolon"
fun d0ynq_symcolon (id: i0de): d0ynq = "d0ynq_symcolon"
fun d0ynq_symdot (id: i0de): d0ynq = "d0ynq_symdot"
fun d0ynq_symdot_symcolon (id_dot: i0de, id_colon: i0de): d0ynq
  = "d0ynq_symdot_symcolon"
// end of [d0ynq_symdot_symcolon]

(* ****** ****** *)

(* qualified static identifiers *)

typedef sqi0de = '{
  sqi0de_loc= loc_t, sqi0de_qua= s0taq, sqi0de_sym= sym_t
} // end of [sqi0de]

fun sqi0de_make_none (id: i0de): sqi0de = "sqi0de_make_none"
fun sqi0de_make_some (q: s0taq, id: i0de): sqi0de = "sqi0de_make_some"

(* ****** ****** *)

(* qualified dynamic identifiers *)

typedef dqi0de = '{
  dqi0de_loc= loc_t, dqi0de_qua= d0ynq, dqi0de_sym= sym_t
} // end of [dqi0de]

fun dqi0de_make_none (id: i0de): dqi0de = "dqi0de_make_none"
fun dqi0de_make_some (q: d0ynq, id: i0de): dqi0de = "dqi0de_make_some"

(* ****** ****** *)

typedef arrqi0de = '{
  arrqi0de_loc= loc_t, arrqi0de_qua= d0ynq, arrqi0de_sym= sym_t
} // end of [arrqi0de]

fun arrqi0de_make_none (id: i0de): arrqi0de =
  "arrqi0de_make_none"
fun arrqi0de_make_some (q: d0ynq, id: i0de): arrqi0de =
  "arrqi0de_make_some"

(* ****** ****** *)

typedef tmpqi0de = '{
  tmpqi0de_loc= loc_t, tmpqi0de_qua= d0ynq, tmpqi0de_sym= sym_t
} // end of [tmpqi0de]

fun tmpqi0de_make_none
  (id: i0de): tmpqi0de = "tmpqi0de_make_none"
// end of [tmpqi0de_make_none]

fun tmpqi0de_make_some
  (q: d0ynq, id: i0de): tmpqi0de = "tmpqi0de_make_some"
// end of [tmpqi0de_make_some]

(* ****** ****** *)

datatype d0atarg_node =
  | D0ATARGsrt of s0rtpol | D0ATARGidsrt of (sym_t, s0rtpol)

typedef d0atarg = '{
  d0atarg_loc= loc_t, d0atarg_node= d0atarg_node
}

fun d0atarg_srt (_: s0rtpol): d0atarg = "d0atarg_srt"
fun d0atarg_id_srt (_: i0de, _: s0rtpol): d0atarg = "d0atarg_id_srt"

typedef d0atarglst = List d0atarg
typedef d0atarglstopt = Option d0atarglst

fun d0atarglst_nil (): d0atarglst = "d0atarglst_nil"
fun d0atarglst_cons (x: d0atarg, xs: d0atarglst): d0atarglst
  = "d0atarglst_cons"

fun d0atarglstopt_none (): d0atarglstopt
  = "d0atarglstopt_none"
fun d0atarglstopt_some (x: d0atarglst): d0atarglstopt
  = "d0atarglstopt_some"

(* ****** ****** *)

typedef s0arg = '{
  s0arg_loc= loc_t, s0arg_sym= sym_t, s0arg_srt= s0rtopt
}

fun s0arg_make (id: i0de, _: s0rtopt): s0arg = "s0arg_make"
fun s0arg_make_none (id: i0de): s0arg = "s0arg_make_none"

typedef s0arglst = List s0arg

fun s0arglst_nil (): s0arglst = "s0arglst_nil"
fun s0arglst_cons (x: s0arg, xs: s0arglst): s0arglst
  = "s0arglst_cons"
fun s0arglst_sing_id (id: i0de): s0arglst = "s0arglst_sing_id"

typedef s0arglstlst = List s0arglst

fun s0arglstlst_nil (): s0arglstlst = "s0arglstlst_nil"
fun s0arglstlst_cons (x: s0arglst, xs: s0arglstlst): s0arglstlst
  = "s0arglstlst_cons"
fun s0arglstlst_cons_ide (id: i0de, xs: s0arglstlst): s0arglstlst
  = "s0arglstlst_cons_ide"

(* ****** ****** *)

datatype sp0at_node =
  | SP0Tcon of (sqi0de, s0arglst)
// end of [sp0at_node]

where sp0at = '{
  sp0at_loc= loc_t, sp0at_node= sp0at_node
} // end of [sp0at]

fun sp0at_con
  (qid: sqi0de, xs: s0arglst, t_end: t0kn): sp0at = "sp0at_con"
// end of [sp0at_con]

(* ****** ****** *)

datatype s0exp_node = 
  | S0Eann of (* ascribed static expression *)
      (s0exp, s0rt)
  | S0Eapp of (* static application *)
      (s0exp, s0exp)
  | S0Echar of (* static character *)
      char
  | S0Eexi of (* existentially quantified type *)
      (int(*funres*), s0qualst)
  | S0Eextype of (* external type *)
      (string(*name*), s0explst(*arglst*))
  | S0Eide of (* static identifier *)
      sym_t
  | S0Eimp of (* decorated implication *)
      e0fftaglst
  | S0Eint of (* static integer *)
      string
  | S0Elam of (* static lambda abstraction *)
      (s0arglst, s0rtopt, s0exp)
  | S0Elist of (* static expression list *)
      s0explst
  | S0Elist2 of (* static expression list *)
      (s0explst (*prop/view*), s0explst (*type/viewtype*))
  | S0Emod of (* module type *)
      (s0taq, sym_t, labs0explst)
(*
// HX-2010-12-04: inadequate design
  | S0Enamed of (sym_t, s0exp) // named types
*)
  | S0Eopide of (* noninfix static identifier *)
      sym_t
  | S0Eqid of (* qualified static identifier *)
      (s0taq, sym_t)
(*
// HX-2010-11-01: simplification
  | S0Estruct of (* struct type *)
      labs0explst 
*)
  | S0Etyarr of (* array type *)
      (s0exp (*element*), s0explstlst (*dimension*))
  | S0Etyrec of (* record type *)
      (int (*flat*), labs0explst)
  | S0Etyrec_ext of (* external tyrec *)
      (string, labs0explst) // it is assumed to be flat
  | S0Etytup of (* tuple type *)
      (int (*flat*), s0explst)
  | S0Etytup2 of (* tuple type *)
      (int (*flat*), s0explst (*prop/view*), s0explst (*type/viewtype*))
  | S0Euni of (* universally quantified type *)
      s0qualst
  | S0Eunion of (* union type *)
      (s0exp (*index*), labs0explst (*body*))
// end of [s0exp_node]

and s0expext = S0EXT of (t0kn, s0tring(*name*), s0explst)

and s0rtext_node =
  | S0TEsrt of s0rt | S0TEsub of (i0de, s0rtext, s0exp, s0explst)
// end of [s0rtext_node]

and s0qua_node =
  | S0QUAprop of s0exp (* e.g., n >= i+j *)
  | S0QUAvars of (i0de, i0delst, s0rtext) (* e.g., a1,a2: type *)
// end of [s0qua_node]

and labs0explst =
  | LABS0EXPLSTnil
  | LABS0EXPLSTcons of (l0ab, s0exp, labs0explst)
// end of [labs0explst]

and t1mps0explstlst =
  | T1MPS0EXPLSTLSTnil
  | T1MPS0EXPLSTLSTcons of (loc_t, s0explst, t1mps0explstlst)
// end of [t1mps0explstlst]

where s0exp = '{
  s0exp_loc= loc_t, s0exp_node= s0exp_node
} // end of [s0exp]

and s0explst: type = List s0exp
and s0expopt: type = Option s0exp
and s0explstlst: type = List s0explst
and s0explstopt: type = Option s0explst

and s0arrind = '{
  s0arrind_loc= loc_t, s0arrind_ind= s0explstlst
}

and s0rtext = '{ (* extended sorts *)
  s0rtext_loc= loc_t, s0rtext_node= s0rtext_node
}

and s0qua = '{ s0qua_loc= loc_t, s0qua_node= s0qua_node }

and s0qualst = List s0qua

typedef s0qualstlst = List s0qualst
typedef s0qualstopt = Option s0qualst

(* ****** ****** *)

fun s0exp_ann (_: s0exp, _: s0rt): s0exp = "s0exp_ann"

fun s0exp_app (_fun: s0exp, _arg: s0exp): s0exp = "s0exp_app"

fun s0exp_char (_: c0har): s0exp = "s0exp_char"

fun s0exp_exi
  (t_beg: t0kn, knd: int, qua: s0qualst, t_end: t0kn): s0exp
  = "s0exp_exi"
// end of [s0exp_exi]

fun s0expext_nam
  (t: t0kn, name: s0tring): s0expext = "s0expext_nam"
fun s0expext_app
  (s0ext: s0expext, arg: s0exp): s0expext = "s0expext_app" 
fun s0exp_extern (s0ext: s0expext): s0exp = "s0exp_extern"

fun s0exp_imp
  (t_beg: t0kn, _: e0fftaglst, t_end: t0kn): s0exp = "s0exp_imp"
// end of [s0exp_imp]
fun s0exp_imp_emp (t: t0kn): s0exp = "s0exp_imp_emp"

fun s0exp_ide (_: i0de): s0exp = "s0exp_ide"

fun s0exp_int (_: i0nt): s0exp = "s0exp_int"

//
// HX: for reporting misuse of specified integers in statics
//
fun s0exp_intsp_err (_: i0nt): s0exp = "s0exp_intsp_err"

fun s0exp_lams (t: t0kn, arg: s0arglstlst, res: s0rtopt, body: s0exp): s0exp
  = "s0exp_lams"

(* ****** ****** *)

fun s0exp_list (t_beg: t0kn, _: s0explst, t_end: t0kn): s0exp
  = "s0exp_list"

fun s0exp_list2
   (t_beg: t0kn, _1: s0explst, _2: s0explst, t_end: t0kn): s0exp
  = "s0exp_list2"

(* ****** ****** *)

(*
// HX-2010-12-04: inadequate design
fun s0exp_named
  (ide: i0de, s0e: s0exp): s0exp = "s0exp_named"
*)

(* ****** ****** *)

fun s0exp_opide (t_op: t0kn, id: i0de): s0exp = "s0exp_opide"

fun s0exp_qid (q: s0taq, id: i0de): s0exp = "s0exp_qid"

(*
// HX-2010-11-01: simplification
fun s0exp_struct (
  t_struct: t0kn, _: labs0explst, t_end: t0kn
) : s0exp = "s0exp_struct"
*)

fun s0exp_tyarr (t_beg: t0kn, elt: s0exp, ind: s0arrind): s0exp
  = "s0exp_tyarr"

fun s0exp_tyrec
  (kind: int, t_beg: t0kn, _: labs0explst, t_end: t0kn): s0exp
  = "s0exp_tyrec"

fun s0exp_tyrec_ext // external record
  (t_beg: t0kn, ext: s0tring, _: labs0explst, t_end: t0kn): s0exp
  = "s0exp_tyrec_ext"

fun s0exp_tytup
  (kind: int, t_beg: t0kn, _: s0explst, t_end: t0kn): s0exp
  = "s0exp_tytup"
fun s0exp_tytup2
  (kind: int, t_beg: t0kn, _1: s0explst, _2: s0explst, t_end: t0kn): s0exp
  = "s0exp_tytup2"

fun s0exp_uni (t_beg: t0kn, qua: s0qualst, t_end: t0kn): s0exp
  = "s0exp_uni"

fun s0exp_union (
  t_union: t0kn, ind: s0exp, _: labs0explst, t_end: t0kn
) : s0exp = "s0exp_union"

(* ****** ****** *)

fun s0explst_nil (): s0explst = "s0explst_nil"
fun s0explst_cons (x: s0exp, xs: s0explst): s0explst = "s0explst_cons"

fun s0expopt_none (): s0expopt = "s0expopt_none"
fun s0expopt_some (x: s0exp): s0expopt = "s0expopt_some"

fun s0explstlst_nil (): s0explstlst = "s0explstlst_nil"
fun s0explstlst_cons (x: s0explst, xs: s0explstlst): s0explstlst
  = "s0explstlst_cons"

fun s0explstopt_none (): s0explstopt = "s0explstopt_none"
fun s0explstopt_some (x: s0explst): s0explstopt = "s0explstopt_some"

//

fun labs0explst_nil (): labs0explst = "labs0explst_nil"
fun labs0explst_cons (_: l0ab, _: s0exp, _: labs0explst): labs0explst
  = "labs0explst_cons"

//

fun s0arrind_make_sing (ind: s0explst, t_rbracket: t0kn): s0arrind
  = "s0arrind_make_sing"
fun s0arrind_make_cons (ind: s0explst, indlst: s0arrind): s0arrind
  = "s0arrind_make_cons"

//

fun gtlt_t1mps0expseqseq_nil (): t1mps0explstlst
  = "gtlt_t1mps0expseqseq_nil"

fun gtlt_t1mps0expseqseq_cons_tok
  (_: t0kn, _: s0explst, _: t1mps0explstlst): t1mps0explstlst
  = "gtlt_t1mps0expseqseq_cons_tok"

//

fun s0rtext_srt (_: s0rt): s0rtext = "s0rtext_srt"
fun s0rtext_sub
  (t_beg: t0kn, id: i0de, _: s0rtext, _fst: s0exp, _rst: s0explst, t_end: t0kn)
  : s0rtext
  = "s0rtext_sub"

//

fun s0qua_prop (_: s0exp): s0qua = "s0qua_prop"
fun s0qua_vars (_fst: i0de, _rst: i0delst, _: s0rtext): s0qua
  = "s0qua_vars"

fun s0qualst_nil (): s0qualst = "s0qualst_nil"
fun s0qualst_cons (x: s0qua, xs: s0qualst): s0qualst = "s0qualst_cons"

fun s0qualstlst_nil (): s0qualstlst = "s0qualstlst_nil"
fun s0qualstlst_cons (x: s0qualst, xs: s0qualstlst): s0qualstlst
  = "s0qualstlst_cons"

fun s0qualstopt_none (): s0qualstopt = "s0qualstopt_none"
fun s0qualstopt_some (x: s0qualst): s0qualstopt = "s0qualstopt_some"

(* ****** ****** *)

typedef
impqi0de = '{
  impqi0de_loc= loc_t
, impqi0de_qua= d0ynq
, impqi0de_sym= sym_t
, impqi0de_arg= t1mps0explstlst
} // end of [impqi0de]

fun impqi0de_make_none
  (qid: dqi0de): impqi0de = "impqi0de_make_none"
// end of [impqi0de_make_none]

fun impqi0de_make_some (
    qid: tmpqi0de, arg: s0explst, args: t1mps0explstlst, t_gt: t0kn
  ) : impqi0de = "impqi0de_make_some"
// end of [impqi0de_make_some]

(* ****** ****** *)

datatype f0xty =
  | F0XTYinf of (p0rec, assoc)
  | F0XTYpre of p0rec
  | F0XTYpos of p0rec
// end of [f0xty]

datatype e0xpact_kind =
  | E0XPACTassert | E0XPACTerror | E0XPACTprint
// end of [e0xpact_kind]

(* ****** ****** *)

typedef s0rtdef = '{
  s0rtdef_loc= loc_t
, s0rtdef_sym= sym_t
, s0rtdef_def= s0rtext
} // end of [s0rtdef]

typedef s0rtdeflst = List s0rtdef

fun s0rtdef_make
  (id: i0de, s0te: s0rtext): s0rtdef = "s0rtdef_make"
// end of [s0rtdef_make]

fun s0rtdeflst_nil (): s0rtdeflst = "s0rtdeflst_nil"
fun s0rtdeflst_cons (x: s0rtdef, xs: s0rtdeflst): s0rtdeflst
  = "s0rtdeflst_cons"

(* ****** ****** *)

typedef s0tacon = '{
  s0tacon_fil= fil_t
, s0tacon_loc= loc_t
, s0tacon_sym= sym_t
, s0tacon_arg= d0atarglstopt
, s0tacon_def= s0expopt
} // end of [s0tacon]

fun s0tacon_make_none_none (id: i0de): s0tacon
  = "s0tacon_make_none_none"
fun s0tacon_make_some_none (id: i0de, arg: d0atarglst): s0tacon
  = "s0tacon_make_some_none"
fun s0tacon_make_none_some (id: i0de, def: s0exp): s0tacon
  = "s0tacon_make_none_some"
fun s0tacon_make_some_some (id: i0de, arg: d0atarglst, def: s0exp): s0tacon
  = "s0tacon_make_some_some"

typedef s0taconlst = List s0tacon
fun s0taconlst_nil (): s0taconlst = "s0taconlst_nil"
fun s0taconlst_cons (x: s0tacon, xs: s0taconlst): s0taconlst
  = "s0taconlst_cons"

typedef s0tacst = '{
  s0tacst_fil= fil_t
, s0tacst_loc= loc_t
, s0tacst_sym= sym_t
, s0tacst_arg= d0atarglstopt
, s0tacst_res= s0rt
} // end of [s0tacst]

fun s0tacst_make_none (id: i0de, srt: s0rt): s0tacst
  = "s0tacst_make_none"
fun s0tacst_make_some (id: i0de, arg: d0atarglst, srt: s0rt): s0tacst
  = "s0tacst_make_some"

typedef s0tacstlst = List s0tacst
fun s0tacstlst_nil (): s0tacstlst = "s0tacstlst_nil"
fun s0tacstlst_cons (x: s0tacst, xs: s0tacstlst): s0tacstlst
  = "s0tacstlst_cons"

(* ****** ****** *)

typedef s0tavar = '{
  s0tavar_loc= loc_t
, s0tavar_sym= sym_t
, s0tavar_srt= s0rt
} // end of [s0tavar]

fun s0tavar_make (id: i0de, srt: s0rt): s0tavar
  = "s0tavar_make"

typedef s0tavarlst = List s0tavar
fun s0tavarlst_nil (): s0tavarlst = "s0tavarlst_nil"
fun s0tavarlst_cons (x: s0tavar, xs: s0tavarlst): s0tavarlst
  = "s0tavarlst_cons"

(* ****** ****** *)

typedef s0expdef = '{
  s0expdef_loc= loc_t
, s0expdef_sym= sym_t
, s0expdef_loc_id= loc_t
, s0expdef_arg= s0arglstlst
, s0expdef_res= s0rtopt
, s0expdef_def= s0exp
} // end of [s0expdef]
typedef s0expdeflst = List s0expdef

fun s0expdef_make
  (id: i0de, arg: s0arglstlst, res: s0rtopt, def: s0exp): s0expdef
  = "s0expdef_make"

fun s0expdeflst_nil (): s0expdeflst = "s0expdeflst_nil"
fun s0expdeflst_cons (x: s0expdef, xs: s0expdeflst): s0expdeflst
  = "s0expdeflst_cons"

(* ****** ****** *)

typedef
s0aspdec = '{
  s0aspdec_fil= fil_t
, s0aspdec_loc= loc_t
, s0aspdec_qid= sqi0de
, s0aspdec_arg= s0arglstlst
, s0aspdec_res= s0rtopt
, s0aspdec_def= s0exp
} // end of [s0aspdec]

fun s0aspdec_make
  (qid: sqi0de, arg: s0arglstlst, res: s0rtopt, def: s0exp): s0aspdec
  = "s0aspdec_make"

(* ****** ****** *)

typedef d0atcon = '{
  d0atcon_loc= loc_t
, d0atcon_sym= sym_t
, d0atcon_qua= s0qualstlst
, d0atcon_arg= s0expopt
, d0atcon_ind= s0expopt
} // end of [d0atcon]

fun d0atcon_make
  (qua: s0qualstlst, id: i0de, ind: s0expopt, arg: s0expopt): d0atcon
  = "d0atcon_make"

typedef d0atconlst = List d0atcon
fun d0atconlst_nil (): d0atconlst = "d0atconlst_nil"
fun d0atconlst_cons (x: d0atcon, xs: d0atconlst): d0atconlst
  = "d0atconlst_cons"

typedef
d0atdec = '{
  d0atdec_fil= fil_t
, d0atdec_loc= loc_t
, d0atdec_headloc= loc_t
, d0atdec_sym= sym_t
, d0atdec_arg= d0atarglstopt
, d0atdec_con= d0atconlst
} // end of [d0atdec]

fun d0atdec_make_none (id: i0de, con: d0atconlst): d0atdec
  = "d0atdec_make_none"
fun d0atdec_make_some
  (id: i0de, arg: d0atarglst, t: t0kn, con: d0atconlst): d0atdec
  = "d0atdec_make_some"

typedef d0atdeclst = List d0atdec
fun d0atdeclst_nil (): d0atdeclst = "d0atdeclst_nil"
fun d0atdeclst_cons (x: d0atdec, xs: d0atdeclst): d0atdeclst
  = "d0atdeclst_cons"

(* ****** ****** *)

typedef
e0xndec = '{
  e0xndec_fil= fil_t
, e0xndec_loc= loc_t
, e0xndec_sym= sym_t
, e0xndec_qua= s0qualstlst
, e0xndec_arg= s0expopt
} // end of [e0xndec]

fun e0xndec_make
  (qua: s0qualstlst, id: i0de, arg: s0expopt): e0xndec
  = "e0xndec_make"

typedef e0xndeclst = List e0xndec

fun e0xndeclst_nil (): e0xndeclst = "e0xndeclst_nil"
fun e0xndeclst_cons (x: e0xndec, xs: e0xndeclst): e0xndeclst
  = "e0xndeclst_cons"

(* ****** ****** *)

(*
//
// HX-2010-05-12: the OOP plan is permanently abandoned
//

abstype f0arglst_t // = f0arglst
castfn f0arglst_t_of_f0arglst (x: f0arglst): f0arglst_t
castfn f0arglst_of_f0arglst_t (x: f0arglst_t): f0arglst
abstype d0exp_t // = d0exp
castfn d0exp_t_of_d0exp (x: d0exp): d0exp_t
castfn d0exp_of_d0exp_t (x: d0exp_t): d0exp
abstype d0expopt_t // = d0expopt
castfn d0expopt_t_of_d0expopt (x: d0expopt): d0expopt_t
castfn d0expopt_of_d0expopt_t (x: d0expopt_t): d0expopt

datatype m0thdec =
  | M0THDECmtd of (
      loc_t, sym_t, f0arglst_t, e0fftaglstopt, s0exp, d0expopt_t
    ) // end of [M0THDECmtd]
  | M0THDECval of (loc_t, sym_t, s0exp, d0expopt_t)
  | M0THDECvar of (loc_t, sym_t, s0exp, d0expopt_t)
  | M0THDECimp of (loc_t, sym_t, f0arglst_t, s0expopt, d0exp_t) 
// end of [m0thdec]
  
fun m0thdec_make_mtd (
    _: t0kn, _: i0de, _: f0arglst_t
  , _: e0fftaglstopt, res: s0exp, def: d0expopt_t
  ) : m0thdec
  = "m0thdec_make_mtd"

fun m0thdec_make_val
  (_: t0kn, _: i0de, res: s0exp, def: d0expopt_t): m0thdec
  = "m0thdec_make_val"

fun m0thdec_make_var
  (_: t0kn, _: i0de, res: s0exp, def: d0expopt_t): m0thdec
  = "m0thdec_make_var"

fun m0thdec_make_imp (
    _: t0kn, _: i0de, arg: f0arglst_t, res: s0expopt, def: d0exp_t
  ) : m0thdec
  = "m0thdec_make_imp"

(* ****** ****** *)

typedef m0thdeclst = List m0thdec

fun m0thdeclst_nil (): m0thdeclst = "m0thdeclst_nil"
fun m0thdeclst_cons (x: m0thdec, xs: m0thdeclst): m0thdeclst
  = "m0thdeclst_cons"

(* ****** ****** *)

typedef c0lassdec = '{
  c0lassdec_loc= loc_t
, c0lassdec_fil= filename_t
, c0lassdec_sym= sym_t
, c0lassdec_arg= s0arglstlst
, c0lassdec_suplst= s0explst
, c0lassdec_mtdlst= m0thdeclst
} // end of [c0lassdec]

fun c0lassdec_make (
    id: i0de, arg: s0arglstlst
  , supclss: s0explst, mtds: m0thdeclst, t_end: t0kn
  ) : c0lassdec
  = "c0lassdec_make"
*)

(* ****** ****** *)

typedef p0arg = '{
  p0arg_loc= loc_t, p0arg_sym= sym_t, p0arg_ann= s0expopt
} // end of [p0arg]

fun p0arg_make_none (_: i0de): p0arg = "p0arg_make_none"
fun p0arg_make_some (_: i0de, _: s0exp): p0arg = "p0arg_make_some"

typedef p0arglst = List p0arg

fun p0arglst_nil (): p0arglst = "p0arglst_nil"
fun p0arglst_cons (x: p0arg, xs: p0arglst): p0arglst = "p0arglst_cons"

(* ****** ****** *)

datatype d0arg_node =
  | D0ARGsta of s0qualst
  | D0ARGdyn of p0arglst
  | D0ARGdyn2 of (p0arglst, p0arglst)
// end of [d0arg_node]

typedef d0arg = '{
  d0arg_loc= loc_t, d0arg_node= d0arg_node
} // end of [d0arg]

fun d0arg_var (id: i0de): d0arg = "d0arg_var"

fun d0arg_dyn (t_beg: t0kn, _: p0arglst, t_end: t0kn): d0arg
  = "d0arg_dyn"

fun d0arg_dyn2
  (t_beg: t0kn, _1: p0arglst, _2: p0arglst, t_end: t0kn): d0arg
  = "d0arg_dyn2"

fun d0arg_sta (t_beg: t0kn, _: s0qualst, t_end: t0kn): d0arg
  = "d0arg_sta"

typedef d0arglst = List d0arg

fun d0arglst_nil (): d0arglst = "d0arglst_nil"
fun d0arglst_cons (x: d0arg, xs: d0arglst): d0arglst = "d0arglst_cons"

(* ****** ****** *)

datatype m0acarg = M0ACARGone of i0de | M0ACARGlst of i0delst

fun m0acarg_one (x: i0de): m0acarg = "m0acarg_one"
fun m0acarg_lst
  (t_beg: t0kn, xs: i0delst, t_end: t0kn): m0acarg
  = "m0acarg_lst"

typedef m0acarglst = List m0acarg

fun m0acarglst_nil (): m0acarglst = "m0acarglst_nil"
fun m0acarglst_cons (x: m0acarg, xs: m0acarglst): m0acarglst
  = "m0acarglst_cons"

(* ****** ****** *)

datatype dcstextdef =
  | DCSTEXTDEFnone of ()
  | DCSTEXTDEFsome_ext of string // extern
  | DCSTEXTDEFsome_mac of string // macro
  | DCSTEXTDEFsome_sta of string // static
// end of [dcstextdef]

fun dcstextdef_is_mac (x: dcstextdef):<> bool
fun dcstextdef_is_sta (x: dcstextdef):<> bool

(* ****** ****** *)

fun extnamopt_none (): Stropt = "extnamopt_none"
fun extnamopt_some (ext: s0tring): Stropt = "extnamopt_some"

(* ****** ****** *)

typedef
d0cstdec = '{
  d0cstdec_fil= fil_t
, d0cstdec_loc= loc_t
, d0cstdec_sym= sym_t
, d0cstdec_arg= d0arglst
, d0cstdec_eff= e0fftaglstopt
, d0cstdec_res= s0exp
, d0cstdec_extdef= Stropt
} // end of [d0cstdec]

fun d0cstdec_make
  (_: i0de, arg: d0arglst, _: e0fftaglstopt, res: s0exp, ext: Stropt)
  : d0cstdec
  = "d0cstdec_make"

typedef d0cstdeclst = List d0cstdec

fun d0cstdeclst_nil (): d0cstdeclst = "d0cstdeclst_nil"
fun d0cstdeclst_cons (x: d0cstdec, xs: d0cstdeclst): d0cstdeclst
  = "d0cstdeclst_cons"

(* ****** ****** *)

datatype floatkind =
  | FLOATKINDfloat | FLOATKINDdouble | FLOATKINDdouble_long
  | FLOATKINDnone (* not supported *)
// end of [floatkind]

datatype intkind =
  | INTKINDint (* signed *) | INTKINDuint (* unsigned *)
  | INTKINDlint (* signed long *) | INTKINDulint (* unsigned long *)
  | INTKINDllint (* signed long long *) | INTKINDullint (* unsigned long long *)
  | INTKINDsint (* signed short *) | INTKINDusint (* unsigned short *)
  | INTKINDint8 | INTKINDuint8 | INTKINDint16 | INTKINDuint16
  | INTKINDint32 | INTKINDuint32 | INTKINDint64 | INTKINDuint64
  | INTKINDnone (* not supported *)
// end of [intkind]

(* ****** ****** *)

datatype s0vararg =
  | S0VARARGone (* {..} *)
  | S0VARARGall (* {...} *)
  | S0VARARGseq of s0arglst
// end of [s0vararg]

fun s0vararg_one ():  s0vararg = "s0vararg_one"
fun s0vararg_all ():  s0vararg = "s0vararg_all"
fun s0vararg_seq (seq: s0arglst):  s0vararg = "s0vararg_seq"

(* ****** ****** *)

typedef s0elop = '{
  s0elop_loc= loc_t, s0elop_knd= int
} // end of [s0elop]

fun s0elop_make (knd: int, t: t0kn): s0elop = "s0elop_make"

(* ****** ****** *)

datatype s0exparg =
  | S0EXPARGone (* {..} *)
  | S0EXPARGall (* {...} *)
  | S0EXPARGseq of s0explst
// end of [s0exparg]

typedef s0expargopt = Option s0exparg

fun s0exparg_one ():  s0exparg = "s0exparg_one"
fun s0exparg_all ():  s0exparg = "s0exparg_all"
fun s0exparg_seq (seq: s0explst):  s0exparg = "s0exparg_seq"

(* ****** ****** *)

datatype witht0ype =
  | WITHT0YPEnone
  | WITHT0YPEprop of s0exp
  | WITHT0YPEtype of s0exp
  | WITHT0YPEview of s0exp
  | WITHT0YPEviewtype of s0exp
// end of [witht0ype]

fun witht0ype_none (): witht0ype = "witht0ype_none"
fun witht0ype_prop (_: s0exp): witht0ype = "witht0ype_prop"
fun witht0ype_type (_: s0exp): witht0ype = "witht0ype_type"
fun witht0ype_view (_: s0exp): witht0ype = "witht0ype_view"
fun witht0ype_viewtype (_: s0exp): witht0ype = "witht0ype_viewtype"

(* ****** ****** *)

datatype p0at_node = 
  | P0Tann of (p0at, s0exp)
  | P0Tapp of (p0at, p0at)
  | P0Tas of (i0de, p0at)
  | P0Tchar of char
  | P0Texist of s0arglst
  | P0Tfloat of string
  | P0Tfree of p0at
  | P0Tide of sym_t
  | P0Tint of string
  | P0Tlist of p0atlst
  | P0Tlist2 of (p0atlst, p0atlst)
  | P0Tlst of p0atlst
  | P0Topide of sym_t
  | P0Tqid of (d0ynq, sym_t)
  | P0Trec of (int (*recknd*), labp0atlst)
  | P0Tref of i0de // reference variable
  | P0Trefas of (i0de, p0at)
  | P0Tstring of string
  | P0Tsvararg of s0vararg
  | P0Ttup of (int (*flat*), p0atlst)
  | P0Ttup2 of (int (*flat*), p0atlst, p0atlst)
// end of [p0at_node]

and labp0atlst =
  | LABP0ATLSTnil | LABP0ATLSTdot | LABP0ATLSTcons of (l0ab, p0at, labp0atlst)
// end of [labp2atlst]

where p0at = '{
   p0at_loc= loc_t, p0at_node= p0at_node
} (* end of [p0at] *)

and p0atlst: type = List p0at
and p0atopt: type = Option p0at

//

fun p0at_ann (_: p0at, _: s0exp): p0at = "p0at_ann"
fun p0at_apps (_fun: p0at, _arg: p0atlst): p0at = "p0at_apps"
fun p0at_as (_: i0de, _: p0at): p0at = "p0at_as"

fun p0at_char (_: c0har): p0at = "p0at_char"

fun p0at_exist (t_beg: t0kn, qua: s0arglst, t_end: t0kn): p0at = "p0at_exist"

fun p0at_float (_: f0loat): p0at = "p0at_float"

fun p0at_free (t_tilde: t0kn, _: p0at): p0at = "p0at_free"

fun p0at_ide (_: i0de): p0at = "p0at_ide"

fun p0at_int (_: i0nt): p0at = "p0at_int"

fun p0at_list (t_beg: t0kn, _: p0atlst, t_end: t0kn): p0at = "p0at_list"
fun p0at_list2 (t_beg: t0kn, _1: p0atlst, _2: p0atlst, t_end: t0kn): p0at
  = "p0at_list2"

fun p0at_lst (t_beg: t0kn, _: p0atlst, t_end: t0kn): p0at = "p0at_lst"

fun p0at_opide (t_op: t0kn, id: i0de): p0at = "p0at_opide"

fun p0at_qid (q: d0ynq, id: i0de): p0at = "p0at_qid"

fun p0at_rec (kind: int, t_beg: t0kn, _: labp0atlst, t_end: t0kn): p0at
  = "p0at_rec"

fun p0at_ref (t_bang: t0kn, _: i0de): p0at = "p0at_ref"
fun p0at_refas (t_bang: t0kn, _: i0de, _: p0at): p0at = "p0at_refas"

fun p0at_string (s: s0tring): p0at = "p0at_string"

fun p0at_svararg (t_beg: t0kn, _: s0vararg, t_end: t0kn): p0at
  = "p0at_svararg"

fun p0at_tup (kind: int, t_beg: t0kn, _: p0atlst, t_end: t0kn): p0at
  = "p0at_tup"
fun p0at_tup2
  (kind: int, t_beg: t0kn, _1: p0atlst, _2: p0atlst, t_end: t0kn): p0at
  = "p0at_tup2"

fun p0atlst_nil (): p0atlst = "p0atlst_nil"
fun p0atlst_cons (x: p0at, xs: p0atlst): p0atlst = "p0atlst_cons"

fun p0atopt_none (): p0atopt = "p0atopt_none"
fun p0atopt_some (x: p0at): p0atopt = "p0atopt_some"

fun labp0atlst_nil (): labp0atlst = "labp0atlst_nil"
fun labp0atlst_dot (): labp0atlst = "labp0atlst_dot"
fun labp0atlst_cons (l: l0ab, x: p0at, xs: labp0atlst): labp0atlst
  = "labp0atlst_cons"

(* ****** ****** *)

datatype f0arg_node =
  | F0ARGdyn of p0at
  | F0ARGsta1 of s0qualst
  | F0ARGsta2 of s0arglst
  | F0ARGmet of s0explst
// end of [f0arg_node]

typedef f0arg = '{ f0arg_loc= loc_t, f0arg_node= f0arg_node }

fun f0arg_sta1 (t_beg: t0kn, _: s0qualst, t_end: t0kn): f0arg
  = "f0arg_sta1"
fun f0arg_sta2 (t_beg: t0kn, _: s0arglst, t_end: t0kn): f0arg
  = "f0arg_sta2"

fun f0arg_dyn (_: p0at): f0arg = "f0arg_dyn"

fun f0arg_met_none (t: t0kn): f0arg = "f0arg_met_none"
fun f0arg_met_some (t_beg: t0kn, met: s0explst, t_end: t0kn): f0arg
  = "f0arg_met_some"

typedef f0arglst = List f0arg

fun f0arglst_nil (): f0arglst = "f0arglst_nil"
fun f0arglst_cons (x: f0arg, xs: f0arglst): f0arglst = "f0arglst_cons"

(* ****** ****** *)

typedef i0nvarg = '{
  i0nvarg_loc= loc_t, i0nvarg_sym= sym_t, i0nvarg_typ= s0expopt
} // end of [i0nvarg]
typedef i0nvarglst = List i0nvarg

fun i0nvarg_make_none (_: i0de): i0nvarg = "i0nvarg_make_none"
fun i0nvarg_make_some (_: i0de, _: s0exp): i0nvarg = "i0nvarg_make_some"

fun i0nvarglst_nil (): i0nvarglst = "i0nvarglst_nil"
fun i0nvarglst_cons (x: i0nvarg, xs: i0nvarglst): i0nvarglst
  = "i0nvarglst_cons"

typedef i0nvresstate = '{
 i0nvresstate_qua= s0qualstopt, i0nvresstate_arg= i0nvarglst
} // end of [i0nvresstate]

fun i0nvresstate_none (): i0nvresstate = "i0nvresstate_none"
fun i0nvresstate_some (qua: s0qualstopt, arg: i0nvarglst): i0nvresstate
  = "i0nvresstate_some"

typedef loopi0nv = '{
  loopi0nv_qua= s0qualstopt
, loopi0nv_met= s0explstopt
, loopi0nv_arg= i0nvarglst
, loopi0nv_res= i0nvresstate
} // end of [loopi0nv]

typedef loopi0nvopt = Option loopi0nv

fun loopi0nv_make (
  qua: s0qualstopt, met: s0explstopt, arg: i0nvarglst, res: i0nvresstate
) : loopi0nv = "loopi0nv_make" // end of [loopi0nv_make]

(* ****** ****** *)

datatype d0exp_node =
  | D0Eann of (* ascribed dynamic expressions *)
      (d0exp, s0exp)
  | D0Eapp of (* functional application *)
      (d0exp, d0exp)
  | D0Earrinit of (* array initilization *)
      (s0exp (*elt*), d0expopt (*asz*), d0explst (*elt*))
  | D0Earrpsz of (* arraysize expression *)
      (s0expopt (*elt*), d0exp (*elts*))
  | D0Earrsub of (* array subscription *)
      (arrqi0de, loc_t(*ind*), d0explstlst)
  | D0Ecaseof of (* case expression *)
      (casehead, d0exp, c0laulst)
  | D0Echar of (* dynamic characters *)
      char
  | D0Ecstsp of cstsp // for special constants
  | D0Ecrypt of (* cryption *)
      int (* 1/-1 : encryptn/decrypt *)
//
  | D0Edecseq of d0eclst // decseq as expression
//
  | D0Edelay of (* lazy evaluation *)
      int(*lin*)
  | D0Edynload (* dynamic loading *)
  | D0Eeffmask of effectlst
  | D0Eempty (* empty expression *)
  | D0Eexist of (* existential sum *)
      (loc_t (*qua*), s0exparg, d0exp)
  | D0Eextval of (* external code *)
      (s0exp (*type*), string (*code*))
  | D0Efix of (* fixed point *)
      (fixkind, i0de, f0arglst, s0expopt, e0fftaglstopt, d0exp)
  | D0Efloat of (* dynamic floats *)
      string
  | D0Efloatsp of (* dynamic specified floats *)
      string
(*
  | D0Efold of (* folding recursive type *)
      (sqi0de, d0exp)
*)
  | D0Efoldat of (* folding at a given address *)
      d0explst(* static arguments *)
  | D0Efor of (* for-loop *)
      (loopi0nvopt, loc_t(*inv*),
       d0exp(*ini*), d0exp(*test*), d0exp(*post*),
       d0exp (*body*))
  | D0Efreeat of (* freeing at a given address *)
      d0explst(* static arguments *)
  | D0Eide of (* identifier *)
      sym_t
  | D0Eidext of (* external identifier for syndef *)
      sym_t
  | D0Eif of (* dynamic conditionals *)
      (ifhead, d0exp, d0exp, d0expopt)
  | D0Eint of (* dynamic integers *)
      string
  | D0Eintsp of (* dynamic specified integers *)
      string
  | D0Elam of (* linear/nonlinear lambda-abstraction *)
      (lamkind, f0arglst, s0expopt, e0fftaglstopt, d0exp)
  | D0Elet of (* dynamic let-expression *)
      (d0eclst, d0exp)
  | D0Elist of (* d0exp list *)
      d0explst
  | D0Elist2 of (* d0exp list *)
      (d0explst, d0explst)
  | D0Eloopexn of (* break: 0 and continue: 1 *)
      int
  | D0Elst of (* for d0exp lists *)
      (int (*lin*), s0expopt, d0exp(*elts*))
  | D0Emacsyn of (* macro syntax *)
      (macsynkind, d0exp)
(*
  | D0Emod of (* for modules *)
      moditemdec list
*)
(*
  | D0Eobj of ( // for objects
      objkind, s0exp(*objcls*), m0thdeclst
    ) // end of [D0Eobj]
*)
  | D0Eopide of sym_t (* for dynamic identifiers *)
(*
  | D0Eparse of ( // parse string
      id (* the name of parse fun *), string (* input *)
    ) // end of [D0Eparse]
*)
  | D0Eptrof (* taking the address of *)
  | D0Eqid of (* qualified dynamic identifiers *)
      (d0ynq, sym_t)
  | D0Eraise of (* raised exception *)
      d0exp
  | D0Erec of (* dynamic record *)
      (int (*recknd*), labd0explst)
  | D0Escaseof of (* static caseof *)
      (casehead, s0exp, sc0laulst)
  | D0Esel_lab of (* dot label selection *)
      (int (*non/ptr*), lab_t)
  | D0Esel_ind of (* dot index selection *)
      (int (*non/ptr*), d0explstlst)
  | D0Eseq of (* sequencing *)
      d0explst
  | D0Esexparg of (* static expression sequence *)
      s0exparg
  | D0Eshowtype of (* $showtype: debugging *)
      d0exp
  | D0Esif of (* static conditionals *)
      (ifhead, s0exp, d0exp, d0exp)
  | D0Estring of (* dynamic strings *)
      (string, int(*length*))
  | D0Estruct of (* structure *)
      labd0explst
  | D0Etmpid of (* template id *)
      (tmpqi0de, t1mps0explstlst)
  | D0Etop (* uninitialized value *)
  | D0Etrywith of (* try-expression *)
      (tryhead, d0exp, c0laulst)
  | D0Etup of (* dynamic tuple expression *)
      (int (*tupknd*), d0explst)
  | D0Etup2 of (* dynamic tuple expression *)
      (int (*tupknd*), d0explst, d0explst)
(*
  | D0Eunfold of (* unfolding recursive type *)
      (sqi0de, d0exp)
*)
  | D0Eviewat (* view at a given address *)
  | D0Ewhere of (* where clause *)
      (d0exp, d0eclst)
  | D0Ewhile of (* while-loop *)
      (loopi0nvopt, loc_t(*inv*), d0exp(*test*), d0exp(*body*))
// end of [d0exp_node]

and labd0explst =
  | LABD0EXPLSTnil | LABD0EXPLSTcons of (l0ab, d0exp, labd0explst)
// end of [labd0explst]

and d0ec_node =
  | D0Cfixity of  (* fixity introduction *)
      (f0xty, i0delst)
  | D0Cnonfix of (* fixity elimination *)
      i0delst
  | D0Cinclude of (* file inclusion *)
      (int(*0:sta/1:dyn*), string(*filename*))
  | D0Csymintr of (* introduction of overloaded symbols *)
      i0delst
  | D0Ce0xpundef of (sym_t) (* undefinition *)
  | D0Ce0xpdef of (sym_t, e0xpopt)
  | D0Ce0xpact of (e0xpact_kind, e0xp)
  | D0Cdatsrts of (* datasort declaration *)
      (int(*para: 0/1*), d0atsrtdec, d0atsrtdeclst)
  | D0Csrtdefs of (* (extended) sort definition *)
      (s0rtdef, s0rtdeflst)
  | D0Cstacons of (abskind, s0tacon, s0taconlst)
  | D0Cstacsts of (s0tacst, s0tacstlst)
  | D0Cstavars of (s0tavar, s0tavarlst)
  | D0Csexpdefs of (s0rtopt, s0expdef, s0expdeflst)
  | D0Csaspdec of s0aspdec
  | D0Cdcstdecs of (* dyncst declaration *)
      (dcstkind, s0qualstlst, d0cstdec, d0cstdeclst)
  | D0Cdatdecs of (datakind, d0atdec, d0atdeclst, s0expdeflst)
  | D0Cexndecs of (e0xndec, e0xndeclst)
(*
  | D0Cclassdec of (* class declaration *)
      (clskind, s0qualstlst, c0lassdec, s0expdeflst)
*)
  | D0Cclassdec of (i0de, s0expopt)
  | D0Coverload of (i0de, dqi0de) // overloading
  | D0Cextype of (string, s0exp) // type to be used in C
  | D0Cextval of (string, d0exp) // value to be used in C
  | D0Cextcode of (* external code *)
      (int (* position: 0/1/2 : top/?/end *), string (* code *))
  | D0Cvaldecs of (* value declaration *)
      (valkind, v0aldec, v0aldeclst)
  | D0Cvaldecs_par of (* parallel value declaration *)
      (v0aldec, v0aldeclst)
  | D0Cvaldecs_rec of (* recursive value declaration *)
      (v0aldec, v0aldeclst)
  | D0Cfundecs of  (* function declaration *)
      (funkind, s0qualstlst, f0undec, f0undeclst)
  | D0Cvardecs of (* local variable declaration *)
      (v0ardec, v0ardeclst)
  | D0Cmacdefs of (* macro declaration *)
      (int (*1+/0: long/short*), m0acdef, m0acdeflst)
  | D0Cimpdec of (s0arglstlst, i0mpdec) // implementation
  | D0Cdynload of string
  | D0Cstaload of (Option sym_t, string)
  | D0Clocal of (d0eclst, d0eclst)
  | D0Cguadec of (srpifkind, guad0ec)
// end of [d0ec_node]

and guad0ec_node =
  | GD0Cone of (e0xp, d0eclst)
  | GD0Ctwo of (e0xp, d0eclst, d0eclst)
  | GD0Ccons of (e0xp, d0eclst, srpifkind, guad0ec_node)
// end of [guad0ec_node]

where d0exp = '{
  d0exp_loc= loc_t, d0exp_node= d0exp_node
} // end of [d0exp]

and d0explst: type = List d0exp
and d0expopt: type = Option d0exp
and d0explstlst: type = List d0explst
and d0explstopt: type = Option d0explst

and d0arrind = '{
  d0arrind_loc= loc_t, d0arrind_ind= d0explstlst
} // end of [d0arrind]

and initestpost = '(d0exp, d0exp, d0exp)

(* ****** ****** *)

and m0atch = '{
  m0atch_loc= loc_t, m0atch_exp= d0exp, m0atch_pat= p0atopt
}

and m0atchlst = List m0atch

(* ****** ****** *)

and guap0at = '{ 
  guap0at_loc= loc_t
, guap0at_pat= p0at
, guap0at_gua= m0atchlst
} // end of [guap0at]

(* ****** ****** *)

and ifhead = '{
  ifhead_tok= t0kn, ifhead_inv= i0nvresstate
} // end of [ifhead]

and casehead = '{
  casehead_tok= t0kn
, casehead_knd= int
, casehead_inv= i0nvresstate
} // end of [casehead]

and loophead = '{
  loophead_tok= t0kn, loophead_inv= loopi0nvopt
} // end of [lookhead]

and tryhead = '{
  tryhead_tok= t0kn, tryhead_inv= i0nvresstate
} // end of [tryhead]

and c0lau = '{
  c0lau_loc= loc_t
, c0lau_pat= guap0at
, c0lau_seq= int
, c0lau_neg= int
, c0lau_body= d0exp
} // end of [c0lau]

and c0laulst: type = List c0lau

and sc0lau = '{
  sc0lau_loc= loc_t
, sc0lau_pat= sp0at
, sc0lau_body= d0exp
} // end of [sc0lau]

and sc0laulst: type = List sc0lau

(* ****** ****** *)

and v0aldec = '{
  v0aldec_loc= loc_t
, v0aldec_pat= p0at
, v0aldec_def= d0exp
, v0aldec_ann= witht0ype
} // end of [v0aldec]

and v0aldeclst: type = List v0aldec

(* ****** ****** *)

and f0undec = '{
  f0undec_loc= loc_t
, f0undec_sym= sym_t
, f0undec_sym_loc= loc_t
, f0undec_arg= f0arglst
, f0undec_eff= e0fftaglstopt
, f0undec_res= s0expopt
, f0undec_def= d0exp
, f0undec_ann= witht0ype
} // end of [f0undec]

and f0undeclst = List f0undec

(* ****** ****** *)

and v0ardec = '{
  v0ardec_loc= loc_t
, v0ardec_knd= int (* BANG: knd = 1 *)
, v0ardec_sym= sym_t
, v0ardec_sym_loc= loc_t
, v0ardec_typ= s0expopt
, v0ardec_wth= i0deopt
, v0ardec_ini= d0expopt
} // end of [v0ardec]

and v0ardeclst = List v0ardec

(* ****** ****** *)

and m0acdef = '{
  m0acdef_loc= loc_t
, m0acdef_sym= sym_t
, m0acdef_arg= m0acarglst
, m0acdef_def= d0exp
} // end of [m0acdef]

and m0acdeflst = List m0acdef

(* ****** ****** *)

and i0mpdec = '{
  i0mpdec_loc= loc_t
, i0mpdec_qid= impqi0de
, i0mpdec_arg= f0arglst
, i0mpdec_res= s0expopt
, i0mpdec_def= d0exp
} // end of [i0mpdec]

(* ****** ****** *)

and d0ec = '{
  d0ec_loc= loc_t, d0ec_node= d0ec_node
} // end of [d0ec]

and d0eclst: type = List d0ec

and guad0ec = '{
  guad0ec_loc= loc_t, guad0ec_node= guad0ec_node
}  // end of [guad0ec]

(* ****** ****** *)

fun d0exp_ann
  (_: d0exp, _: s0exp): d0exp = "d0exp_ann"
fun d0exp_apps
  (_fun: d0exp, _arg: d0explst): d0exp = "d0exp_apps"
// end of [d0exp_apps]

(* ****** ****** *)

fun d0exp_arrinit (
    t_beg: t0kn
  , elt: s0exp, asz: d0expopt, elts: d0explst
  , t_end: t0kn
  ) : d0exp
  = "d0exp_arrinit"
  
fun d0exp_arrinit_none (
    t_beg: t0kn
  , elt: s0exp, elts: d0explst
  , t_end: t0kn
  ) : d0exp
  = "d0exp_arrinit_none"

fun d0exp_arrinit_some (
    t_beg: t0kn
  , elt: s0exp, asz: d0exp, elts: d0explst
  , t_end: t0kn
  ) : d0exp
  = "d0exp_arrinit_some"

(* ****** ****** *)

fun d0exp_arrpsz (
  t_beg: t0kn, elt: s0expopt
, t_lp: t0kn, elts: d0explst, t_rp: t0kn
) : d0exp = "d0exp_arrpsz"

(* ****** ****** *)

fun d0exp_arrsub
  (qid: arrqi0de, ind: d0arrind): d0exp = "d0exp_arrsub"
// end of [d0exp_arrsub]

(* ****** ****** *)

fun d0exp_char (_: c0har): d0exp = "d0exp_char"

fun d0exp_caseof
  (hd: casehead, d0e: d0exp, t_of: t0kn, c0ls: c0laulst): d0exp
  = "d0exp_caseof"

fun d0exp_crypt (knd: int, t_crypt: t0kn): d0exp = "d0exp_crypt"

fun d0exp_decseq (
  t_lbrace: t0kn, d0cs: d0eclst, t_rbrace: t0kn
) : d0exp = "d0exp_decseq"

fun d0exp_delay
  (lin: int, t_delay: t0kn): d0exp = "d0exp_delay"
// end of [d0exp_delay]

fun d0exp_dynload
  (t_dynload: t0kn): d0exp = "d0exp_dynload"
// end of [d0exp_dynload]

//
// HX: implemented in [ats_effect.dats]
//
fun d0exp_effmask_all (t: t0kn): d0exp = "d0exp_effmask_all"
fun d0exp_effmask_exn (t: t0kn): d0exp = "d0exp_effmask_exn"
fun d0exp_effmask_ntm (t: t0kn): d0exp = "d0exp_effmask_ntm"
fun d0exp_effmask_ref (t: t0kn): d0exp = "d0exp_effmask_ref"

fun d0exp_empty (_: loc_t): d0exp = "d0exp_empty"

fun d0exp_exist (
  t_beg: t0kn
, s0a: s0exparg
, t_bar: t0kn
, d0e: d0exp
, t_end: t0kn
) : d0exp = "d0exp_exist"

fun d0exp_extval (
  t_beg: t0kn, type: s0exp, code: s0tring, t_end: t0kn
) : d0exp = "d0exp_extval"

fun d0exp_fix (
  knd: fixkind
, f: i0de
, arg: f0arglst
, res: s0expopt
, efs: e0fftaglstopt
, body: d0exp
): d0exp = "d0exp_fix"

(* ****** ****** *)

fun d0exp_float (_: f0loat): d0exp = "d0exp_float"
fun d0exp_floatsp (_: f0loatsp): d0exp = "d0exp_floatsp"

(* ****** ****** *)

fun d0exp_foldat
  (t_foldat: t0kn, _: d0explst): d0exp = "d0exp_foldat"
// end of [d0exp_foldat]

fun d0exp_freeat
  (t_freeat: t0kn, _: d0explst): d0exp = "d0exp_freeat"
// end of [d0exp_freeat]

(* ****** ****** *)

fun d0exp_for_itp (
  hd: loophead, itp: initestpost, body: d0exp
) : d0exp = "d0exp_for_itp"

(* ****** ****** *)

fun d0exp_ide (ide: i0de): d0exp = "d0exp_ide"
fun d0exp_idext (idext: i0dext): d0exp = "d0exp_idext"

(* ****** ****** *)

fun d0exp_if_none
  (hd: ifhead, d0e_cond: d0exp, d0e_then: d0exp): d0exp
  = "d0exp_if_none"
fun d0exp_if_some (
  hd: ifhead, d0e_cond: d0exp, d0e_then: d0exp, d0e_else: d0exp
) : d0exp = "d0exp_if_some"

(* ****** ****** *)

fun d0exp_int (i: i0nt): d0exp = "d0exp_int"
fun d0exp_intsp (i: i0ntsp): d0exp = "d0exp_intsp"

(* ****** ****** *)

fun d0exp_lam (
  knd: lamkind
, arg: f0arglst, res: s0expopt, eff: e0fftaglstopt, d0e: d0exp
) : d0exp = "d0exp_lam"

(* ****** ****** *)

fun d0exp_let_seq (
  t_let: t0kn, d0cs: d0eclst, t_in: t0kn, d0e: d0explst, t_end: t0kn
) : d0exp = "d0exp_let_seq"

(* ****** ****** *)

fun d0exp_list (
  t_beg: t0kn, d0es: d0explst, t_end: t0kn
) : d0exp = "d0exp_list"

fun d0exp_list2 (
  t_beg: t0kn, d0es1: d0explst, d0es2: d0explst, t_end: t0kn
) : d0exp = "d0exp_list2"

(* ****** ****** *)

fun d0exp_loopexn (i: int, t: t0kn): d0exp = "d0exp_loopexn"

(* ****** ****** *)

fun d0exp_lst (
  lin: int
, t_beg: t0kn, os0e: s0expopt
, t_lp: t0kn, elts: d0explst, t_rp: t0kn
) : d0exp = "d0exp_lst"

fun d0exp_lst_quote (
  t_beg: t0kn, elts: d0explst, t_end: t0kn
) : d0exp = "d0exp_lst_quote"

(* ****** ****** *)

fun d0exp_macsyn_cross
  (t_beg: t0kn, _: d0exp, t_end: t0kn): d0exp = "d0exp_macsyn_cross"
// end of [d0exp_macsyn_cross]

fun d0exp_macsyn_decode
  (t_beg: t0kn, _: d0exp, t_end: t0kn): d0exp = "d0exp_macsyn_decode"
// end of [d0exp_macsyn_decode]

fun d0exp_macsyn_encode_seq
  (t_beg: t0kn, _: d0explst, t_end: t0kn): d0exp = "d0exp_macsyn_encode_seq"
// end of [d0exp_macsyn_encode_seq]

(* ****** ****** *)

(*
// HX-2010-05-12: the OOP plan is permanently suspended
fun d0exp_obj (knd: objkind, cls: s0exp, _: m0thdeclst, t_end: t0kn): d0exp
  = "d0exp_obj"
// end of [d0exp_obj]
*)

//

fun d0exp_opide (t_op: t0kn, id: i0de): d0exp = "d0exp_opide"

//

fun d0exp_ptrof (t_amp: t0kn): d0exp = "d0exp_ptrof"

//

fun d0exp_qid (d0q: d0ynq, id: i0de): d0exp = "d0exp_qid"

//

fun d0exp_raise (t_raise: t0kn, d0e: d0exp): d0exp = "d0exp_raise"

//

fun d0exp_rec
  (flat: int, t_beg: t0kn, ld0es: labd0explst, t_end: t0kn): d0exp
  = "d0exp_rec"

//

fun d0exp_scaseof
  (hd: casehead, s0e: s0exp, t_of: t0kn, sc0ls: sc0laulst): d0exp
  = "d0exp_scaseof"

//

fun d0exp_sel_lab (s: s0elop, l: l0ab): d0exp = "d0exp_sel_lab"
fun d0exp_sel_ind (s: s0elop, ind: d0arrind): d0exp = "d0exp_sel_ind"

//

fun d0exp_seq (t_beg: t0kn, d0es: d0explst, t_end: t0kn): d0exp
  = "d0exp_seq"

//

fun d0exp_sexparg (t_beg: t0kn, s0a: s0exparg, t_end:t0kn): d0exp
  = "d0exp_sexparg"

//

fun d0exp_showtype (t_showtype: t0kn, d0e: d0exp): d0exp = "d0exp_showtype"

//

fun d0exp_sif
  (hd: ifhead, s0e_cond: s0exp, d0e_then: d0exp, d0e_else: d0exp): d0exp
  = "d0exp_sif"

//

fun d0exp_string (s: s0tring): d0exp = "d0exp_string"

fun d0exp_struct (t_beg: t0kn, ld0es: labd0explst, t_end: t0kn): d0exp
  = "d0exp_struct"

fun d0exp_tmpid
  (qid: tmpqi0de, arg: s0explst, args: t1mps0explstlst, t_gt: t0kn): d0exp
  = "d0exp_tmpid"

fun d0exp_trywith_seq
  (hd: tryhead, d0es: d0explst, t_with: t0kn, c0ls: c0laulst): d0exp
  = "d0exp_trywith_seq"

fun d0exp_tup (flat: int, t_beg: t0kn, d0es: d0explst, t_end: t0kn): d0exp
  = "d0exp_tup"

fun d0exp_tup2
  (flat: int, t_beg: t0kn, d0es1: d0explst, d0es2: d0explst, t_end: t0kn): d0exp
  = "d0exp_tup2"

fun d0exp_viewat (t_viewat: t0kn): d0exp = "d0exp_viewat"

fun d0exp_where (d0e: d0exp, d0cs: d0eclst, t_end: t0kn): d0exp
  = "d0exp_where"

fun d0exp_while (hd: loophead, test: d0exp, body: d0exp): d0exp
  = "d0exp_while"

(* ****** ****** *)

fun d0exp_FILENAME (tok: t0kn): d0exp = "d0exp_FILENAME"
fun d0exp_LOCATION (tok: t0kn): d0exp = "d0exp_LOCATION"

(* ****** ****** *)

fun d0explst_nil (): d0explst = "d0explst_nil"
fun d0explst_cons (x: d0exp, xs: d0explst): d0explst = "d0explst_cons"
fun d0explst_sing (x: d0exp): d0explst = "d0explst_sing"

fun d0expopt_none (): d0expopt = "d0expopt_none"
fun d0expopt_some (x: d0exp): d0expopt = "d0expopt_some"

fun labd0explst_nil (): labd0explst = "labd0explst_nil"
fun labd0explst_cons (l: l0ab, x: d0exp, xs: labd0explst): labd0explst
  = "labd0explst_cons"

fun d0expopt_none (): d0expopt = "d0expopt_none"
fun d0expopt_some (x: d0exp): d0expopt = "d0expopt_some"

fun d0explstopt_none (): d0explstopt = "d0explstopt_none"
fun d0explstopt_some (xs: d0explst): d0explstopt = "d0explstopt_some"

//

fun d0arrind_make_sing (d0es: d0explst, t_rbracket: t0kn): d0arrind
  = "d0arrind_make_sing"
fun d0arrind_make_cons (d0es: d0explst, ind: d0arrind): d0arrind
  = "d0arrind_make_cons"

//

fun initestpost_make
  (t1: t0kn,
   ini: d0explst,
   t2: t0kn,
   test: d0explst,
   t3: t0kn,
   post: d0explst,
   t4: t0kn)
  : initestpost
  = "initestpost_make"

//

fun m0atch_make_none (d0e: d0exp): m0atch = "m0atch_make_none"
fun m0atch_make_some (d0e: d0exp, p0t: p0at): m0atch = "m0atch_make_some"
fun m0atchlst_nil (): m0atchlst = "m0atchlst_nil"
fun m0atchlst_cons (_: m0atch, _: m0atchlst): m0atchlst = "m0atchlst_cons"

//

fun guap0at_make_none (p0t: p0at): guap0at
  = "guap0at_make_none"

fun guap0at_make_some (p0t: p0at, m0ats: m0atchlst): guap0at
  = "guap0at_make_some"

//

fun ifhead_make (t_if: t0kn, inv: i0nvresstate): ifhead
  = "ifhead_make"

fun casehead_make (k: int, t_case: t0kn, inv: i0nvresstate): casehead
  = "casehead_make"

fun loophead_make_none (t_head: t0kn): loophead
  = "loophead_make_none"
fun loophead_make_some (t_head: t0kn, inv: loopi0nv, t_eqgt: t0kn): loophead
  = "loophead_make_some"

fun tryhead_make (t_try: t0kn): tryhead = "tryhead_make"

(* ****** ****** *)

fun c0lau_make (
    gp0t: guap0at, seq: int, neg: int, body: d0exp
  ) : c0lau = "c0lau_make"
fun c0laulst_nil (): c0laulst = "c0laulst_nil"
fun c0laulst_cons
  (x: c0lau, xs: c0laulst): c0laulst = "c0laulst_cons"

fun sc0lau_make
  (sp0t: sp0at, body: d0exp): sc0lau = "sc0lau_make"
fun sc0laulst_nil (): sc0laulst = "sc0laulst_nil"
fun sc0laulst_cons
  (x: sc0lau, xs: sc0laulst): sc0laulst = "sc0laulst_cons"

(* ****** ****** *)

fun v0aldec_make
  (p0t: p0at, def: d0exp, ann: witht0ype): v0aldec
  = "v0aldec_make"

fun v0aldeclst_nil (): v0aldeclst = "v0aldeclst_nil"
fun v0aldeclst_cons (x: v0aldec, xs: v0aldeclst): v0aldeclst
  = "v0aldeclst_cons"

(* ****** ****** *)

fun f0undec_make_none
  (id: i0de, arg: f0arglst, def: d0exp, ann: witht0ype): f0undec
  = "f0undec_make_none"

fun f0undec_make_some
  (id: i0de,
   arg: f0arglst,
   eff: e0fftaglstopt,
   res: s0exp,
   def: d0exp,
   ann: witht0ype): f0undec
  = "f0undec_make_some"

fun f0undeclst_nil (): f0undeclst = "f0undeclst_nil"
fun f0undeclst_cons (x: f0undec, xs: f0undeclst): f0undeclst
  = "f0undeclst_cons"

(* ****** ****** *)

fun v0arwth_none (): i0deopt = "v0arwth_none"
fun v0arwth_some (id: i0de): i0deopt = "v0arwth_some"

fun v0ardec_make_none_some
  (knd: int, id: i0de, wth: i0deopt, d0e: d0exp): v0ardec
  = "v0ardec_make_none_some"

fun v0ardec_make_some_none
  (knd: int, id: i0de, s0e: s0exp, wth: i0deopt): v0ardec
  = "v0ardec_make_some_none"

fun v0ardec_make_some_some
  (knd: int, id: i0de, s0e: s0exp, wth: i0deopt, d0e: d0exp): v0ardec
  = "v0ardec_make_some_some"

fun v0ardeclst_nil (): v0ardeclst = "v0ardeclst_nil"
fun v0ardeclst_cons (x: v0ardec, xs: v0ardeclst): v0ardeclst
  = "v0ardeclst_cons"

(* ****** ****** *)

fun m0acdef_make
  (id: i0de, arg: m0acarglst, def: d0exp): m0acdef
  = "m0acdef_make"

fun m0acdeflst_nil (): m0acdeflst = "m0acdeflst_nil"
fun m0acdeflst_cons (x: m0acdef, xs: m0acdeflst): m0acdeflst
  = "m0acdeflst_cons"

(* ****** ****** *)

fun i0mpdec_make
  (qid: impqi0de, arg: f0arglst, res: s0expopt, def: d0exp): i0mpdec
  = "i0mpdec_make"

(* ****** ****** *)

(* declaration *)

(* ****** ****** *)

dataviewtype d0ecllst =
  | D0CLLSTnil | D0CLLSTcons of (d0ecllst, d0ec)
// end of [d0ecllst]

(* ****** ****** *)

fun d0ec_infix
 (t: t0kn, p: p0rec, i: int, ids: i0delst): d0ec = "d0ec_infix"
fun d0ec_prefix (t: t0kn, p: p0rec, ids: i0delst): d0ec = "d0ec_prefix"
fun d0ec_postfix (t: t0kn, p: p0rec, ids: i0delst): d0ec = "d0ec_postfix"
fun d0ec_nonfix (t: t0kn, ids: i0delst): d0ec = "d0ec_nonfix"

fun d0ec_include (stadyn: int, name: s0tring): d0ec = "d0ec_include"

fun d0ec_symintr (t: t0kn, ids: i0delst): d0ec = "d0ec_symintr"

fun d0ec_e0xpundef (id: i0de): d0ec = "d0ec_e0xpundef"
fun d0ec_e0xpdef (id: i0de, def: e0xpopt): d0ec = "d0ec_e0xpdef"

fun d0ec_e0xpact_assert (e: e0xp): d0ec = "d0ec_e0xpact_assert"
fun d0ec_e0xpact_error (e: e0xp): d0ec = "d0ec_e0xpact_error"
fun d0ec_e0xpact_print (e: e0xp): d0ec = "d0ec_e0xpact_print"

fun d0ec_datsrts (para: int, d: d0atsrtdec, ds: d0atsrtdeclst): d0ec
  = "d0ec_datsrts"
  
fun d0ec_srtdefs (d: s0rtdef, ds: s0rtdeflst): d0ec = "d0ec_srtdefs"

fun d0ec_stacons (k: abskind, d: s0tacon, ds: s0taconlst): d0ec
  = "d0ec_stacons"

fun d0ec_stacsts (d: s0tacst, ds: s0tacstlst): d0ec = "d0ec_stacsts"

fun d0ec_stavars (d: s0tavar, ds: s0tavarlst): d0ec = "d0ec_stavars"

fun d0ec_sexpdefs (k: stadefkind, d: s0expdef, ds: s0expdeflst): d0ec
  = "d0ec_sexpdefs"

fun d0ec_saspdec (d: s0aspdec): d0ec = "d0ec_saspdec"

fun d0ec_dcstdecs
  (k: dcstkind, qua: s0qualstlst, d: d0cstdec, ds: d0cstdeclst): d0ec
  = "d0ec_dcstdecs"

fun d0ec_datdecs
  (k: datakind, d: d0atdec, ds_dec: d0atdeclst, ds_def: s0expdeflst): d0ec
  = "d0ec_datdecs"

fun d0ec_exndecs (t: t0kn, d: e0xndec, ds: e0xndeclst): d0ec
  = "d0ec_exndecs"

(* ****** ****** *)

(*
fun d0ec_classdec (
    knd: clskind, arg: s0qualstlst, d_dec: c0lassdec, ds_def: s0expdeflst
  ) : d0ec = "d0ec_classdec"
// end of [d0ec_classdec]
*)

fun d0ec_classdec_none
  (t: t0kn, id: i0de): d0ec = "d0ec_classdec_none"
fun d0ec_classdec_some
  (t: t0kn, id: i0de, sup: s0exp): d0ec = "d0ec_classdec_some"
// end of [d0ec_classdec_some]

(* ****** ****** *)

fun d0ec_overload
  (t: t0kn, id: i0de, qid: dqi0de): d0ec = "d0ec_overload"
// end of [d0ec_overload]

fun d0ec_overload_lrbrackets
  (t: t0kn, t_l: t0kn, t_r: t0kn, qid: dqi0de): d0ec = "d0ec_overload_lrbrackets"
// end of [d0ec_overload_lrbrackets]

(* ****** ****** *)

fun d0ec_extype (name: s0tring, s0e: s0exp): d0ec = "d0ec_extype"

fun d0ec_extval (name: s0tring, d0e: d0exp): d0ec = "d0ec_extval"

fun d0ec_extcode_dyn (code: e0xtcode): d0ec = "d0ec_extcode_dyn"
fun d0ec_extcode_sta (code: e0xtcode): d0ec = "d0ec_extcode_sta"

fun d0ec_valdecs (k: valkind, d: v0aldec, ds: v0aldeclst): d0ec
  = "d0ec_valdecs"

fun d0ec_valdecs_par (d: v0aldec, ds: v0aldeclst): d0ec
  = "d0ec_valdecs_par"

fun d0ec_valdecs_rec (d: v0aldec, ds: v0aldeclst): d0ec
  = "d0ec_valdecs_rec"

fun d0ec_fundecs
  (k: funkind, arg: s0qualstlst, d: f0undec, ds: f0undeclst): d0ec
  = "d0ec_fundecs"

fun d0ec_vardecs
  (d: v0ardec, ds: v0ardeclst): d0ec = "d0ec_vardecs"

fun d0ec_macdefs
  (i: int (*0/1/2: short/long/long rec*), d: m0acdef, ds: m0acdeflst): d0ec
  = "d0ec_macdefs"

fun d0ec_impdec (t_implement: t0kn, arg: s0arglstlst, d: i0mpdec): d0ec
  = "d0ec_impdec"

(* ****** ****** *)

fun d0ec_dynload (name: s0tring): d0ec = "d0ec_dynload"

fun d0ec_staload_none (name: s0tring): d0ec = "d0ec_staload_none"
fun d0ec_staload_some (id: i0de, name: s0tring): d0ec = "d0ec_staload_some"

fun d0ec_local
  (t_local: t0kn, ds_head: d0eclst, ds_body: d0eclst, t_end: t0kn): d0ec
  = "d0ec_local"

fun d0ec_guadec (kndtok: srpifkindtok, gd: guad0ec): d0ec = "d0ec_guadec"

(* ****** ****** *)

fun d0eclst_nil (): d0eclst = "d0eclst_nil"
fun d0eclst_cons (x: d0ec, xs: d0eclst): d0eclst = "d0eclst_cons"

fun d0ecllst_nil (): d0ecllst = "d0ecllst_nil"
fun d0ecllst_cons (xs: d0ecllst, x: d0ec): d0ecllst = "d0ecllst_cons"

fun d0ecllst_reverse (xs: d0ecllst): d0eclst = "d0ecllst_reverse"

(* ****** ****** *)

fun guad0ec_one
  (gua: e0xp, d0cs_then: d0eclst, t_endif: t0kn): guad0ec
  = "guad0ec_one"

fun guad0ec_two (
    gua: e0xp, d0cs_then: d0eclst, d0cs_else: d0eclst, t_endif: t0kn
  ) : guad0ec = "guad0ec_two"
// end of [guad0ec_two]

fun guad0ec_cons (
    gua: e0xp, d0cs: d0eclst, kndtok: srpifkindtok, rest: guad0ec
  ) : guad0ec = "guad0ec_cons"
// end of [guad0ec_cons]

(* ****** ****** *)

fun p0at_posmark (p0t: p0at): void
fun p0atlst_posmark (p0ts: p0atlst): void

fun d0exp_posmark (d0e: d0exp): void
fun d0explst_posmark (d0es: d0explst): void
fun d0explstopt_posmark (d0es: d0explstopt): void

fun d0ec_posmark (d0c: d0ec): void
fun d0eclst_posmark (d0cs: d0eclst): void

(* ****** ****** *)

fun fprint_depgen {m:file_mode}
(
  pf: file_mode_lte (m, w) | out: &FILE m, basename: string, d0cs: d0eclst
) : void // end of [fprint_depgen]

(* ****** ****** *)

fun fprint_taggen {m:file_mode}
(
  pf: file_mode_lte (m, w) | out: &FILE m, basename: string, d0cs: d0eclst
) : void // end of [fprint_taggen]

(* ****** ****** *)

(* end of [ats_syntax.sats] *)
