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

(* Mainly for handling environments during the third translation *)

(* ****** ****** *)

staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_patcst2.sats"
staload "ats_dynexp3.sats"

(* ****** ****** *)

datatype c3strkind =
  | C3STRKINDmain of ()
  | C3STRKINDmetric_nat (* checking for metric being welfounded *)
  | C3STRKINDmetric_dec (* checking for metric being decreasing *)
  | C3STRKINDpattern_match_exhaustiveness of
      (int (* kind: warning, error, etc. *), p2atcstlst)
  | C3STRKINDvarfin of (d2var_t, s2exp, s2exp)
  | C3STRKINDloop of int (* 0/1/2: enter/break/continue *)
// end of [c3strkind]

datatype s3item =
  | S3ITEMcstr of c3str
  | S3ITEMcstr_ref of ref (c3stropt)
  | S3ITEMdisj of s3itemlstlst
  | S3ITEMhypo of h3ypo
  | S3ITEMsvar of s2var_t
  | S3ITEMsVar of s2Var_t
// end of [s3item]

and c3str_node =
  | C3STRprop of s2exp
  | C3STRitmlst of s3itemlst
// end of [c3str_node]

and h3ypo_node =
  | H3YPOprop of s2exp
  | H3YPObind of (s2var_t, s2exp)
  | H3YPOeqeq of (s2exp, s2exp)
// end of [h3ypo_node]

where s3itemlst = List s3item
and s3itemlstlst = List s3itemlst

and c3str = '{
  c3str_loc= loc_t, c3str_kind= c3strkind, c3str_node= c3str_node
}

and c3stropt = Option c3str

and h3ypo = '{
  h3ypo_loc= loc_t, h3ypo_node= h3ypo_node
}

viewtypedef s3itemlst_vt = List_vt s3item
viewtypedef s3itemlstlst_vt = List_vt s3itemlst_vt

(* ****** ****** *)

fun fprint_s3item {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3i: s3item): void
overload fprint with fprint_s3item

fun fprint_s3itemlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3is: s3itemlst): void
overload fprint with fprint_s3itemlst

fun fprint_s3itemlstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3iss: s3itemlstlst): void
overload fprint with fprint_s3itemlstlst

fun fprint_c3strkind {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, knd: c3strkind): void
overload fprint with fprint_c3strkind

fun fprint_c3str {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, c3t: c3str): void
overload fprint with fprint_c3str

fun fprint_h3ypo {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, h3p: h3ypo): void
overload fprint with fprint_h3ypo

(* ****** ****** *)

fun print_s3itemlst
  (s3is: s3itemlst): void = "atsopt_print_s3itemlst"
overload print with print_s3itemlst

fun prerr_s3itemlst
  (s3is: s3itemlst): void = "atsopt_prerr_s3itemlst"
overload prerr with prerr_s3itemlst

fun print_s3itemlstlst
  (s3iss: s3itemlstlst): void = "atsopt_print_s3itemlstlst"
overload print with print_s3itemlstlst

fun prerr_s3itemlstlst
  (s3iss: s3itemlstlst): void = "atsopt_prerr_s3itemlstlst"
overload prerr with prerr_s3itemlstlst

//

fun print_s3itemlst_vt
  (s3is: !s3itemlst_vt): void = "atsopt_print_s3itemlst"
overload print with print_s3itemlst_vt

fun prerr_s3itemlst_vt
  (s3is: !s3itemlst_vt): void = "atsopt_prerr_s3itemlst"
overload prerr with prerr_s3itemlst_vt

fun print_s3itemlstlst_vt
  (s3iss: !s3itemlstlst_vt): void = "atsopt_print_s3itemlstlst"
overload print with print_s3itemlstlst_vt

fun prerr_s3itemlstlst_vt
  (s3iss: !s3itemlstlst_vt): void = "atsopt_prerr_s3itemlstlst"
overload prerr with prerr_s3itemlstlst_vt

//

fun print_c3str (c3t: c3str): void
overload print with print_c3str

fun prerr_c3str (c3t: c3str): void
overload prerr with prerr_c3str

//

fun print_h3ypo (h3p: h3ypo): void
overload print with print_h3ypo

fun prerr_h3ypo (h3y: h3ypo): void
overload prerr with prerr_h3ypo

(* ****** ****** *)

fun c3str_prop (_: loc_t, _: s2exp): c3str
fun c3str_itmlst (_: loc_t, knd: c3strkind, _: s3itemlst): c3str
fun c3str_metric_nat (_: loc_t, _: s2exp): c3str
fun c3str_metric_dec {n:nat}
  (_: loc_t, met: s2explst n, met_bound: s2explst n): c3str
fun c3str_pattern_match_exhaustiveness
  (_: loc_t, knd: int, p2tcs: p2atcstlst): c3str

(* ****** ****** *)

fun h3ypo_prop (_: loc_t, _: s2exp): h3ypo
fun h3ypo_bind (_: loc_t, _: s2var_t, _: s2exp): h3ypo
fun h3ypo_eqeq (_: loc_t, _: s2exp, _: s2exp): h3ypo

(* ****** ****** *)

// for binding and unbinding static constants
absview s2cstlst_env_token
fun the_s2cstlst_env_pop (pf: s2cstlst_env_token | (*none*)): s2cstlst
fun the_s2cstlst_env_pop_and_unbind (pf: s2cstlst_env_token | (*none*)): void
fun the_s2cstlst_env_push (): (s2cstlst_env_token | void)
fun the_s2cstlst_env_add (s2c: s2cst_t): void
fun the_s2cstlst_env_addlst (s2cs: s2cstlst): void
fun the_s2cstlst_env_bind_and_add (loc: loc_t, s2c: s2cst_t, s2e: s2exp): void

(* ****** ****** *)

fun the_s2Varset_env_add (s2V: s2Var_t): void
fun the_s2Varset_env_get (): s2Varset_t
fun the_s2Varset_env_get_prev (): s2Varset_t
fun the_s2Varset_env_pop (): void and the_s2Varset_env_push (): void

(* ****** ****** *)

fun the_s2varbindmap_initize (): void
//
fun fprint_the_s2varbindmap {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m): void
fun print_the_s2varbindmap (): void and prerr_the_s2varbindmap (): void
//
fun the_s2varbindmap_add (s2v: s2var_t, s2e: s2exp): void
fun the_s2varbindmap_find (s2v: s2var_t): s2expopt_vt
//
// absview s2varbindmap_token_v
// fun the_s2varbindmap_pop (): (s2varbindmap_token_v | void)
// fun the_s2varbindmap_push (pf: s2varbindmap_token_v | (*none*)): void
//
fun the_s2varbindmap_pop (): void
fun the_s2varbindmap_push (): void

(* ****** ****** *)

absview metric_env_token

fun metric_nat_check (loc0: loc_t, met: s2explst): void

fun metric_env_get (d2v: stamp_t): s2explstopt

fun metric_env_pop (pf: metric_env_token | (*none*)): void
fun metric_env_push
  (d2vs: d2varlst, met: s2explst): (metric_env_token | void)

fun s2exp_metfn_load
  (s2e0: s2exp, d2v0: d2var_t): Option_vt @(s2exp, s2rtlst)

(* ****** ****** *)

absview effect_env_token

fun the_effect_env_add_lam (_: s2eff): void
fun the_effect_env_add_eff (_: $Syn.effect_t): void

fun the_effect_env_pop (pf: effect_env_token | (*none*)): void

fun the_effect_env_push (): (effect_env_token | void)
fun the_effect_env_push_lam (_: s2eff): (effect_env_token | void)

fun the_effect_env_push_delay (): (effect_env_token | void)

fun the_effect_env_push_eff
  (_: $Syn.effectlst): (effect_env_token | void)
fun the_effect_env_push_effmask
  (_: $Syn.effectlst): (effect_env_token | void)

fun the_effect_env_check_exn (loc0: loc_t): void
fun the_effect_env_check_ntm (loc0: loc_t): void
fun the_effect_env_check_ref (loc0: loc_t): void
fun the_effect_env_check_all (loc0: loc_t): void
fun the_effect_env_check_effvar (loc0: loc_t, s2v0: s2var_t): void
fun the_effect_env_check_seff (loc0: loc_t, s2fe0: s2eff): void

(* ****** ****** *)

fun trans3_env_s3itemlst_copy (): s3itemlst_vt
fun trans3_env_s3itemlst_get (): s3itemlst_vt
fun trans3_env_s3itemlst_set (_: s3itemlst_vt): Option_vt (s3itemlst_vt)

fun trans3_env_add_svar (s2v: s2var_t): void
fun trans3_env_add_svarlst (s2vs: s2varlst): void

fun trans3_env_add_sVar (s2V: s2Var_t): void
fun trans3_env_add_sVarlst (s2Vs: s2Varlst): void

fun trans3_env_add_cstr (c3t: c3str): void
fun trans3_env_add_cstr_ref (r: ref c3stropt): void
fun trans3_env_add_prop (loc: loc_t, s2p: s2exp): void
fun trans3_env_add_proplst (loc: loc_t, s2ps: s2explst): void
fun trans3_env_add_proplstlst (loc: loc_t, s2pss: s2explstlst): void
fun trans3_env_add_eqeq
  (loc: loc_t, s2e1: s2exp, s2e2: s2exp): void
fun trans3_env_add_tyleq
  (loc: loc_t, s2e1: s2exp, s2e2: s2exp): void

(* ****** ****** *)

fun trans3_env_hypo_add_prop (loc: loc_t, s2p: s2exp): void
fun trans3_env_hypo_add_proplst (loc: loc_t, s2ps: s2explst): void

fun trans3_env_hypo_add_bind
  (loc: loc_t, s2v1: s2var_t, s2e2: s2exp): void
fun trans3_env_hypo_add_eqeq
  (loc: loc_t, s2e1: s2exp, s2e2: s2exp): void

fun trans3_env_hypo_add_s2qualst (loc: loc_t, s2qs: s2qualst): void

fun trans3_env_hypo_add_p2atcst
  (loc: loc_t, p2tc: p2atcst, s2e: s2exp): void
fun trans3_env_hypo_add_p2atcstlst
  (loc: loc_t, p2tcs: p2atcstlst, s2es: s2explst): void
fun trans3_env_hypo_add_labp2atcstlst
  (loc: loc_t, lp2tcs: labp2atcstlst, ls2es: labs2explst): void

fun trans3_env_hypo_add_p2atcstlstlst
  (loc: loc_t, p2tcss: p2atcstlstlst, s2es: s2explst): void

(* ****** ****** *)

fun trans3_env_add_metric_dec {n:nat}
  (loc: loc_t, metric: s2explst n, metric_bound: s2explst n): void

fun trans3_env_add_p2atcstlstlst_false
  (loc: loc_t, casknd: int, p2tcss: p2atcstlstlst, s2es: s2explst): void

(* ****** ****** *)

fun s2exp_Var_make_srt (_: loc_t, _: s2rt): s2exp
fun s2exp_Var_make_var (_: loc_t, _: s2var_t): s2exp

(* ****** ****** *)

fun s2qua_instantiate_and_add
  (_: loc_t, s2vs: s2varlst, s2ps: s2explst): stasub_t

fun s2qua_instantiate_with_and_add
  (loc: loc_t, s2vs: s2varlst, s2ps: s2explst, loc_arg: loc_t, s2es: s2explst)
  : stasub_t

fun s2qua_hypo_instantiate_and_add
  (_: loc_t, s2vs: s2varlst, s2ps: s2explst): stasub_t

(* ****** ****** *)

fun s2exp_metric_instantiate
  (_: loc_t, d2vopt: Option stamp_t, met: s2explst): void

(* ****** ****** *)

fun s2exp_exi_instantiate_all (_: loc_t, _: s2exp): s2exp
fun s2exp_exi_instantiate_one (_: loc_t, _: s2exp): s2exp
fun s2exp_exi_instantiate_seq
  (loc: loc_t, _: s2exp, loc_arg: loc_t, _: s2explst): s2exp

fun s2exp_exi_instantiate_sexparg (_: loc_t, _: s2exp, _: s2exparg): s2exp

fun funarg_varfin_check (loc0: loc_t): void
fun s2exp_wth_instantiate (loc: loc_t, _: s2exp): s2exp

(* ****** ****** *)

fun s2exp_uni_instantiate_all (_: loc_t, _: s2exp): s2exp
fun s2exp_uni_instantiate_one (_: loc_t, _: s2exp): s2exp
fun s2exp_uni_instantiate_seq
  (loc: loc_t, _: s2exp, loc_arg: loc_t, _: s2explst): s2exp

fun s2exp_uni_instantiate_sexparg (_: loc_t, _: s2exp, _: s2exparg): s2exp
fun s2exp_uni_instantiate_sexparglst (_: loc_t, _: s2exp, _: s2exparglst): s2exp

(* ****** ****** *)

fun s2exp_template_instantiate (
  _: loc_t, _: s2qualst, _: tmps2explstlst, s2e: s2exp
) : @(List stasub_t, s2exp) // end of ...

(* ****** ****** *)

fun s2exp_absuni_and_add (loc: loc_t, _: s2exp): s2exp

fun s2exp_opnexi_and_add (loc: loc_t, _: s2exp): s2exp
fun s2explst_opnexi_and_add (loc: loc_t, _: s2explst): s2explst
fun s2expopt_opnexi_and_add (loc: loc_t, _: s2expopt): s2expopt

(* ****** ****** *)
//
// HX: for tracking linear dynamic variables
//
absview d2varset_env_token

fun the_d2varset_env_add (d2v: d2var_t): void
fun the_d2varset_env_addlst (d2vs: d2varlst): void
fun the_d2varset_env_add_p2at (p2t: p2at): void
fun the_d2varset_env_add_p2atlst (p2ts: p2atlst): void

fun the_d2varset_env_prerr_ld2vs (): void // print local d2varset on stderr
fun the_d2varset_env_print_ld2vs (): void // print local d2varset on stdout

fun the_d2varset_env_pop_lam (pf: d2varset_env_token | (*none*)): void
fun the_d2varset_env_push_lam (lin: int): (d2varset_env_token | void)

fun the_d2varset_env_pop_let (pf: d2varset_env_token | (*none*)): void
fun the_d2varset_env_push_let (): (d2varset_env_token | void)

fun the_d2varset_env_pop_try (pf: d2varset_env_token | (*none*)): void
fun the_d2varset_env_push_try (): (d2varset_env_token | void)

fun the_d2varset_env_d2var_is_lam_local (d2v: d2var_t): bool
fun the_d2varset_env_d2var_is_llam_local (d2v: d2var_t): bool

fun the_d2varset_env_check (loc0: loc_t): void
fun the_d2varset_env_check_llam (loc0: loc_t): void

(* ****** ****** *)

fun the_d2varset_env_find_view (_v: s2exp): Option_vt d2var_t

typedef d2varset_env_find_viewat_t =
  @(d2var_t, s2exp(*elt*), s2exp(*addr*), s2lablst(*front*), s2lablst(*back*))

fun the_d2varset_env_find_viewat
  (root: s2exp, path: s2lablst): Option_vt d2varset_env_find_viewat_t

(* ****** ****** *)
//
// HX: record linear dynamic variables before branching
//
abstype stbefitem_t // assumed in [ats_trans3_env_state.dats]
typedef stbefitemlst (n:int) = list (stbefitem_t, n)
typedef stbefitemlst = [n:nat] stbefitemlst (n)

fun the_d2varset_env_stbefitemlst_save (): stbefitemlst

fun stbefitem_make (d2v: d2var_t, lin: int): stbefitem_t

fun stbefitemlst_restore_typ (sbis: stbefitemlst): void
fun stbefitemlst_restore_lin_typ (sbis: stbefitemlst): void

abstype staftitem_t // assumed in [ats_trans3_env_state.dats]
typedef staftitemlst (n:int) = list (staftitem_t, n)

(* ****** ****** *)
//
// HX: assumed in [ats_trans3_env_state.dats]
//
abstype
staftscstr_t (n:int)

fun
staftscstr_met_set{n:nat}
(
  sac: staftscstr_t n, met: s2explstopt
) : void = "atsopt_state_staftscstr_met_set"
// end of [staftscstr_met_set]
//
fun
staftscstr_initize{n:nat}
  (res: i2nvresstate, sbis: stbefitemlst n): staftscstr_t n
//
fun
staftscstr_stbefitemlst_merge{n:nat}
  (loc: loc_t, sac: staftscstr_t n, sbis: stbefitemlst n): void
// end of [staftscstr_stbefitemlst_merge]
//
// HX-2010-05-27:
// This version of [staftscstr_stbefitemlst_merge] skips termination
// metric checking even if termination metric is provided.
//
fun staftscstr_stbefitemlst_merge_skipmetck {n:nat}
  (loc: loc_t, sac: staftscstr_t n, sbis: stbefitemlst n): void
// end of [staftscstr_stbefitemlst_merge]

fun staftscstr_stbefitemlst_check {n:nat}
  (loc0: loc_t, sac: staftscstr_t n, sbis: stbefitemlst n): void

fun staftscstr_stbefitemlst_update {n:nat}
  (loc0: loc_t, sac: staftscstr_t n, sbis: stbefitemlst n): void

(* ****** ****** *)

absview lamloop_env_token

//
// [LMLPloop0]: for the first round typechecking
// [LMLPloop1]: for the second round typechekcing
//
// HX: the break/continue statements are skipped during the first round.
//
datatype lamloop =
  | LMLPlam of p3atlst (* function arguments *)
  | LMLPloop0 of ()
  | {n:nat} LMLPloop1 of (* sbis, sac_init, sac_exit *)
      (stbefitemlst n, staftscstr_t n, staftscstr_t n, d2expopt)
  | LMLPnone of ()
// end of [lamloop]

fun the_lamloop_env_top (): lamloop

fun the_lamloop_env_pop (pf: lamloop_env_token | (*none*)): void

fun the_lamloop_env_push_lam (arg: p3atlst): (lamloop_env_token | void)

fun the_lamloop_env_push_loop0
  () : (lamloop_env_token | void)

fun the_lamloop_env_push_loop1 {n:nat} (
  sbis: stbefitemlst n
, sac_init: staftscstr_t n
, sac_exit: staftscstr_t n
, post: d2expopt
) : (
  lamloop_env_token | void
) // end of [the_lamloop_env_push_loop1]

fun the_lamloop_env_arg_get (): Option_vt (p3atlst)

(* ****** ****** *)
//
fun
trans3_env_pop_sta(): s3itemlst_vt
//
fun
trans3_env_pop_sta_and_free(): void
//
fun
trans3_env_pop_sta_and_add
  (_: loc_t, _: c3strkind): void
//
fun
trans3_env_pop_sta_and_add_none (_: loc_t): void
//
fun
trans3_env_push_sta ((*void*)): void
//
(* ****** ****** *)

fun trans3_env_initize ((*void*)): void

(* ****** ****** *)

(* end of [ats_trans3_env.sats] *)
