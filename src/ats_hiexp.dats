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

staload Err = "ats_error.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

#define ABS_TYPE_NAME           "ats_abs_type"
#define BOOL_TYPE_NAME          "ats_bool_type"
#define CHAR_TYPE_NAME          "ats_char_type"
#define CLO_TYPE_NAME           "ats_clo_type"
#define CLO_PTR_TYPE_NAME       "ats_clo_ptr_type"
#define CLO_REF_TYPE_NAME       "ats_clo_ref_type"
#define DOUBLE_TYPE_NAME        "ats_double_type"
#define FLOAT_TYPE_NAME         "ats_float_type"
#define INT_TYPE_NAME           "ats_int_type"
#define PROOF_TYPE_NAME         "ats_proof_type"
#define PTR_TYPE_NAME           "ats_ptr_type"
#define REF_TYPE_NAME           "ats_ref_type"
#define RECTEMP_TYPE_NAME       "ats_rectemp_type"
// #define STRING_TYPE_NAME     "ats_string_type"
#define STRING_TYPE_NAME        "ats_ptr_type"
#define SUM_PTR_TYPE_NAME       "ats_sum_ptr_type"
#define SUMTEMP_TYPE_NAME       "ats_sumtemp_type"
#define VAR_TYPE_NAME           "ats_var_type"
#define VARET_TYPE_NAME         "ats_varet_type"
#define VOID_TYPE_NAME          "ats_void_type"

(* ****** ****** *)

implement hityp_abs = hityp_extype_nil ABS_TYPE_NAME
implement hityp_bool = hityp_extype_nil BOOL_TYPE_NAME
implement hityp_char = hityp_extype_nil CHAR_TYPE_NAME
implement hityp_clo = hityp_extype_nil CLO_TYPE_NAME
implement hityp_clo_ptr = hityp_extype_nil CLO_PTR_TYPE_NAME
implement hityp_clo_ref = hityp_extype_nil CLO_REF_TYPE_NAME
implement hityp_double = hityp_extype_nil DOUBLE_TYPE_NAME
implement hityp_float = hityp_extype_nil FLOAT_TYPE_NAME
implement hityp_int = hityp_extype_nil INT_TYPE_NAME
implement hityp_proof = hityp_extype_nil PROOF_TYPE_NAME
implement hityp_ptr = hityp_extype_nil PTR_TYPE_NAME
implement hityp_string = hityp_extype_nil STRING_TYPE_NAME
implement hityp_tysum_ptr = hityp_extype_nil SUM_PTR_TYPE_NAME
(*
implement hityp_var = hityp_extype_nil VAR_TYPE_NAME
implement hityp_varet = hityp_extype_nil VARET_TYPE_NAME
*)
implement hityp_void = hityp_extype_nil VOID_TYPE_NAME

(* ****** ****** *)

val hityp_name_ptr: hityp_name = HITNAM (0, PTR_TYPE_NAME)
val hityp_name_ref: hityp_name = HITNAM (0, REF_TYPE_NAME)
val hityp_name_var: hityp_name = HITNAM (0, VAR_TYPE_NAME)
val hityp_name_varet: hityp_name = HITNAM (0, VARET_TYPE_NAME)

val hityp_name_tyrectemp_box: hityp_name =
  HITNAM (1(*box*), RECTEMP_TYPE_NAME)

val hityp_name_tyrectemp_flt: hityp_name =
  HITNAM (0(*flt*), RECTEMP_TYPE_NAME)

val hityp_name_tysumtemp: hityp_name =
  HITNAM (1(*box*), SUMTEMP_TYPE_NAME)

val hityp_name_vararg = HITNAM (0(*non*), "...")

(* ****** ****** *)

implement
hityp_cltype (fl) = '{
  hityp_name= HITNAM(0(*non*), CLO_TYPE_NAME)
, hityp_node = HITcltype (fl)
} // end of [hityp_cltype]

(* ****** ****** *)

implement
hityp_extype
  (name, arglst) = '{
  hityp_name= HITNAM (0(*non*), name)
, hityp_node= HITextype (name, arglst)
} // end of [hityp_extype]

implement
hityp_extype_nil (name) = hityp_extype (name, list_nil)

(* ****** ****** *)

implement
hityp_fun (fc, hits_arg, hit_res) = '{
  hityp_name= hityp_name_ptr, hityp_node= HITfun (fc, hits_arg, hit_res)
} // end of [hityp_fun]

implement
hityp_refarg (refval, hit_arg) = let
  val name = (
    if refval > 0 then hityp_name_ref else hit_arg.hityp_name
  ) : hityp_name
in '{
  hityp_name= name
, hityp_node= HITrefarg (refval, hit_arg)
} end // end of [hityp_refarg]

(* ****** ****** *)

fn hityp_namstr_get
  (hit: hityp): string = let
  val HITNAM (knd, name) = hit.hityp_name
in
  if knd > 0 then PTR_TYPE_NAME else name
end // end of [hityp_namstr_get]

implement hityp_tyarr
  (hit_elt, s2ess_dim) = let
  val name_elt = hityp_namstr_get (hit_elt)
  val sbp = stringlst_concat '[ "[", name_elt, "]"]
  val name_arr = string_of_strptr (sbp)
in '{
  hityp_name= HITNAM (0(*non*), name_arr)
, hityp_node= HITtyarr (hit_elt, s2ess_dim)
} end // end of [hityp_tyarr]

(* ****** ****** *)

implement
hityp_tyrec (knd, name, lhits) = '{
  hityp_name= HITNAM (knd(*non/ptr*), name), hityp_node= HITtyrec (knd, lhits)
} // end of [hityp_tyrecflt]

implement
hityp_tyrectemp (knd, lhits) = let
  val name = (
    if knd > 0 then hityp_name_tyrectemp_box else hityp_name_tyrectemp_flt
  ) : hityp_name
in '{
  hityp_name= name, hityp_node= HITtyrectemp (knd, lhits)
} end // end of [hityp_tyrecflttemp]

implement
hityp_tyrecsin (hit) = '{
  hityp_name= hit.hityp_name, hityp_node= HITtyrecsin hit
} // end of [hityp_sin]

(* ****** ****** *)

implement
hityp_tysum (name, d2c, hits) = '{
  hityp_name= HITNAM (1(*box*), name), hityp_node= HITtysum (d2c, hits)
} // end of [hityp_tysum]

implement
hityp_tysumtemp (d2c, hits) = '{
  hityp_name= hityp_name_tysumtemp, hityp_node= HITtysumtemp (d2c, hits)
} // end of [hityp_tysumtemp]

(* ****** ****** *)

implement
hityp_union (name, lhits) = '{
  hityp_name= HITNAM (0, name), hityp_node= HITunion lhits
} // end of [hityp_union]

implement
hityp_varetize (hit) = let
  val HITNAM (knd, name) = hit.hityp_name
in
  if name = VAR_TYPE_NAME then '{
    hityp_name= hityp_name_varet, hityp_node= hit.hityp_node
  } else hit
end // end of [hityp_varetize]

(* ****** ****** *)

implement
hityp_s2var (s2v) = begin
  if s2var_is_boxed s2v then begin
    '{ hityp_name= hityp_name_ptr, hityp_node= HITs2var s2v }
  end else begin
    '{ hityp_name= hityp_name_var, hityp_node= HITs2var s2v }
  end // end of [if]
end (* end of [hityp_s2var] *)

implement hityp_vararg = '{
  hityp_name= hityp_name_vararg, hityp_node= HITvararg ()
} // end of [hityp_vararg]

(* ****** ****** *)

implement hipat_ann
  (loc, hit, hip, hit_ann) = '{
  hipat_loc= loc
, hipat_node= HIPann (hip, hit_ann)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_ann]

implement
hipat_any (loc, hit) = '{
  hipat_loc= loc
, hipat_node= HIPany ()
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_any]

implement hipat_as
  (loc, hit, refknd, d2v, hip) = '{
  hipat_loc= loc
, hipat_node= HIPas (refknd, d2v, hip)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_as]

implement
hipat_bool (loc, hit, b) = '{
  hipat_loc= loc
, hipat_node= HIPbool b
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_bool]

implement
hipat_char (loc, hit, c) = '{
  hipat_loc= loc
, hipat_node= HIPchar c
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_char]

implement hipat_con
  (loc, hit, freeknd, d2c, hips, hit_sum) = '{
  hipat_loc= loc
, hipat_node= HIPcon (freeknd, d2c, hips, hit_sum)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_con]

implement hipat_con_any
  (loc, hit, freeknd, d2c) = '{
  hipat_loc= loc
, hipat_node= HIPcon_any (freeknd, d2c)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_con_any]

implement hipat_empty (loc, hit) = '{
  hipat_loc= loc
, hipat_node= HIPempty ()
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_empty]

implement
hipat_int (loc, hit, str, int) = '{
  hipat_loc= loc
, hipat_node= HIPint (str, int)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_int]

implement hipat_lst
  (loc, hit_lst, hit_elt, hips) = '{
  hipat_loc= loc
, hipat_node= HIPlst (hit_elt, hips)
, hipat_typ= hit_lst
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_lst]

implement hipat_rec
  (loc, hit, knd, lhips, hit_rec) = '{
  hipat_loc= loc
, hipat_node= HIPrec (knd, lhips, hit_rec)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_rec]

implement
hipat_string (loc, hit, str) = '{
  hipat_loc= loc
, hipat_node= HIPstring str
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_string]

implement
hipat_var (loc, hit, refknd, d2v) = '{
  hipat_loc= loc
, hipat_node= HIPvar (refknd, d2v)
, hipat_typ= hit
, hipat_asvar= D2VAROPTnone ()
} // end of [hipat_var]

(* ****** ****** *)

implement hiexp_app
  (loc, hit_app, hit_fun, hie_fun, hies_arg) = '{
  hiexp_loc= loc
, hiexp_node= HIEapp (hit_fun, hie_fun, hies_arg)
, hiexp_typ= hit_app
} // end of [hiexp_app]

implement hiexp_arrinit
  (loc, hit_arr, hit_elt, ohie_asz, hies_elt) = '{
  hiexp_loc= loc
, hiexp_node= HIEarrinit (hit_elt, ohie_asz, hies_elt)
, hiexp_typ= hit_arr
} // end of [hiexp_arrinit]

implement hiexp_arrpsz
  (loc, hit_arr, hit_elt, hies_elt) = '{
  hiexp_loc= loc
, hiexp_node= HIEarrpsz (hit_elt, hies_elt)
, hiexp_typ= hit_arr
} // end of [hiexp_arrpsz]

implement hiexp_assgn_ptr
  (loc, hit, hie_ptr, hils, hie_val) = '{
  hiexp_loc= loc
, hiexp_node= HIEassgn_ptr (hie_ptr, hils, hie_val)
, hiexp_typ= hit
} // end of [hiexp_assgn_ptr]

implement hiexp_assgn_var
  (loc, hit, d2v_ptr, hils, hie_val) = '{
  hiexp_loc= loc
, hiexp_node= HIEassgn_var (d2v_ptr, hils, hie_val)
, hiexp_typ= hit
} // end of [hiexp_assgn_var]

implement
hiexp_bool (loc, hit, b) = '{
  hiexp_loc= loc, hiexp_node= HIEbool b, hiexp_typ= hit
} // end of [hiexp_bool]

implement hiexp_caseof
  (loc, hit, knd, hies, hicls) = '{
  hiexp_loc= loc
, hiexp_node= HIEcaseof (knd, hies, hicls)
, hiexp_typ= hit
} // end of [hiexp_caseof]

implement hiexp_castfn
  (loc, hit, d2c, hie) = '{
  hiexp_loc= loc
, hiexp_node= HIEcastfn (d2c, hie)
, hiexp_typ= hit
} // end of [hiexp_castfn]

implement
hiexp_char (loc, hit, c) = '{
  hiexp_loc= loc, hiexp_node= HIEchar c, hiexp_typ= hit
} // end of [hiexp_char]

implement hiexp_con
  (loc, hit, hit_sum, d2c, hies_arg) = '{
  hiexp_loc= loc
, hiexp_node= HIEcon (hit_sum, d2c, hies_arg)
, hiexp_typ= hit
} // end of [hiexp_con]

implement
hiexp_cst (loc, hit, d2c) = '{
  hiexp_loc= loc, hiexp_node= HIEcst d2c, hiexp_typ= hit
} // end of [hiexp_cst]

implement
hiexp_cstsp (loc, hit, cst) = '{
  hiexp_loc= loc, hiexp_node= HIEcstsp cst, hiexp_typ= hit
} // end of [hiexp_cstsp]

implement
hiexp_dynload (loc, hit, fil) = '{
  hiexp_loc= loc, hiexp_node= HIEdynload fil, hiexp_typ= hit
} // end of [hiexp_dynload]

implement
hiexp_empty (loc, hit) = '{
  hiexp_loc= loc, hiexp_node= HIEempty (), hiexp_typ= hit
} // end of [hiexp_empty]

implement
hiexp_extval (loc, hit, code) = '{
  hiexp_loc= loc, hiexp_node= HIEextval code, hiexp_typ= hit
} // end of [hiexp_extval]

implement
hiexp_fix (loc, hit, knd, d2v, hie) = '{
  hiexp_loc= loc, hiexp_node= HIEfix (knd, d2v, hie), hiexp_typ= hit
} // end of [hiexp_fix]

implement
hiexp_float (loc, hit, str) = '{
  hiexp_loc= loc, hiexp_node= HIEfloat str, hiexp_typ= hit
} // end of [hiexp_float]

implement
hiexp_floatsp (loc, hit, str) = '{
  hiexp_loc= loc, hiexp_node= HIEfloatsp str, hiexp_typ= hit
} // end of [hiexp_floatsp]

implement
hiexp_freeat (loc, hit, hie) = '{
  hiexp_loc= loc, hiexp_node= HIEfreeat hie, hiexp_typ= hit
} // end of [hiexp_freeat]

implement hiexp_if
  (loc, hit, _cond, _then, _else) = '{
  hiexp_loc= loc
, hiexp_node= HIEif (_cond, _then, _else)
, hiexp_typ= hit
} // end of [hiexp_if]

implement
hiexp_int (loc, hit, str, int) = '{
  hiexp_loc= loc, hiexp_node= HIEint (str, int), hiexp_typ= hit
} // end of [hiexp_int]

implement
hiexp_intsp (loc, hit, str, int) = '{
  hiexp_loc= loc, hiexp_node= HIEintsp (str, int), hiexp_typ= hit
} // end of [hiexp_intsp]

(* ****** ****** *)

implement hiexp_is_lam (hie) = (
  case+ hie.hiexp_node of HIElam _ => true | _ => false
) // end of [hiexp_is_lam]

implement hiexp_lam
  (loc, hit, hips_arg, hie_body) = '{
  hiexp_loc= loc
, hiexp_node= HIElam (hips_arg, hie_body)
, hiexp_typ= hit
} // end of [hiexp_lam]

implement hiexp_laminit
  (loc, hit, hips_arg, hie_body) = '{
  hiexp_loc= loc
, hiexp_node= HIElaminit (hips_arg, hie_body)
, hiexp_typ= hit
} // end of [hiexp_laminit]

(* ****** ****** *)

implement
hiexp_lazy_delay
  (loc, hit, hie) = '{
  hiexp_loc= loc
, hiexp_node= HIElazy_delay (hie(*eval*))
, hiexp_typ= hit (* type of eval *)
} // end of [hiexp_lazy_delay]

implement
hiexp_lazy_ldelay
  (loc, hit, hie1, hie2) = '{
  hiexp_loc= loc
, hiexp_node= HIElazy_ldelay (hie1(*eval*), hie2(*free*))
, hiexp_typ= hit (* type of eval *)
} // end of [hiexp_lazy_ldelay]

implement
hiexp_lazy_force
  (loc, hit, lin: int, hie) = '{
  hiexp_loc= loc
, hiexp_node= HIElazy_force (lin, hie)
, hiexp_typ= hit (* type of lazy value *)
} // end of [hiexp_lazy_force]

(* ****** ****** *)

implement
hiexp_let (loc, hit, hids, hie) = '{
  hiexp_loc= loc, hiexp_node= HIElet (hids, hie), hiexp_typ= hit
} // end of [hiexp_let]

(* ****** ****** *)

implement hiexp_loop
  (loc, hit, _init, _test, _post, _body) = '{
  hiexp_loc= loc
, hiexp_node= HIEloop (_init, _test, _post, _body)
, hiexp_typ= hit
} // end of [hiexp_loop]

implement
hiexp_loopexn (loc, hit, i) = '{
  hiexp_loc= loc, hiexp_node= HIEloopexn i, hiexp_typ= hit
} // end of [hiexp_loopexn]

(* ****** ****** *)

implement hiexp_lst
  (loc, hit, lin, hit_elt, hies_elt) = '{
  hiexp_loc= loc
, hiexp_node= HIElst (lin, hit_elt, hies_elt)
, hiexp_typ= hit
} // end of [hiexp_lst]

implement
hiexp_ptrof_ptr
  (loc, hit, hie_ptr, hils) = '{
  hiexp_loc= loc
, hiexp_node= HIEptrof_ptr (hie_ptr, hils)
, hiexp_typ= hit
} // end of [hiexp_ptrof_ptr]

implement
hiexp_ptrof_var
  (loc, hit, d2v_ptr, hils) = '{
  hiexp_loc= loc
, hiexp_node= HIEptrof_var (d2v_ptr, hils)
, hiexp_typ= hit
} // end of [hiexp_ptrof_ptr]

implement
hiexp_raise (loc, hit, hie) = '{
  hiexp_loc= loc, hiexp_node= HIEraise hie, hiexp_typ= hit
} // end of [hiexp_raise]

implement hiexp_rec
  (loc, hit, knd, hit_rec, lhies) = '{
  hiexp_loc= loc
, hiexp_node= HIErec (knd, hit_rec, lhies)
, hiexp_typ= hit
} // end of [hiexp_rec]

implement hiexp_refarg
  (loc, hit, refval, freeknd, hie) = '{
  hiexp_loc= loc
, hiexp_node= HIErefarg (refval, freeknd, hie)
, hiexp_typ= hit
} // end of [hiexp_refarg]

(* ****** ****** *)

implement hiexp_sel
  (loc, hit, hie, hils) = '{
  hiexp_loc= loc
, hiexp_node= HIEsel (hie, hils)
, hiexp_typ= hit
} // end of [hiexp_sel]

implement hiexp_sel_ptr
  (loc, hit, hie_ptr, hils) = '{
  hiexp_loc= loc
, hiexp_node= HIEsel_ptr (hie_ptr, hils)
, hiexp_typ= hit
} // end of [hiexp_sel_ptr]

implement hiexp_sel_var
  (loc, hit, d2v_ptr, hils) = '{
  hiexp_loc= loc
, hiexp_node= HIEsel_var (d2v_ptr, hils)
, hiexp_typ= hit
} // end of [hiexp_sel_var]

(* ****** ****** *)

implement
hiexp_seq (loc, hit, hies) = '{
  hiexp_loc= loc, hiexp_node= HIEseq hies, hiexp_typ= hit
} // end of [hiexp_seq]

implement
hiexp_sif (loc, hit, hie_then, hie_else) = '{
  hiexp_loc= loc, hiexp_node= HIEsif (hie_then, hie_else), hiexp_typ= hit
} // end of [hiexp_sif]

implement
hiexp_sizeof (loc, hit, hit_arg) = '{
  hiexp_loc= loc, hiexp_node= HIEsizeof hit_arg, hiexp_typ= hit
} // end of [hiexp_sizeof]

implement
hiexp_string (loc, hit, str, len) = '{
  hiexp_loc= loc, hiexp_node= HIEstring (str, len), hiexp_typ= hit
} // end of [hiexp_string]

(* ****** ****** *)

implement hiexp_tmpcst
  (loc, hit, d2c, hitss_arg) = '{
  hiexp_loc= loc
, hiexp_node= HIEtmpcst (d2c, hitss_arg)
, hiexp_typ= hit
} // end of [hiexp_tmpcst]

implement hiexp_tmpvar
  (loc, hit, d2v, hitss_arg) = '{
  hiexp_loc= loc
, hiexp_node= HIEtmpvar (d2v, hitss_arg)
, hiexp_typ= hit
} // end of [hiexp_tmpvar]

(* ****** ****** *)

implement
hiexp_top (loc, hit) = '{
  hiexp_loc= loc, hiexp_node= HIEtop (), hiexp_typ= hit
} // end of [hiexp_top]

implement hiexp_trywith
  (loc, hit, hie, hicls) = '{
  hiexp_loc= loc
, hiexp_node= HIEtrywith (hie, hicls)
, hiexp_typ= hit
} // end of [hiexp_trywith]

implement
hiexp_var (loc, hit, d2v) = '{
  hiexp_loc= loc, hiexp_node= HIEvar d2v, hiexp_typ= hit
} // end of [hiexp_var]

(* ****** ****** *)

implement
hilab_lab (loc, l, hit_rec) = '{
  hilab_loc= loc, hilab_node= HILlab (l, hit_rec)
} // end of [hilab_lab]

implement
hilab_ind (loc, hiess_ind, hit_elt) = '{
  hilab_loc= loc, hilab_node= HILind (hiess_ind, hit_elt)
} // end of [hilab_ind]

(* ****** ****** *)

implement
himat_make (loc, hie, ohip) = '{
  himat_loc= loc, himat_exp= hie, himat_pat= ohip
} // end of [himat_make]

implement
hiclau_make
  (loc, hips, gua, body) = '{
  hiclau_loc= loc
, hiclau_pat= hips
, hiclau_gua= gua
, hiclau_exp= body
} // end of [hiclau_make]

(* ****** ****** *)

implement
hidec_list (loc, hids) = '{
  hidec_loc= loc, hidec_node= HIDlist hids
} // end of [hidec_list]

implement
hidec_saspdec (loc, saspdec) = '{
  hidec_loc= loc, hidec_node= HIDsaspdec saspdec
} // end of [hidec_saspdec]

implement
hidec_dcstdec (loc, knd, d2cs) = '{
  hidec_loc= loc, hidec_node= HIDdcstdec (knd, d2cs)
} // end of [hidec_dcstdec]

implement
hidec_datdec (loc, knd, s2cs) = '{
  hidec_loc= loc, hidec_node= HIDdatdec (knd, s2cs)
} // end of [hidec_datdec]

implement
hidec_exndec (loc, d2cs) = '{
  hidec_loc= loc, hidec_node= HIDexndec (d2cs)
} // end of [hidec_exndec]

implement
hidec_extern (loc, position, code) = '{
  hidec_loc= loc, hidec_node= HIDextern (position, code)
} // end of [hidec_extern]

implement
hidec_extype (loc, name, hit_def) = '{
  hidec_loc= loc, hidec_node= HIDextype (name, hit_def)
} // end of [hidec_extype]

implement
hidec_extval (loc, name: string, hie_def) = '{
  hidec_loc= loc, hidec_node= HIDextval (name, hie_def)
} // end of [hidec_extval]

(* ****** ****** *)

implement
hidec_impdec (loc, impdec) = '{
  hidec_loc= loc, hidec_node= HIDimpdec (impdec)
} // end of [hidec_impdec]

implement
hidec_impdec_prf (loc, impdec_prf) = '{
  hidec_loc= loc, hidec_node= HIDimpdec_prf (impdec_prf)
} // end of [hidec_impdec_prf]

(* ****** ****** *)

implement
hifundec_make (loc, _fun, _def) = '{
  hifundec_loc= loc, hifundec_var= _fun, hifundec_def= _def
} // end of [hifundec_make]

implement
hidec_fundecs (loc, tmp, knd, hids) = '{
  hidec_loc= loc, hidec_node= HIDfundecs (tmp, knd, hids)
} // end of [hidec_fundecs]

(* ****** ****** *)

implement
hivaldec_make (loc, _pat, _def) = '{
  hivaldec_loc= loc, hivaldec_pat= _pat, hivaldec_def= _def
}

implement
hidec_valdecs (loc, knd, hids) = '{
  hidec_loc= loc, hidec_node= HIDvaldecs (knd, hids)
}

implement
hidec_valdecs_par (loc, hids) = '{
  hidec_loc= loc, hidec_node= HIDvaldecs_par (hids)
}

implement
hidec_valdecs_rec (loc, hids) = '{
  hidec_loc= loc, hidec_node= HIDvaldecs_rec (hids)
}

(* ****** ****** *)

implement
hivardec_make (loc, knd, d2v, ini) = '{
  hivardec_loc= loc, hivardec_knd= knd, hivardec_ptr= d2v, hivardec_ini= ini
} // end of [hivardec_make]

implement
hidec_vardecs (loc, hids) = '{
  hidec_loc= loc, hidec_node= HIDvardecs (hids)
}

(* ****** ****** *)

implement hiimpdec_make
  (loc, d2c, tmp, decarg, tmparg, hie_def, d2cs) = '{
  hiimpdec_loc= loc
, hiimpdec_cst= d2c
, hiimpdec_tmp= tmp
, hiimpdec_decarg= decarg(*s2qualst*), hiimpdec_tmparg= tmparg(*hityplstlst*)
, hiimpdec_def= hie_def
, hiimpdec_cstset= d2cs
} // end of [hiimpdec_make]

implement hiimpdec_prf_make (loc, d2c, d2cs) = '{
  hiimpdec_prf_loc= loc, hiimpdec_prf_cst= d2c, hiimpdec_prf_cstset= d2cs
} // end of [hiimpdec_prf_make]

(* ****** ****** *)

implement
hidec_local (loc, _head, _body) = '{
  hidec_loc= loc, hidec_node= HIDlocal (_head, _body)
} // end of [hidec_local]

implement
hidec_staload
  (loc, fil, loadflag) = '{
  hidec_loc= loc, hidec_node= HIDstaload (fil, loadflag)
} // end of [hidec_staload]

implement
hidec_dynload (loc, fil) = '{
  hidec_loc= loc, hidec_node= HIDdynload (fil)
} // end of [hidec_dynload]

(* ****** ****** *)

local

typedef vartyp = '{
  vartyp_var= d2var_t, vartyp_typ= hityp_t
}

assume vartyp_t = vartyp

in // in of [local]

fn _vartyp_make
  (d2v: d2var_t, hit: hityp_t)
  : vartyp = '{
  vartyp_var= d2v, vartyp_typ= hit
} // end of [_vartyp_make]

implement
vartyp_make (d2v, hit) = _vartyp_make (d2v, hit)

implement vartyp_get_typ (vtp) = vtp.vartyp_typ
implement vartyp_get_var (vtp) = vtp.vartyp_var

implement
eq_vartyp_vartyp (vtp1, vtp2) =
  eq_d2var_d2var (vtp1.vartyp_var, vtp2.vartyp_var)
// end of [eq_vartyp_vartyp]

implement
compare_vartyp_vartyp (vtp1, vtp2) =
  compare_d2var_d2var (vtp1.vartyp_var, vtp2.vartyp_var)
// end of [compare_vartyp_vartyp]

end // end of [local]

(* ****** ****** *)

extern typedef "hipat_t" = hipat

%{$

ats_void_type
atsopt_hipat_set_asvar (
  ats_ptr_type hip, ats_ptr_type od2v
) {
  ((hipat_t)hip)->atslab_hipat_asvar = od2v; return ;
} // end of [ats_hiexp_hipat_set_asvar]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_hiexp.dats] *)
