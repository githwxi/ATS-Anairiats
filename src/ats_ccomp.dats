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

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

typedef stamp_t = $Stamp.stamp_t

(* ****** ****** *)
  
fn prerr_interror () = prerr "INTERNAL ERROR (ats_ccomp)"

(* ****** ****** *)

local

typedef tmplab = '{
  tmplab_stamp = stamp_t
} // end of [tmplab]

assume tmplab_t = tmplab

fn _tmplab_make (): tmplab = '{
  tmplab_stamp= $Stamp.tmplab_stamp_make ()
} // end of [tmplab]

in // in of [local]

implement tmplab_make () = _tmplab_make ()

implement tmplab_get_stamp (tl) = tl.tmplab_stamp

implement
fprint_tmplab
  (pf | out, tl) = () where {
  val () = fprint1_string (pf | out, "__ats_lab_")
  val () = $Stamp.fprint_stamp (pf | out, tl.tmplab_stamp)
} // end of [fprint_tmplab]

end // end of [local]

(* ****** ****** *)

local

typedef tmpvar = '{
  tmpvar_typ= hityp_t
, tmpvar_ret= int (* return status *)
, tmpvar_top= int (* 0/1 : local/top(static) *)
(*
, tmpvar_root= tmpvaropt // HX-2012-10-06: removed
*)
, tmpvar_stamp= stamp_t (* unicity *)
} // end of [tmpvar]

assume tmpvar_t = tmpvar

in // in of [local]

extern typedef "tmpvar_t" = tmpvar

implement
fprint_tmpvar
  (pf | out, tmp) = () where {
  val () = fprint1_string (pf | out, "tmp(")
  val () = $Stamp.fprint_stamp (pf | out, tmp.tmpvar_stamp)
  val () = fprint1_string (pf | out, ")")
} // end of [fprint_tmpvar]

(* ****** ****** *)

implement
eq_tmpvar_tmpvar (tmp1, tmp2) =
  $Stamp.eq_stamp_stamp (tmp1.tmpvar_stamp, tmp2.tmpvar_stamp)
// end of [eq_tmpvar_tmpvar]

implement
compare_tmpvar_tmpvar (tmp1, tmp2) =
  $Stamp.compare_stamp_stamp (tmp1.tmpvar_stamp, tmp2.tmpvar_stamp)
// end of [compare_tmpvar_tmpvar]

(* ****** ****** *)

implement
tmpvar_make (hit) = let
  val stamp = $Stamp.tmpvar_stamp_make () in '{
  tmpvar_typ= hit
, tmpvar_ret= 0
, tmpvar_top= 0 (*local*)
(*
, tmpvar_root= TMPVAROPTnone () // HX-2012-10-06: removed
*)
, tmpvar_stamp= stamp
} end // end of [tmpvar_make]

(* ****** ****** *)

local

extern fun tmpvar_set_ret
  (tmp: tmpvar, ret: int): void = "atsopt_tmpvar_set_ret"
// end of [tmpvar_set_ret]

in

implement
tmpvar_make_ret (hit) = let
  val tmp = tmpvar_make (hit)
  val () = tmpvar_set_ret (tmp, 1) in tmp
end // end of [tmpvar_make_ret]

end // end of [local]

(* ****** ****** *)

implement
tmpvarlst_make (hits) = let
  val hits = hityplst_decode (hits)
  fn aux (hit: hityp): tmpvar_t = tmpvar_make (hityp_encode hit)
in
  $Lst.list_map_fun (hits, aux) 
end // end of [tmpvarlst_make]

(* ****** ****** *)

implement tmpvar_get_ret (tmp) = tmp.tmpvar_ret
implement tmpvar_get_top (tmp) = tmp.tmpvar_top
implement tmpvar_get_stamp (tmp) = tmp.tmpvar_stamp
implement tmpvar_get_typ (tmp) = tmp.tmpvar_typ

implement tmpvar_is_void (tmp) = hityp_t_is_void (tmp.tmpvar_typ)

implement tmpvar_is_nonvoid (tmp) = begin
  if hityp_t_is_void (tmp.tmpvar_typ) then false else true
end // end of [tmpvar_is_nonvoid]

end // end of [local]

(* ****** ****** *)

local

typedef funlab = '{
  funlab_name= string
, funlab_lev= int
, funlab_typ= hityp_t (* function type *)
, funlab_qua= d2cstopt (* local or global *)
, funlab_stamp= stamp_t
, funlab_tailjoined= tmpvarlst (* tail-call optimization *)
, funlab_entry= funentryopt
, funlab_prfck= int (* prfck function status *)
} // end of [typedef]

assume funlab_t = funlab

in // in of [local]

extern typedef "funlab_t" = funlab

implement
fprint_funlab (pf | out, fl) = begin
  fprint1_string (pf | out, fl.funlab_name)
end // end of [fprint_funlab]

implement
eq_funlab_funlab (fl1, fl2) = begin
  $Stamp.eq_stamp_stamp (fl1.funlab_stamp, fl2.funlab_stamp)
end // end of [eq_funlab_funlab]

implement
compare_funlab_funlab (fl1, fl2) = begin
  $Stamp.compare_stamp_stamp (fl1.funlab_stamp, fl2.funlab_stamp)
end // end of [compare_funlab_funlab]

(* ****** ****** *)

fn _funlab_make (
  name: string, level: int, hit: hityp_t, stamp: stamp_t, prfck: int
) : funlab = '{
  funlab_name= name
, funlab_lev= level
, funlab_typ= hit
, funlab_qua= D2CSTOPTnone ()
, funlab_stamp= stamp
, funlab_tailjoined= list_nil ()
, funlab_entry= None ()
, funlab_prfck= prfck
} // end of [funlab_make]

implement
funlab_make_typ (hit) = let
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
  val name = "__ats_fun_" + $Stamp.tostring_stamp stamp
in
  _funlab_make (name, level, hit, stamp, 0(*prfck*))
end // end of [funlab_make_typ]

implement
funlab_make_nam_typ
  (name, hit) = let
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
in
  _funlab_make (name, level, hit, stamp, 0(*prfck*))
end // end of [funlab_make_nam_typ]

(* ****** ****** *)

fn global_cst_name_make
  (d2c: d2cst_t): string = let
  val extdef = d2cst_get_extdef (d2c) in
  case+ extdef of
//
  | $Syn.DCSTEXTDEFnone () => $Sym.symbol_name (d2cst_get_sym d2c)
//
  | $Syn.DCSTEXTDEFsome_ext name => name
  | $Syn.DCSTEXTDEFsome_sta name => name
//
  | $Syn.DCSTEXTDEFsome_mac name => begin
      prerr_interror ();
      prerr ": global_cst_name_make: DCSTEXTDEFcall: d2c = "; prerr_d2cst d2c;
      prerr_newline ();
      $Err.abort {string} ()
    end // end of [DSTEXTDEFsome_mac]
//
end // end of [global_cst_name_make]

(* ****** ****** *)

implement
funlab_make_cst_typ
  (d2c, tmparg, hit) = let
  val is_global =
    (case+ tmparg of list_cons _ => false | _ => true): bool
  val name: string = (
    if is_global then begin
      global_cst_name_make (d2c)
    end else let
      val tmparg = hityplstlst_normalize (tmparg)
    in
      template_cst_name_make (d2c, tmparg)
    end // end of [if]
  ) : string
(*
  val () = begin
    print "funlab_make_cst_type: name = "; print name; print_newline ()
  end // end of [val]
*)
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
  val fl = _funlab_make (name, level, hit, stamp, 0(*prfck*))
  // note that template instantiation is always *local* !!!
  val () = if is_global then funlab_set_qua (fl, D2CSTOPTsome d2c)
in
  fl
end // end of [funlab_make_cst_typ]

implement
funlab_make_var_typ (d2v, hit) = let
  val d2v_name = $Sym.symbol_name (d2var_get_sym d2v)
  val level = d2var_current_level_get ()
  val stamp = $Stamp.funlab_stamp_make ()
  val stamp_name = $Stamp.tostring_stamp stamp
  val name = tostringf ("%s_%s", @(d2v_name, stamp_name))
  val name = string_of_strptr (name)
in
  _funlab_make (name, level, hit, stamp, 0(*prfck*))
end // end of [funlab_make_var_typ]

(* ****** ****** *)

implement
funlab_make_cst_prfck (d2c) = let
  val name = global_cst_name_make (d2c)
  val hit = hityp_encode (
    hityp_fun ($Syn.FUNCLOfun (), list_nil (), hityp_void)
  ) // end of [val]
  val stamp = $Stamp.funlab_stamp_make ()
  val fl = _funlab_make (name, 0(*level*), hit, stamp, 1(*prfck*))
  val () = funlab_set_qua (fl, D2CSTOPTsome d2c)
in
  fl
end // end of [funlab_make_cst_prfck] 

(* ****** ****** *)

implement funlab_get_lev (fl) = fl.funlab_lev

implement funlab_get_name (fl) = fl.funlab_name

implement funlab_get_typ (fl) = fl.funlab_typ

implement
funlab_get_typ_arg (fl) = let
  val hit_fun = hityp_decode (fl.funlab_typ) in
  case+ hit_fun.hityp_node of
  | HITfun (_(*fc*), hits_arg, _(*hit_res*)) =>
      hityplst_encode (hits_arg)
  | _ => begin
      prerr_interror ();
      prerr ": funlab_get_typ_arg: hit_fun = "; prerr_hityp hit_fun;
      prerr_newline ();
      $Err.abort {hityplst_t} ()
    end (* end of [_] *)
end // end of [funlab_get_typ_arg]

implement
funlab_get_typ_res (fl) = let
  val hit_fun = hityp_decode (fl.funlab_typ) in
  case+ hit_fun.hityp_node of
  | HITfun (_(*fc*), _(*hits_arg*), hit_res) =>
      hityp_encode (hit_res)
  | _ => begin
      prerr_interror ();
      prerr ": funlab_get_typ_res: hit_fun = "; prerr_hityp hit_fun;
      prerr_newline ();
      $Err.abort {hityp_t} ()
    end (* end of [_] *)
end // end of [funlab_get_typ_res]

implement
funlab_get_funclo (fl) = let
  val hit_fun = hityp_decode (fl.funlab_typ) in
  case+ hit_fun.hityp_node of
  | HITfun (funclo, _(*hits_arg*), _(*hit_res*)) => funclo
  | _ => begin
      prerr_interror ();
      prerr ": funlab_get_funclo: hit_fun = "; prerr_hityp hit_fun;
      prerr_newline ();
      $Err.abort {$Syn.funclo} ()
    end // end of [_]
end // end of [funlab_get_funclo]

implement funlab_get_qua (fl) = fl.funlab_qua

implement funlab_get_tailjoined (fl) = fl.funlab_tailjoined

implement funlab_get_entry (fl) = fl.funlab_entry

implement
funlab_get_entry_some (fl) = begin
  case+ fl.funlab_entry of
  | Some entry => entry | None () => begin
      prerr_interror ();
      prerr ": funlab_get_entry_some: fl = "; prerr_funlab fl; prerr_newline ();
      $Err.abort {funentry_t} ()
    end // end of [None]
end (* end of [funlab_get_entry_some] *)

implement funlab_get_prfck (fl) = fl.funlab_prfck

end // end of [local]

(* ****** ****** *)

implement
valprim_is_const (vp) =
  case+ vp.valprim_node of
  | VPbool _ => true
  | VPcastfn (_d2c, vp) => valprim_is_const (vp)
  | VPchar _ => true
  | VPcst _ => true
  | VPfloat _ => true
  | VPfun _ => true
  | VPint _ => true
  | VPsizeof _ => true
  | VPstring _ => true
  | VPtop _ => true
  | VPvoid _ => true
  | _ => false
// end of [valprim_is_const]

(* ****** ****** *)

implement
valprim_is_mutable (vp) = begin
  case+ vp.valprim_node of
  | VPargref _ => true
  | VPtmpref _ => true
  | VPcastfn (_d2c, vp) => valprim_is_mutable (vp)
  | VPargtmpref _ => true
  | _ => false
end // end of [valprim_is_mutable]

(* ****** ****** *)

implement
valprim_arg (n, hit) = '{
  valprim_node= VParg (n), valprim_typ= hit
} // end of [valprim_arg]

implement
valprim_argref (n, hit) = '{
  valprim_node= VPargref (n), valprim_typ= hit
} // end of [valprim_argref]

implement
valprim_argtmpref (n, hit) = '{
  valprim_node= VPargtmpref (n), valprim_typ= hit
} // end of [valprim_argtmpref]

(* ****** ****** *)

implement
valprim_bool (b) = '{
  valprim_node= VPbool b, valprim_typ= hityp_encode (hityp_bool)
} // end of [valprim_bool]

implement
valprim_castfn (d2c, vp, hit) = '{
  valprim_node= VPcastfn (d2c, vp), valprim_typ= hit
} // end of [valprim_castfn]

implement
valprim_char (c) = '{
  valprim_node= VPchar c, valprim_typ= hityp_encode (hityp_char)
} // end of [valprim_char]

implement
valprim_cst (d2c, hit) = '{
  valprim_node= VPcst (d2c), valprim_typ= hit
} // end of [valprim_cst]

implement
valprim_cstsp (loc, cst, hit) = '{
  valprim_node= VPcstsp (loc, cst), valprim_typ= hit
} // end of [valprim_cstsp]

implement
valprim_env (vt, hit) = '{
  valprim_node= VPenv vt, valprim_typ= hit
} // end of [valprim_env]

implement
valprim_ext (code, hit) = '{
  valprim_node= VPext code, valprim_typ= hit
} // end of [valprim_ext]

(* ****** ****** *)

implement
valprim_fix (vpr, hit) = '{
  valprim_node= VPfix (vpr), valprim_typ = hit
} // end of [valprim_fix]

(* ****** ****** *)

implement
valprim_float f(*string*) = '{
  valprim_node= VPfloat f, valprim_typ= hityp_encode (hityp_double)
} // end of [valprim_float]

implement
valprim_floatsp (f, hit) = '{
  valprim_node= VPfloatsp f, valprim_typ= hit
} // end of [valprim_floatsp]

(* ****** ****** *)

implement
valprim_clo (knd, fl, env) = let
  val hit = (if knd <> 0 then hityp_ptr else hityp_clo): hityp
in '{
  valprim_node= VPclo (knd, fl, env), valprim_typ= hityp_encode hit
} end // end of [valprim_clo]

implement
valprim_fun (funlab) = '{
  valprim_node= VPfun funlab, valprim_typ= funlab_get_typ funlab
} // end of [valprim_fun]

(* ****** ****** *)

implement
valprim_int (int) = '{
  valprim_node= VPint (int), valprim_typ= hityp_encode (hityp_int)
} // end of [valprim_int]

implement
valprim_intsp (str, int, hit) = '{
  // [valprim_typ] is incorrect
  valprim_node= VPintsp (str, int), valprim_typ= hit
} // end of [valprim_intsp]

(* ****** ****** *)

implement
valprim_ptrof (vp) = '{
  valprim_node= VPptrof vp, valprim_typ= hityp_encode (hityp_ptr)
} // end of [valprim_ptrof]

implement
valprim_ptrof_ptr_offs
  (vp, offs) = begin case+ offs of
  | list_cons _ => '{
      valprim_node= VPptrof_ptr_offs (vp, offs)
    , valprim_typ= hityp_encode (hityp_ptr)
    } // end of [list_cons]
  | list_nil () => valprim_ptrof (vp)
end // end of [valprim_ptrof_ptr_offs]

implement
valprim_ptrof_var_offs
  (vp, offs) = begin case+ offs of
  | list_cons _ => '{
      valprim_node= VPptrof_var_offs (vp, offs)
    , valprim_typ= hityp_encode (hityp_ptr)
    } // end of [list_cons]
  | list_nil () => valprim_ptrof (vp)
end // end of [valprim_ptrof_var_offs]

(* ****** ****** *)

implement
valprim_sizeof (hit) = '{
  valprim_node= VPsizeof hit
, valprim_typ= hityp_encode (hityp_int)
} // end of [valprim_sizeof]

implement
valprim_string (str, len) = '{
  valprim_node= VPstring (str, len)
, valprim_typ= hityp_encode (hityp_string)
} // end of [valprim_string]

implement
valprim_tmp (tmp) = '{
  valprim_node= VPtmp tmp, valprim_typ= tmpvar_get_typ tmp
} // end of [valprim_tmp]

implement
valprim_tmpref (tmp) = '{
  valprim_node= VPtmpref tmp, valprim_typ= tmpvar_get_typ tmp
} // end of [valprim_tmpref]

implement
valprim_top (hit) = '{
  valprim_node= VPtop (), valprim_typ= hit
} // end of [valprim_top]

implement
valprim_void () = '{
  valprim_node= VPvoid (), valprim_typ= hityp_encode (hityp_void)
} // end of [valprim_void]

(* ****** ****** *)

implement
valprim_is_void (vp) = begin
  hityp_is_void (hityp_decode vp.valprim_typ)
end // end of [valprim_is_void]

(* ****** ****** *)

implement
instr_call
  (loc, tmp_res, hit_fun, vp_fun, vps_arg) = '{
  instr_loc= loc
, instr_node= INSTRcall (tmp_res, hit_fun, vp_fun, vps_arg)
} // end of [instr_call]

implement
instr_call_tail (loc, fl) = '{
  instr_loc= loc, instr_node= INSTRcall_tail (fl)
} // end of [instr_call_tail]

(* ****** ****** *)

implement
instr_cond (loc, _test, _then, _else) = '{
  instr_loc= loc, instr_node= INSTRcond (_test, _then, _else)
} // end of [instr_cond]

(* ****** ****** *)

implement
instr_function
  (loc, tmp_res, vps_arg, _body, tmp_ret) = '{
  instr_loc= loc
, instr_node= INSTRfunction (tmp_res, vps_arg, _body, tmp_ret)
} // end of [instr_function]

(* ****** ****** *)

implement
instr_funlab (fl) = '{
  instr_loc= $Loc.location_dummy, instr_node= INSTRfunlab (fl)
} // end of [instr_funlab]

(* ****** ****** *)

implement
instr_prfck_beg (d2c) = '{
  instr_loc= $Loc.location_dummy
, instr_node= INSTRprfck_beg (d2c)
}
implement
instr_prfck_tst (d2c) = '{
  instr_loc= $Loc.location_dummy
, instr_node= INSTRprfck_tst (d2c)
}
implement
instr_prfck_end (d2c) = '{
  instr_loc= $Loc.location_dummy
, instr_node= INSTRprfck_end (d2c)
}

(* ****** ****** *)

fun instr_arr_heap (
  loc: loc_t
, tmp_res: tmpvar_t, asz: int, hit_elt: hityp_t
) : instr = '{
  instr_loc= loc
, instr_node= INSTRarr_heap (tmp_res, asz, hit_elt)
} // end of [instr_arr_heap]

implement
instr_add_arr_heap
  (res, loc, tmp_res, asz, hit_elt) = begin
  res := list_vt_cons (instr_arr_heap (loc, tmp_res, asz, hit_elt), res)
end // end of [instr_add_arr_heap]

(* ****** ****** *)

fun instr_arr_stack (
  loc: loc_t
, tmp_res: tmpvar_t
, level: int // top: level = 0; inner: level > 0
, vp_asz: valprim
, hit_elt: hityp_t
) : instr = '{
  instr_loc= loc
, instr_node= INSTRarr_stack (tmp_res, level, vp_asz, hit_elt)
} // end of [instr_arr_stack]

implement
instr_add_arr_stack
  (res, loc, tmp_res, level, vp_asz, hit_elt) = begin
  res := list_vt_cons (instr_arr_stack (loc, tmp_res, level, vp_asz, hit_elt), res)
end // end of [instr_add_arr_stack]

(* ****** ****** *)

fun instr_assgn_arr (
  loc: loc_t
, tmp_ptr: tmpvar_t
, vp_asz: valprim, tmp_elt: tmpvar_t, vp_tsz: valprim
) : instr = '{
  instr_loc= loc
, instr_node= INSTRassgn_arr (tmp_ptr, vp_asz, tmp_elt, vp_tsz)
} // end of [instr_assgn_arr]

implement
instr_add_assgn_arr
  (res, loc, vp_arr, vp_asz, tmp_elt, vp_tsz) = res :=
  list_vt_cons (instr_assgn_arr (loc, vp_arr, vp_asz, tmp_elt, vp_tsz), res)
// end of [instr_add_assgn_arr]

(* ****** ****** *)

fun instr_assgn_clo (
  loc: loc_t
, tmp_ptr: tmpvar_t
, tmp_clo: tmpvar_t
, fl: funlab_t
, env: envmap_t
) : instr = '{
  instr_loc= loc
, instr_node= INSTRassgn_clo (tmp_ptr, tmp_clo, fl, env)
} // end of [instr_assgn_clo]

implement
instr_add_assgn_clo
  (res, loc, vp_clo, tmp_clo, fl, env) =
  res := list_vt_cons (instr_assgn_clo (loc, vp_clo, tmp_clo, fl, env), res)
// end of [instr_add_assgn_clo]

(* ****** ****** *)

implement
instr_add_call
  (res, loc, tmp_res, hit_fun, vp_fun, vps_arg) = let
  val ins = instr_call (loc, tmp_res, hit_fun, vp_fun, vps_arg)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_call]

implement
instr_add_call_tail (res, loc, fl) =
  res := list_vt_cons (instr_call_tail (loc, fl), res)
// end of [instr_add_call_tail]

(* ****** ****** *)

fun instr_define_clo (
  loc: loc_t, d2c: d2cst_t, fl: funlab_t
) : instr = '{
  instr_loc= loc, instr_node= INSTRdefine_clo (d2c, fl)
} // end of [instr_define_clo]

implement
instr_add_define_clo (res, loc, d2c, fl) =
  res := list_vt_cons (instr_define_clo (loc, d2c, fl), res)
// end of [instr_add_define_clo]

fun instr_define_fun (
  loc: loc_t, d2c: d2cst_t, fl: funlab_t
) : instr = '{
  instr_loc= loc, instr_node= INSTRdefine_fun (d2c, fl)
} // end of [instr_define_fun]

implement
instr_add_define_fun (res, loc, d2c, fl) =
  res := list_vt_cons (instr_define_fun (loc, d2c, fl), res)
// end of [instr_add_define_fun]

fun instr_define_val (
  loc: loc_t, d2c: d2cst_t, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRdefine_val (d2c, vp)
} // end of [instr_define_val]

implement
instr_add_define_val (res, loc, d2c, vp) =
  res := list_vt_cons (instr_define_val (loc, d2c, vp), res)
// end of [instr_add_define_val]

(* ****** ****** *)

//
// HX-2011-01-15: partial value template
//
fun instr_define_partval (
  loc: loc_t, name: string, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRdefine_partval (name, vp)
} // end of [instr_define_partval]

implement
instr_add_define_partval (res, loc, name, vp) =
  res := list_vt_cons (instr_define_partval (loc, name, vp), res)
// end of [instr_add_define_partval]

(* ****** ****** *)

fun instr_extval (
  loc: loc_t, name: string, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRextval (name, vp)
} // end of [instr_extval]

implement
instr_add_extval (res, loc, name, vp) =
  res := list_vt_cons (instr_extval (loc, name, vp), res)
// end of [instr_add_extval]

(* ****** ****** *)

fun instr_freeptr
  (loc: loc_t, vp: valprim): instr = '{
  instr_loc= loc, instr_node= INSTRfreeptr (vp)
} // end of [instr_freeptr]

implement
instr_add_freeptr (res, loc, vp) =
  res := list_vt_cons (instr_freeptr (loc, vp), res)
// end of [instr_add_freeptr]

(* ****** ****** *)

fun instr_patck (
  loc: loc_t
, vp: valprim, patck: patck, fail: kont
) : instr = '{
  instr_loc= loc, instr_node= INSTRpatck (vp, patck, fail)
} // end of [instr_patck]

implement
instr_add_patck (res, loc, vp, patck, fail) =
  res := list_vt_cons (instr_patck (loc, vp, patck, fail), res)
// end of [instr_add_patck]

(* ****** ****** *)

fun instr_dynload_file
  (loc: loc_t, fil: fil_t): instr = '{
  instr_loc= loc, instr_node= INSTRdynload_file (fil)
} // end of [instr_dynload]

implement
instr_add_dynload_file (res, loc, fil) =
  res := list_vt_cons (instr_dynload_file (loc, fil), res)
// end of [instr_add_dynload_file]

(* ****** ****** *)

fun instr_load_ptr (
  loc: loc_t, tmp: tmpvar_t, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRload_ptr (tmp, vp)
} // end of [instr_load_ptr]

fun instr_load_var (
  loc: loc_t, tmp: tmpvar_t, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRload_var (tmp, vp)
} // end of [instr_load_var]

fun instr_load_ptr_offs (
  loc: loc_t, tmp: tmpvar_t, vp: valprim, offs: offsetlst
) : instr = '{
  instr_loc= loc, instr_node= INSTRload_ptr_offs (tmp, vp, offs)
} // end of [instr_load_ptr_offs]

fun instr_load_var_offs (
  loc: loc_t, tmp: tmpvar_t, vp: valprim, offs: offsetlst
) : instr = '{
  instr_loc= loc, instr_node= INSTRload_var_offs (tmp, vp, offs)
} // end of [instr_load_var_offs]

implement
instr_add_load_ptr
  (res, loc, tmp, vp) = begin
  res := list_vt_cons (instr_load_ptr (loc, tmp, vp), res)
end (* end of [instr_add_load_ptr] *)

implement
instr_add_load_ptr_offs
  (res, loc, tmp, vp, offs) = let
  val ins = (case+ offs of
    | list_cons _ =>
        instr_load_ptr_offs (loc, tmp, vp, offs)
    | list_nil () => instr_load_ptr (loc, tmp, vp)
  ) : instr // end of [val]
in
  res := list_vt_cons (ins, res)
end (* end of [instr_add_load_ptr_offs] *)

implement
instr_add_load_var_offs
  (res, loc, tmp, vp, offs) = let
  val ins = (case+ offs of
    | list_cons _ =>
        instr_load_var_offs (loc, tmp, vp, offs)
    | list_nil () => instr_load_var (loc, tmp, vp)
  ) : instr // end of [val]
in
  res := list_vt_cons (ins, res)
end (* end of [instr_add_load_var_offs] *)

(* ****** ****** *)

fun instr_loop (
  loc: loc_t
, lab_init: tmplab_t
, lab_fini: tmplab_t
, lab_cont: tmplab_t
, inss_init: instrlst
, vp_test: valprim
, inss_test: instrlst
, inss_post: instrlst
, inss_body: instrlst
) : instr = '{
  instr_loc= loc
, instr_node= INSTRloop (
    lab_init, lab_fini, lab_cont, inss_init, vp_test, inss_test, inss_post, inss_body
  ) // end of [INSTRloop]
} // end of [instr_loop]

implement
instr_add_loop (
    res
  , loc
  , lab_init, lab_fini, lab_cont
  , inss_init
  , vp_test, inss_test
  , inss_post
  , inss_body
  ) = let
  val ins = instr_loop (
    loc, lab_init, lab_fini, lab_cont, inss_init, vp_test, inss_test, inss_post, inss_body
  ) // end of [INSTRloop]
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_loop]

fun instr_loopexn (
  loc: loc_t, knd: int, tl: tmplab_t
) : instr = '{
  instr_loc= loc, instr_node= INSTRloopexn (knd, tl)
} // end of [instr_loopexn]

implement
instr_add_loopexn (res, loc, knd, tl) = 
  res := list_vt_cons (instr_loopexn (loc, knd, tl), res)
// end of [instr_add_loopexn]

(* ****** ****** *)

fun instr_move_arg (
  loc: loc_t, arg: int, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRmove_arg (arg, vp)
} // end of [instr_move_arg]

implement
instr_add_move_arg
  (res, loc, arg, vp) =
  res := list_vt_cons (instr_move_arg (loc, arg, vp), res)
// end of [instr_add_move_arg]

fun instr_move_con (
  loc: loc_t
, tmp_res: tmpvar_t
, hit_sum: hityp_t
, d2c: d2con_t
, vps_arg: valprimlst
) : instr = '{
  instr_loc= loc, instr_node= INSTRmove_con (tmp_res, hit_sum, d2c, vps_arg)
} // end of [instr_move_arg]

implement
instr_add_move_con
  (res, loc, tmp_res, hit_sum, d2c, vps_arg) =
  res := list_vt_cons (instr_move_con (loc, tmp_res, hit_sum, d2c, vps_arg), res)
// end of [instr_add_move_con]

(* ****** ****** *)

fun instr_move_lazy_delay (
  loc: loc_t
, tmp_res: tmpvar_t
, lin: int
, hit_body: hityp_t
, vp_clo: valprim
) : instr = '{
  instr_loc= loc
, instr_node= INSTRmove_lazy_delay (tmp_res, lin, hit_body, vp_clo)
} // end of [instr_add_move_lazy_delay]

implement
instr_add_move_lazy_delay
  (res, loc, tmp_res, lin, hit_body, vp_clo) = let
  val ins = instr_move_lazy_delay (loc, tmp_res, lin, hit_body, vp_clo)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_move_lazy_delay]

(* ****** ****** *)

fun instr_move_lazy_force (
  loc: loc_t
, tmp_res: tmpvar_t
, lin: int
, hit_val: hityp_t
, vp_lazy: valprim
) : instr = '{
  instr_loc= loc
, instr_node= INSTRmove_lazy_force (tmp_res, lin, hit_val, vp_lazy)
} // end of [instr_move_lazy_force]

implement
instr_add_move_lazy_force
  (res, loc, tmp_res, lin, hit_val, vp_lazy) = let
  val ins = instr_move_lazy_force (loc, tmp_res, lin, hit_val, vp_lazy)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_move_lazy_force]

(* ****** ****** *)

fun instr_move_rec_flt (
  loc: loc_t
, tmp_res: tmpvar_t
, hit_rec: hityp_t
, lvps: labvalprimlst
) : instr = '{
  instr_loc= loc
, instr_node= INSTRmove_rec_flt (tmp_res, hit_rec, lvps)
} // end of [instr_move_rec_flt]

fun instr_move_rec_box (
  loc: loc_t
, tmp_res: tmpvar_t
, hit_rec: hityp_t
, lvps: labvalprimlst
) : instr = '{
  instr_loc= loc
, instr_node= INSTRmove_rec_box (tmp_res, hit_rec, lvps)
} // end of [instr_move_rec_box]

implement
instr_add_move_rec
  (res, loc, tmp_res, recknd, hit_rec, lvps) = let
  val ins = (case+ 0 of
    | _ when recknd = 0 => instr_move_rec_flt (loc, tmp_res, hit_rec, lvps)
    | _ when recknd > 0 => instr_move_rec_box (loc, tmp_res, hit_rec, lvps)
    | _ => begin
        prerr_interror ();
        prerr ": instr_add_move_rec: recknd = "; prerr recknd; prerr_newline ();
        $Err.abort {instr} ()
      end // end of [_]
    ) : instr // end of [val]
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_move_rec]

(* ****** ****** *)

fun instr_move_ref (
  loc: loc_t, tmp_res: tmpvar_t, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRmove_ref (tmp_res, vp)
} // end of [instr_move_ref]

implement
instr_add_move_ref (res, loc, tmp_res, vp) =
  res := list_vt_cons (instr_move_ref (loc, tmp_res, vp), res)
// end of [instr_add_move_ref]

fun instr_move_val (
  loc: loc_t, tmp_res: tmpvar_t, vp: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRmove_val (tmp_res, vp)
} // end of [instr_move_val]

implement
instr_add_move_val (res, loc, tmp_res, vp) =
  res := list_vt_cons (instr_move_val (loc, tmp_res, vp), res)
// end of [instr_add_move_val]

(* ****** ****** *)

fun instr_raise (
  loc: loc_t, tmp_res: tmpvar_t, vp_exn: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRraise (tmp_res, vp_exn)
} // end of [instr_raise]

implement
instr_add_raise (res, loc, tmp_res, vp_exn) =
  res := list_vt_cons (instr_raise (loc, tmp_res, vp_exn), res)
// end of [instr_add_raise]

(* ****** ****** *)

fun instr_select (
  loc: loc_t
, tmp_res: tmpvar_t
, vp_root: valprim
, offs: offsetlst
) : instr = '{
  instr_loc= loc
, instr_node= INSTRselect (tmp_res, vp_root, offs)
} // end of [instr_select]

implement
instr_add_select 
  (res, loc, tmp_res, vp_root, offs) =
  res := list_vt_cons (instr_select (loc, tmp_res, vp_root, offs), res)
// end of [instr_add_select]

fun instr_selcon (
  loc: loc_t
, tmp_res: tmpvar_t
, vp_sum: valprim
, hit_sum: hityp_t
, ind: int
) : instr = '{
  instr_loc= loc
, instr_node= INSTRselcon (tmp_res, vp_sum, hit_sum, ind)
} // end of [instr_selcon]

implement
instr_add_selcon
  (res, loc, tmp_res, vp_sum, hit_sum, ind) =
  res := list_vt_cons (instr_selcon (loc, tmp_res, vp_sum, hit_sum, ind), res)
// end of [instr_add_selcon]

fun instr_selcon_ptr (
  loc: loc_t
, tmp_res: tmpvar_t
, vp_sum: valprim
, hit_sum: hityp_t
, ind: int
) : instr = '{
  instr_loc= loc
, instr_node= INSTRselcon_ptr (tmp_res, vp_sum, hit_sum, ind)
} // end of [instr_selcon_ptr]

implement
instr_add_selcon_ptr
  (res, loc, tmp_res, vp_sum, hit_sum, ind) = let
  val ins = instr_selcon_ptr (loc, tmp_res, vp_sum, hit_sum, ind)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_selcon_ptr]

(* ****** ****** *)

fun instr_store_ptr (
  loc: loc_t, vp_ptr: valprim, vp_all: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRstore_ptr (vp_ptr, vp_all)
} // end of [instr_store_ptr]

fun instr_store_ptr_offs (
  loc: loc_t
, vp_ptr: valprim, offs: offsetlst, vp_all: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRstore_ptr_offs (vp_ptr, offs, vp_all)
} // end of [instr_store_ptr_offs]

implement
instr_add_store_ptr_offs
  (res, loc, vp_ptr, offs, vp_val) = let
  val ins = case+ offs of
    | list_cons _ =>
        instr_store_ptr_offs (loc, vp_ptr, offs, vp_val)
    | list_nil () => instr_store_ptr (loc, vp_ptr, vp_val)
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_store_ptr_offs]

(* ****** ****** *)

fun instr_store_var (
  loc: loc_t, vp_mut: valprim, vp_all: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRstore_var (vp_mut, vp_all)
} // end of [instr_store_var]

fun instr_store_var_offs (
  loc: loc_t
, vp_mut: valprim, offs: offsetlst, vp_all: valprim
) : instr = '{
  instr_loc= loc, instr_node= INSTRstore_var_offs (vp_mut, offs, vp_all)
} // end of [instr_store_var_offs]

implement
instr_add_store_var_offs
  (res, loc, vp_mut, offs, vp_val) = let
  val ins = (case+ offs of
    | list_cons _ =>
        instr_store_var_offs (loc, vp_mut, offs, vp_val)
    | list_nil () => instr_store_var (loc, vp_mut, vp_val)
  ) : instr // end of [val]
in
  res := list_vt_cons (ins, res)
end // end of [instr_add_store_var_offs]

(* ****** ****** *)

fun instr_switch 
  (loc: loc_t, brs: branchlst): instr = '{
  instr_loc= loc, instr_node= INSTRswitch (brs)
} // end of [instr_switch]

implement
instr_add_switch (res, loc, brs) =
  res := list_vt_cons (instr_switch (loc, brs), res)
// end of [instr_add_switch]

fun instr_tmplabint
  (loc: loc_t, tl: tmplab_t, ind: int): instr = '{
  instr_loc= loc, instr_node= INSTRtmplabint (tl, ind)
} // end of [instr_tmplabint]

implement
instr_add_tmplabint (res, loc, tl, ind) =
  res := list_vt_cons (instr_tmplabint (loc, tl, ind), res)
// end of [instr_add_tmplabint]

(* ****** ****** *)

fun instr_trywith (
  loc: loc_t
, res_try: instrlst
, tmp_exn: tmpvar_t
, brs: branchlst
) : instr = '{
  instr_loc= loc
, instr_node= INSTRtrywith (res_try, tmp_exn, brs)
} // end of [instr_trywith]

implement
instr_add_trywith
  (res, loc, res_try, tmp_exn, brs) =
  res := list_vt_cons (instr_trywith (loc, res_try, tmp_exn, brs), res)
// end of [instr_add_trywith]

fun instr_vardec
  (loc: loc_t, tmp: tmpvar_t): instr = '{
  instr_loc= loc, instr_node= INSTRvardec (tmp)
} // end of [instr_vardec]

implement
instr_add_vardec (res, loc, tmp) =
  res := list_vt_cons (instr_vardec (loc, tmp), res)
// end of [instr_add_vardec]

(* ****** ****** *)

%{$

ats_void_type
atsopt_funlab_set_qua
  (ats_ptr_type fl, ats_ptr_type od2c) {
  ((funlab_t)fl)->atslab_funlab_qua = od2c ; return ;
} // end of [atsopt_funlab_set_qua]

ats_void_type
atsopt_funlab_set_entry
  (ats_ptr_type fl, ats_ptr_type entry) {
  ((funlab_t)fl)->atslab_funlab_entry = entry ; return ;
} // end of [atsopt_funlab_set_entry]

ats_void_type
atsopt_funlab_set_tailjoined
  (ats_ptr_type fl, ats_ptr_type tmps) {
  ((funlab_t)fl)->atslab_funlab_tailjoined = tmps ; return ;
} // end of [atsopt_funlab_set_tailjoined]

ats_void_type
atsopt_tmpvar_set_ret
  (ats_ptr_type tmp, ats_int_type ret) {
  ((tmpvar_t)tmp)->atslab_tmpvar_ret = ret ; return ;
} // end of [atsopt_tmpvar_set_ret]

ats_void_type
atsopt_tmpvar_set_top
  (ats_ptr_type tmp, ats_int_type top) {
  ((tmpvar_t)tmp)->atslab_tmpvar_top = top ; return ;
} // end of [atsopt_tmpvar_set_top]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_ccomp.dats] *)
