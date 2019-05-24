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

staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_dynexp3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

implement p3at_ann
  (loc, s2e, p3t, s2e_ann) = '{
  p3at_loc= loc
, p3at_node= P3Tann (p3t, s2e_ann)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_ann]

implement p3at_any
  (loc, s2e, d2v) = '{
  p3at_loc= loc
, p3at_node= P3Tany d2v
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_any]

implement p3at_as
  (loc, s2e, refknd, d2v, p3t) = '{
  p3at_loc= loc
, p3at_node= P3Tas (refknd, d2v, p3t)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_as]

implement p3at_bool (loc, s2e, b) = '{
  p3at_loc= loc
, p3at_node= P3Tbool b
, p3at_typ= s2e
, p3at_typ_lft= None ()
}

implement p3at_char (loc, s2e, chr) = '{
  p3at_loc= loc
, p3at_node= P3Tchar chr
, p3at_typ= s2e
, p3at_typ_lft= None ()
}

implement p3at_con
  (loc, s2e, freeknd, d2c, npf, p3ts_arg) = '{
  p3at_loc= loc
, p3at_node= P3Tcon (freeknd, d2c, npf, p3ts_arg)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_con]

implement p3at_empty (loc, s2e) = '{
  p3at_loc= loc
, p3at_node= P3Tempty ()
, p3at_typ= s2e
, p3at_typ_lft= None ()
}

implement p3at_exist
  (loc, s2e, s2vs, p3t) = '{
  p3at_loc= loc
, p3at_node= P3Texist (s2vs, p3t)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_exist]

implement p3at_float
  (loc, s2e, f(*string*)) = '{
  p3at_loc= loc
, p3at_node= P3Tfloat f
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_float]

implement p3at_int
  (loc, s2e, str, int(*intinf*)) = '{
  p3at_loc= loc
, p3at_node= P3Tint (str, int)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_int]

implement p3at_lst
  (loc, s2e_elt, s2e_lst, p3ts) = '{
  p3at_loc= loc
, p3at_node= P3Tlst (s2e_elt, p3ts)
, p3at_typ= s2e_lst
, p3at_typ_lft= None ()
} // end of [p3at_lst]

implement p3at_rec
  (loc, s2e, knd, npf, lp3ts) = '{
  p3at_loc= loc
, p3at_node= P3Trec (knd, npf, lp3ts)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_rec]

implement p3at_string
  (loc, s2e, str) = '{
  p3at_loc= loc
, p3at_node= P3Tstring str
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_string]

implement p3at_var
  (loc, s2e, refknd, d2v) = '{
  p3at_loc= loc
, p3at_node= P3Tvar (refknd, d2v)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_var]

implement p3at_vbox
  (loc, s2e, d2v) = '{
  p3at_loc= loc
, p3at_node= P3Tvbox (d2v)
, p3at_typ= s2e
, p3at_typ_lft= None ()
} // end of [p3at_vbox]

(* ****** ****** *)

extern typedef "p3at_t" = p3at

%{$

ats_void_type
atsopt_p3at_set_typ (
  ats_ptr_type p3t, ats_ptr_type s2e) {
  ((p3at_t)p3t)->atslab_p3at_typ = s2e ; return ;
} // end of [atsopt_p3at_set_typ]

ats_void_type
atsopt_p3at_set_typ_lft (
  ats_ptr_type p3t, ats_ptr_type os2e) {
  ((p3at_t)p3t)->atslab_p3at_typ_lft = os2e ; return ;
} // end of [atsopt_p3at_set_typ_lft]

%} // end of [%{$]

(* ****** ****** *)

fun d3exp_eff_union (s2fe: s2eff, d3e: d3exp): s2eff =
  s2eff_union_s2eff (s2fe, d3e.d3exp_eff)

fun d3expopt_eff_union
  (s2fe: s2eff, od3e: d3expopt): s2eff = case+ od3e of
  | Some d3e => d3exp_eff_union (s2fe, d3e) | None () => s2fe
// end of [d3expopt_eff_union]

fun d3explst_eff_union (s2fe: s2eff, d3es: d3explst): s2eff =
  case+ d3es of
  | cons (d3e, d3es) => begin
      d3explst_eff_union (d3exp_eff_union (s2fe, d3e), d3es)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [d3explst_eff_union]

fun d3explstlst_eff_union (s2fe: s2eff, d3ess: d3explstlst): s2eff =
  case+ d3ess of
  | cons (d3es, d3ess) => begin
      d3explstlst_eff_union (d3explst_eff_union (s2fe, d3es), d3ess)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [d3explstlst_eff_union]

fun labd3explst_eff_union (s2fe: s2eff, ld3es: labd3explst): s2eff =
  case+ ld3es of
  | LABD3EXPLSTcons (_(*lab*), d3e, ld3es) => begin
      labd3explst_eff_union (d3exp_eff_union (s2fe, d3e), ld3es)
    end // end of [LABD3EXPLSTcons]
  | LABD3EXPLSTnil () => s2fe // end of [LABD3EXPLSTnil]
// end of [labd3explst_eff_union]

fn d3lab1_eff_union (s2fe: s2eff, d3l: d3lab1): s2eff =
  case+ d3l.d3lab1_node of
  | D3LAB1ind (d3ess, _) => d3explstlst_eff_union (s2fe, d3ess)
  | D3LAB1lab _ => s2fe
// end of [d3lab1_eff_union]

fun d3lab1lst_eff_union (s2fe: s2eff, d3ls: d3lab1lst): s2eff =
  case+ d3ls of
  | cons (d3l, d3ls) => begin
      d3lab1lst_eff_union (d3lab1_eff_union (s2fe, d3l), d3ls)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [d3lab1lst_eff_union]

fun c3laulst_eff_union (s2fe: s2eff, c3ls: c3laulst): s2eff =
  case+ c3ls of
  | cons (c3l, c3ls) => begin
      c3laulst_eff_union (d3exp_eff_union (s2fe, c3l.c3lau_exp), c3ls)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [c3laulst_eff_union]

fun sc3laulst_eff_union (s2fe: s2eff, sc3ls: sc3laulst): s2eff =
  case+ sc3ls of
  | cons (sc3l, sc3ls) => begin
      sc3laulst_eff_union (d3exp_eff_union (s2fe, sc3l.sc3lau_exp), sc3ls)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [sc3laulst_eff_union]

fun v3aldeclst_eff_union (s2fe: s2eff, d3cs: v3aldeclst): s2eff =
  case+ d3cs of
  | cons (d3c, d3cs) => begin
      v3aldeclst_eff_union (d3exp_eff_union (s2fe, d3c.v3aldec_def), d3cs)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [v3aldeclst_eff_union]

fun v3ardeclst_eff_union (s2fe: s2eff, d3cs: v3ardeclst): s2eff =
  case+ d3cs of
  | cons (d3c, d3cs) => begin case+ d3c.v3ardec_ini of
    | Some d3e => begin
        v3ardeclst_eff_union (d3exp_eff_union (s2fe, d3e), d3cs)
      end // end of [Some]
    | None () => v3ardeclst_eff_union (s2fe, d3cs)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
// end of [v3ardeclst_eff_union]

fun d3ec_eff_union (s2fe: s2eff, d3c: d3ec): s2eff = begin
  case+ d3c.d3ec_node of
  | D3Cextval (_(*name*), d3e_def) => begin
      s2eff_union_s2eff (s2fe, d3e_def.d3exp_eff)
    end // end of [D3Cextval]
  | D3Cextcode _ => S2EFFall ()
  | D3Cvaldecs (valknd, d3cs) => begin case+ valknd of
      | $Syn.VALKINDprval () => s2fe | _ => v3aldeclst_eff_union (s2fe, d3cs)
    end // end of [D3Cvaldecs]
  | D3Cvardecs (d3cs) => v3ardeclst_eff_union (s2fe, d3cs)
  | D3Cimpdec (d3c) => d3exp_eff_union (s2fe, d3c.i3mpdec_def)
  | D3Clocal (d3cs_head, d3cs_body) => let
      val s2fe = d3eclst_eff_union (s2fe, d3cs_head)
      val s2fe = d3eclst_eff_union (s2fe, d3cs_body)
    in
      s2fe
    end // end of [D3Clocal]
  | _ => s2fe // end of [_]
end // end of [d3ec_eff_union]

and d3eclst_eff_union
  (s2fe: s2eff, d3cs: d3eclst): s2eff = begin case+ d3cs of
  | cons (d3c, d3cs) => begin
      d3eclst_eff_union (d3ec_eff_union (s2fe, d3c), d3cs)
    end // end of [cons]
  | nil () => s2fe // end of [nil]
end // end of [d3eclst_eff_union]

(* ****** ****** *)

implement d3exp_ann_type (loc, d3e, s2e) = '{
  d3exp_loc= loc
, d3exp_eff= d3e.d3exp_eff, d3exp_typ= s2e
, d3exp_node= D3Eann_type (d3e, s2e)
}

implement d3exp_app_dyn
  (loc, s2e_app, s2fe_app, d3e_fun, npf, d3es_arg) = let
  val s2fe = s2eff_union_s2eff (s2fe_app, d3e_fun.d3exp_eff)
  val s2fe = d3explst_eff_union (s2fe, d3es_arg)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_app
, d3exp_node= D3Eapp_dyn (d3e_fun, npf, d3es_arg)
} end // end of [d3exp_app_dyn]

implement d3exp_app_sta (loc, s2e_app, d3e_fun) = '{
  d3exp_loc= loc
, d3exp_eff= d3e_fun.d3exp_eff, d3exp_typ= s2e_app
, d3exp_node= D3Eapp_sta d3e_fun
}

(* ****** ****** *)

implement
d3exp_arrinit (
  loc, s2e_arr, s2e_elt, od3e_asz, d3es_elt
) = let
  val s2fe = S2EFFnil ()
  val s2fe = d3expopt_eff_union (s2fe, od3e_asz)
  val s2fe = d3explst_eff_union (s2fe, d3es_elt)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_arr
, d3exp_node= D3Earrinit (s2e_elt, od3e_asz, d3es_elt)
} end // end of [d3exp_arrinit]

implement
d3exp_arrpsz (
  loc, s2e_arr, s2e_elt, d3es_elt
) = let
  val s2fe = d3explst_eff_union (S2EFFnil (), d3es_elt)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_arr
, d3exp_node= D3Earrpsz (s2e_elt, d3es_elt)
} end // end of [d3exp_arrpsz]

(* ****** ****** *)

implement d3exp_assgn_ptr
  (loc, d3e_ptr, d3ls, d3e_val) = let
  val s2fe = d3e_ptr.d3exp_eff
  val s2fe = d3lab1lst_eff_union (s2fe, d3ls)
  val s2fe = d3exp_eff_union (s2fe, d3e_val)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Eassgn_ptr (d3e_ptr, d3ls, d3e_val)
} end // end of [d3exp_assgn_ptr]

implement d3exp_assgn_var
  (loc, d2v, d3ls, d3e) = let
  val s2fe = d3lab1lst_eff_union (S2EFFnil (), d3ls)
  val s2fe = d3exp_eff_union (s2fe, d3e)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Eassgn_var (d2v, d3ls, d3e)
} end // end of [d3exp_assgn_var]

//

implement d3exp_bool
  (loc, s2e, b(*bool*)) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Ebool b
} // end of [d3exp_bool]

//

implement d3exp_caseof
  (loc, s2e_case, casknd, d3es, c3ls) = let
  val s2fe = S2EFFnil ()
  val s2fe = d3explst_eff_union (s2fe, d3es)
  val s2fe = c3laulst_eff_union (s2fe, c3ls)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_case
, d3exp_node= D3Ecaseof (casknd, d3es, c3ls)
} end // end of [d3exp_caseof]

implement d3exp_char
  (loc, s2e, c(*char*)) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Echar c
} // end of [d3exp_char]

implement d3exp_con
  (loc, s2e, d2c, npf, d3es_arg) = let
  val isuni = aux d3es_arg where {
    fun aux (d3es: d3explst): bool = case+ d3es of
      | list_cons (d3e, d3es) => begin
          case+ d3e.d3exp_node of D3Etop () => true | _ => aux d3es
        end
      | list_nil () => false
  } // end of [where]
  var s2e: s2exp = s2e
  val () =
    if isuni then let
      val s2es_arg = d3explst_get_typ d3es_arg
    in
      s2e := s2exp_datcontyp (d2c, s2es_arg)
    end 
  val s2fe = d3explst_eff_union (S2EFFnil (), d3es_arg)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Econ (d2c, npf, d3es_arg)
} end // end of [d3exp_con]

implement
d3exp_crypt (loc, s2e, knd, d3e) =  '{
  d3exp_loc= loc
, d3exp_eff= d3e.d3exp_eff, d3exp_typ= s2e
, d3exp_node= D3Ecrypt (knd, d3e)
} // end of [d3exp_crypt]

(* ****** ****** *)

implement
d3exp_cst (loc, d2c) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= d2cst_get_typ d2c
, d3exp_node= D3Ecst d2c
} // end of [d3exp_cst]

implement
d3exp_cstsp (loc, s2e, cst) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Ecstsp cst
} // end of [d3exp_cstsp]

(* ****** ****** *)

implement
d3exp_dynload (loc, fil) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFall (), d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Edynload (fil)
}

implement
d3exp_effmask (loc, effs, d3e) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= d3e.d3exp_typ
, d3exp_node= D3Eeffmask (effs, d3e)
}

implement
d3exp_empty (loc, s2e) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Eempty ()
}

implement
d3exp_extval (loc, s2e, code) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Eextval (code)
} // end of [d3exp_extval]

implement
d3exp_fix (
  loc, s2e_fix, knd, d2v, d3e_def
) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil ()
, d3exp_typ= s2e_fix
, d3exp_node= D3Efix (knd, d2v, d3e_def)
} // end of [d3exp_fix]

implement
d3exp_float (loc, s2e, str) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Efloat str
}

implement
d3exp_floatsp (loc, s2e, str) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Efloatsp str
}

implement
d3exp_foldat (loc, d3e) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Efoldat d3e
}

implement
d3exp_freeat (loc, d3e) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Efreeat d3e
}

implement
d3exp_if (
  loc, s2e, d3e_cond, d3e_then, d3e_else
) = let
  val s2fe = d3e_cond.d3exp_eff
  val s2fe = d3exp_eff_union (s2fe, d3e_then)
  val s2fe = d3exp_eff_union (s2fe, d3e_else)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Eif (d3e_cond, d3e_then, d3e_else)
} end // end of [d3exp_if]

implement
d3exp_int (loc, s2e_int, str, int) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e_int
, d3exp_node= D3Eint (str, int)
} // end of [d3exp_int]

implement
d3exp_intsp (loc, s2e_int, str, int) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e_int
, d3exp_node= D3Eintsp (str, int)
} // end of [d3exp_int]

(* ****** ****** *)

implement d3exp_lam_dyn
  (loc, s2e_fun, lin, npf, p3ts_arg, d3e_body) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e_fun
, d3exp_node= D3Elam_dyn (lin, npf, p3ts_arg, d3e_body)
} // end of [d3exp_lam_dyn]

implement d3exp_laminit_dyn
  (loc, s2e_fun, lin, npf, p3ts_arg, d3e_body) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e_fun
, d3exp_node= D3Elaminit_dyn (lin, npf, p3ts_arg, d3e_body)
} // end of [d3exp_laminit_dyn]

(* ****** ****** *)

implement d3exp_lam_met
  (loc, s2es_met, d3e_body) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= d3e_body.d3exp_typ
, d3exp_node= D3Elam_met (s2es_met, d3e_body)
} // end of [d3exp_lam_met]

implement d3exp_lam_sta
  (loc, s2e0, s2vs, s2ps, d3e_body) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e0
, d3exp_node= D3Elam_sta (s2vs, s2ps, d3e_body)
} // end of [d3exp_lam_dyn]

(* ****** ****** *)

implement
d3exp_lazy_delay
  (loc, s2e, d3e) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Elazy_delay (d3e)
} // end of [d3exp_lazy_delay]

implement
d3exp_lazy_ldelay
  (loc, s2e, d3e1, d3e2) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Elazy_ldelay (d3e1, d3e2)
} // end of [d3exp_lazy_ldelay]

implement
d3exp_lazy_force
  (loc, s2e, lin, d3e) =  '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Elazy_force (lin, d3e)
} // end of [d3exp_lazy_force]

(* ****** ****** *)

implement d3exp_let (loc, d3cs, d3e) = let
  val s2fe = d3eclst_eff_union (d3e.d3exp_eff, d3cs)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= d3e.d3exp_typ
, d3exp_node= D3Elet (d3cs, d3e)
} end // end of [d3exp_let]

(* ****** ****** *)

implement d3exp_loop
  (loc, od3e_init, d3e_test, od3e_post, d3e_body) = let
  val s2fe = case+ od3e_init of
    | None () => S2EFFnil () | Some d3e => d3e.d3exp_eff
  val s2fe = d3exp_eff_union (s2fe, d3e_test)
  val s2fe = case+ od3e_post of
    | None () => s2fe | Some d3e => d3exp_eff_union (s2fe, d3e)
  val s2fe = d3exp_eff_union (s2fe, d3e_body)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Eloop (od3e_init, d3e_test, od3e_post, d3e_body)
} end // end of [d3exp_for]

implement d3exp_loopexn (loc, knd) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Eloopexn knd
} // end of [d3exp_loopexn]

(* ****** ****** *)

implement d3exp_lst (loc, s2e_lst, lin, s2e_elt, d3es_elt) = let
  val s2fe = d3explst_eff_union (S2EFFnil (), d3es_elt)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_lst
, d3exp_node= D3Elst (lin, s2e_elt, d3es_elt)
} end // end of [d3exp_lst]

(* ****** ****** *)

implement d3exp_ptrof_ptr
  (loc, s2e_ptr, d3e, d3ls) = let
  val s2fe = d3lab1lst_eff_union (d3e.d3exp_eff, d3ls)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_ptr
, d3exp_node= D3Eptrof_ptr (d3e, d3ls)
} end // end of [d3exp_ptrof_ptr]

implement d3exp_ptrof_var
  (loc, s2e_ptr, d2v, d3ls) = let
  val s2fe = d3lab1lst_eff_union (S2EFFnil (), d3ls)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_ptr
, d3exp_node= D3Eptrof_var (d2v, d3ls)
} end // end of [d3exp_ptrof_var]

(* ****** ****** *)

implement
d3exp_raise (loc, s2e, d3e_exn) = let
  val s2fe = s2eff_union_eff (d3e_exn.d3exp_eff, $Eff.effect_exn)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Eraise (d3e_exn)
} end // end of [d3exp_raise]


implement
d3exp_rec (
  loc, s2e_rec, recknd, npf, ld3es
) = let
  val s2fe = labd3explst_eff_union (S2EFFnil (), ld3es)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_rec
, d3exp_node= D3Erec (recknd, npf, ld3es)
} end // end of [d3exp_rec]

implement
d3exp_refarg (
  loc, s2e, refval, freeknd, d3e
) = '{
  d3exp_loc= loc
, d3exp_eff= d3e.d3exp_eff, d3exp_typ= s2e
, d3exp_node= D3Erefarg (refval, freeknd, d3e)
} // end of [d3exp_refarg]

implement
d3exp_scaseof (
  loc, s2e, s2e_val, sc3ls
) = let
  val s2fe = S2EFFnil ()
  val s2fe = sc3laulst_eff_union (s2fe, sc3ls)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Escaseof (s2e_val, sc3ls)
} end // end of [d3exp_scaseof]

implement
d3exp_sel (loc, s2e, root, path) = let
  val s2fe = d3lab1lst_eff_union (root.d3exp_eff, path)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Esel (root, path)
} end // end of [d3exp_sel]

implement d3exp_sel_ptr (loc, s2e, root, path) = let
  val s2fe = d3lab1lst_eff_union (root.d3exp_eff, path)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Esel_ptr (root, path)
} end // end of [d3exp_sel_ptr]

implement d3exp_sel_var (loc, s2e, root, path) = let
  val s2fe = d3lab1lst_eff_union (S2EFFnil (), path)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Esel_var (root, path)
} end // end of [d3exp_sel_var]

implement d3exp_seq (loc, s2e, d3es) = let
  val s2fe = d3explst_eff_union (S2EFFnil (), d3es)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Eseq (d3es)
} end // end of [d3exp_seq]

implement d3exp_sif
  (loc, s2e, s2e_cond, d3e_then, d3e_else) = let
  val s2fe = d3e_then.d3exp_eff
  val s2fe = d3exp_eff_union (s2fe, d3e_else)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e
, d3exp_node= D3Esif (s2e_cond, d3e_then, d3e_else)
} end // end of [d3exp_if]

implement d3exp_string (loc, s2e, str, len) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Estring (str, len)
} // end of [d3exp_string]

implement d3exp_struct (loc, s2e_struct, ld3es) = let
  val s2fe = labd3explst_eff_union (S2EFFnil (), ld3es)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= s2e_struct
, d3exp_node= D3Estruct (ld3es)
} end // end of [d3exp_rec]

(* ****** ****** *)

implement d3exp_tmpcst (loc, s2e, d2c, s2ess) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Etmpcst (d2c, s2ess)
}

implement d3exp_tmpvar (loc, s2e, d2v, s2ess) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Etmpvar (d2v, s2ess)
}

(* ****** ****** *)

implement d3exp_top (loc, s2e) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Etop ()
}

implement d3exp_trywith (loc, d3e, c3ls) = let
  val s2fe = d3e.d3exp_eff
  val s2fe = c3laulst_eff_union (s2fe, c3ls)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= d3e.d3exp_typ
, d3exp_node= D3Etrywith (d3e, c3ls)
} end // end of [d3exp_trywith]

implement d3exp_var (loc, s2e, d2v) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil (), d3exp_typ= s2e
, d3exp_node= D3Evar d2v
} // end of [d3exp_var]

(* ****** ****** *)

implement d3exp_viewat_ptr
  (loc, s2e_at, d3e, d3ls, d2v_view, s2ls_view) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil ()
, d3exp_typ= s2e_at
, d3exp_node= D3Eviewat_ptr (d3e, d3ls, d2v_view, s2ls_view)
}

implement d3exp_viewat_var
  (loc, s2e_at, d2v, d3ls, d2v_view, s2ls_view) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil ()
, d3exp_typ= s2e_at
, d3exp_node= D3Eviewat_var (d2v, d3ls, d2v_view, s2ls_view)
}

(* ****** ****** *)

implement d3exp_viewat_assgn_ptr (loc, d3e_l, d3ls, d3e_r) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil ()
, d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Eviewat_assgn_ptr (d3e_l, d3ls, d3e_r)
}

implement d3exp_viewat_assgn_var (loc, d2v_l, d3ls, d3e_r) = '{
  d3exp_loc= loc
, d3exp_eff= S2EFFnil ()
, d3exp_typ= s2exp_void_t0ype ()
, d3exp_node= D3Eviewat_assgn_var (d2v_l, d3ls, d3e_r)
}

(* ****** ****** *)

implement d3exp_where (loc, d3e, d3cs) = let
  val s2fe = d3eclst_eff_union (d3e.d3exp_eff, d3cs)
in '{
  d3exp_loc= loc
, d3exp_eff= s2fe, d3exp_typ= d3e.d3exp_typ
, d3exp_node= D3Ewhere (d3e, d3cs)
} end // end of [d3exp_where]

(* ****** ****** *)

implement d3lab0_ind (loc, d3ess_ind) = '{
  d3lab0_loc= loc, d3lab0_node= D3LAB0ind d3ess_ind
}

implement d3lab0_lab (loc, lab) = '{
  d3lab0_loc= loc, d3lab0_node= D3LAB0lab lab
}

implement d3lab1_ind (loc, d3ess_ind, s2e_elt) = '{
  d3lab1_loc= loc, d3lab1_node= D3LAB1ind (d3ess_ind, s2e_elt)
}

implement d3lab1_lab (loc, lab, s2e) = '{
  d3lab1_loc= loc, d3lab1_node= D3LAB1lab (lab, s2e)
}

(* ****** ****** *)

implement m3atch_make (loc, d3e, op3t) = '{
  m3atch_loc= loc, m3atch_exp= d3e, m3atch_pat= op3t
}

implement c3lau_make (loc, p3ts, gua, seq, neg, d3e) = '{
  c3lau_loc= loc
, c3lau_pat= p3ts
, c3lau_gua= gua, c3lau_seq= seq, c3lau_neg= neg
, c3lau_exp= d3e
} // end of [c3lau_make]

implement sc3lau_make (loc, sp2t, d3e) = '{
  sc3lau_loc= loc, sc3lau_pat= sp2t, sc3lau_exp= d3e
} // end of [sc3lau_make]

(* ****** ****** *)

implement v3aldec_make (loc, p3t, d3e) = '{
  v3aldec_loc= loc, v3aldec_pat= p3t, v3aldec_def= d3e
} // end of [v3aldec_make]

implement v3ardec_make
  (loc, knd, d2v_ptr, d2v_viw, s2e_typ, d3e_ini) = '{
  v3ardec_loc= loc
, v3ardec_knd= knd
, v3ardec_dvar_ptr= d2v_ptr
, v3ardec_dvar_viw= d2v_viw
, v3ardec_typ= s2e_typ
, v3ardec_ini= d3e_ini
} // end of [v3ardec_make]

(* ****** ****** *)

implement f3undec_make (loc, d2v, d3e) = '{
  f3undec_loc= loc, f3undec_var= d2v, f3undec_def= d3e
} // end of [f3undec_make]

(* ****** ****** *)

implement i3mpdec_make (loc, d2c, s2vpss, s2es, d3e) = '{
  i3mpdec_loc= loc
, i3mpdec_cst= d2c
, i3mpdec_decarg= s2vpss, i3mpdec_tmparg= s2es (* one must be nil *)
, i3mpdec_def= d3e
} // end of [i3mpdec_make]

(* ****** ****** *)

implement d3ec_none (loc) = '{
  d3ec_loc= loc, d3ec_node= D3Cnone ()
}

implement d3ec_list (loc, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Clist (d3cs)
}

implement d3ec_saspdec (loc, d2c) = '{
  d3ec_loc= loc, d3ec_node= D3Csaspdec (d2c)
}

implement d3ec_dcstdec (loc, dck, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cdcstdec (dck, d3cs)
}

implement d3ec_datdec (loc, dck, s2cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cdatdec (dck, s2cs)
}

implement d3ec_exndec (loc, d2cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cexndec (d2cs)
}

implement d3ec_extype (loc, name, s2e_def) = '{
  d3ec_loc= loc, d3ec_node= D3Cextype (name, s2e_def)
}

implement d3ec_extval (loc, name, d3e_def) = '{
  d3ec_loc= loc, d3ec_node= D3Cextval (name, d3e_def)
}

implement d3ec_extcode (loc, position, code) = '{
  d3ec_loc= loc, d3ec_node= D3Cextcode (position, code)
}

implement d3ec_valdecs (loc, valknd, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cvaldecs (valknd, d3cs)
}

implement d3ec_valdecs_par (loc, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cvaldecs_par (d3cs)
}

implement d3ec_valdecs_rec (loc, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cvaldecs_rec (d3cs)
}

implement d3ec_fundecs (loc, decarg, funknd, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cfundecs (decarg, funknd, d3cs)
}

implement d3ec_vardecs (loc, d3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cvardecs (d3cs)
}

implement d3ec_impdec (loc, d3c) = '{
  d3ec_loc= loc, d3ec_node= D3Cimpdec (d3c)
}

implement d3ec_local (loc, d3cs_head, d3cs_body) = '{
  d3ec_loc= loc, d3ec_node= D3Clocal (d3cs_head, d3cs_body)
} // end of [d3ec_local]

implement d3ec_staload (loc, fil, loadflag, od3cs) = '{
  d3ec_loc= loc, d3ec_node= D3Cstaload (fil, loadflag, od3cs)
} // end of [d3ec_staload]

implement d3ec_dynload (loc, fil) = '{
  d3ec_loc= loc, d3ec_node= D3Cdynload (fil)
} // end of [d3ec_dynload]

(* ****** ****** *)

extern typedef "d3exp_t" = d3exp

%{$

ats_void_type
ats_dynexp3_d3exp_set_typ (
  ats_ptr_type d3e, ats_ptr_type s2e
) {
  ((d3exp_t)d3e)->atslab_d3exp_typ = s2e ; return ;
} // end of [ats_dynexp3_d3exp_set_typ]

%} // end of [%{$]

(* ****** ****** *)

implement
d3explst_get_typ
  (d3es) = begin case+ d3es of
  | cons (d3e, d3es) => cons (d3e.d3exp_typ, d3explst_get_typ d3es)
  | nil () => nil ()
end // end of [d3explst_get_typ]

implement
labd3explst_get_typ
  (ld3es) = begin case+ ld3es of
  | LABD3EXPLSTcons (l, d3e, ld3es) => begin
      LABS2EXPLSTcons (l, d3e.d3exp_typ, labd3explst_get_typ ld3es)
    end // end of [LABD3EXPLSTcons]
  | LABD3EXPLSTnil () => LABS2EXPLSTnil ()
end // end of [labd3explst_get_typ]

(* ****** ****** *)

(* end of [ats_dynexp3.dats] *)
