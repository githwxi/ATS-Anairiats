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
// Time: December 2007
//
(* ****** ****** *)

(* Mainly for handling dynamic expressions during type-checking *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_staexp2_pprint.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_stadyncst2.sats"
staload "ats_patcst2.sats"
staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

#define THISFILENAME "ats_trans3_util.dats"

(* ****** ****** *)

extern val "FLOATKINDfloat" = $Syn.FLOATKINDfloat ()
extern val "FLOATKINDdouble" = $Syn.FLOATKINDdouble ()
extern val "FLOATKINDdouble_long" = $Syn.FLOATKINDdouble_long ()
extern val "FLOATKINDnone" = $Syn.FLOATKINDnone ()

extern val "INTKINDint" = $Syn.INTKINDint ()
extern val "INTKINDuint" = $Syn.INTKINDuint ()
extern val "INTKINDlint" = $Syn.INTKINDlint ()
extern val "INTKINDulint" = $Syn.INTKINDulint ()
extern val "INTKINDllint" = $Syn.INTKINDllint ()
extern val "INTKINDullint" = $Syn.INTKINDullint ()
extern val "INTKINDnone" = $Syn.INTKINDnone ()

%{$

ats_ptr_type
atsopt_floatkind_eval
  (ats_ptr_type s0) {
//
  char *s = s0 ;
  while (*s) { ++s ; } ; --s ;
  switch (*s) {
    case 'f': case 'F': return FLOATKINDfloat ;
    case 'd': case 'D': return FLOATKINDdouble ;
    case 'l': case 'L': return FLOATKINDdouble_long ;
    default : ;
  }
  return FLOATKINDnone ;
} // end of [atsopt_floatkind_eval]

ats_ptr_type
atsopt_intkind_eval
  (ats_ptr_type s0) {
//
  char c, *s ; int nL, nU ;
//
  s = s0 ; nL = 0 ; nU = 0 ;
  while ((c = *s)) {
    s += 1 ; switch (c) {
      case 'l': case 'L': ++nL ; break ;
      case 'u': case 'U': ++nU ; break ;
      default : break ;
    } // end of [switch]
  } /* end of [while] */
//
  if (nL == 0) {
    if (nU == 0) return INTKINDint ; /* deadcode */
    if (nU == 1) return INTKINDuint ; /* unsigned */
  } // end of [if]
//
  if (nL == 1) {
    if (nU == 0) return INTKINDlint ; /* long */
    if (nU == 1) return INTKINDulint ; /* unsigned long */
  } // end of [if]
//
  if (nL == 2) {
    if (nU == 0) return INTKINDllint ; /* long long */
    if (nU == 1) return INTKINDullint ; /* unsigned long long */
  } // end of [if]
//
  return INTKINDnone ;
} // end of [atsopt_intkind_eval]

%} // end of [%{$]

(* ****** ****** *)

fn prerr_loc_error3
  (loc: loc_t): void = (
  $Loc.prerr_location loc; prerr ": error(3)"
) // end of [prerr_loc_error3]

(* ****** ****** *)

implement
fshowtype_d3exp
  (d3e) = let
//
val loc = d3e.d3exp_loc
val s2e = d3e.d3exp_typ
//
val out = stdout_ref
val () = print "**SHOWTYPE**("
val () = $Loc.print_location (loc)
val () = print "): "
val () = fpprint_s2exp (out, s2e)
val () = print_newline ()
//
in
  // nothing
end // end of [fshowtype_d3exp]

(* ****** ****** *)
//
// typedef funclo =  $Syn.funclo // declared in [ats_trans3.sats]
//
(* ****** ****** *)

implement
d2exp_funclo_of_d2exp (d2e0, fc0) =
  case+ :(fc0: funclo) => d2e0.d2exp_node of
  | D2Eann_funclo (d2e, fc) => (fc0 := fc; d2e) | _ => d2e0
// end of [d2exp_funclo_of_d2exp]

(* ****** ****** *)

implement
d2exp_s2eff_of_d2exp
  (d2e0, s2fe0) = begin
  case+ :(s2fe0: s2eff) => d2e0.d2exp_node of
  | D2Eann_seff (d2e, s2fe) => (s2fe0 := s2fe; d2e)
  | D2Elam_dyn _ => (s2fe0 := S2EFFnil (); d2e0)
  | D2Elaminit_dyn _ => (s2fe0 := S2EFFnil (); d2e0)
  | D2Elam_sta _ => (s2fe0 := S2EFFnil (); d2e0)
  | _ => (s2fe0 := S2EFFall (); d2e0)
end // end of [d2exp_s2eff_of_d2exp]

(* ****** ****** *)

fn s2eff_of_d2exp
  (d2e0: d2exp): s2eff =
  case+ d2e0.d2exp_node of
  | D2Eann_seff (_, s2fe) => s2fe
  | D2Elam_dyn _ => S2EFFnil ()
  | D2Elaminit_dyn _ => S2EFFnil ()
  | D2Elam_sta _ => S2EFFnil ()
  | _ => S2EFFall ()
// end of [s2eff_of_d2exp]

fn d2exp_arg_body_typ_syn (
    d2e0: d2exp
  , fc0: $Syn.funclo
  , lin: int, npf: int
  , p2ts_arg: p2atlst, d2e_body: d2exp
  ) : s2exp = let
(*
  val () = begin
    print "d2exp_arg_body_typ_syn: d2e_body = "; print d2e_body;
    print_newline ()
  end // end of [val]
*)
  val loc0 = d2e0.d2exp_loc
  var fc: $Syn.funclo = fc0
  val s2es_arg = p2atlst_typ_syn p2ts_arg
  val s2e_res = d2exp_typ_syn (d2e_body)
  val d2e_body = d2exp_funclo_of_d2exp (d2e_body, fc)
  val s2fe = s2eff_of_d2exp d2e_body
  val isprf = s2exp_is_proof s2e_res
  val islin = (if lin > 0 then true else false): bool
  val s2t_fun: s2rt = s2rt_prf_lin_fc (loc0, isprf, islin, fc)
  val s2e_fun = s2exp_fun_srt
    (s2t_fun, fc, lin, s2fe, npf, s2es_arg, s2e_res)
  // end of [val]
(*
  val () = begin
    print "d2exp_arg_body_typ_syn: s2e_fun = "; print s2e_fun;
    print_newline ()
  end // end of [val]
*)
in
  s2e_fun
end // end of [d2exp_arg_body_typ_syn]

(* ****** ****** *)

implement
d2exp_cstsp_typ_syn
  (cst) = case+ cst of
  | $Syn.CSTSPfilename () => s2exp_string_type ()
  | $Syn.CSTSPlocation () => s2exp_string_type ()
// end of [d2exp_cstsp_typ_syn]

implement
d2exp_seq_typ_syn (d2es) = let
  fun aux (d2e: d2exp, d2es: d2explst): s2exp = case+ d2es of
    | cons (d2e, d2es) => aux (d2e, d2es) | nil () => d2exp_typ_syn d2e
  // end of [aux]
in
  case+ d2es of
  | cons (d2e, d2es) => aux (d2e, d2es) | nil () => s2exp_void_t0ype ()
end // end of [d2exp_seq_typ_syn]

(* ****** ****** *)

implement
d2exp_typ_syn (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eann_type (_, s2e) => s2e
  | D2Eann_seff (d2e, _) => d2exp_typ_syn (d2e)
  | D2Eann_funclo (d2e, _) => d2exp_typ_syn (d2e)
//
  | D2Earrpsz (opt, d2es) => let
      val loc0 = d2e0.d2exp_loc
      val sz = $Lst.list_length d2es
      val s2e_elt = (case+ opt of
        | Some s2e => s2e | None () => let
            val s2t = s2rt_t0ype in s2exp_Var_make_srt (loc0, s2t)
          end // end of [None]
      ) : s2exp // end of [val]
    in
      s2exp_arrayptrsize_viewt0ype_int_viewt0ype (s2e_elt, sz)
    end // end of [D2Earrpsz]
//
  | D2Eassgn _ => s2exp_void_t0ype ()
  | D2Echar _ => s2exp_char_t0ype ()
  | D2Ecst d2c => d2cst_get_typ d2c
  | D2Ecstsp cst => d2exp_cstsp_typ_syn (cst)
  | D2Eeffmask (_, d2e) => d2exp_typ_syn (d2e)
  | D2Eempty () => s2exp_void_t0ype ()
  | D2Efix (_, _, d2e) => d2exp_typ_syn (d2e)
  | D2Efloat _ => s2exp_double_t0ype ()
  | D2Efor _ => s2exp_void_t0ype ()
  | D2Eint _ => s2exp_int_t0ype ()
  | D2Elam_dyn (lin, npf, p2ts_arg, d2e_body) => let
      val fc0: funclo = $Syn.FUNCLOfun () // default
    in
      d2exp_arg_body_typ_syn (d2e0, fc0, lin, npf, p2ts_arg, d2e_body)
    end // end of [D2Elam_dyn]
  | D2Elaminit_dyn (lin, npf, p2ts_arg, d2e_body) => let
      val fc: funclo = $Syn.FUNCLOclo 0(*unboxed*) // default
    in
      d2exp_arg_body_typ_syn (d2e0, fc, lin, npf, p2ts_arg, d2e_body)
    end // end of [D2Elaminit_dyn]
  | D2Elam_met (r_d2vs, s2es_met, d2e) => begin
    case+ !r_d2vs of
    | list_cons _ => begin
        s2exp_metfn (None (), s2es_met, d2exp_typ_syn d2e)
      end // end of [list_cons]
    | list_nil () => begin
        prerr_loc_error3 d2e0.d2exp_loc;
        prerr ": illegal use of termination metric.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end (* end of [list_nil] *)
    end // end of [D2Elam_met]
  | D2Elam_sta (s2vs, s2ps, d2e) => begin
      s2exp_uni (s2vs, s2ps, d2exp_typ_syn d2e)
    end // end of [D2Elam_sta]
  | D2Elet (_, d2e) => d2exp_typ_syn (d2e)
  | D2Estring (_(*str*), _(*len*)) => s2exp_string_type ()
  | D2Ewhere (d2e, _) => d2exp_typ_syn (d2e)
  | D2Ewhile _ => s2exp_void_t0ype ()
  | _ => s2e where {
      val s2e = s2exp_Var_make_srt (d2e0.d2exp_loc, s2rt_t0ype)
      val () = d2exp_set_typ (d2e0, Some s2e)
    } // end of [_]
end // end of [d2exp_typ_syn]

(* ****** ****** *)

implement
d3exp_open_and_add (d3e) = let
  val s2e = s2exp_opnexi_and_add (d3e.d3exp_loc, d3e.d3exp_typ)
in
  d3exp_set_typ (d3e, s2e)
end // end of [d3exp_open_and_add]

implement
d3explst_open_and_add
  (d3es) = case+ d3es of
  | list_cons (d3e, d3es) => begin
      d3exp_open_and_add d3e; d3explst_open_and_add d3es 
    end // end of [list_cons]
  | list_nil () => ()
// end of [d3explst_open_and_add]

(* ****** ****** *)

local

fn d3exp_get_ind
  (d3e: d3exp): s2exp = let
//
  val () = d3exp_open_and_add (d3e)
//
  val s2e = d3e.d3exp_typ // HX: WHNF
  val os2i = un_s2exp_int_int_t0ype (s2e)
  val os2i = (case+ os2i of
    | Some_vt _ => (fold@ os2i; os2i)
    | ~None_vt () => un_s2exp_size_int_t0ype (s2e)
  ) : s2expopt_vt // end of [val]
in
  case+ os2i of
  | ~Some_vt s2i => s2i
  | ~None_vt () => let
      val () = $Loc.prerr_location d3e.d3exp_loc
      val () = prerr ": error(3)"
      val () = prerr ": the array index is assigned the type ["
      val () = prerr_s2exp (s2e)
      val () = prerr "], which is not an indexed integer type."
      val () = prerr_newline ()
    in
      $Err.abort {s2exp} ()
    end // end of [None_vt]
end // end of [d3exp_get_ind]

fn d3explst_get_ind
  (d3es: d3explst): s2explst =
  $Lst.list_map_fun (d3es, d3exp_get_ind)
// end of [d3explst_get_ind]

in // in of [local]

implement
d3explstlst_get_ind (d3ess) =
  $Lst.list_map_fun (d3ess, d3explst_get_ind)
// end of [d3explstlst_get_ind]

end // end of [local]

(* ****** ****** *)

(* end of [ats_trans3_util.dats] *)
