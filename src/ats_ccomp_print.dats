(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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

staload Cnt = "ats_counter.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
macdef fprint_filename = $Fil.fprint_filename
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
macdef fprint_label = $Lab.fprint_label
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

staload "ats_hiexp.sats"; staload "ats_ccomp.sats"

(* ****** ****** *)

implement
print_tmplab (tl) = print_mac (fprint_tmplab, tl)
implement
prerr_tmplab (tl) = prerr_mac (fprint_tmplab, tl)

(* ****** ****** *)

implement
print_tmpvar (tmp) = print_mac (fprint_tmpvar, tmp)
implement
prerr_tmpvar (tmp) = prerr_mac (fprint_tmpvar, tmp)

(* ****** ****** *)

implement
fprint_tmpvarlst (pf | out, xs) = 
  $Lst.fprintlst (pf | out, xs, ", ", fprint_tmpvar)
// end of [fprint_tmpvarlst]

implement
print_tmpvarlst (tmps) = print_mac (fprint_tmpvarlst, tmps)
implement
prerr_tmpvarlst (tmps) = prerr_mac (fprint_tmpvarlst, tmps)

(* ****** ****** *)

implement
print_funlab (fl) = print_mac (fprint_funlab, fl)
implement
prerr_funlab (fl) = prerr_mac (fprint_funlab, fl)

(* ****** ****** *)

implement
fprint_funlablst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_funlab)
// end of [fprint_funlablst]

implement
print_funlablst (fls) = print_mac (fprint_funlablst, fls)
implement
prerr_funlablst (fls) = prerr_mac (fprint_funlablst, fls)

(* ****** ****** *)

implement
fprint_valprim (pf | out, vp) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ vp.valprim_node of
  | VParg i => begin
      prstr "VParg("; fprint1_int (pf | out, i); prstr ")"
    end // end of [VParg]
  | VPargref i => begin
      prstr "VPargref("; fprint1_int (pf | out, i); prstr ")"
    end // end of [VPargref]
  | VPargtmpref i => begin // HX: for handling variadic arg
      prstr "VPargtmpref("; fprint1_int (pf | out, i); prstr ")"
    end // end of [VPargtmpref]
  | VPbool b => begin
      prstr "VPbool("; fprint1_bool (pf | out, b); prstr ")"
    end // end of [VPbool]
  | VPcastfn (d2c, vp) => begin
      prstr "VPcast(";
      fprint_d2cst (pf | out, d2c); prstr ", "; fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [VPcast]
  | VPchar c => begin
      prstr "VPchar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [VPchar]
  | VPclo (knd, fl, ctx) => begin
      prstr "VPclo(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_funlab (pf | out, fl);
      prstr "; ";
      fprint1_string (pf | out, "...");
      prstr ")"
    end // end of [VPclo]
  | VPcst (d2c) => begin
      prstr "VPcst("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [VPcst]
  | VPcstsp _ => begin
      prstr "VPcstsp("; fprint1_string (pf | out, "..."); prstr ")"
    end // end of [VPcstsp]
  | VPenv vtp => begin
      prstr "VPenv("; fprint_vartyp (pf | out, vtp); prstr ")"
    end // end of [VPenv]
  | VPext code => begin
      fprintf1_exn (pf | out, "VPext(\"%s\")", @(code));
    end // end of [VPext]
  | VPfix vpr => begin
      prstr "VPfix("; fprint_valprim (pf | out, !vpr); prstr ")"
    end // end of [VPfix]
  | VPfloat f(*string*) => begin
      fprintf1_exn (pf | out, "VPfloat(%s)", @(f))
    end // end of [VPfloat]
  | VPfloatsp f(*string*) => begin
      fprintf1_exn (pf | out, "VPfloatsp(%s)", @(f))
    end // end of [VPfloatsp]
  | VPfun fl => begin
      prstr "VPfun("; fprint_funlab (pf | out, fl); prstr ")"
    end // end of [VPfun]
  | VPint (int) => begin
      prstr "VPint("; $IntInf.fprint_intinf (pf | out, int); prstr ")"
    end // end of [VPint]
  | VPintsp (str, int) => begin
      fprintf1_exn (pf | out, "VPintsp(%s)", @(str))
    end // end of [VPintsp]
  | VPptrof vp => begin
      prstr "VPptrof("; fprint_valprim (pf | out, vp); prstr ")"
    end // end of [VPptrof]
  | VPptrof_ptr_offs (vp, offs) => begin
      prstr "VPptrof_ptr_offs(";
      fprint_valprim (pf | out, vp);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr ")"
    end // end of [VPptrof_ptr_offs]
  | VPptrof_var_offs (vp, offs) => begin
      prstr "VPptrof_var_offs(";
      fprint_valprim (pf | out, vp);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr ")"
    end // end of [VPptrof_var_offs]
  | VPsizeof hit => begin
      prstr "VPsizeof(";
      fprint_hityp (pf | out, hityp_decode hit);
      prstr ")"
    end // end of [VPsizeof]
  | VPstring (str, len) => begin
      fprint1_string (pf | out, "VPstring(...)")
    end // end of [VPstring]
  | VPtmp tmp => begin
      prstr "VPtmp("; fprint_tmpvar (pf | out, tmp); prstr ")"
    end // end of [VPtmp]
  | VPtmpref tmp => begin
      prstr "VPtmpref("; fprint_tmpvar (pf | out, tmp); prstr ")"
    end // end of [VPtmpref]
  | VPtop () => begin
      fprint1_string (pf | out, "VPtop()")
    end // end of [VPtop]
  | VPvoid () => begin
      fprint1_string (pf | out, "VPvoid()")
    end // end of [VPvoid]
(*
  | _ => begin
      fprint1_string (pf | out, "fprint_valprim: not yet implemented.");
      fprint_newline (pf | out);
      $Err.abort {void} ()
    end // end of [_]
*)
end // end of [fprint_valprim]

implement
print_valprim (vp) = print_mac (fprint_valprim, vp)
implement
prerr_valprim (vp) = prerr_mac (fprint_valprim, vp)

(* ****** ****** *)

implement
fprint_valprimlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_valprim)
// end of [fprint_valprimlst]

implement
print_valprimlst (vps) = print_mac (fprint_valprimlst, vps)
implement
prerr_valprimlst (vps) = prerr_mac (fprint_valprimlst, vps)
        
(* ****** ****** *)

implement
fprint_labvalprimlst
  {m} (pf | out, lvps) = let
  fun aux (
    out: &FILE m, i: int, lvps: labvalprimlst
  ) : void =
    case+ lvps of
    | LABVALPRIMLSTcons (l, vp, lvps) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_label (pf | out, l)
        val () = fprint1_string (pf | out, "= ")
        val () = fprint_valprim (pf | out, vp)
      in
        aux (out, i+1, lvps)
      end // end of [LABVALPRIMLSTcons]
    | LABVALPRIMLSTnil () => () // end of [nil]
  // end of [aux]
in
  aux (out, 0, lvps)
end // end of [fprint_labvalprimlst]

(* ****** ****** *)

implement
fprint_offset
  {m} (pf | out, off) = begin
  case+ off of
  | OFFSETlab (l, _(*hit_rec*)) => begin
      fprint1_string (pf | out, "."); fprint_label (pf | out, l)
    end // end of [OFFSETlab]
  | OFFSETind (
      vpss, _(*hit_elt*)
    ) => aux (out, vpss) where {
      fun aux (
        out: &FILE m, vpss: valprimlstlst
      ) : void = case+ vpss of
        | list_cons (vps, vpss) => let
            val () = fprint1_string (pf | out, "[")
            val () = fprint_valprimlst (pf | out, vps)
            val () = fprint1_string (pf | out, "]")
          in
            aux (out, vpss)
          end // end of [list_cons]
        | list_nil () => () // end of [list_nil]
      // end of [aux]
    } // end of [OFFSETind]
end // end of [fprint_offset]

implement
fprint_offsetlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_offset)
// end of [fprint_offsetlst]

(* ****** ****** *)

implement
fprint_patck (pf | out, patck) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ patck of
  | PATCKbool b => begin
      prstr "PATCKbool("; fprint1_bool (pf | out, b); prstr ")"
    end // end of [PATCKbool]
  | PATCKchar c => begin
      prstr "PATCKchar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [PATCKchar]
  | PATCKcon d2c => begin
      prstr "PATCKcon("; fprint_d2con (pf | out, d2c); prstr ")"
    end // end of [PATCKcon]
  | PATCKexn d2c => begin
      prstr "PATCKexn("; fprint_d2con (pf | out, d2c); prstr ")"
    end // end of [PATCKexn]
  | PATCKfloat f(*string*) => begin
      prstr "PATCKfloat("; fprint1_string (pf | out, f); prstr ")"
    end // end of [PATCHfloat]
  | PATCKint i => begin
      prstr "PATCKint("; $IntInf.fprint_intinf (pf | out, i); prstr ")"
    end // end of [PATCKint]
  | PATCKstring s => begin
      fprintf1_exn (pf | out, "PATCKstring(\"%s\")", @(s))
    end // end of [PATCKstring]
end // end of [fprint_patck]

implement
fprint_patcklst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_patck)
// end of [fprint_patcklst]

(* ****** ****** *)

implement
fprint_kont {m} (pf | out, k) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ k of
  | KONTtmplab tl => begin
      prstr "KONTtmplab(";
      fprint_tmplab (pf | out, tl);
      prstr ")"
    end // end of [KONTtmplab]
  | KONTtmplabint (tl, i) => begin
      prstr "KONTtmplabint(";
      fprint_tmplab (pf | out, tl);
      prstr ", ";
      fprint1_int (pf | out, i);
      prstr ")"
    end // end of [KONTtmplabint]
  | KONTcaseof_fail (loc) => begin
      fprint1_string (pf | out, "KONTcaseof_fail(...)")
    end // end of [KONTcaseof_fail]
  | KONTfunarg_fail (loc, fl) => begin
      prstr "KONTfunarg_fail(..., "; fprint_funlab (pf | out, fl); prstr ")"
    end // end of [KONTfunarg_fail]
  | KONTmatpnt mpt => begin
      fprint1_string (pf | out, "KONTmatpnt(...)")
    end // end of [KONTmatpnt]
  | KONTraise vp => begin
      prstr "KONTraise("; fprint_valprim (pf | out, vp); prstr ")"
    end // end of [KONTraise]
  | KONTnone () => begin
      fprint1_string (pf | out, "KONTnone()")
    end // end of [KONTnone]
end (* end of [fprint_kont] *)

implement
fprint_kontlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_kont)
// end of [fprint_kontlst]

(* ****** ****** *)

implement
fprint_instr (pf | out, ins) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ ins.instr_node of
  | INSTRarr_heap (tmp, asz, hit_elt) => begin
      prstr "INSTRarr_heap(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_int (pf | out, asz);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_elt);
      prstr ")";
    end // end of [INSTRarr_heap]
  | INSTRarr_stack (tmp, level, vp_asz, hit_elt) => begin
      prstr "INSTRarr_stack(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_int (pf | out, level);
      prstr "; ";
      fprint_valprim (pf | out, vp_asz);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_elt);
      prstr ")";
    end // end of [INSTRarr_stack]
  | INSTRassgn_arr (
      tmp_ptr, vp_asz, tmp_elt, vp_tsz
    ) => begin
      prstr "INSTRassgn_arr(";
      fprint_tmpvar (pf | out, tmp_ptr);
      prstr "; ";
      fprint_valprim (pf | out, vp_asz);
      prstr "; ";
      fprint_tmpvar (pf | out, tmp_elt);
      prstr "; ";
      fprint_valprim (pf | out, vp_tsz);
      prstr ")";
    end // end of [INSTRassgn_arr]
  | INSTRassgn_clo (
      tmp_ptr, tmp_clo, fl, env
    ) => begin
      prstr "INSTRassgn_clo(";
      fprint_tmpvar (pf | out, tmp_ptr);
      prstr "; ";
      fprint_tmpvar (pf | out, tmp_clo);
      prstr "; ";
      fprint_funlab (pf | out, fl);
      prstr "; ";
      fprint1_string (pf | out, "...");
      prstr ")";
    end // end of [INSTRassgn_clo]
  | INSTRcall (tmp, hit_fun, vp_fun, vps_arg) => begin
      prstr "INSTRcall(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_fun);
      prstr "; ";
      fprint_valprim (pf | out, vp_fun);
      prstr "; ";
      fprint_valprimlst (pf | out, vps_arg);
      prstr ")"
    end // end of [INSTRcall]
  | INSTRcall_tail (fl) => begin
      prstr "INSTRcall_tail("; fprint_funlab (pf | out, fl); prstr ")"
    end // end of [INSTRcall_tail]
  | INSTRcond (vp, inss1, inss2) => begin
      prstr "INSTRcond(";
      fprint_valprim (pf | out, vp);
      fprint_newline (pf | out);
      prstr "INSTRcond_then:";
      fprint_newline (pf | out);
      fprint_instrlst (pf | out, inss1);
      fprint_newline (pf | out);
      prstr "INSTRcond_else:";
      fprint_newline (pf | out);
      fprint_instrlst (pf | out, inss2);
      fprint_newline (pf | out);
      prstr ")"
    end // end of [INSTRcond]
  | INSTRdefine_clo (d2c, fl) => begin
      prstr "INSTRdefine_clo(";
      fprint_d2cst (pf | out, d2c);
      prstr ", ";
      fprint_funlab (pf | out, fl);
      prstr ")"
    end // end of [INSTRdefine_clo]
  | INSTRdefine_fun (d2c, fl) => begin
      prstr "INSTRdefine_fun(";
      fprint_d2cst (pf | out, d2c);
      prstr ", ";
      fprint_funlab (pf | out, fl);
      prstr ")"
    end // end of [INSTRdefine_fun]
  | INSTRdefine_val (d2c, vp) => begin
      prstr "INSTRdefine_val(";
      fprint_d2cst (pf | out, d2c);
      prstr ", ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRdefine_val]
//
// HX-2011-01-15: partial value template
//
  | INSTRdefine_partval (name, vp) => begin
      prstr "INSTRdefine_partval(";
      fprint_string (pf | out, name);
      prstr ", ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRdefine_partval]
//
  | INSTRextern cmd => begin
      fprintf1_exn (pf | out, "INSTRextern(\"%s\")", @(cmd))
    end // end of [INSTRextern]
  | INSTRextval (name, vp) => begin
      prstr "INSTRextval(";
      fprint1_string (pf | out, name);
      prstr ", ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRextval]
  | INSTRfreeptr vp => begin
      prstr "INSTRfreeptr("; fprint_valprim (pf | out, vp); prstr ")"
    end // end of [INSTRfreeptr]
  | INSTRfunction _ => begin
      fprint1_string (pf | out, "INSTRfunction(...)")
    end // end of [INSTRfunction]
  | INSTRfunlab fl => begin
      prstr "INSTRfunlab("; fprint_funlab (pf | out, fl); prstr ")"
    end // end of [INSTRfunlab]
  | INSTRdynload_file (fil) => begin
      prstr "INSTRdynload_file(";
      $Fil.fprint_filename (pf | out, fil);
      prstr ")"
    end // end of [INSTRdynload]
  | INSTRload_ptr (tmp, vp_ptr) => begin
      prstr "INSTRload_ptr(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_ptr);
      prstr ")"
    end // end of [INSTRload_ptr]
  | INSTRload_ptr_offs (tmp, vp_ptr, offs) => begin
      prstr "INSTRload_ptr_offs(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_ptr);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr ")"
    end // end of [INSTRload_ptr_offs]
  | INSTRload_var (tmp, vp_var) => begin
      prstr "INSTRload_var(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_var);
      prstr ")"
    end // end of [INSTRload_var]
  | INSTRload_var_offs (tmp, vp_var, offs) => begin
      prstr "INSTRload_var_offs(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_var);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr ")"
    end // end of [INSTRload_var_offs]
  | INSTRloop _ => begin
      fprint1_string (pf | out, "INSTRloop(...)")
    end // end of [INSTRloop]
  | INSTRloopexn (knd, tl) => begin
      prstr "INSTRloopexn(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_tmplab (pf | out, tl);
      prstr ")"
    end // end of [INSTRloopexn]
  | INSTRmove_arg (arg, vp) => begin
      prstr "INSTRmove_arg(";
      fprint1_int (pf | out, arg);
      prstr ", ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRmove_arg]
  | INSTRmove_con (tmp, hit_sum, d2c, vps_arg) => begin
      prstr "INSTRmove_con(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_sum);
      prstr "; ";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_valprimlst (pf | out, vps_arg);
      prstr ")"
    end // end of [INSTRmove_con]
  | INSTRmove_lazy_delay (tmp, lin, hit, vp) => begin
      prstr "INSTRmove_lazy_delay(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_int (pf | out, lin);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit);
      prstr "; ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRlazy_force]
  | INSTRmove_lazy_force (tmp, lin, hit, vp) => begin
      prstr "INSTRmove_lazy_force(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_int (pf | out, lin);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit);
      prstr "; ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRlazy_force]
  | INSTRmove_rec_box (tmp, hit_rec, lvps) => begin
      prstr "INSTRmove_rec_box(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_rec);
      prstr "; ";
      fprint_labvalprimlst (pf | out, lvps);
      prstr ")"
    end // end of [INSTRmove_rec_box]
  | INSTRmove_rec_flt (tmp, hit_rec, lvps) => begin
      prstr "INSTRmove_rec_flt(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_rec);
      prstr "; ";
      fprint_labvalprimlst (pf | out, lvps);
      prstr ")"
    end // end of [INSTRmove_rec_flt]
  | INSTRmove_val (tmp, vp) => begin
      prstr "INSTRmove_val(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRmove_val]
  | INSTRmove_ref (tmp, vp) => begin
      prstr "INSTRmove_ref(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRmove_ref]
  | INSTRpatck (vp, patck, k_fail) => begin
      prstr "INSTRpatck(";
      fprint_valprim (pf | out, vp);
      prstr "; ";
      fprint_patck (pf | out, patck);
      prstr "; ";
      fprint_kont (pf | out, k_fail);
      prstr ")"
    end // end of [INSTRpatck]
  | INSTRraise (tmp, vp) => begin
      prstr "INSTRraise(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp);
      prstr ")"
    end // end of [INSTRraise]
  | INSTRselcon (tmp, vp_sum, hit_sum, i) => begin
      prstr "INSTRselcon(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_sum);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_sum);
      prstr "; ";
      fprint1_int (pf | out, i);
      prstr ")"
    end // end of [INSTRselcon]
  | INSTRselcon_ptr (tmp, vp_sum, hit_sum, i) => begin
      prstr "INSTRselcon_ptr(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_sum);
      prstr "; ";
      fprint_hityp (pf | out, hityp_decode hit_sum);
      prstr "; ";
      fprint_int (pf | out, i);
      prstr ")"
    end // end of [INSTRselcon_ptr]
  | INSTRselect (tmp, vp_root, offs) => begin
      prstr "INSTRselect(";
      fprint_tmpvar (pf | out, tmp);
      prstr "; ";
      fprint_valprim (pf | out, vp_root);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr ")"
    end // end of [INSTRselect]
  | INSTRstore_ptr (vp_ptr, vp_val) => begin
      prstr "INSTRstore_ptr(";
      fprint_valprim (pf | out, vp_ptr);
      prstr "; ";
      fprint_valprim (pf | out, vp_val);
      prstr ")"
    end // end of [INSTRstore_ptr]
  | INSTRstore_ptr_offs (vp_ptr, offs, vp_val) => begin
      prstr "INSTRstore_ptr_offs(";
      fprint_valprim (pf | out, vp_ptr);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr "; ";
      fprint_valprim (pf | out, vp_val);
      prstr ")"
    end // end of [INSTRstore_ptr_offs]
  | INSTRstore_var (vp_var, vp_val) => begin
      prstr "INSTRstore_var(";
      fprint_valprim (pf | out, vp_var);
      prstr "; ";
      fprint_valprim (pf | out, vp_val);
      prstr ")"
    end // end of [INSTRstore_var]
  | INSTRstore_var_offs (vp_var, offs, vp_val) => begin
      prstr "INSTRstore_var_offs(";
      fprint_valprim (pf | out, vp_var);
      prstr "; ";
      fprint_offsetlst (pf | out, offs);
      prstr "; ";
      fprint_valprim (pf | out, vp_val);
      prstr ")"
    end // end of [INSTRstore_var_offs]
  | INSTRswitch _ => begin
      fprint1_string (pf | out, "INSTRswitch(...)")
    end // end of [INSTRswitch]
  | INSTRtmplabint (tl, i) => begin
      prstr "INSTRtmplabint(";
      fprint_tmplab (pf | out, tl);
      prstr "_";
      fprint1_int (pf | out, i);
      prstr ")"
    end // end of [INSTRtmplabint]
//
  | INSTRprfck_beg (d2c) => begin
      prstr "INSTRprfck_beg("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [INSTRprfck_beg]
  | INSTRprfck_end (d2c) => begin
      prstr "INSTRprfck_end("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [INSTRprfck_end]
  | INSTRprfck_tst (d2c) => begin // HX: test
      prstr "INSTRprfck_tst("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [INSTRprfck_tst]
//
  | INSTRtrywith _ => begin
      fprint1_string (pf | out, "INSTRtrywith(...)")
    end // end of [INSTRtrywith]
  | INSTRvardec tmp => begin
      prstr "INSTRvardec("; fprint_tmpvar (pf | out, tmp); prstr ")"
    end // end of [INSTRvardec]
(*
  | _ => begin
      prstr "fprint_instr: not yet implemented.");
      fprint_newline (pf | out);
      $Err.abort {void} ()
    end // end of [_]
*)
end // end of [fprint_instr]

implement
print_instr (ins) = print_mac (fprint_instr, ins)
implement
prerr_instr (ins) = prerr_mac (fprint_instr, ins)

(* ****** ****** *)

implement
fprint_instrlst (pf | out, xs) = let
  val sep = "\n"
  val () = $Lst.fprintlst (pf | out, xs, sep, fprint_instr)
in
  case+ xs of
  | list_cons _ => fprint_newline (pf | out)
  | list_nil () => ()
end // end of [fprint_instrlst]

implement
print_instrlst (inss) = print_mac (fprint_instrlst, inss)
implement
prerr_instrlst (inss) = prerr_mac (fprint_instrlst, inss)

(* ****** ****** *)

implement
fprint_branch {m} (pf | out, br) = begin
  fprint_tmplab (pf | out, br.branch_lab);
  fprint1_string (pf | out, ": "); fprint_newline (pf | out);
  fprint_instrlst (pf | out, br.branch_inss);
end // end of [fprint_branch]

implement
fprint_branchlst
  {m} (pf | out, brs) = let
  fun aux (
    out: &FILE m, brs: branchlst
  ) : void =
    case+ brs of
    | list_cons (br, brs) => begin
        fprint_branch (pf | out, br); aux (out, brs)
      end // end of [list_cons]
    | list_nil () => () // end of [list_nil]
  // end of [aux]
in
  aux (out, brs)
end // end of [fprint_branchlst]

(* ****** ****** *)

(* end of [ats_ccomp_print.dats] *)
