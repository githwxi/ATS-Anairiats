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

staload Fil = "ats_filename.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement
fprint_hityp (pf | out, hit) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hit.hityp_node of
  | HITextype (name, hitss_arg) => begin
      prstr "HITextype(";
      fprint_string (pf | out, name);
      prstr "; ";
      fprint_hityplstlst (pf | out, hitss_arg);
      prstr ")"
    end // end of [HITextype]
  | HITfun (fc, hits_arg, hit_res) => begin
      prstr "HITfun(";
      $Syn.fprint_funclo (pf | out, fc);
      prstr "; ";
      fprint_hityplst (pf | out, hits_arg);
      prstr "; ";
      fprint_hityp (pf | out, hit_res);
      prstr ")"
    end // end of [HITfun]
  | HITrefarg (refval, hit) => begin
      prstr "HITrefarg(";
      fprint1_int (pf | out, refval);
      prstr "; ";
      fprint_hityp (pf | out, hit);
      prstr ")"
    end // end of [HITrefarg]
  | HITtyrecsin hit => begin
      prstr "HITtyrecsin(";
      fprint_hityp (pf | out, hit);
      prstr ")"
    end // end of [HITtyrecsin]
  | HITtyrectemp (knd, lhits) => begin
      fprint1_string (pf | out, "HITtyrectemp(...)")
    end
  | HITtysumtemp (d2c, hits) => begin
      prstr "HITsumtemp(";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_hityplst (pf | out, hits);
      prstr ")"
    end // end of [HITtysumtemp]
  | HITs2var s2v => begin
      prstr "HITs2var("; fprint_s2var (pf | out, s2v); prstr ")"
    end // end of [HITs2var]
  | _ => let
      val HITNAM (knd, name) = hit.hityp_name
    in
      if knd > 0 then fprint1_string (pf | out, "*");
      fprint1_string (pf | out, name)
    end // end of [_]
end // end of [fprint_hityp]

implement
print_hityp (hit) = print_mac (fprint_hityp, hit)
implement
prerr_hityp (hit) = prerr_mac (fprint_hityp, hit)

(* ****** ****** *)

implement
fprint_hityplst (pf | out, xs) =
  $Lst.fprintlst {hityp} (pf | out, xs, ", ", fprint_hityp)
// end of [fprint_hityplst]

implement
print_hityplst (hits) = print_mac (fprint_hityplst, hits)
implement
prerr_hityplst (hits) = prerr_mac (fprint_hityplst, hits)

(* ****** ****** *)

implement
fprint_hityplstlst (pf | out, xss) =
  $Lst.fprintlst {hityplst} (pf | out, xss, "; ", fprint_hityplst)
// end of [fprint_hityplstlst]

(* ****** ****** *)

implement
fprint_hipat (pf | out, hip0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hip0.hipat_node of
  | HIPann (hip, hit_ann) => begin
      prstr "HIPann(";
      fprint_hipat (pf | out, hip);
      prstr "; ";
      fprint_hityp (pf | out, hit_ann);
      prstr ")"
    end // end of [HIPann]
  | HIPany () => begin
      fprint1_string (pf | out, "HIPany()")
    end // end of [HIPany]
  | HIPas (knd, d2v, hip) => begin
      prstr "HIPas(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_d2var (pf | out, d2v);
      prstr "; ";
      fprint_hipat (pf | out, hip);
      prstr ")"
    end // end of [HIPas]
  | HIPbool b => begin
      prstr "HIPbool("; fprint1_bool (pf | out, b); prstr ")"
    end // end of [HIPbool]
  | HIPchar c => begin
      prstr "HIPchar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [HIPchar]
  | HIPcon (freeknd, d2c, hips_arg, hit_sum) => begin
      prstr "HIPcon(";
      fprint1_int (pf | out, freeknd);
      prstr "; ";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_hipatlst (pf | out, hips_arg);
      prstr "; ";
      fprint_hityp (pf | out, hit_sum);
      prstr ")"
    end // end of [HIPcon]
  | HIPcon_any (freeknd, d2c) => begin
      prstr "HIPcon_any(";
      fprint1_int (pf | out, freeknd);
      prstr "; ";
      fprint_d2con (pf | out, d2c);
      prstr ")"
    end // end of [HIPcon_any]
  | HIPempty () => begin
      fprint1_string (pf | out, "HIPempty()");
    end // end of [HIPempty]
  | HIPfloat f(*string*) => begin
      fprintf1_exn (pf | out, "HIPfloat(%s)", @(f))
    end // end of [HIPfloat]
  | HIPint (str, int) => begin
      prstr "HIPint(";
      $IntInf.fprint_intinf (pf | out, int);
      prstr ")"
    end // end of [HIPint]
  | HIPlst (hit_elt, hips_elt) => begin
      prstr "HIPlst(";
      fprint_hityp (pf | out, hit_elt);
      prstr "; ";
      fprint_hipatlst (pf | out, hips_elt);
      prstr ")"
    end // end of [HIPlst]
  | HIPrec (knd, lhips, hit_rec) => begin
      prstr "HIPrec(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_labhipatlst (pf | out, lhips);
      prstr "; ";
      fprint_hityp (pf | out, hit_rec);
      prstr ")"
    end // end of [HIPrec]
  | HIPstring s => begin
      prstr "HIPstring("; fprint1_string (pf | out, s); prstr ")"
    end // end of [HIPstring]
  | HIPvar (refknd, d2v) => begin
      prstr "HIPvar("; fprint_d2var (pf | out, d2v); prstr ")"
    end // end of [HIPvar]
end // end of [fprint_hipat]

implement
print_hipat (hip) = print_mac (fprint_hipat, hip)
implement
prerr_hipat (hip) = prerr_mac (fprint_hipat, hip)

(* ****** ****** *)

implement
fprint_hipatlst (pf | out, xs) =
  $Lst.fprintlst {hipat} (pf | out, xs, ", ", fprint_hipat)
// end of [fprint_hipatlst]

implement
print_hipatlst (hips) = print_mac (fprint_hipatlst, hips)
implement
prerr_hipatlst (hips) = prerr_mac (fprint_hipatlst, hips)

(* ****** ****** *)

implement
fprint_labhipatlst {m}
  (pf | out, lhips0) = let
  fun aux
    (out: &FILE m, i: int, lhips: labhipatlst): void =
    case+ lhips of
    | LABHIPATLSTcons (l, hip, lhips) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_label (pf | out, l);
        fprint1_string (pf | out, "= ");
        fprint_hipat (pf | out, hip);
        aux (out, i+1, lhips)
      end // end of [LABHIPATLSTcons]
    | LABHIPATLSTdot () => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint1_string (pf | out, "...")
      end // end of [LABHIPATLSTdot]
    | LABHIPATLSTnil () => () // end of [LABHIPATLSTnil]
  // end of [aux]
in
  aux (out, 0, lhips0)
end // end of [fprint_labhipatlst]

(* ****** ****** *)

implement
fprint_hiexp (pf | out, hie0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hie0.hiexp_node of
  | HIEapp (hit_fun, hie_fun, hies_arg) => begin
      prstr "HIEapp(";
      fprint_hityp (pf | out, hit_fun);
      prstr "; ";
      fprint_hiexp (pf | out, hie_fun);
      prstr "; ";
      fprint_hiexplst (pf | out, hies_arg);
      prstr ")"
    end // end of [HIEapp]
  | HIEarrinit (hit_elt, ohie_asz, hies_elt) => begin
      prstr "HIEarrinit(";
      fprint_hityp (pf | out, hit_elt);
      prstr "; ";
      begin case+ ohie_asz of
      | Some hie => fprint_hiexp (pf | out, hie) | None () => ()
      end;
      prstr "; ";
      fprint_hiexplst (pf | out, hies_elt);
      prstr ")"
    end // end of [HIEarrinit]
  | HIEarrpsz (hit_elt, hies_elt) => begin
      prstr "HIEarrpsz(";
      fprint_hityp (pf | out, hit_elt);
      prstr "; ";
      fprint_hiexplst (pf | out, hies_elt);
      prstr ")"
    end // end of [HIEarrpsz]
  | HIEassgn_ptr (hie, hils, hie_val) => begin
      prstr "HIEassgn_ptr(";
      fprint_hiexp (pf | out, hie);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr "; ";
      fprint_hiexp (pf | out, hie_val);
      prstr ")"
    end // end of [HIEassgn_ptr]
  | HIEassgn_var (d2v, hils, hie_val) => begin
      prstr "HIEassgn_var(";
      fprint_d2var (pf | out, d2v);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr "; ";
      fprint_hiexp (pf | out, hie_val);
      prstr ")"
    end // end of [HIEassgn_var]
  | HIEbool b => begin
      prstr "HIEbool("; fprint1_bool (pf | out, b); prstr ")"
    end // end of [HIEbool]
  | HIEcaseof _ => begin
      prstr "HIEcaseof("; fprint1_string (pf | out, "..."); prstr ")"
    end // end of [HIEcaseof]
  | HIEcastfn (d2c, hie) => begin
      prstr "HIEcastfn(";
      fprint_d2cst (pf | out, d2c); prstr "; "; fprint_hiexp (pf | out, hie);
      prstr ")"
    end // end of [HIEcastfn]
  | HIEchar c => begin
      prstr "HIEchar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [HIEchar]
  | HIEcon (hit_sum, d2c, hies_arg) => begin
      prstr "HIEcon(";
      fprint_hityp (pf | out, hit_sum);
      prstr "; ";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_hiexplst (pf | out, hies_arg);
      prstr ")"
    end // end of [HIEcon]
  | HIEcst d2c => begin
      prstr "HIEcst("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [HiEcst]
  | HIEcstsp cst => begin
      prstr "HIEcstsp("; $Syn.fprint_cstsp (pf | out, cst); prstr ")"
    end // end of [HiEcstsp]
  | HIEdynload fil => begin
      prstr "HIEdynload(";
      $Fil.fprint_filename (pf | out, fil);
      prstr ")";
    end // end of [HIEdynload]
  | HIEempty () => begin
      fprint1_string (pf | out, "HIEempty()")
    end // end of [HIEempty]
  | HIEextval code => begin
      prstr "HIEextval("; fprint1_string (pf | out, code); prstr ")"
    end // end of [HIEexval]
  | HIEfix (knd, d2v_fun, hie_body) => begin
      prstr "HIEfix(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_d2var (pf | out, d2v_fun);
      prstr "; ";
      fprint_hiexp (pf | out, hie_body);
      prstr ")"
    end // end of [HIEfix]
  | HIEfloat f(*string*) => begin
      prstr "HIEfloat("; fprint1_string (pf | out, f); prstr ")"
    end
  | HIEfloatsp f(*string*) => begin
      prstr "HIEfloatsp("; fprint1_string (pf | out, f); prstr ")"
    end
  | HIEfreeat hie => begin
      prstr "HIEfreeat("; fprint_hiexp (pf | out, hie); prstr ")"
    end
  | HIEif (hie_cond, hie_then, hie_else) => begin
      prstr "HIEif(";
      fprint_hiexp (pf | out, hie_cond);
      prstr "; ";
      fprint_hiexp (pf | out, hie_then);
      prstr "; ";
      fprint_hiexp (pf | out, hie_else);
      prstr ")"
    end // end of [HIEif]
  | HIEint (str, int) => begin
      prstr "HIEint(";
      $IntInf.fprint_intinf (pf | out, int);
      prstr ")"
    end // end of [HIEint]
  | HIEintsp (str, int) => begin
      prstr "HIEintsp("; fprint1_string (pf | out, str); prstr ")"
    end
  | HIElam (hips_arg, hie_body) => begin
      prstr "HIElam(";
      fprint_hipatlst (pf | out, hips_arg);
      prstr "; ";
      fprint_hiexp (pf | out, hie_body);
      prstr ")"
    end // end of [HIElam]
  | HIElaminit (hips_arg, hie_body) => begin
      prstr "HIElaminit(";
      fprint_hipatlst (pf | out, hips_arg);
      prstr "; ";
      fprint_hiexp (pf | out, hie_body);
      prstr ")"
    end // end of [HIElaminit]
  | HIElazy_delay (hie_eval) => begin
      prstr "HIElazy_delay(";
      fprint_hiexp (pf | out, hie_eval);
      prstr ")"
    end // end of [HIElazy_delay]
  | HIElazy_ldelay (hie_eval, hie_free) => begin
      prstr "HIElazy_delay(";
      fprint_hiexp (pf | out, hie_eval);
      prstr "; ";
      fprint_hiexp (pf | out, hie_free);
      prstr ")"
    end // end of [HIElazy_ldelay]
  | HIElazy_force (lin, hie_lazy) => begin
      prstr "HIElazy_force(";
      fprint_int (pf | out, lin);
      prstr "; ";
      fprint_hiexp (pf | out, hie_lazy);
      prstr ")"
    end // end of [HIElazy_force]
  | HIElet (hids, hie) => begin
      prstr "HIElet(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_hiexp (pf | out, hie);
      prstr ")"
    end // end of [HIElet]
  | HIEloop (ohie_init, hie_test, ohie_post, hie_body) => begin
      prstr "HIEloop(";
      begin case+ ohie_post of
        | None () => () | Some hie => fprint_hiexp (pf | out, hie)
      end;
      prstr "; ";
      fprint_hiexp (pf | out, hie_test);
      prstr "; ";
      begin case+ ohie_post of
        | None () => () | Some hie => fprint_hiexp (pf | out, hie)
      end;
      prstr "; ";
      fprint_hiexp (pf | out, hie_body);
      prstr ")"
    end // end of [HIEloop]
  | HIEloopexn i => begin
      prstr "HIEloopexn("; fprint1_int (pf | out, i); prstr ")"
    end // end of [HIEloopexn]
  | HIElst (lin, hit, hies) => begin
      prstr "HIElst(";
      fprint1_int (pf | out, lin);
      prstr "; ";
      fprint_hityp (pf | out, hit);
      prstr "; ";
      fprint_hiexplst (pf | out, hies);
      prstr ")"
    end // end of [HIElst]
  | HIEptrof_ptr (hie, hils) => begin
      prstr "HIEptrof_ptr(";
      fprint_hiexp (pf | out,  hie);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr ")"
    end // end of [HIEptrof_ptr]
  | HIEptrof_var (d2v, hils) => begin
      prstr "HIEptrof_var(";
      fprint_d2var (pf | out,  d2v);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr ")"
    end // end of [HIEptrof_var]
  | HIEraise (hie) => begin
      prstr "HIEraise("; fprint_hiexp (pf | out, hie); prstr ")"
    end // end of [HIEraise]
  | HIErec (knd, hit_rec, lhies) => begin
      prstr "HIErec(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_hityp (pf | out, hit_rec);
      prstr "; ";
      fprint_labhiexplst (pf | out, lhies);
      prstr ")"
    end // end of [HIErec]
  | HIErefarg (refval, freeknd, hie_arg) => begin
      prstr "HIErefarg(";
      fprint1_int (pf | out, refval);
      prstr "; ";
      fprint1_int (pf | out, freeknd);
      prstr "; ";
      fprint_hiexp (pf | out, hie_arg);
      prstr ")"
    end // end of [HIErefarg]
  | HIEsel (hie, hils) => begin
      prstr "HIEsel(";
      fprint_hiexp (pf | out,  hie);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr ")"
    end // end of [HIEsel]
  | HIEsel_ptr (hie, hils) => begin
      prstr "HIEsel_ptr(";
      fprint_hiexp (pf | out,  hie);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr ")"
    end // end of [HIEsel_ptr]
  | HIEsel_var (d2v, hils) => begin
      prstr "HIEsel_var(";
      fprint_d2var (pf | out,  d2v);
      prstr "; ";
      fprint_hilablst (pf | out, hils);
      prstr ")"
    end // end of [HIEsel_var]
  | HIEseq (hies) => begin
      prstr "HIEseq("; fprint_hiexplst (pf | out, hies); prstr ")"
    end // end of [HIEseq]
  | HIEsif (hie_then, hie_else) => begin
      prstr "HIEsif(";
      fprint_hiexp (pf | out, hie_then);
      prstr ", ";
      fprint_hiexp (pf | out, hie_else);      
      prstr ")"
    end // end of [HIEsif]
  | HIEsizeof (hit) => begin
      prstr "HIEsizeof("; fprint_hityp (pf | out, hit); prstr ")"
    end // end of [HIEsizeof]
  | HIEstring (str, len) => begin
      fprint1_string (pf | out, "HIEstring(...)")
    end // end of [HIEstring]
  | HIEtmpcst (d2c, hitss) => begin
      prstr "HIEtmpcst(";
      fprint_d2cst (pf | out, d2c);
      prstr "; ";
      fprint_hityplstlst (pf | out, hitss);
      prstr ")"
    end // end of [HIEtmpcst]
  | HIEtmpvar (d2v, hitss) => begin
      prstr "HIEtmpvar(";
      fprint_d2var (pf | out, d2v);
      prstr "; ";
      fprint_hityplstlst (pf | out, hitss);
      prstr ")"
    end // end of [HIEtmpvar]
  | HIEtop () => begin
      fprint1_string (pf | out, "HIEtop()")
    end // end of [HIEtop]
  | HIEtrywith _ => begin
      fprint1_string (pf | out, "HIEtrywith(...)")
    end // end of [HIEtrywith]
  | HIEvar d2v => begin
      prstr "HIEvar("; fprint_d2var (pf | out, d2v); prstr ")"
    end // end of [HIEvar]
end // end of [fprint_hiexp]

implement print_hiexp (hie) = print_mac (fprint_hiexp, hie)
implement prerr_hiexp (hie) = prerr_mac (fprint_hiexp, hie)

(* ****** ****** *)

implement
fprint_hiexplst (pf | out, xs) =
  $Lst.fprintlst {hiexp} (pf | out, xs, ", ", fprint_hiexp)
// end of [fprint_hiexplst]

implement
print_hiexplst (hies) = print_mac (fprint_hiexplst, hies)
implement
prerr_hiexplst (hies) = prerr_mac (fprint_hiexplst, hies)

(* ****** ****** *)

implement
fprint_hiexplstlst (pf | out, xss) =
  $Lst.fprintlst {hiexplst} (pf | out, xss, "; ", fprint_hiexplst)
// end of [fprint_hiexplstlst]

implement
fprint_labhiexplst {m}
  (pf | out, lhies0) = let
  fun aux (
    out: &FILE m, i: int, lhies: labhiexplst
  ) : void =
    case+ lhies of
    | LABHIEXPLSTcons (l, hie, lhies) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_label (pf | out, l);
        fprint1_string (pf | out, "= ");
        fprint_hiexp (pf | out, hie);
        aux (out, i+1, lhies)
      end // end of [LABHIEXPLSTcons]
    | LABHIEXPLSTnil () => () // end of [LABHIEXPLSTnil]
  // end of [aux]
in
  aux (out, 0, lhies0)
end // end of [fprint_labhiexplst]

(* ****** ****** *)

implement
fprint_hilab (pf | out, hil) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hil.hilab_node of
  | HILlab (l, s2e_rec) => begin
      prstr "HILlab("; fprint_label (pf | out, l); prstr ")"
    end // end of [HILlab]
  | HILind (hiess, s2e_elt) => begin
      prstr "HILind("; fprint_hiexplstlst (pf | out, hiess); prstr ")"
    end // end of [HILind]
end // end of [fprint_hilab]

implement
fprint_hilablst (pf | out, xs) =
  $Lst.fprintlst {hilab} (pf | out, xs, ", ", fprint_hilab)
// end of [fprint_hilablst]

(* ****** ****** *)

implement
fprint_vartyp (pf | out, vtp) = begin
  fprint_d2var (pf | out, vartyp_get_var vtp);
  fprint1_string (pf | out, "(");
  fprint_hityp (pf | out, hityp_decode (vartyp_get_typ vtp));
  fprint1_string (pf | out, ")")
end // end of [fprint_vartyp]

implement print_vartyp (vtp) = print_mac (fprint_vartyp, vtp)
implement prerr_vartyp (vtp) = prerr_mac (fprint_vartyp, vtp)

(* ****** ****** *)

(* end of [ats_hiexp_print.dats] *)
