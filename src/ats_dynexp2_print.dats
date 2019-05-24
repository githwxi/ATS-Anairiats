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
// Start Time: December 2007
//
(* ****** ****** *)

staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label
macdef fprint_symbol = $Sym.fprint_symbol

(* ****** ****** *)

implement fprint_d2sym (pf | out, d2s) = begin
  $Syn.fprint_d0ynq (pf | out, d2s.d2sym_qua);
  fprint_symbol (pf | out, d2s.d2sym_sym)
end // end of [fprint_d2sym]

implement print_d2sym (d2s) = print_mac (fprint_d2sym, d2s)
implement prerr_d2sym (d2s) = prerr_mac (fprint_d2sym, d2s)

(* ****** ****** *)

implement fprint_d2item (pf | out, d2i) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d2i of
  | D2ITEMcon d2cs => begin
      prstr "D2ITEMcon("; fprint_d2conlst (pf | out, d2cs); prstr ")"
    end // end of [D2ITEMcon]
  | D2ITEMcst d2c => begin
      prstr "D2ITEMcst("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [D2ITEMcst]
  | D2ITEMe1xp e1xp => begin
      prstr "D2ITEMe1xp("; fprint_e1xp (pf | out, e1xp); prstr ")"
    end // end of [D2ITEMe1xp]
  | D2ITEMmacdef d2m => begin
      prstr "D2ITEMmacdef("; fprint_d2mac (pf | out, d2m); prstr ")"
    end // end of [D2ITEMmacdef]
  | D2ITEMmacvar d2v => begin
      prstr "D2ITEMmacvar("; fprint_d2var (pf | out, d2v); prstr ")"
    end // end of [D2ITEMmacvar]
  | D2ITEMsymdef d2is => begin
      prstr "D2ITEMsymdef("; fprint_d2itemlst (pf | out, d2is); prstr ")";
    end // end of [D2ITEMsymdef]
  | D2ITEMvar d2v => begin
      prstr "D2ITEMvar("; fprint_d2var (pf | out, d2v); prstr ")"
    end // end of [D2ITEMvar]
end // end of [fprint_d2item]

implement print_d2item (d2i) = print_mac (fprint_d2item, d2i)
implement prerr_d2item (d2i) = prerr_mac (fprint_d2item, d2i)

(* ****** ****** *)

implement
fprint_d2itemlst (pf | out, xs) =
  $Lst.fprintlst {d2item} (pf | out, xs, ", ", fprint_d2item)
// end of [fprint_s2qualst]

implement print_d2itemlst (d2is) = print_mac (fprint_d2itemlst, d2is)
implement prerr_d2itemlst (d2is) = prerr_mac (fprint_d2itemlst, d2is)

(* ****** ****** *)

implement
fprint_p2at (pf | out, p2t) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ p2t.p2at_node of
  | P2Tann (p2t, s2e) => begin
      prstr "P2Tann(";
      fprint_p2at (pf | out, p2t);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [P2Tann]
  | P2Tany () => fprint1_string (pf | out, "P2Tany()")
  | P2Tas (refknd, d2v, p2t) => begin
      prstr "P2Tas(";
      if (refknd > 0) then prstr "!";
      fprint_d2var (pf | out, d2v);
      prstr "; ";
      fprint_p2at (pf | out, p2t);
      prstr ")"
    end // end of [P2Tas]
  | P2Tbool b => begin
      prstr "P2Tbool("; fprint1_bool (pf | out, b); prstr ")"
    end // end of [P2Tbool]
  | P2Tchar c => begin
      prstr "P2Tchar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [P2Tchar]
  | P2Tcon (freeknd, d2c, s2qs, s2e, npf, p2ts) => begin
      prstr "P2Tcon(";
      if (freeknd < 0) then prstr "~";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_p2atlst (pf | out, p2ts);
      prstr ")"
    end // end of [P2Tcon]
  | P2Tempty () => begin
      fprint1_string (pf | out, "P2Tempty()")
    end // end of [P2Tempty]
  | P2Texist (s2vs, p2t) => begin
      prstr "P2Texist(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_p2at (pf | out, p2t);
      prstr ")"
    end // end of [P2Texist]
  | P2Tfloat f(*string*) => begin
      prstr "P2Tfloat("; fprint1_string (pf | out, f); prstr ")"
    end // end of [P2Tfloat]
  | P2Tint (str, _(*intinf*)) => begin
      prstr "P2Tint("; fprint1_string (pf | out, str); prstr ")"
    end // end of [P2Tint]
  | P2Tlist (npf, p2ts) => begin
      prstr "P2Tlist(";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_p2atlst (pf | out, p2ts);
      prstr ")"
    end // end of [P2Tlist]
  | P2Tlst p2ts => begin
      prstr "P2Tlst("; fprint_p2atlst (pf | out, p2ts); prstr ")"
    end // end of [P2Tlst]
  | P2Trec (recknd, npf, lp2ts) => begin
      prstr "P2Trec(";
      fprint1_int (pf | out, recknd);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_labp2atlst (pf | out, lp2ts);
      prstr ")"
    end // end of [P2Trec]
  | P2Tstring str => begin
      prstr "P2Tstring(\""; fprint1_string (pf | out, str); prstr "\")"
    end // end of [P2Tstring]
  | P2Tvar (refknd, d2v) => begin
      prstr "P2Tvar(";
      if (refknd > 0) then prstr "!";
      fprint_d2var (pf | out, d2v);
      prstr ")"
    end // end of [P2Tvar]
  | P2Tvbox (d2v) => begin
      prstr "P2Tvbox("; fprint_d2var (pf | out, d2v); prstr ")"
    end // end of [P2Tvbox]
(*
  | _ => begin
      prerr "INTERNAL ERROR (ats_dynexp2_print)";
      prerr ": fprint_p2at: the pattern at [";
      prerr p2t.p2at_loc; prerr "] is not supported.";
      prerr_newline ();
      exit (1)
    end // end of [_]
*)
end // end of [fprint_p2at]

implement print_p2at (p2t) = print_mac (fprint_p2at, p2t)
implement prerr_p2at (p2t) = prerr_mac (fprint_p2at, p2t)

(* ****** ****** *)

implement
fprint_p2atlst (pf | out, xs) =
  $Lst.fprintlst {p2at} (pf | out, xs, ", ", fprint_p2at)
// end of [fprint_p2atlst]

implement print_p2atlst (p2ts) = print_mac (fprint_p2atlst, p2ts)
implement prerr_p2atlst (p2ts) = prerr_mac (fprint_p2atlst, p2ts)

(* ****** ****** *)

implement
fprint_labp2atlst {m} (pf | out, lp2ts) = let
  fun aux (out: &FILE m, i: int, lp2ts: labp2atlst): void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ lp2ts of
    | LABP2ATLSTcons (l, p2t, lp2ts) => begin
        if i > 0 then prstr ", ";
        fprint_label (pf | out, l); prstr "= "; fprint_p2at (pf | out, p2t);
        aux (out, i+1, lp2ts)
      end // end of [LABP2ATLSTcons]
    | LABP2ATLSTnil () => ()
    | LABP2ATLSTdot () => begin
        if i > 0 then prstr ", "; fprint1_string (pf | out, "...")
      end // end of [LABP2ATLSTdot]
  end // end of [aux]
in
  aux (out, 0, lp2ts)
end // end of [fprint_labp2atlst]

(* ****** ****** *)

implement
fprint_i2nvarg (pf | out, i2nv) = let
  val () = fprint_d2var (pf | out, i2nv.i2nvarg_var)
  val () = fprint1_string (pf | out, ": ")
  val () = fprint_s2expopt (pf | out, i2nv.i2nvarg_typ)
in
  // empty
end // end of [fprint_i2nvarg]

implement
fprint_i2nvarglst (pf | out, xs) =
  $Lst.fprintlst {i2nvarg} (pf | out, xs, ", ", fprint_i2nvarg)
// end of [fprint_i2nvarglst]

implement
print_i2nvarglst (args) = print_mac (fprint_i2nvarglst, args)
implement
prerr_i2nvarglst (args) = prerr_mac (fprint_i2nvarglst, args)

(* ****** ****** *)

implement
fprint_i2nvresstate
  (pf | out, res) = let
  val () = fprint1_string (pf | out, "[");
  val () = fprint_s2varlst (pf | out, res.i2nvresstate_svs);
  val () = fprint1_string (pf | out, "; ");
  val () = fprint_s2explst (pf | out, res.i2nvresstate_gua);
  val () = fprint1_string (pf | out, "] (");
  val () = fprint_i2nvarglst (pf | out, res.i2nvresstate_arg);
  val () = fprint_string (pf | out, ")")
in
  // empty
end // end of [fprint_i2nvresstate]

implement
print_i2nvresstate (res) = print_mac (fprint_i2nvresstate, res)
implement
prerr_i2nvresstate (res) = prerr_mac (fprint_i2nvresstate, res)

(* ****** ****** *)

implement
fprint_d2exparg
  (pf | out, d2a) = begin
  case+ d2a of
  | D2EXPARGsta s2as => begin
      fprint_s2exparglst (pf | out, s2as)
    end // end of [D2EXPARGsta]
  | D2EXPARGdyn (_(*loc_arg*), _(*npf*), d2es) => begin
      fprint_d2explst (pf | out, d2es)
    end // end of [D2EXPARGdyn]
end // end of [fprint_d2exparg]

implement
print_d2exparg (arg) = print_mac (fprint_d2exparg, arg)
implement
prerr_d2exparg (arg) = prerr_mac (fprint_d2exparg, arg)

(* ****** ****** *)

implement
fprint_d2exparglst (pf | out, xs) =
  $Lst.fprintlst {d2exparg} (pf | out, xs, ", ", fprint_d2exparg)
// end of [fprint_d2exparglst]

implement
print_d2exparglst (args) = print_mac (fprint_d2exparglst, args)
implement
prerr_d2exparglst (args) = prerr_mac (fprint_d2exparglst, args)

(* ****** ****** *)

implement
fprint_d2exp (pf | out, d2e0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d2e0.d2exp_node of
  | D2Eann_seff (d2e, s2fe) => begin
      prstr "D2Eann_seff(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      fprint_s2eff (pf | out, s2fe);
      prstr ")"
    end // end of [D2Eann_seff]
  | D2Eann_funclo (d2e, fc) => begin
      prstr "D2Eann_funclo(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      $Syn.fprint_funclo (pf | out, fc);
      prstr ")"
    end // end of [D2Eann_funclo]
  | D2Eann_type (d2e, s2e) => begin
      prstr "D2Eann_type(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [D2Eann_type]
  | D2Eapps (d2e_fun, d2as_arg) => begin
      prstr "D2Eapps(";
      fprint_d2exp (pf | out, d2e_fun);
      prstr "; ";
      fprint_d2exparglst (pf | out, d2as_arg);
      prstr ")"
    end // end of [D2Eapps]
  | D2Earrinit (s2e_elt, od2e_asz, d2es_elt) => begin
      prstr "D2Earrinit(";
      fprint_s2exp (pf | out, s2e_elt);
      prstr "; ";
      begin case+ od2e_asz of
      | Some d2e => fprint_d2exp (pf | out, d2e) | None () => ()
      end;
      prstr "; ";
      fprint_d2explst (pf | out, d2es_elt);
      prstr ")"
    end // end of [D2Earrinit]
  | D2Earrpsz (os2e_elt, d2es_elt) => begin
      prstr "D2Earrpsz(";
      begin case+ os2e_elt of
      | Some s2e => fprint_s2exp (pf | out, s2e) | None () => ()
      end;
      prstr "; ";
      fprint_d2explst (pf | out, d2es_elt);
      prstr ")"
    end // end of [D2Earrpsz]
  | D2Earrsub (d2s, d2e_arr, _(*loc_ind*), d2ess_ind) => begin
      prstr "D2Earrsub(";
      fprint_d2sym (pf | out, d2s);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_arr);
      prstr "; ";
      fprint1_string (pf | out, "...");
      prstr ")"
    end // end of [D2Earrsub]
  | D2Eassgn (d2e_lval, d2e_val) => begin
      prstr "D2Eassgn(";
      fprint_d2exp (pf | out, d2e_lval);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_val);
      prstr ")"
    end // end of [D2Eassgn]
  | D2Ebool b => begin
      if b then
        fprint_string (pf | out, "D2Ebool(true)")
      else
        fprint_string (pf | out, "D2Ebool(false)")
      // end of [if]
    end // end of [D3Ebool]
  | D2Ecaseof _ => begin
      prstr "D2Ecaseof("; fprint1_string (pf | out, "..."); prstr ")"
    end // end of [D2Ecaseof]
  | D2Echar c => begin
      prstr "D2Echar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [D2Echar]
  | D2Econ (d2c, s2as, npf, d2es) => begin
      prstr "D2Econ(";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_d2explst (pf | out, d2es);
      prstr ")"
    end // end of [D2Econ]
  | D2Ecst d2c => begin
      prstr "D2Ecst("; fprint_d2cst (pf | out, d2c); prstr ")"
    end // end of [D2Ecst]
  | D2Ecstsp cst => begin
      prstr "D2Ecstsp("; $Syn.fprint_cstsp (pf | out, cst); prstr ")"
    end // end of [D2Ecstsp]
  | D2Ecrypt (knd, d2e) => begin
      prstr "D2Ecrypt(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Ecrypt]
  | D2Elazy_delay (d2e) => begin
      prstr "D2Elazy_delay("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Elazy_delay]
  | D2Elazy_ldelay (d2e_eval, d2e_free) => begin
      prstr "D2Elazy_ldelay(";
      fprint_d2exp (pf | out, d2e_eval);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_free);
      prstr ")"
    end // end of [D2Elazy_ldelay]
  | D2Ederef d2e => begin
      prstr "D2Ederef("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Ederef]
  | D2Edynload (fil) => begin
      prstr "D2Edynload("; $Fil.fprint_filename (pf | out, fil); prstr ")"
    end // end of [D2Edynload]
  | D2Eeffmask (effs, d2e) => begin
      prstr "D2Eeffmask(";
      $Eff.fprint_effectlst (pf | out, effs);
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Eeffmask]
  | D2Eempty () => begin
      fprint1_string (pf | out, "D2Eempty()")
    end // end of [D2Eempty]
  | D2Eexist (s2a, d2e) => begin
      prstr "D2Eexist(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Eexist]
  | D2Eextval (s2e, code) => begin
      prstr "D2Eextval(";
      fprint_s2exp (pf | out, s2e);
      prstr "; ";
      prstr "\"";
      fprint1_string (pf | out, code);
      prstr "\"";
      prstr ")"
    end // end of [D2Eextval]
  | D2Efix (knd, d2v_fun, d2e_body) => begin
      prstr "D2Efix(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_d2var (pf | out, d2v_fun);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_body);
      prstr ")"
    end // end of [D2Efix]
  | D2Efloat f(*string*) => begin
      prstr "D2Efloat("; fprint1_string (pf | out, f); prstr ")"
    end // end of [D2Efloat]
  | D2Efloatsp f(*string*) => begin
      prstr "D2Efloatsp("; fprint1_string (pf | out, f); prstr ")"
    end // end of [D2Efloatsp]
  | D2Efoldat (sarg, d2e) => begin
      prstr "D2Efoldat("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Efoldat]
  | D2Efor (inv, ini, test, post, body) => begin
      prstr "D2Efor(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_d2exp (pf | out, ini);
      prstr "; ";
      fprint_d2exp (pf | out, test);
      prstr "; ";
      fprint_d2exp (pf | out, post);
      prstr "; ";
      fprint_d2exp (pf | out, body);
      prstr ")"
    end // end of [D2Efor]
  | D2Efreeat (sarg, d2e) => begin
      prstr "D2Efreeat("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Efree]
  | D2Eif (_(*inv*), d2e_cond, d2e_then, od2e_else) => begin
      prstr "D2Eif(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_d2exp (pf | out, d2e_cond);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_then);
      begin case+ od2e_else of
        | Some d2e_else => begin
           prstr "; "; fprint_d2exp (pf | out, d2e_else)
          end // end of [Some]
        | None () => ()
      end; // end of [begin]
      prstr ")"
    end // end of [D2Eif]
  | D2Eint (str, int) => begin
      prstr "D2Eint("; fprint1_string (pf | out, str); prstr ")"
    end // end of [D2Eint]
  | D2Eintsp (str, int) => begin
      prstr "D2Eintsp("; fprint1_string (pf | out, str); prstr ")"
    end // end of [D2Eintsp]
  | D2Elam_dyn (lin, npf, p2ts, d2e) => begin
      prstr "D2Elam_dyn(";
      fprint1_int (pf | out, lin);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_p2atlst (pf | out, p2ts);
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Elam_dyn]
  | D2Elaminit_dyn (lin, npf, p2ts, d2e) => begin
      prstr "D2Elaminit_dyn(";
      fprint1_int (pf | out, lin);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_p2atlst (pf | out, p2ts);
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Elaminit_dyn]
  | D2Elam_met (_, s2es, d2e) => begin
      prstr "D2Elam_met(";
      fprint_s2explst (pf | out, s2es);
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Elam_met]
  | D2Elam_sta (s2vs, s2ps, d2e) => begin
      prstr "D2Elam_sta(";
      fprint_s2varlst (pf | out, s2vs);
      prstr "; ";
      fprint_s2explst (pf | out, s2ps);
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")";
    end // end of [D2Elam_sta]
  | D2Elet (d2cs, d2e) => begin
      prstr "D2Elet(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_d2exp (pf | out, d2e);
      prstr ")"
    end // end of [D2Elet]
  | D2Emac d2m => begin
      prstr "D2Emac("; fprint_d2mac (pf | out, d2m); prstr ")"
    end // end of [D2Emac]
  | D2Emacsyn (knd, d2e) => let
      val () = (case+ knd of
        | $Syn.MACSYNKINDcross () => fprint1_string (pf | out, "%(")
        | $Syn.MACSYNKINDdecode () => fprint1_string (pf | out, ",(")
        | $Syn.MACSYNKINDencode () => fprint1_string (pf | out, "`(")
      ) : void // end of [val]
    in
      fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Emacsyn]
  | D2Elist (npf, d2es) => begin
      prstr "D2Elist(";
      fprint_int (pf | out, npf);
      prstr "; ";
      fprint_d2explst (pf | out, d2es);
      prstr ")"
    end // end of [D2Elist]
  | D2Eloopexn i => begin
      prstr "D2Eloopexn("; fprint1_int (pf | out, i); prstr ")"
    end // end of [D2Eloopexn]
  | D2Elst (lin, os2e, d2es) => begin
      prstr "D2Elst(";
      fprint1_int (pf | out, lin);
      prstr "; ";
      begin case+ os2e of
        | Some s2e => begin
            fprint_s2exp (pf | out, s2e); prstr "; "
          end
        | None () => ()
      end;
      fprint_d2explst (pf | out, d2es);
      prstr ")"
    end // end of [D2Elst]
  | D2Eptrof d2e => begin
      prstr "D2Eptrof("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Eptrof]
  | D2Eraise (d2e) => begin
      prstr "D2Eraise("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Eraise]
  | D2Erec (recknd, npf, ld2es) => begin
      prstr "D2Erec(";
      fprint1_int (pf | out, recknd);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_labd2explst (pf | out, ld2es);
      prstr ")"
    end // end of [D2Erec]
  | D2Escaseof _ => begin
      prstr "D2Escaseof("; fprint1_string (pf | out, "..."); prstr ")"
    end // end of [D2Escaseof]
  | D2Esel (d2e, d2ls) => begin
      prstr "D2Esel(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      fprint_d2lablst (pf | out, d2ls);
      prstr ")"
    end // end of [D2Esel]
  | D2Eseq d2es => begin
      prstr "D2Eseq("; fprint_d2explst (pf | out, d2es); prstr ")"
    end // end of [D2Eseq]
  | D2Eshowtype (d2e) => begin
      prstr "D2Eshowtype("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Eshowtype]
  | D2Esif (_(*inv*), s2e_cond, d2e_then, d2e_else) => begin
      prstr "D2Esif(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_s2exp (pf | out, s2e_cond);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_then);
      prstr "; ";
      fprint_d2exp (pf | out, d2e_else);
      prstr ")"
    end // end of [D2Esif]
  | D2Estring (str, len) => begin
      fprintf1_exn (pf | out, "D2Estring(\"%s\", %i)", @(str, len))
    end // end of [D2Estring]
  | D2Estruct (ld2es) => begin
      prstr "D2Estruct("; fprint_labd2explst (pf | out, ld2es); prstr ")"
    end // end of [D2Estruct]
  | D2Esym d2s => begin
      prstr "D2Esym("; fprint_d2sym (pf | out, d2s); prstr ")"
    end // end of [D2Esym]
  | D2Etmpid (d2e, ts2ess) => begin
      prstr "D2Etmpid(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      fprint_tmps2explstlst (pf | out, ts2ess);
      prstr ")"
    end // end of [D2Etmpid]
  | D2Etop () => begin
      fprint1_string (pf | out, "D2Etop()")
    end // end of [D2Etop]
  | D2Etrywith (_(*r2es*), d2e, c2ls) => begin
      prstr "D2Etrywith(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      fprint1_string (pf | out, "...");
      prstr ")"
    end // end of [D2Etrywith]
  | D2Evar (d2v) => begin
      prstr "D2Evar("; fprint_d2var (pf | out, d2v); prstr ")"
    end // end of [D2Evar]
  | D2Eviewat (d2e) => begin
      prstr "D2Eviewat("; fprint_d2exp (pf | out, d2e); prstr ")"
    end // end of [D2Eviewat]
  | D2Ewhere (d2e, d2cs) => begin
      prstr "D2Ewhere(";
      fprint_d2exp (pf | out, d2e);
      prstr "; ";
      fprint1_string (pf | out, "...");
      prstr ")"
    end // end of [D2Ewhere]
  | D2Ewhile (inv, test, body) => begin
      prstr "D2Ewhile(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_d2exp (pf | out, test);
      prstr "; ";
      fprint_d2exp (pf | out, body);
      prstr ")"
    end // end of [D2Ewhile]
end // end of [fprint_d2exp]

implement print_d2exp (d2e) = print_mac (fprint_d2exp, d2e)
implement prerr_d2exp (d2e) = prerr_mac (fprint_d2exp, d2e)

(* ****** ****** *)

implement
fprint_d2explst (pf | out, xs) =
  $Lst.fprintlst {d2exp} (pf | out, xs, ", ", fprint_d2exp)
// end of [fprint_d2explst]

implement print_d2explst (d2es) = print_mac (fprint_d2explst, d2es)
implement prerr_d2explst (d2es) = prerr_mac (fprint_d2explst, d2es)

(* ****** ****** *)

implement
fprint_d2explstlst (pf | out, xs) =
  $Lst.fprintlst {d2explst} (pf | out, xs, "; ", fprint_d2explst)
// end of [fprint_d2explstlst]

implement print_d2explstlst (d2ess) = print_mac (fprint_d2explstlst, d2ess)
implement prerr_d2explstlst (d2ess) = prerr_mac (fprint_d2explstlst, d2ess)

(* ****** ****** *)

implement
fprint_labd2explst
  {m} (pf | out, ld2es) = let
  fun aux (
    out: &FILE m, i: int, ld2es: labd2explst
  ) : void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ld2es of
    | LABD2EXPLSTcons (l, d2e, ld2es) => begin
        if i > 0 then prstr ", ";
        fprint_label (pf | out, l); prstr "= "; fprint_d2exp (pf | out, d2e);
        aux (out, i+1, ld2es)
      end // end of [LABD2EXPLSTcons]
    | LABD2EXPLSTnil () => () // end of [LABD2EXPLSTnil]
  end // end of [aux]
in
  aux (out, 0, ld2es)
end // end of [fprint_labd2explst]

implement
print_labd2explst (ld2es) = print_mac (fprint_labd2explst, ld2es)
implement
prerr_labd2explst (ld2es) = prerr_mac (fprint_labd2explst, ld2es)

(* ****** ****** *)

implement
fprint_d2lab (pf | out, d2l) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d2l.d2lab_node of
  | D2LABlab lab => fprint_label (pf | out, lab)
  | D2LABind ind =>  begin
      prstr "["; fprint_d2explstlst (pf | out, ind); prstr "]"
    end // end of [D2LABind]
end // end of [fprint_d2lab]

implement print_d2lab (d2l) = print_mac (fprint_d2lab, d2l)
implement prerr_d2lab (d2l) = prerr_mac (fprint_d2lab, d2l)

(* ****** ****** *)

implement
fprint_d2lablst (pf | out, xs) =
  $Lst.fprintlst {d2lab} (pf | out, xs, ", ", fprint_d2lab)
// end of [fprint_d2lablst]

implement print_d2lablst (d2ls) = print_mac (fprint_d2lablst, d2ls)
implement prerr_d2lablst (d2ls) = prerr_mac (fprint_d2lablst, d2ls)

(* ****** ****** *)

datatype l2val = // type for left-values

implement
fprint_l2val (pf | out, l2v) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ l2v of
  | L2VALarrsub (d2s, d2e_arr, loc, d2ess_ind) => let
      val () = prstr "L2VALarrsub("
      val () = fprint_d2exp (pf | out, d2e_arr)
      val () = prstr "; "
      val () = fprint_d2explstlst (pf | out, d2ess_ind)
      val () = prstr ")"
    in
      // nothing
    end // end of [L2VALarrsub]
  | L2VALptr (d2e_ptr, d2ls) => let
      val () = prstr "L2VALptr("
      val () = fprint_d2exp (pf | out, d2e_ptr)
      val () = prstr ", "
      val () = fprint_d2lablst (pf | out, d2ls)
      val () = prstr ")"
    in
      // nothing
    end // end of [L2VALptr]
  | L2VALvar_lin (d2v, d2ls) => let
      val () = prstr "L2VALvar_lin("
      val () = fprint_d2var (pf | out, d2v)
      val () = prstr ", "
      val () = fprint_d2lablst (pf | out, d2ls)
      val () = prstr ")"
    in
      // nothing
    end // end of [L2VALptr]
  | L2VALvar_mut (d2v, d2ls) => let
      val () = prstr "L2VALvar_mut("
      val () = fprint_d2var (pf | out, d2v)
      val () = prstr ", "
      val () = fprint_d2lablst (pf | out, d2ls)
      val () = prstr ")"
    in
      // nothing
    end // end of [L2VALptr]
  | L2VALnone d2e => let
      val () = prstr "L2VALnone("
      val () = fprint_d2exp (pf | out, d2e)
      val () = prstr ")"
    in
      // nothing
    end // end of [L2VALnone]
end // end of [fprint_l2val]

implement print_l2val (l2v) = print_mac (fprint_l2val, l2v)
implement prerr_l2val (l2v) = prerr_mac (fprint_l2val, l2v)

(* ****** ****** *)

(* end of [ats_dynexp2_print.dats] *)
