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
// Time: October 2007
//
(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Fil = "ats_filename.sats"
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef l0ab = $Syn.l0ab

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement
fprint_p1at (pf | out, p1t) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ p1t.p1at_node of
  | P1Tann (p1t, s1e) => begin
      prstr "P1Tann(";
      fprint_p1at (pf | out, p1t);
      prstr "; ";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [P1Tann]
  | P1Tany () => fprint1_string (pf | out, "P1Tany()")
  | P1Tany2 () => fprint1_string (pf | out, "P1Tany2()")
  | P1Tapp_sta (p1t, s1as) => begin
      prstr "P1Tapp_sta(";
      fprint_p1at (pf | out, p1t);
      prstr "; ";
      fprint1_string (pf | out, "...");
      prstr ")"
    end // end of [P1Tapp_sta]
  | P1Tapp_dyn (p1t, _(*loc_arg*), npf, p1ts) => begin
      prstr "P1Tapp_dyn(";
      fprint_p1at (pf | out, p1t);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_p1atlst (pf | out, p1ts);
      prstr ")"
    end // end of [P1Tapp_dyn]
  | P1Tas (id, p1t) => begin
      prstr "P1Tas(";
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      prstr "; ";
      fprint_p1at (pf | out, p1t);
      prstr ")"
    end // end of [P1Tas]
  | P1Tchar c => begin
      prstr "P1Tchar("; fprint1_char (pf | out, c); prstr ")"
    end
  | P1Tempty () => begin
      fprint1_string (pf | out, "P1Tempty()")
    end
  | P1Texist (s1vs, p1t) => begin
      prstr "P1Texist(";
      fprint1_string (pf | out, "...");
      prstr "; ";
      fprint_p1at (pf | out, p1t);
      prstr ")"
    end // end of [P1Texist]
  | P1Tfloat f(*string*) => begin
      prstr "P1Tfloat("; fprint1_string (pf | out, f); prstr ")"
    end // end of [P1Tfloat]
  | P1Tfree p1t => begin
      prstr "P1Tfree("; fprint_p1at (pf | out, p1t); prstr ")"
    end // end of [P1Tfree]
  | P1Tint i(*string*) => begin
      prstr "P1Tint("; fprint1_string (pf | out, i); prstr ")"
    end
  | P1Tlist (npf, p1ts) => begin
      prstr "P1Tlist(";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_p1atlst (pf | out, p1ts);
      prstr ")"
    end // end of [P1Tlist]
  | P1Tlst p1ts => begin
      prstr "P1Tlst("; fprint_p1atlst (pf | out, p1ts); prstr ")"
    end // end of [P1Tlst]
  | P1Tqid (d0q, id) => begin
      $Syn.fprint_d0ynq (pf | out, d0q);
      $Sym.fprint_symbol (pf | out, id)
    end // end of [P1Tqid]
  | P1Trec (rk, lp1ts) => begin
      prstr "P1Trec(";
      fprint1_int (pf | out, rk);
      prstr "; ";
      fprint_labp1atlst (pf | out, lp1ts);
      prstr ")"
    end // end of [P1Trec]
  | P1Tref (id) => begin
      prstr "P1Tref(";
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      prstr ")"
    end // end of [P1Tref]
  | P1Trefas (id, p1t) => begin
      prstr "P1Tref(";
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      prstr "; ";
      fprint_p1at (pf | out, p1t);
      prstr ")"
    end // end of [P1Trefas]
  | P1Tstring s => begin
      prstr "P1Tstring(\""; fprint1_string (pf | out, s); prstr "\")"
    end // end of [P1Tstring]
  | P1Tsvararg s1a => begin
      prstr "P1Tsvararg("; fprint1_string (pf | out, "..."); prstr ")"
    end // end of [P1Tsvararg]
  | P1Ttup (tupknd, npf, p1ts) => begin
      prstr "P1Ttup(";
      fprint1_int (pf | out, tupknd);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_p1atlst (pf | out, p1ts);
      prstr ")"
    end // end of [P1Ttup]
(*
  | _ => begin
      $Loc.prerr_location p1t.p1at_loc;
      prerr "INTERNAL ERROR (ats_dynexp1_print)";
      prerr ": fprint_p1at: the pattern is not supported yet";
      prerr_newline ();
      exit (1)
    end // end of [_]
*)
end // end of [fprint_p1at]

implement print_p1at (p1t) = print_mac (fprint_p1at, p1t)
implement prerr_p1at (p1t) = prerr_mac (fprint_p1at, p1t)

(* ****** ****** *)

implement
fprint_p1atlst (pf | out, xs) =
  $Lst.fprintlst {p1at} (pf | out, xs, ", ", fprint_p1at)
// end of [fprint_p1atlst]

implement
fprint_labp1atlst
  {m} (pf | out, lp1ts0) = let
  fun aux (
    out: &FILE m, i: int, lp1ts: labp1atlst
  ) : void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ lp1ts of
    | LABP1ATLSTcons (l, p1t, lp1ts) => begin
        if i > 0 then prstr ", ";
        fprint_label (pf | out, l.l0ab_lab); prstr "= ";
        fprint_p1at (pf | out, p1t);
        aux (out, i+1, lp1ts)
      end
    | LABP1ATLSTnil () => ()
    | LABP1ATLSTdot () => begin
        if i > 0 then prstr ", "; fprint1_string (pf | out, "...")
      end // end of [LABP1ATLSTdot]
  end // end of [aux]
in
  aux (out, 0, lp1ts0)
end // end of [fprint_labp1atlst]

(* ****** ****** *)

implement
fprint_d1exp (
  pf | out, d1e0
) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
//
case+ d1e0.d1exp_node of
| D1Eann_effc (d1e, efc) => begin
    prstr "D1Eann_effc(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    $Eff.fprint_effcst (pf | out, efc);
    prstr ")"
  end // end of [D1Eann_effc]
| D1Eann_funclo (d1e, fc) => begin
    prstr "D1Eann_funclo(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    $Syn.fprint_funclo (pf | out, fc);
    prstr ")"
  end // end of [D1Eann_funclo]
| D1Eann_type (d1e, s1e) => begin
    prstr "D1Eann_type(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    fprint_s1exp (pf | out, s1e);
    prstr ")"
  end // end of [D1Eann_type]
| D1Eapp_dyn (d1e, _(*loc_arg*), npf, d1es) => begin
    prstr "D1Eapp_dyn(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    fprint1_int (pf | out, npf );
    prstr "; ";
    fprint_d1explst (pf | out, d1es);
    prstr ")"
  end // end of [D1Eapp_dyn]
| D1Eapp_sta (d1e, s1as) => begin
    prstr "D1Eapp_sta(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    fprint1_string (pf | out, "...");
    prstr ")"
  end // end of [D1Eapp_sta]
| D1Earrinit (s1e, od1e_asz, d1es_elt) => begin
    prstr "D1Earrinit(";
    fprint_s1exp (pf | out, s1e);
    prstr "; ";
    begin case+ od1e_asz of
    | Some d1e => fprint_d1exp (pf | out, d1e) | None () => ()
    end;
    prstr "; ";      
    fprint_d1explst (pf | out, d1es_elt);
    prstr ")"
  end // end of [D1Earrinit]
| D1Earrpsz (os1e_elt, d1es_elt) => begin
    prstr "D1Earrpsz(";
    begin case+ os1e_elt of
    | Some s1e => fprint_s1exp (pf | out, s1e) | None () => ()
    end; // end of [begin]
    prstr "; ";
    fprint_d1explst (pf | out, d1es_elt);
    prstr ")"
  end // end of [D1Earrpsz]
| D1Earrsub (d1e_arr, _(*loc_ind*), d1ess_ind) => begin
    prstr "D1Earrsub(";
    fprint_d1exp (pf | out, d1e_arr);
    prstr "; ";
    fprint_d1explstlst (pf | out, d1ess_ind);
    prstr ")"
  end // end of [D1Earrsub]
| D1Ebool (tf) => begin
    prstr "D1Ebool("; fprint1_bool (pf | out, tf); prstr ")"
  end // end of [D1Ebool]
| D1Ecaseof _ => begin
    prstr "D1Ecaseof("; fprint1_string (pf | out, "..."); prstr ")"
  end // end of [D1Ecaseof]
| D1Echar c => begin
    prstr "D1Echar("; fprint1_char (pf | out, c); prstr ")"
  end // end of [D1Ecst]
| D1Ecstsp cst => begin
    prstr "D1Ecstsp("; $Syn.fprint_cstsp (pf | out, cst); prstr ")"
  end // end of [D1Ecstsp]
| D1Ecrypt (knd, d1e) => begin
    prstr "D1Ecrypt(";
    fprint1_int (pf | out, knd);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Ecrypt]
//
| D1Edecseq (d1cs) => begin
    prstr "D1Edecseq(";
    fprint1_string (pf | out, "...");
    prstr ")"
  end // end of [D1Edecseq]
//
| D1Edynload (fil) => begin
    prstr "D1Edynload(";
    $Fil.fprint_filename (pf | out, fil);
    prstr ")"
  end // end of [D1Edynload]
| D1Eeffmask (effs, d1e) => begin
    prstr "D1Eeffmask(";
    $Eff.fprint_effectlst (pf | out, effs);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Eeffmask]
| D1Eempty () => begin
    prstr "D1Eempty()";
  end // end of [D1Eempty]
| D1Eexist (s1a, d1e) => begin
    prstr "D1Eexist(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Eexist]
| D1Eextval (s1e, code) => begin
    fprint_s1exp (pf | out, s1e);
    prstr "; ";
    prstr "\"";
    fprint1_string (pf | out, code);
    prstr "\"";
    prstr ")"
  end // end of [D1Eextval]
| D1Efix (knd, id_fun, d1e_def) => begin
    prstr "D1Efix(";
    fprint1_int (pf | out, knd);
    prstr "; ";
    $Syn.fprint_i0de (pf | out, id_fun);
    prstr "; ";
    fprint_d1exp (pf | out, d1e_def);
    prstr ")"
  end // end of [D1Efix]
| D1Efloat f(*string*) => begin
    prstr "D1Efloat("; fprint1_string (pf | out, f); prstr ")"
  end // end of [D1Efloat]
| D1Efloatsp f(*string*) => begin
    prstr "D1Efloatsp("; fprint1_string (pf | out, f); prstr ")"
  end // end of [D1Efloatsp]
| D1Efoldat (_(*s1as*), d1e) => begin
    prstr "D1Efoldat(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Efoldat]
| D1Efor (
    inv, ini, test, post, body
  ) => begin
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, ini);
    prstr "; ";
    fprint_d1exp (pf | out, test);
    prstr "; ";
    fprint_d1exp (pf | out, post);
    prstr "; ";
    fprint_d1exp (pf | out, body);
  end // end of [D1Efor]
| D1Efreeat (_(*s1as*), d1e) => begin
    prstr "D1Efreeat(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Efreeat]
| D1Eidextapp
    (id, ns, d1es_arg) => () where {
    val () = prstr "D1Eidextall(";
    val () = $Sym.fprint_symbol (pf | out, id)
    val () = prstr "; "
    val () = fprint1_string (pf | out, "...")
    val () = prstr "; "
    val () = fprint_d1explst (pf | out, d1es_arg)
    val () = prstr ")"
  } // end of [D1Eidext]
| D1Eif (
    _(*inv*), d1e_cond, d1e_then, od1e_else
  ) => () where {
    val () = prstr "D1Eif("
    val () = fprint1_string (pf | out, "...")
    val () = prstr "; "
    val () = fprint_d1exp (pf | out, d1e_cond)
    val () = prstr "; "
    val () = fprint_d1exp (pf | out, d1e_then)
    val () = case+ od1e_else of
      | Some d1e_else => begin
          prstr "; "; fprint_d1exp (pf | out, d1e_else)
        end // end of [Some]
      | None () => ()
    // end of [val]
    val () = prstr ")"
  } // end of [D1Eif]
| D1Eint i(*string*) => begin
    prstr "D1Eint("; fprint1_string (pf | out, i); prstr ")"
  end // end of [D1Eint]
| D1Eintsp i(*string*) => begin
    prstr "D1Eintsp("; fprint1_string (pf | out, i); prstr ")"
  end // end of [D1Eintsp]
| D1Elam_dyn (lin, p1t, d1e) => begin
    prstr "D1Elam_dyn(";
    fprint1_int (pf | out, lin);
    prstr "; ";
    fprint_p1at (pf | out, p1t);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Elam_dyn]
| D1Elaminit_dyn (lin, p1t, d1e) => begin
    prstr "D1Elaminit_dyn(";
    fprint1_int (pf | out, lin);
    prstr "; ";
    fprint_p1at (pf | out, p1t);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Elaminit_dyn]
| D1Elam_met (_, s1es, d1e) => begin
    prstr "D1Elam_met(";
    fprint_s1explst (pf | out, s1es);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Elam_met]
| D1Elam_sta_ana (_, s1as, d1e) => begin
    prstr "D1Elam_sta_ana(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")";
  end // end of [D1Elam_sta_ana]
| D1Elam_sta_syn (_, s1qs, d1e) => begin
    prstr "D1Elam_sta_syn(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")";
  end // end of [D1Elam_sta_syn]
| D1Elazy_delay (lin, d1e) => begin
    prstr "D1Elazy_delay(";
    fprint1_int (pf | out, lin);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Elazy_delay]
| D1Elet (d1cs, d1e) => begin
    prstr "D1Elet(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr ")"
  end // end of [D1Elet]
| D1Eptrof d1e => begin
    prstr "D1Eptrof("; fprint_d1exp (pf | out, d1e); prstr ")"
  end // end of [D1Eptrof]
| D1Elist (npf, d1es) => begin
    prstr "D1Elist(";
    fprint1_int (pf | out, npf);
    prstr "; ";
    fprint_d1explst (pf | out, d1es);
    prstr ")"
  end // end of [D1Elist]
| D1Eloopexn i => begin
    prstr "D1Eloopexn("; fprint1_int (pf | out, i); prstr ")"
  end // end of [D1Eloopexn]
| D1Elst (lin, os1e, d1es) => begin
    prstr "D1Elst(";
    fprint1_int (pf | out, lin);
    prstr "; ";
    begin case+ os1e of
      | Some s1e => begin
          fprint_s1exp (pf | out, s1e); prstr "; "
        end
      | None () => ()
    end;
    fprint_d1explst (pf | out, d1es);
    prstr ")"
  end // end of [D1Elst]
| D1Emacsyn (knd, d1e) => let
    val () = (case+ knd of
      | $Syn.MACSYNKINDcross () => fprint1_string (pf | out, "%(")
      | $Syn.MACSYNKINDdecode () => fprint1_string (pf | out, ",(")
      | $Syn.MACSYNKINDencode () => fprint1_string (pf | out, "`(")
    ) : void // end of [val]
  in
    fprint_d1exp (pf | out, d1e); prstr ")"
  end // end of [D1Emacsyn]
| D1Eqid (q, id) => begin
    $Syn.fprint_d0ynq (pf | out, q); $Sym.fprint_symbol (pf | out, id)
  end // end of [D1Eqid]
| D1Eraise (d1e) => begin
    prstr "D1Eraise("; fprint_d1exp (pf | out, d1e); prstr ")"
  end // end of [D1Eraise]
| D1Erec (recknd, ld1es) => begin
    prstr "D1Erec(";
    fprint1_int (pf | out, recknd);
    prstr "; ";
    fprint1_string (pf | out, "...");
    prstr ")"
  end // end of [D1Erec]
| D1Escaseof _ => begin
    prstr "D1Escaseof("; fprint1_string (pf | out, "..."); prstr ")"
  end // end of [D1Escaseof]
| D1Esel (knd, d1e, d1l) => begin
    prstr "D1Esel(";
    fprint1_int (pf | out, knd);
    prstr "; ";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    fprint_d1lab (pf | out, d1l);
    prstr ")"
  end // end of [D1Esel]
| D1Eseq d1es => begin
    prstr "D1Eseq("; fprint_d1explst (pf | out, d1es); prstr ")"
  end // end of [D1Eseq]
| D1Esexparg s1a => begin
    prstr "D1Esexparg("; fprint1_string (pf | out, "..."); prstr ")"
  end // end of [D1Esexparg]
| D1Eshowtype (d1e) => begin
    prstr "D1Eshowtype("; fprint_d1exp (pf | out, d1e); prstr ")"
  end // end of [D1Eshowtype]
| D1Esif (_(*inv*), s1e_cond, d1e_then, d1e_else) => begin
    prstr "D1Esif(";
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_s1exp (pf | out, s1e_cond);
    prstr "; ";
    fprint_d1exp (pf | out, d1e_then);
    prstr "; ";
    fprint_d1exp (pf | out, d1e_else);
    prstr ")"
  end // end of [D1Esif]
| D1Estring (str, len) => begin
    fprintf1_exn (pf | out, "D1Estring(\"%s\", %i)", @(str, len))
  end // end of [D1Estring]
| D1Estruct (ld1es) => begin
    prstr "D1Estruct(";
    fprint_labd1explst (pf | out, ld1es);
    prstr ")"
  end // end of [D1Estruct]
| D1Etmpid (qid, ts1ess) => begin
    prstr "D1Etmpid(";
    $Syn.fprint_d0ynq (pf | out, qid.tmpqi0de_qua);
    $Sym.fprint_symbol (pf | out, qid.tmpqi0de_sym);
    prstr "; ";
    fprint_tmps1explstlst (pf | out, ts1ess);
    prstr ")"
  end // end of [D1Etmpid]
| D1Etop () => begin
    fprint1_string (pf | out, "D1Etop()")
  end // end of [D1Etop]
| D1Etrywith (_(*r1es*), d1e, c1ls) => begin
    prstr "D1Etrywith(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    fprint1_string (pf | out, "...");
    prstr ")"
  end // end of [D1Etrywith]
| D1Etup (tupknd, npf, d1es) => begin
    prstr "D1Etup(";
    fprint1_int (pf | out, tupknd);
    prstr "; ";
    fprint1_int (pf | out, npf);
    prstr "; ";
    fprint_d1explst (pf | out, d1es);
    prstr ")"
  end // end of [D1Etup]
| D1Eviewat (d1e) => begin
    prstr "D1Eviewat("; fprint_d1exp (pf | out, d1e); prstr ")"
  end // end of [D1Eviewat]
| D1Ewhere (d1e, d1cs) => begin
    prstr "D1Ewhere(";
    fprint_d1exp (pf | out, d1e);
    prstr "; ";
    fprint1_string (pf | out, "...");
    prstr ")"
  end // end of [D1Ewhere]
| D1Ewhile (inv, test, body) => begin
    fprint1_string (pf | out, "...");
    prstr "; ";
    fprint_d1exp (pf | out, test);
    prstr "; ";
    fprint_d1exp (pf | out, body);
  end // end of [D1Ewhile]
(*
| _ => begin
    $Loc.prerr_location d1e0.d1exp_loc;
    prerr "INTERNAL ERROR (ats_dynexp1_print)";
    prerr "fprint_d1exp: not yet available"; prerr_newline ();
    exit {void} (1)
  end // end of [_]
*)
end // end of [fprint_d1exp]

implement print_d1exp (d1e) = print_mac (fprint_d1exp, d1e)
implement prerr_d1exp (d1e) = prerr_mac (fprint_d1exp, d1e)

(* ****** ****** *)

implement
fprint_d1explst (pf | out, xs) =
  $Lst.fprintlst {d1exp} (pf | out, xs, ", ", fprint_d1exp)
// end of [fprint_d1explst]

implement
fprint_d1explstlst (pf | out, xs) =
  $Lst.fprintlst {d1explst} (pf | out, xs, "; ", fprint_d1explst)
// end of [fprint_d1explstlst]

implement
fprint_labd1explst
  {m} (pf | out, ld1es0) = let
  fun aux (
    out: &FILE m, i: int, ld1es: labd1explst
  ) : void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ld1es of
    | LABD1EXPLSTcons (l, d1e, ld1es) => begin
        if i > 0 then prstr ", ";
        fprint_label (pf | out, l.l0ab_lab); prstr "= ";
        fprint_d1exp (pf | out, d1e);
        aux (out, i+1, ld1es)
      end // end of [LABD1EXPLSTcons]
    | LABD1EXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, 0, ld1es0)
end // end of [fprint_labd1explst]

(* ****** ****** *)

implement
fprint_d1lab (pf | out, d1l) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d1l.d1lab_node of
  | D1LABlab lab => fprint_label (pf | out, lab)
  | D1LABind ind => begin
      prstr "["; fprint_d1explstlst (pf | out, ind); prstr "]"
    end // end of [D1LABind]
end // end of [fprint_d1lab]

(* ****** ****** *)

(* end of [ats_dynexp1_print.dats] *)
