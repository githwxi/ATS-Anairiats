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
// Start Time: August 2007
//
(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Lab = "ats_label.sats"
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

typedef lab_t = $Lab.label_t
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement
fprint_e1xp (pf | out, e0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ e0.e1xp_node of
  | E1XPapp (e, _(*loc_arg*), es) => begin
      prstr "E1XPapp(";
      fprint_e1xp (pf | out, e);
      prstr "; ";
      fprint_e1xplst (pf | out, es);
      prstr ")"
    end // end of [E1XPapp]
  | E1XPchar (c: char) => begin
      prstr "E1XPchar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [E1XPchar]
  | E1XPfloat (f: string) => begin
      prstr "E1XPfloat("; fprint1_string (pf | out, f); prstr ")"
    end // end of [E1XPfloat]
  | E1XPide (id: sym_t) => begin
      $Sym.fprint_symbol (pf | out, id)
    end // end of [E1XPide]
  | E1XPint (int(*string*)) => begin
      prstr "E1XPint("; fprint1_string (pf | out, int); prstr ")"
    end // end of [E1XPint]
  | E1XPlist es => begin
      prstr "E1XPlist("; fprint_e1xplst (pf | out, es); prstr ")"
    end // end of [E1XPlist]
  | E1XPnone () => begin
      fprint1_string (pf | out, "E1XPnone()")
    end // end of [E1XPnone]
  | E1XPstring (str, len) => begin
      prstr "E1XPstring(";
      fprint1_string (pf | out, str);
      prstr ", ";
      fprint1_int (pf | out, len);
      prstr ")"
    end // end of [E1XPstring]
  | E1XPundef () => begin
      fprint1_string (pf | out, "E1XPundef()")
    end // end of [E1XPundef]
  | E1XPcstsp (cst) => begin
      prstr "E1XPcstsp(";
      $Syn.fprint_cstsp (pf | out, cst);
      prstr ")"
    end // end of [E1XPcstsp]
 
end // end of [fprint_e1xp]

implement print_e1xp (e) = print_mac (fprint_e1xp, e)
implement prerr_e1xp (e) = prerr_mac (fprint_e1xp, e)

(* ****** ****** *)

implement
fprint_e1xplst (pf | out, xs) =
  $Lst.fprintlst {e1xp} (pf | out, xs, ", ", fprint_e1xp)
// end of [fprint_e1xplst]

implement print_e1xplst (es) = print_mac (fprint_e1xplst, es)
implement prerr_e1xplst (es) = prerr_mac (fprint_e1xplst, es)

(* ****** ****** *)

implement
fprint_s1rt (pf | out, s1t0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1t0.s1rt_node of
  | S1RTapp (s1t, s1ts) => begin
      prstr "S1RTapp(";
      fprint_s1rt (pf | out, s1t);
      prstr "; ";
      fprint_s1rtlst (pf | out, s1ts);
      prstr ")"
    end // end of [S1RTapp]
  | S1RTlist s1ts => begin
      prstr "S1RTlist("; fprint_s1rtlst (pf | out, s1ts); prstr ")"
    end // end of [S1RTlist]
  | S1RTqid (q, id) => begin
      prstr "S1RTqid(";
      $Syn.fprint_s0rtq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id);
      prstr ")"
    end // end of [S1RTqid]
  | S1RTtup s1ts => begin
      prstr "S1RTtup(";
      fprint_s1rtlst (pf | out, s1ts);
      prstr ")"
    end // end of [S1RTtup]
end // end of [fprint_s1rt]

implement print_s1rt (s1t) = print_mac (fprint_s1rt, s1t)
implement prerr_s1rt (s1t) = prerr_mac (fprint_s1rt, s1t)

(* ****** ****** *)

implement
fprint_s1rtlst (pf | out, xs) =
  $Lst.fprintlst {s1rt} (pf | out, xs, ", ", fprint_s1rt)
// end of [fprint_s1rtlst]

implement print_s1rtlst (s1ts) = print_mac (fprint_s1rtlst, s1ts)
implement prerr_s1rtlst (s1ts) = prerr_mac (fprint_s1rtlst, s1ts)

(* ****** ****** *)

implement fprint_s1rtopt
  (pf | out, os1t) = case+ os1t of
  | Some s1t => fprint_s1rt (pf | out, s1t) | None () => ()
// end of [fprint_s1rtopt]

(* ****** ****** *)

fn fprint_s1arg {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, s1a: s1arg
) : void = let
  val () = $Sym.fprint_symbol (pf | out, s1a.s1arg_sym)
in
  case+ s1a.s1arg_srt of
  | Some s1t => begin
      fprint1_string (pf | out, ": "); fprint_s1rt (pf | out, s1t)
    end // end of [Some]
  | None () => () // end of [None]
end // end of [fprint_s1arg]

fn fprint_s1arglst {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, xs: s1arglst
) : void =
  $Lst.fprintlst {s1arg} (pf | out, xs, ", ", fprint_s1arg)
// end of [fprint_s1arglst]

(* ****** ****** *)

fun fprint_s1qua {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, s1q: s1qua
) : void = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1q.s1qua_node of
  | S1Qprop s1e => begin
      prstr "S1Qprop(";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [S1Qprop]
  | S1Qvars (ids, s1te) => begin
      prstr "S1Qvars(";
      $Syn.fprint_i0delst (pf | out, ids);
      prstr "; ";
      fprint_s1rtext (pf | out, s1te);
      prstr ")"
    end // end of [S1Qvars]
end // end of [fprint_s1qua]

fun fprint_s1qualst {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, s1qs0: s1qualst
) : void = let
  fun aux (out: &FILE m, i: int, s1qs: s1qualst): void =
    case+ s1qs of
    | cons (s1q, s1qs) => begin
        if i > 0 then fprint1_string (pf | out, ", "); 
        fprint_s1qua (pf | out, s1q); aux (out, i+1, s1qs)
      end // end of [cons]
    | nil () => () // end of [nil]
  // end of [aux]
in
  aux (out, 0, s1qs0)
end // end of [fprint_s1qualst]

(* ****** ****** *)

implement
fprint_s1exp (pf | out, s1e0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1e0.s1exp_node of
  | S1Eann (s1e, s1t) => begin
      prstr "S1Eann(";
      fprint_s1exp (pf | out, s1e);
      prstr ", ";
      fprint_s1rt (pf | out, s1t);
      prstr ")"
    end
  | S1Eany () => fprint1_string (pf | out, "S1Eany()")
  | S1Eapp (s1e_fun, _(*loc_arg*), s1es_arg) => begin
      prstr "S1Eapp(";
      fprint_s1exp (pf | out, s1e_fun);
      prstr "; ";
      fprint_s1explst (pf | out, s1es_arg);
      prstr ")"
    end // end of [S1Eapp]
  | S1Echar c => begin
      prstr "S1Echar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [S1Echar]
  | S1Eexi (knd(*funres*), s1qs, s1e) => begin
      prstr "S1Eexi(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_s1qualst (pf | out, s1qs);
      prstr "; ";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [S1Eexi]
  | S1Eextype (name, arg) => begin
      prstr "S1Eextype(";
      fprint1_string (pf | out, name);
      prstr "; ";
      fprint_s1explstlst (pf | out, arg);
      prstr ")"
    end // end of [S1Eextype]
  | S1Eimp (fc, lin, prf, oefc) => begin
      prstr "S1Eimp(";
      $Syn.fprint_funclo (pf | out, fc); prstr "; ";
      fprint1_int (pf | out, lin); prstr "; ";
      fprint1_int (pf | out, prf); prstr "; ";
      begin case+ oefc of
      | Some efc => $Eff.fprint_effcst (pf | out, efc)
      | None () => ()
      end;
      prstr ")"
    end // end of [S1Eimp]
  | S1Eint str => begin
      prstr "S1Eint("; fprint1_string (pf | out, str); prstr ")"
    end // end of [S1Eint]
  | S1Einvar (refval, s1e) => begin
      prstr "S1Einvar(";
      fprint1_int (pf | out, refval);
      prstr "; ";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [S1Einvar]
  | S1Elam _ => prstr "S1Elam(...)"
  | S1Elist (npf, s1es) => begin
      prstr "S1Elist(";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_s1explst (pf | out, s1es);
      prstr ")"
    end // end of [S1Elist]
(*
// HX-2010-12-04: simplification
  | S1Emod _ => begin
      prstr "S1Emod(";
      fprint1_string (pf | out, "...");
      prstr ")"
    end // end of [S1Emod]
*)
(*
// HX-2010-12-04: inadequate design
  | S1Enamed (name, s1e) => begin
      prstr "S1Enamed(";
      $Sym.fprint_symbol (pf | out, name);
      prstr ", ";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [S1Enamed]
*)
  | S1Eqid (q, id: sym_t) => begin
      $Syn.fprint_s0taq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id)
    end // end of [S1Eqid]
  | S1Eread (s1e1, s1e2) => begin
      prstr "S1Eread(";
      fprint_s1exp (pf | out, s1e1);
      prstr ", ";
      fprint_s1exp (pf | out, s1e2);
      prstr ")"
    end // end of [S1Eread]
(*
// HX-2010-11-01: simplification
  | S1Estruct ls1es => begin
      prstr "S1Estruct(";
      fprint_labs1explst (pf | out, ls1es);
      prstr ")"
    end // end of [S1Estruct]
*)
  | S1Etop (knd, s1e) => begin
      prstr "S1Etop(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [S1Etop]
  | S1Etrans (s1e1, s1e2) => begin
      prstr "S1Etrans(";
      fprint_s1exp (pf | out, s1e1);
      prstr ", ";
      fprint_s1exp (pf | out, s1e2);
      prstr ")"
    end // end of [S1Etrans]
  | S1Etyarr (s1e_elt, s1ess_dim) => begin
      prstr "S1Earray(";
      fprint_s1exp (pf | out, s1e_elt);
      fprint1_string (pf | out, ", ...");
      prstr ")"
    end // end pf [S1Etyarr]
  | S1Etyrec (knd, ls1es) => begin
      prstr "S1Etyrec(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_labs1explst (pf | out, ls1es);
      prstr ")"
    end // end of [S1Etyrec]
  | S1Etyrec_ext (name, ls1es) => begin
      prstr "S1Etyrec_ext(";
      fprint1_string (pf | out, name);
      prstr "; ";
      fprint_labs1explst (pf | out, ls1es);
      prstr ")"
    end // end of [S1Etyrec]
  | S1Etytup (flat, s1es) => begin
      prstr "S1Etytup(";
      fprint1_int (pf | out, flat);
      prstr "; ";
      fprint_s1explst (pf | out, s1es);
      prstr ")"
    end // end of [S1Etytup]
  | S1Etytup2 (flat, s1es1, s1es2) => begin
      prstr "S1Etytup2(";
      fprint1_int (pf | out, flat);
      prstr "; ";
      fprint_s1explst (pf | out, s1es1);
      prstr "; ";
      fprint_s1explst (pf | out, s1es2);
      prstr ")"
    end // end of [S1Etytup2]
  | S1Euni (s1qs, s1e) => begin
      prstr "S1Euni(";
      fprint_s1qualst (pf | out, s1qs);
      prstr "; ";
      fprint_s1exp (pf | out, s1e);
      prstr ")"
    end // end of [S1Euni]
  | S1Eunion (s1e, ls1es) => begin
      prstr "S1Eunion(";
      fprint_s1exp (pf | out, s1e);
      prstr "; ";
      fprint_labs1explst (pf | out, ls1es);
      prstr ")"
    end // end of [S1Eunion]
end // end of [fprint_s1exp]

implement print_s1exp (s1e) = print_mac (fprint_s1exp, s1e)
implement prerr_s1exp (s1e) = prerr_mac (fprint_s1exp, s1e)

(* ****** ****** *)

implement
fprint_s1explst (pf | out, xs) =
  $Lst.fprintlst {s1exp} (pf | out, xs, ", ", fprint_s1exp)
// end of [fprint_s1explst]

implement print_s1explst (s1es) = print_mac (fprint_s1explst, s1es)
implement prerr_s1explst (s1es) = prerr_mac (fprint_s1explst, s1es)

(* ****** ****** *)

implement
fprint_s1expopt (pf | out, os1e) = begin
  case+ os1e of Some s1e => fprint_s1exp (pf | out, s1e) | None () => ()
end // end of [fprint_s1expopt]

implement
fprint_s1explstlst (pf | out, xss) =
  $Lst.fprintlst {s1explst} (pf | out, xss, ", ", fprint_s1explst)
// end of [fprint_s1explstlst]

implement
fprint_labs1explst
  {m} (pf | out, ls1es) = let
  fun aux (
    out: &FILE m, i: int, ls1es: labs1explst
  ) : void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ls1es of
    | LABS1EXPLSTcons (l, s1e, ls1es) => begin
        if i > 0 then prstr ", ";
        fprint_label (pf | out, l); prstr "=";
        fprint_s1exp (pf | out, s1e); aux (out, i + 1, ls1es)
      end // end of [LABS1EXPLSTcons]
    | LABS1EXPLSTnil () => () // end of [nil]
  end // end of [aux]
in
  aux (out, 0, ls1es)
end // end of [fprint_labs1explst]

(* ****** ****** *)

implement
fprint_tmps1explstlst
  {m} (pf | out, ts1ess0) = let
  fun aux (
    out: &FILE m, i: int, ts1ess: tmps1explstlst
  ) : void =
    case+ ts1ess of
    | TMPS1EXPLSTLSTcons (_(*loc*), s1es, ts1ess) => let
        val () = if i > 0 then fprint1_string (pf | out, "; ")
      in
        fprint_s1explst (pf | out, s1es); aux (out, i + 1, ts1ess)
      end // end of [TMPS1EXPLSTLSTcons]
    | TMPS1EXPLSTLSTnil () => ()
  // end of [aux]
in
  aux (out, 0, ts1ess0)
end // end of [fprint_s1explstlst]

(* ****** ****** *)

implement
fprint_s1rtext (pf | out, s1te) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1te.s1rtext_node of
  | S1TEsrt s1t => fprint_s1rt (pf | out, s1t)
  | S1TEsub (sym, s1te, s1es) => begin
      prstr "S1TEsub(";
      $Sym.fprint_symbol (pf | out, sym);
      prstr "; ";
      fprint_s1rtext (pf | out, s1te);
      prstr "; ";
      fprint_s1explst (pf | out, s1es);
      prstr ")"
    end // end of [S1TEsub]
end // end of [fprint_s1rtext]

(* ****** ****** *)

(* end of [ats_staexp1_print.dats] *)
