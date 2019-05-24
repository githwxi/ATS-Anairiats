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
// Time: October 2007

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Lab = "ats_label.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_staexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label
macdef fprint_stamp = $Stamp.fprint_stamp
macdef fprint_symbol = $Sym.fprint_symbol

(* ****** ****** *)

fun fprint_tyreckind {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, k: tyreckind): void =
  case+ k of
  | TYRECKINDbox _ => fprint1_string (pf | out, "box")
  | TYRECKINDflt0 _ => fprint1_string (pf | out, "flt")
  | TYRECKINDflt1 stamp => begin
      fprint1_string (pf | out, "flt(");
      fprint_stamp (pf | out, stamp);
      fprint1_string (pf | out, ")")
    end // end of [TYRECKINDflt1]
  | TYRECKINDflt_ext name => begin
      fprint1_string (pf | out, "flt(");
      fprint1_string (pf | out, name);
      fprint1_string (pf | out, ")")
    end // end of [TYRECKINDflt_ext]
// end of [fprint_tyreckind]

(* ****** ****** *)

fn fprint_s2rtdat {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2td: s2rtdat_t): void =
  fprint_symbol (pf | out, s2rtdat_get_sym s2td)
// end of [fprint_s2rtdat]

fn fprint_s2rtbas {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2tb: s2rtbas): void =
  case+ s2tb of
  | S2RTBASpre x => fprint_symbol (pf | out, x)
  | S2RTBASimp (x, _, _) => fprint_symbol (pf | out, x)
  | S2RTBASdef x => fprint_s2rtdat (pf | out, x)
// end of [fprint_s2rtbas]

(* ****** ****** *)

implement
fprint_s2item (pf | out, s2i) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2i of
  | S2ITEMcst _ => begin
      fprint1_string (pf | out, "S2ITEMcst(...)")
    end // end of [S2ITEMcst]
  | S2ITEMdatconptr d2c => begin
      prstr "S2ITEMdatconptr("; fprint_d2con (pf | out, d2c); prstr ")"
    end // end of [S2ITEMdatconptr]
  | S2ITEMdatcontyp d2c => begin
      prstr "S2ITEMdatcontyp("; fprint_d2con (pf | out, d2c); prstr ")"
    end // end of [S2ITEMdatcontyp]
  | S2ITEMe1xp e1xp => begin
      prstr "S2ITEMe1xp("; fprint_e1xp (pf | out, e1xp); prstr ")"
    end // end of [S2ITEMe1xp]
  | S2ITEMfil fil => begin
      prstr "S2ITEMfil(";
      $Fil.fprint_filename (pf | out, fil);
      prstr ")"
    end // end of [S2ITEMfil]
  | S2ITEMvar s2v => begin
      prstr "S2ITEMvar("; fprint_s2var (pf | out, s2v); prstr ")"
    end // end of [S2ITEMvar]
end (* end of [fprint_s2item] *)

implement
print_s2item (s2i) = print_mac (fprint_s2item, s2i)
implement
prerr_s2item (s2i) = prerr_mac (fprint_s2item, s2i)

(* ****** ****** *)

implement
fprint_s2rt (pf | out, s2t) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2t of
  | S2RTbas s2tb => fprint_s2rtbas (pf | out, s2tb)
  | S2RTfun (s2ts, s2t) => begin
      prstr "S2RTfun(";
      fprint_s2rtlst (pf | out, s2ts);
      prstr "; ";
      fprint_s2rt (pf | out, s2t);
      prstr ")"
    end // end of [S2RTfun]
  | S2RTtup s2ts => begin
      prstr "S2RTtup("; fprint_s2rtlst (pf | out, s2ts); prstr ")"
    end // end of [S2RTtup]
end (* end of [fprint_s2rt] *)

implement
print_s2rt (s2t) = print_mac (fprint_s2rt, s2t)
implement
prerr_s2rt (s2t) = prerr_mac (fprint_s2rt, s2t)

(* ****** ****** *)

implement
fprint_s2rtlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2rt)
// end of [fprint_s2rtlst]

implement
fprint_s2rtlstlst (pf | out, xss) =
  $Lst.fprintlst (pf | out, xss, "; ", fprint_s2rtlst)
// end of [fprint_s2rtlstlst]

(* ****** ****** *)

implement
fprint_s2rtext (pf | out, s2te) = begin
  case+ s2te of
  | S2TEsrt s2t => fprint_s2rt (pf | out, s2t)
  | S2TEsub (s2v, s2t, s2es) => begin
      fprint1_string (pf | out, "{");
      fprint_s2var (pf | out, s2v);
      fprint1_string (pf | out, ": ");
      fprint_s2rt (pf | out, s2t);
      fprint1_string (pf | out, " | ");
      fprint_s2explst (pf | out, s2es);
      fprint1_string (pf | out, "}")
    end // end of [S2TEsub]
(*
  | S2TElam (s2vs, s2te) => begin
      fprint1_string (pf | out, "S2TElam(");
      fprint_s2varlst (pf | out, s2vs);
      fprint1_string (pf | out, "; ");
      fprint_s2rtext (pf | out, s2te);
      fprint1_string (pf | out, ")")
    end // end of [S2TElam]
  | S2TEapp (s2te, s2es) => begin
      fprint1_string (pf | out, "S2TEapp(");
      fprint_s2rtext (pf | out, s2te);
      fprint1_string (pf | out, "; ");
      fprint_s2explst (pf | out, s2es);
      fprint1_string (pf | out, ")")
    end // end of [S2TEapp]
*)
end (* end of [fprint_s2rtext] *)

(* ****** ****** *)

implement
fprint_s2eff (pf | out, s2fe) = begin
  case+ s2fe of
  | S2EFFall () => begin
      fprint1_string (pf | out, "<all>")
    end
  | S2EFFnil () => begin
      fprint1_string (pf | out, "<nil>")
    end
  | S2EFFset (effs, s2es) => begin
      fprint1_string (pf | out, "<");
      $Eff.fprint_effset (pf | out, effs);
      fprint1_string (pf | out, ";");
      fprint_s2explst (pf | out, s2es);
      fprint1_string (pf | out, ">")
    end
end (* end of [fprint_s2eff] *)

implement
print_s2eff (s2fe) = print_mac (fprint_s2eff, s2fe)
implement
prerr_s2eff (s2fe) = prerr_mac (fprint_s2eff, s2fe)

(* ****** ****** *)

implement
fprint_s2exp (pf | out, s2e0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
      prstr "S2Eapp(";
      fprint_s2exp (pf | out, s2e_fun);
      prstr "; ";
      fprint_s2explst (pf | out, s2es_arg);
      prstr ")"
    end // end of [S2Eapp]
  | S2Echar c => begin
      prstr "S2Echar("; fprint1_char (pf | out, c); prstr ")"
    end // end of [S2Echar]
  | S2Eclo (knd, s2e) => begin
      prstr "S2Eclo(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Eclo]
  | S2Ecrypt (s2e) => begin
      prstr "S2Ecrypt("; fprint_s2exp (pf | out, s2e); prstr ")"
    end // end of [S2Ecrypt]
  | S2Ecst s2c => begin
      prstr "S2Ecst("; fprint_s2cst (pf | out, s2c); prstr ")"
    end // end of [S2Ecst]
  | S2Edatconptr (d2c, s2es) => begin
      prstr "S2Edatconptr(";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_s2explst (pf | out, s2es);
      prstr ")"
    end // end of [S2Edatconptr]
  | S2Edatcontyp (d2c, s2es) => begin
      prstr "S2Edatcontyp(";
      fprint_d2con (pf | out, d2c);
      prstr "; ";
      fprint_s2explst (pf | out, s2es);
      prstr ")"
    end // end of [S2Edatcontyp]
  | S2Eeff s2fe => begin
      prstr "S2Eeff("; fprint_s2eff (pf | out, s2fe); prstr ")"
    end // end of [S2Eeff]
  | S2Eeqeq (s2e1, s2e2) => begin
      prstr "S2Eeqeq(";
      fprint_s2exp (pf | out, s2e1);
      prstr ", ";
      fprint_s2exp (pf | out, s2e2);
      prstr ")"
    end // end of [S2Eeqeq]
  | S2Eexi (s2vs, s2ps, s2e) => begin
      prstr "S2Eexi(";
      fprint_s2varlst (pf | out, s2vs);
      prstr "; ";
      fprint_s2explst (pf | out, s2ps);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Eexi]
  | S2Eextype (name, arglst) => begin
      prstr "S2Eextype(";
      fprint1_string (pf | out, name);
      prstr "; ";
      fprint_s2explstlst (pf | out, arglst);
      prstr ")"
    end // end of [S2Eextype]
  | S2Efun (fc, lin, s2fe, npf, s2es, s2e) => begin
      prstr "S2Efun(";
      $Syn.fprint_funclo (pf | out, fc);
      prstr "; ";
      fprint1_int (pf | out, lin);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_s2explst (pf | out, s2es);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Efun]
  | S2Eint i(*int*) => begin
      prstr "S2Eint("; fprint1_int (pf | out, i); prstr ")"
    end // end of [S2Eint]
  | S2Eintinf i(*intinf*) => begin
      prstr "S2Eint(";
      $IntInf.fprint_intinf (pf | out, i);
      prstr ")"
    end // end of [S2Eintinf]
  | S2Elam (s2vs, s2e) => begin
      prstr "S2Elam(";
      fprint_s2varlst (pf | out, s2vs);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Elam]
  | S2Emetfn (_(*stamp*), s2es, s2e) => begin
      prstr "S2Emetfn(";
      fprint_s2explst (pf | out, s2es);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Emetfn]
  | S2Emetlt (s2es1, s2es2) => begin
      prstr "S2Emetlt(";
      fprint_s2explst (pf | out, s2es1);
      prstr ", ";
      fprint_s2explst (pf | out, s2es2);
      prstr ")"
    end // end of [S2Emetlt]
(*
// HX-2010-12-04: inadequate design
  | S2Enamed (name, s2e) => begin
      prstr "S2Enamed(";
      $Sym.fprint_symbol (pf | out, name);
      prstr ", ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Enamed]
*)
  | S2Eout s2e => begin
      prstr "S2Eout("; fprint_s2exp (pf | out, s2e); prstr ")"
    end // end of [S2Eout]
  | S2Eproj (s2e, s2l) => begin
      prstr "S2Eproj(";
      fprint_s2exp (pf | out, s2e);
      prstr "; ";
      fprint_s2lab (pf | out, s2l);
      prstr ")"
    end // end of [S2Eproj]
  | S2Eread (s2e_v, s2e_vt) => begin
      prstr "S2Eread(";
      fprint_s2exp (pf | out, s2e_v);
      prstr ", ";
      fprint_s2exp (pf | out, s2e_vt);
      prstr ")"
    end // end of [S2Eread]
  | S2Erefarg (refval, s2e) => begin
      prstr "S2Erefarg(";
      fprint1_int (pf | out, refval);
      prstr ", ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Erefarg]
  | S2Esel (s2e, i) => begin
      prstr "S2Esel(";
      fprint_s2exp (pf | out, s2e);
      prstr "; ";
      fprint1_int (pf | out, i);
      prstr ")"
    end // end of [S2Esel]
  | S2Esize (s2ze) => begin
      prstr "S2Esize("; fprint_s2zexp (pf | out, s2ze); prstr ")"
    end // end of [S2Esize]
  | S2Esizeof (s2e) => begin
      prstr "S2Esizeof("; fprint_s2exp (pf | out, s2e); prstr ")"
    end // end of [S2Esizeof]
  | S2Etop (knd, s2e) => begin
      prstr "S2Etop(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Etop]
  | S2Etup s2es => begin
      prstr "S2Etup(";
      fprint_s2explst (pf | out, s2es);
      prstr ")"
    end // end of [S2Etup]
  | S2Etyarr (s2e_elt, s2ess_dim) => begin
      prstr "S2Etyarr(";
      fprint_s2exp (pf | out, s2e_elt);
      prstr "; ";
      fprint_s2explstlst (pf | out, s2ess_dim);
      prstr ")"
    end // end of [S2Etyarr]
  | S2Etyleq (knd, s2e1, s2e2) => begin
      prstr "S2Etyleq(";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_s2exp (pf | out, s2e1);
      prstr ", ";
      fprint_s2exp (pf | out, s2e2);
      prstr ")"
    end // end of [S2Etyleq]
  | S2Etylst s2es => begin
      prstr "S2Etylst("; fprint_s2explst (pf | out, s2es); prstr ")"
    end // end of [S2Etylst]
  | S2Etyrec (k, npf, ls2es) => begin
      prstr "S2Etyrec(";
      fprint_tyreckind (pf | out, k);
      prstr "; ";
      fprint1_int (pf | out, npf);
      prstr "; ";
      fprint_labs2explst (pf | out, ls2es);
      prstr ")"
    end // end of [S2Etyrec]
  | S2Euni (s2vs, s2ps, s2e) => begin
      prstr "S2Euni(";
      fprint_s2varlst (pf | out, s2vs);
      prstr "; ";
      fprint_s2explst (pf | out, s2ps);
      prstr "; ";
      fprint_s2exp (pf | out, s2e);
      prstr ")"
    end // end of [S2Euni]
  | S2Eunion (stamp, s2e_ind, ls2es) => begin
      prstr "S2Eunion(";
      fprint_stamp (pf | out, stamp);
      prstr "; ";
      fprint_s2exp (pf | out, s2e_ind);
      prstr "; ";
      fprint_labs2explst (pf | out, ls2es);
      prstr ")"
    end // end of [S2Eunion]
  | S2Evar s2v => begin
      prstr "S2Evar("; fprint_s2var (pf | out, s2v); prstr ")"
    end // end of [S2Evar]
  | S2EVar s2V => let
      val () = begin
        prstr "S2EVar("; fprint_s2Var (pf | out, s2V); prstr ")"
      end // end of [val]
(*
      val () = let
        val os2e = s2Var_link_get s2V in case+ os2e of
        | Some s2e => begin
            prstr "["); fprint_s2exp (pf | out, s2e); prstr "]")
          end (* end of [Some] *)
        | None () => ()
      end // end of [val]
*)
    in
      // empty
    end // end of [S2EVar]
  | S2Evararg s2e => begin
      prstr "S2Evararg("; fprint_s2exp (pf | out, s2e); prstr ")"
    end // end of [S2Evararg]
  | S2Ewth (s2e_res, wths2es) => begin
      prstr "S2Ewth(";
      fprint_s2exp (pf | out, s2e_res);
      prstr "; ";
      fprint_wths2explst (pf | out, wths2es);
      prstr ")"
    end // end of [S2Ewth]
(*
  | _ => exit (1) where {
      val () = prerr "INTERNAL ERROR (ats_staexp2_print): "
      val () = prerr "[fprint_s2exp]: unsupported static expression"
      val () = prerr_newline ()
    } (* end of [_] *)
*)
end (* end of [fprint_s2exp] *)

implement
print_s2exp (s2e) = print_mac (fprint_s2exp, s2e)
implement
prerr_s2exp (s2e) = prerr_mac (fprint_s2exp, s2e)

(* ****** ****** *)

implement
fprint_s2explst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2exp)
(* end of [fprint_s2explst] *)

implement
print_s2explst (s2es) = print_mac (fprint_s2explst, s2es)
implement
prerr_s2explst (s2es) = prerr_mac (fprint_s2explst, s2es)

(* ****** ****** *)

implement
fprint_s2explstlst (pf | out, xss) =
  $Lst.fprintlst (pf | out, xss, "; ", fprint_s2explst)
(* end of [fprint_s2explstlst] *)

(* ****** ****** *)

implement
fprint_s2expopt
  {m} (pf | out, os2e) =
  case+ os2e of
  | Some s2e => begin
      fprint1_string (pf | out, "Some(");
      fprint_s2exp (pf | out, s2e);
      fprint1_string (pf | out, ")")
    end // end of [Some]
  | None () => begin
      fprint1_string (pf | out, "None()")
    end // end of [None]
(* end of [fprint_s2expopt] *)

(* ****** ****** *)

implement
fprint_labs2explst
  {m} (pf | out, ls2es) = let
  fun aux (
    out: &FILE m, ls2es: labs2explst, i: int
  ) : void =
    case+ ls2es of
    | LABS2EXPLSTcons (l, s2e, ls2es) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_label (pf | out, l)
        val () = fprint1_string (pf | out, "=")
        val () = fprint_s2exp (pf | out, s2e)
      in
        aux (out, ls2es, i+1)
      end // end of [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => ()
  // end of [aux]
in
  aux (out, ls2es, 0)
end (* end of [fprint_labs2explst] *)

implement
print_labs2explst (ls2es) = print_mac (fprint_labs2explst, ls2es)
implement
prerr_labs2explst (ls2es) = prerr_mac (fprint_labs2explst, ls2es)

(* ****** ****** *)

implement
fprint_tmps2explstlst
  {m} (pf | out, ts2ess) =
  aux (out, ts2ess, 0) where {
  fun aux (
      out: &FILE m
    , ts2ess: tmps2explstlst
    , i: int
    ) : void =
    case+ ts2ess of
    | TMPS2EXPLSTLSTcons
        (loc, s2es, ts2ess) => let
        val () = if i > 0 then
          fprint1_string (pf | out, "; ")
        val () = fprint_s2explst (pf | out, s2es)
      in
         aux (out, ts2ess, i+1)
      end // end of [TMPS2EXPLSTLSTcons]
    | TMPS2EXPLSTLSTnil () => ()
  // end of [aux]
} // end of [fprint_s2explstlst]

implement print_tmps2explstlst
  (ts2ess) = print_mac (fprint_tmps2explstlst, ts2ess)
implement prerr_tmps2explstlst
  (ts2ess) = prerr_mac (fprint_tmps2explstlst, ts2ess)

(* ****** ****** *)

implement
fprint_wths2explst {m}
  (pf | out, wths2es) = aux (out, wths2es, 0) where {
  fun aux (
      out: &FILE m, wths2es: wths2explst, i: int
    ) : void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ wths2es of
    | WTHS2EXPLSTcons_some
        (refval, s2e, wths2es) =>
        aux (out, wths2es, i+1) where {
        val () = if i > 0 then prstr "; "
        val () = begin
          prstr "Some("; fprint_s2exp (pf | out, s2e); prstr ")"
        end // end of [val]
      } // end of [WTHS2EXPLSTcons_some]
    | WTHS2EXPLSTcons_none
        (wths2es) => aux (out, wths2es, i+1) where {
        val () = if i > 0 then prstr "; "
        val () = fprint1_string (pf | out, "None()")
      } // end of [STHS2EXPLSTcons_none]
    | WTHS2EXPLSTnil () => ()
  end // end of [aux]
} (* end of [fprint_wths2explst] *)

implement
print_wths2explst
  (wths2es) = print_mac (fprint_wths2explst, wths2es)
// end of [print_wths2explst]

implement
prerr_wths2explst
  (wths2es) = prerr_mac (fprint_wths2explst, wths2es)
// end of [prerr_wths2explst]

(* ****** ****** *)

implement
fprint_s2lab (pf | out, s2l) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2l of
  | S2LAB0lab l => fprint_label (pf | out, l)
  | S2LAB0ind s2ess => begin
      prstr "["; fprint_s2explstlst (pf | out, s2ess); prstr "]"
    end // end of [S2LAB0ind]
  | S2LAB1lab (l, _) => fprint_label (pf | out, l)
  | S2LAB1ind (s2ess, _) => begin
      prstr "["; fprint_s2explstlst (pf | out, s2ess); prstr "]"
    end // end of [S2LAB1ind]
end (* end of [fprint_s2lab] *)

implement
print_s2lab (s2l) = print_mac (fprint_s2lab, s2l)
implement
prerr_s2lab (s2l) = prerr_mac (fprint_s2lab, s2l)

(* ****** ****** *)

implement
fprint_s2lablst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2lab)
(* end of [fprint_s2lablst] *)

implement
print_s2lablst (s2ls) = print_mac (fprint_s2lablst, s2ls)
implement
prerr_s2lablst (s2ls) = prerr_mac (fprint_s2lablst, s2ls)

(* ****** ****** *)

implement
fprint_s2kexp (pf | out, s2ke) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2ke of
  | S2KEany () => begin
      fprint1_string (pf | out, "S2KEany()")
    end // end of [S2KEany]
  | S2KEapp(s2ke, s2kes) => begin
      prstr "S2KEapp(";
      fprint_s2kexp (pf | out, s2ke);
      prstr "; ";
      fprint_s2kexplst (pf | out, s2kes);
      prstr ")"
    end // end of [S2KEapp]
  | S2KEcst s2c => begin
      fprint_s2cst (pf | out, s2c)
    end // end of [S2KEcst]
  | S2KEfun (fc, s2kes, s2ke) => begin
      prstr "S2KEfun(";
      $Syn.fprint_funclo (pf | out, fc);
      prstr "; ";
      fprint_s2kexplst (pf | out, s2kes);
      prstr "; ";
      fprint_s2kexp (pf | out, s2ke);
      prstr ")"
    end // end of [S2KEfun]
  | S2KEtyarr () => begin
      fprint1_string (pf | out, "S2KEtyarr()")
    end // end of [S2KEtyarr]
  | S2KEtyrec (recknd, ls2kes) => begin
      prstr "S2KEtyrec(";
      fprint_labs2kexplst (pf | out, ls2kes);
      prstr ")"
    end // end of [S2KEtyrec]
  | S2KEunion (s2kes) => begin
      prstr "S2KEunion("; fprint_s2kexplst (pf | out, s2kes); prstr ")"
    end // end of [S2KEunion]
  | S2KEvar s2v => begin
      fprint_s2var (pf | out, s2v)
    end // end of [S2KEvar]
end // end of [fprint_sk2exp]

implement
print_s2kexp (s2ke) = print_mac (fprint_s2kexp, s2ke)
implement
prerr_s2kexp (s2ke) = prerr_mac (fprint_s2kexp, s2ke)

(* ****** ****** *)

implement
fprint_s2kexplst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2kexp)
// end of [fprint_s2kexplst]

(* ****** ****** *)

implement
fprint_labs2kexplst
  {m} (pf | out, ls2kes) = let
  fun aux (
      out: &FILE m
    , ls2kes: labs2kexplst
    , i: int
    ) : void = let
    macdef prstr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ls2kes of
    | LABS2KEXPLSTcons (l, s2ke, ls2kes) => let
        val () = if (i > 0) then prstr ", "
        val () = (fprint_label (pf | out, l); prstr "=")
        val () = fprint_s2kexp (pf | out, s2ke)
      in
        aux (out, ls2kes, i+1)
      end // end of [LABS2KEXPLSTcons]
    | LABS2KEXPLSTnil () => () // end of [LABS2KEXPLSTnil]
  end // end of [aux]
in
  aux (out, ls2kes, 0)
end (* end of [fprint_labs2kexplst] *)

(* ****** ****** *)

implement
fprint_s2zexp (pf | out, s2ze) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2ze of
  | S2ZEapp (s2ze_fun, s2zes_arg) => begin
      prstr "S2ZEapp(";
      fprint_s2zexp (pf | out, s2ze_fun);
      prstr "; ";
      fprint_s2zexplst (pf | out, s2zes_arg);
      prstr ")"
    end // end of [S2ZEapp]
  | S2ZEbot () => prstr "S2ZEbot()"
  | S2ZEcst s2c => begin
      prstr "S2ZEcst("; fprint_s2cst (pf | out, s2c); prstr ")"
    end // end of [S2ZEcst]
  | S2ZEextype name => begin
      prstr "S2ZEextype("; fprint1_string (pf | out, name); prstr ")"
    end // end of [S2ZEextype]
(*
  | S2ZEout s2ze => begin
      prstr "S2ZEout(");
      fprint_s2zexp (pf | out, s2ze);
      prstr ")")
    end // end of [S2ZEout]
*)
  | S2ZEptr () => prstr "S2ZEptr()"
  | S2ZEtyarr (s2ze, s2ess_dim) => begin
      prstr "S2ZEtyarr(";
      fprint_s2zexp (pf | out, s2ze);
      prstr "; ";
      fprint_s2explstlst (pf | out, s2ess_dim);
      prstr ")"
    end // end of [S2ZEtyarr]
  | S2ZEtyrec (_(*knd*), ls2zes) => begin
      prstr "S2ZEtyrec(";
      fprint_labs2zexplst (pf | out, ls2zes);
      prstr ")"
    end // end of [S2ZEtyrec]
  | S2ZEunion (_(*stamp*), ls2zes) => begin
      prstr "S2ZEunion(";
      fprint_labs2zexplst (pf | out, ls2zes);
      prstr ")"
    end // end of [S2ZEunion]
  | S2ZEvar s2v => begin
      prstr "S2ZEvar("; fprint_s2var (pf | out, s2v); prstr ")"
    end // end of [S2ZEvar]
end (* end of [fprint_s2zexp] *)

implement
print_s2zexp (s2ze) = print_mac (fprint_s2zexp, s2ze)

implement
prerr_s2zexp (s2ze) = prerr_mac (fprint_s2zexp, s2ze)

(* ****** ****** *)

implement
fprint_s2zexplst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2zexp)
(* end of [fprint_s2zexplst] *)

(* ****** ****** *)

implement
fprint_labs2zexplst
  {m} (pf | out, ls2zes) = let
  fun aux (
    out: &FILE m, ls2zes: labs2zexplst, i: int
  ) : void =
    case+ ls2zes of
    | LABS2ZEXPLSTcons
        (l, s2ze, ls2zes) => aux (out, ls2zes, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = (fprint_label (pf | out, l); fprint1_string (pf | out, "="))
        val () = fprint_s2zexp (pf | out, s2ze)
      } // end of [LABS2ZEXPLSTcons]
    | LABS2ZEXPLSTnil () => () // end of [LABS2ZEXPLSTnil]
  // end of [aux]
in
  aux (out, ls2zes, 0)
end (* end of [fprint_labs2zexplst] *)

(* ****** ****** *)

implement
fprint_s2exparg (pf | out, s2a) =
  case+ s2a.s2exparg_node of
  | S2EXPARGone() => fprint1_string (pf | out, "..")
  | S2EXPARGall() => fprint1_string (pf | out, "...")
  | S2EXPARGseq s2es => fprint_s2explst (pf | out, s2es)
// end of [fprint_s2exparg]

(* ****** ****** *)

implement
fprint_s2exparglst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2exparg)
(* end of [fprint_s2exparglst] *)

implement
print_s2exparglst (s2as) = print_mac (fprint_s2exparglst, s2as)
implement
prerr_s2exparglst (s2as) = prerr_mac (fprint_s2exparglst, s2as)

(* ****** ****** *)

implement
fprint_s2qua
  (pf | out, s2q) = begin
  fprint_string (pf | out, "(");
  fprint_s2varlst (pf | out, s2q.0);
  fprint_string (pf | out, " | ");
  fprint_s2explst (pf | out, s2q.1);
  fprint_string (pf | out, ")");
end // end of [fprint_s2qua]

(* ****** ****** *)

implement
fprint_s2qualst
  {m} (pf | out, s2qs) = let
  fun aux (
    out: &FILE m, i: int, s2qs: s2qualst
  ) : void =
    case+ s2qs of
    | cons (s2q, s2qs) => let
        val () = if i > 0 then
          fprint1_string (pf | out, ", ")
        val () = fprint_s2qua (pf | out, s2q)
      in
        aux (out, i+1, s2qs)
      end // end of [cons]
    | nil () => () // end of [nil]
  // end of [aux]
in
  aux (out, 0, s2qs)
end // end of [fprint_s2qualst]

implement
print_s2qualst (s2qs) = print_mac (fprint_s2qualst, s2qs)
implement
prerr_s2qualst (s2qs) = prerr_mac (fprint_s2qualst, s2qs)

(* ****** ****** *)

(* end of [ats_staexp2_print.dats] *)
