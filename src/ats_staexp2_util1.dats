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

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
#include "ats_intinf.cats"  /* only needed for [ATS/Geizella] */
%} // end [%{^]

(* ****** ****** *)

staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Lst = "ats_list.sats"
staload Loc = "ats_location.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

overload = with $Lab.eq_label_label
overload = with $Sym.eq_symbol_symbol
overload prerr with $Loc.prerr_location
overload prerr with $Sym.prerr_symbol

(* ****** ****** *)

fn prerr_loc_error2 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(2)")
// end of [prerr_loc_error2]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_staexp2_util1)"
fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_staexp2_util1)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

extern
fun lte_s2rtbas_s2rtbas (s2tb1: s2rtbas, s2tb2: s2rtbas): bool
overload <= with lte_s2rtbas_s2rtbas

implement
lte_s2rtbas_s2rtbas (s2tb1, s2tb2) = begin
  case+ (s2tb1, s2tb2) of
  | (S2RTBASpre id1, S2RTBASpre id2) => (id1 = id2)
  | (S2RTBASimp (id1, prf1, lin1), S2RTBASimp (id2, prf2, lin2)) =>
    if prf1 <= prf2 then lin1 <= lin2 else false
  | (S2RTBASdef s2td1, S2RTBASdef s2td2) => (s2td1 = s2td2)
  | (_, _) => false
end // end of [lte_s2rtbas_s2rtbas]

(* ****** ****** *)

implement
lte_s2rt_s2rt (s2t1, s2t2) = begin
  case+ (s2t1, s2t2) of
  | (S2RTbas s2tb1, S2RTbas s2tb2) => s2tb1 <= s2tb2
  | (S2RTfun (s2ts1, s2t1), S2RTfun (s2ts2, s2t2)) =>
    if s2ts2 <= s2ts1 then s2t1 <= s2t2 else false
  | (S2RTtup s2ts1, S2RTtup s2ts2) => s2ts1 <= s2ts2
  | (_, _) => false
end // end of [lte_s2rt_s2rt]

implement
lte_s2rtlst_s2rtlst (s2ts1, s2ts2) = begin
 case+ (s2ts1, s2ts2) of
 | (s2t1 :: s2ts1, s2t2 :: s2ts2) =>
   if s2t1 <= s2t2 then s2ts1 <= s2ts2 else false
 | (list_nil (), list_nil ()) => true
 | (_, _) => false
end // end of [lte_s2rtlst_s2rtlst]

(* ****** ****** *)

implement
s2rt_is_cls (s2t) = begin case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASpre id => id = $Sym.symbol_CLS | _ => false
    end // end of [S2RTbas]
  | _ => false
end // end of [s2rt_is_int]

implement
s2rt_is_dat (s2t) = begin case+ s2t of
  | S2RTbas s2tb => (case+ s2tb of S2RTBASdef _ => true | _ => false)
  | _ => false // end of [S2RTbas]
end // end of [s2rt_is_dat]

implement
s2rt_is_int (s2t) = begin case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASpre id => id = $Sym.symbol_INT | _ => false
    end // end of [S2RTbas]
  | _ => false
end // end of [s2rt_is_int]

(* ****** ****** *)

implement
s2rt_is_fun (s2t) = case+ s2t of S2RTfun _ => true | _ => false

(* ****** ****** *)

implement
s2rt_is_prop (s2t) = begin
  case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_PROP | _ => false
    end
  | _ => false
end // end of [s2rt_is_prop]

implement
s2rt_is_type (s2t) = begin
  case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_TYPE | _ => false
    end
  | _ => false
end // end of [s2rt_is_type]

implement
s2rt_is_t0ype (s2t) = begin
  case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_T0YPE | _ => false
    end // end of [S2RTbas]
  | _ => false
end // end of [s2rt_is_t0ype]

implement
s2rt_is_view (s2t) = begin
  case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_VIEW | _ => false
    end // end of [S2RTbas]
  | _ => false
end // end of [s2rt_is_view]

implement
s2rt_is_viewtype (s2t) = begin
  case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_VIEWTYPE | _ => false
    end // end of [S2RTbas]
  | _ => false
end // end of [s2rt_is_viewtype]

implement
s2rt_is_viewtype_fun (s2t) = begin
  case+ s2t of
  | S2RTfun (_, s2t) => s2rt_is_viewtype_fun s2t | _ => s2rt_is_viewtype s2t
end // end of [s2rt_is_viewtype_fun]

implement
s2rt_is_viewt0ype (s2t) = begin
  case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_VIEWT0YPE | _ => false
    end // end of [S2RTbas]
  | _ => false
end // end of [s2rt_is_viewt0ype]

(* ****** ****** *)

implement
s2rt_is_types (s2t) = case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, _) => id = $Sym.symbol_TYPES | _ => false
    end // end of [S2RTbas]
  | _ => false
// end of [s2rt_is_types]

(* ****** ****** *)

implement
s2rt_is_linear (s2t) = case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, _, lin) => (lin > 0) | _ => false
    end // end of [S2RTbas]
  | _ => false
// end of [s2rt_is_linear]

implement
s2rt_is_linear_fun (s2t) = case+ s2t of
  | S2RTfun (_, s2t) => s2rt_is_linear_fun s2t | _ => s2rt_is_linear s2t
// end of [s2rt_is_linear]

#define PROOF_LEVEL 2

implement
s2rt_is_proof (s2t) = case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, prf, _) => prf >= PROOF_LEVEL | _ => false
    end // end of [S2RTbas]
  | _ => false
// end of [s2rt_is_proof]

implement
s2rt_is_proof_fun (s2t) = case+ s2t of
  | S2RTfun (_, s2t) => s2rt_is_proof_fun s2t | _ => s2rt_is_proof s2t
// end of [s2rt_is_proof_fun]

implement
s2rt_is_program (s2t) = case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, prf, _) => prf < PROOF_LEVEL | _ => false
    end // end of [S2RTbas]
  | _ => false
// end of [s2rt_is_program]

implement
s2rt_is_program_fun (s2t) = case+ s2t of
  | S2RTfun (_, s2t) => s2rt_is_program_fun s2t | _ => s2rt_is_program s2t
// end of [s2rt_is_program_fun]

implement
s2rt_is_impredicative (s2t) = case+ s2t of
  | S2RTbas s2tb => begin
      case+ s2tb of S2RTBASimp _ => true | _ => false
    end // end of [S2RTbas]
  | _ => false
// end of [s2rt_is_impredicative]

implement
s2rt_is_impredicative_fun (s2t) = case+ s2t of
  | S2RTfun (_, s2t) => s2rt_is_impredicative_fun s2t
  | _ => s2rt_is_impredicative s2t
// end of [s2rt_is_impredicative_fun]

implement
s2rt_is_boxed (s2t) = case+ s2t of
  | S2RTbas s2tb => begin case+ s2tb of
    | S2RTBASimp (id, prf, _) => (prf = 0) | _ => false
    end // end of [S2RTbas]
  | _ => false
// end of [s2rt_is_boxed]

implement
s2rt_is_boxed_fun (s2t) = case+ s2t of
  | S2RTfun (_, s2t) => s2rt_is_boxed_fun s2t | _ => s2rt_is_boxed s2t
// end of [s2rt_is_boxed_fun]

(* ****** ****** *)

implement
s2rt_base_fun (s2t) = case+ s2t of
  | S2RTfun (_, s2t) => s2rt_base_fun s2t | _ => s2t
// end of [s2rt_base_fun]

implement
s2rt_datakind
  (datknd) = case+ datknd of
  | $Syn.DATAKINDprop () => s2rt_prop
  | $Syn.DATAKINDtype () => s2rt_type
  | $Syn.DATAKINDview () => s2rt_view
  | $Syn.DATAKINDviewtype () => s2rt_viewtype
// end of [s2rt_datakind]

implement
s2rt_readize (s2t) =
  if s2rt_is_proof s2t then s2rt_prop else begin
    if s2rt_is_boxed s2t then s2rt_type else s2rt_t0ype
  end
// end of [s2rt_readize]

(* ****** ****** *)

#define CLO 0; #define CLOPTR 1; #define CLOREF ~1

implement
s2rt_prf_lin_fc
  (loc0, isprf, islin, fc) = begin
  if isprf then begin
    (if islin then s2rt_view else s2rt_prop)
  end else begin case+ islin of
    | _ when islin => begin case+ fc of
      | $Syn.FUNCLOclo (knd) => begin case+ knd of
        | CLO => s2rt_viewt0ype
        | CLOPTR => s2rt_viewtype
        | _ (*CLOREF*) => begin
            prerr_loc_error2 loc0;
            prerr ": a closure reference cannot be linear.";
            prerr_newline ();
            $Err.abort {s2rt} ()
          end // end of [_]
        end (* end of [FUNCLOclo] *)
      | $Syn.FUNCLOfun () => s2rt_viewtype
      end // end of [_ when islin]
    | _ => begin case+ fc of
      | $Syn.FUNCLOclo (knd) => begin case+ knd of
        | CLO => s2rt_t0ype
        | CLOPTR => s2rt_viewtype (*ptr*)
        | _ (*CLOREF*) => s2rt_type (*ref*)
        end // end of [FUNCLOclo]
      | $Syn.FUNCLOfun () => s2rt_type
      end // end of [_]
  end (* end of [if] *)
end // end of [s2rt_prf_lin_fc]

(* ****** ****** *)

implement
s2eff_union_eff
  (s2fe, eff) = case+ s2fe of
  | S2EFFall () => S2EFFall ()
  | S2EFFnil () => S2EFFset
      ($Eff.effset_add ($Eff.effset_nil, eff), list_nil ())
    // end of [S2EFFnil]
  | S2EFFset (efs, s2es) => begin
      S2EFFset ($Eff.effset_add (efs, eff), s2es)
    end // end of [S2EFFset]
// end of [s2eff_union_eff]

implement
s2eff_union_s2eff (s2fe1, s2fe2) =
  case+ (s2fe1, s2fe2) of
  | (S2EFFall (), _) => S2EFFall ()
  | (_, S2EFFall ()) => S2EFFall ()
  | (S2EFFnil (), _) => s2fe2
  | (_, S2EFFnil ()) => s2fe1
  | (S2EFFset (efs1, s2es1), S2EFFset (efs2, s2es2)) => let
      val efs = $Eff.effset_union (efs1, efs2)
      val s2es = $Lst.list_append (s2es1, s2es2)
    in
      S2EFFset (efs, s2es)
    end // end of [S2EFFset, S2EFFset]
// end of [s2eff_union_s2eff]

// ------------------------------------------------

fun s2exp_contain_eff
  (s2e0: s2exp, eff: $Syn.effect_t): bool = let
  val s2e0 = s2exp_whnf s2e0
in
  case+ s2e0.s2exp_node of
  | S2Eeff s2fe => s2eff_contain_eff (s2fe, eff)
  | S2EVar s2V => begin
      prerr (s2Var_get_loc s2V);
      prerr ": INTERNAL WARNING (ats_staexp2_util1)";
      prerr ": s2exp_contain_eff: s2e0 = "; prerr s2e0; prerr_newline ();
      false
    end // end of [S2EVar]
  | _ => false
end // end of [s2exp_contain_eff]

and s2explst_contain_eff (
  s2es: s2explst, eff: $Syn.effect_t
) : bool = begin case+ s2es of
  | list_cons (s2e, s2es) => begin
      if s2exp_contain_eff (s2e, eff) then
        true else s2explst_contain_eff (s2es, eff)
      // end of [if]
    end // end of [list_cons]
  | list_nil () => false
end // end of [s2explst_contain_eff]

implement
s2eff_contain_eff (s2fe, eff) = let
(*
  val () = begin
    print "s2eff_contain_eff: s2fe = "; print s2fe; print_newline ();
    print "s2eff_contain_eff: eff = "; print eff; print_newline ();
  end // end of [val]
*)
in
  case+ s2fe of
  | S2EFFall () => true
  | S2EFFnil () => false
  | S2EFFset (efs, s2es) => begin
      if $Eff.effset_contain (efs, eff) then true
      else s2explst_contain_eff (s2es, eff)
    end
end // end of [s2eff_contain_eff]

implement
s2eff_contain_effset (s2fe, efs) = let
  fun aux (
    xs: $Syn.effectlst
  ) :<cloptr1> bool = case+ xs of
    | list_cons (x, xs) => (
        if $Eff.effset_contain (efs, x) then
          if s2eff_contain_eff (s2fe, x) then aux (xs) else false
        else aux (xs)
      ) // end of [list_cons]
    | list_nil () => true
  // end of [aux]
in
  aux ($Eff.effectlst_all)
end // end of [s2eff_contain_effset]

// ------------------------------------------------

fun s2exp_contain_effvar
  (s2e: s2exp, s2v0: s2var_t): bool = let
  val s2e = s2exp_whnf s2e
in
  case+ s2e.s2exp_node of
  | S2Eeff s2fe => s2eff_contain_effvar (s2fe, s2v0)
  | S2Evar s2v => eq_s2var_s2var (s2v0, s2v)
  | S2EVar s2V => begin
      prerr (s2Var_get_loc s2V);
      prerr ": INTERNAL WARNING (ats_staexp2_util1)";
      prerr ": s2exp_contain_effvar: s2e = "; prerr s2e; prerr_newline ();
      false
    end // end of [S2EVar]
  | _ => false
end // end of [s2exp_contain_effvar]

and s2explst_contain_effvar (
  s2es0: s2explst, s2v0: s2var_t
) : bool = begin
  case+ s2es0 of
  | list_cons (s2e, s2es) => begin
      if s2exp_contain_effvar (s2e, s2v0) then true
      else s2explst_contain_effvar (s2es, s2v0)
    end // end of [list_cons]
  | list_nil () => false // end of [list_nil]
end // end of [s2explist_contain_effvar]

implement
s2eff_contain_effvar
  (s2fe, s2v) = case+ s2fe of
  | S2EFFall () => true
  | S2EFFnil () => false
  | S2EFFset (efs, s2es) => s2explst_contain_effvar (s2es, s2v)
// end of [s2eff_contain_effvar]

// ------------------------------------------------

fun s2eff_contain_s2exp
  (s2fe1: s2eff, s2e2: s2exp): bool = let
  val s2e2 = s2exp_whnf s2e2
in
  case+ s2e2.s2exp_node of
  | S2Eeff s2fe2 => s2eff_contain_s2eff (s2fe1, s2fe2)
  | S2Evar s2v2 => s2eff_contain_effvar (s2fe1, s2v2)
  | S2EVar s2V2 => begin
      prerr (s2Var_get_loc s2V2);
      prerr ": INTERNAL WARNING";
      prerr ": s2eff_contain_s2exp: s2e2 = "; prerr s2e2; prerr_newline ();
      false
    end // end of [S2EVar]
  | _ => false
end // end of [s2eff_contain_s2exp]

and s2eff_contain_s2explst (
  s2fe: s2eff, s2es: s2explst
) : bool = begin
  case+ s2es of
  | list_cons (s2e, s2es) => begin
      if s2eff_contain_s2exp (s2fe, s2e) then s2eff_contain_s2explst (s2fe, s2es)
      else false
    end // end of [list_cons]
  | list_nil () => true
end // end of [s2eff_contain_s2explst]

implement
s2eff_contain_s2eff
  (s2fe1, s2fe2) = case+ s2fe1 of
  | S2EFFall () => true
  | _ => begin case+ s2fe2 of
    | S2EFFall () => s2eff_contain_effset (s2fe1, $Eff.effset_all)
    | S2EFFnil () => true
    | S2EFFset (efs, s2es) => begin
        if s2eff_contain_effset (s2fe1, efs) then
          s2eff_contain_s2explst (s2fe1, s2es)
        else false
      end // end of [S2EFFset]
    end // end of [_]
// end of [s2eff_contain_s2eff]

(* ****** ****** *)

implement
s2lab_syneq (s2l1, s2l2) = begin
  case+ (s2l1, s2l2) of
  | (S2LAB0lab l1, S2LAB0lab l2) => l1 = l2
  | (S2LAB1lab (l1, _), S2LAB1lab (l2, _)) => l1 = l2
  | (S2LAB0ind s2ess1, S2LAB0ind s2ess2) => begin
      s2explstlst_syneq (s2ess1, s2ess2)
    end
  | (S2LAB1ind (s2ess1, _), S2LAB1ind (s2ess2, _)) => begin
      s2explstlst_syneq (s2ess1, s2ess2)
    end // end of [S2LAB1ind, S2LAB1ind]
  | (_,  _) => false
end // end of [s2lab_syneq]

//
// the function is used in
// [ats_trans3_assgn, ats_trans3_deref, ats_trans3_view]
//
implement
s2lablst_trim_s2lablst_s2lablst
  (s2ls0_ft, s2ls_ft, s2ls_bk) = let
(*
  val () = begin
    print "s2lablst_trim_s2lablst_s2lablst: s2ls0_ft = "; print_s2lablst s2ls0_ft; print_newline ();
    print "s2lablst_trim_s2lablst_s2lablst: s2ls_ft = "; print_s2lablst s2ls_ft; print_newline ();
    print "s2lablst_trim_s2lablst_s2lablst: s2ls_bk = "; print_s2lablst s2ls_bk; print_newline ();
  end // end of [val]
*)
  fun aux (
      s2ls1: s2lablst, s2ls2: s2lablst
    ) : s2lablst = begin
    case+ s2ls1 of
    | list_cons (_, s2ls1) => begin case+ s2ls2 of
      | list_cons (_, s2ls2) => aux (s2ls1, s2ls2)
      | list_nil () => begin
          prerr_interror (); prerr ": s2lablst_trim"; prerr_newline ();
          $Err.abort {s2lablst} ()
        end // end of [_]
      end (* end of [list_cons] *)
    | list_nil () => s2ls2
  end // end of [aux]
in
  case+ s2ls0_ft of
  | list_cons (_, s2ls0_ft1) => begin case+ s2ls_ft of
    | list_cons (_, s2ls_ft) => begin
        s2lablst_trim_s2lablst_s2lablst (s2ls0_ft1, s2ls_ft, s2ls_bk)
      end // end of [val]
    | list_nil () => aux (s2ls0_ft, s2ls_bk)
    end // end of [list_cons]
  | list_nil () => $Lst.list_append (s2ls_ft, s2ls_bk)
end // end of [s2lablst_trim_s2lablst_s2lablst]

(* ****** ****** *)

implement
s2exp_is_proof (s2e) = s2rt_is_proof (s2e.s2exp_srt)
implement
s2exp_is_proof_fun (s2e) = s2rt_is_proof_fun (s2e.s2exp_srt)

implement
s2exp_is_linear (s2e) = s2rt_is_linear (s2e.s2exp_srt)
implement
s2exp_is_nonlin (s2e) =
  if s2rt_is_linear s2e.s2exp_srt then false else true
// end of [s2exp_is_nonlin]

implement s2exp_is_impredicative
  (s2e) = s2rt_is_impredicative (s2e.s2exp_srt)
implement s2exp_is_types (s2e) = s2rt_is_types (s2e.s2exp_srt)

(* ****** ****** *)

implement
s2exp_is_abscon (s2e) =
  case+ s2e.s2exp_node of
  | S2Ecst s2c => begin
      if s2cst_is_abstract s2c then true else s2cst_get_iscon s2c
    end // end of [S2Ecst]
  | S2Eapp (s2e, _) => s2exp_is_abscon s2e
  | _ => false
// end  of [s2exp_is_abscon]

implement
s2exp_is_non_fun (s2e) =
  case+ s2e.s2exp_node of
  | S2Efun _ => false
  | S2EVar _ => false
  | S2Euni (_, _, s2e) => let
      val s2e = s2exp_whnf (s2e) in s2exp_is_non_fun s2e
    end // end of [S2Euni]
  | _ => true
// end of [s2exp_is_non_fun]

implement
s2exp_is_non_tyrec (s2e) =
  case+ s2e.s2exp_node of
  | S2Etyrec _ => false
  | S2EVar _ => false
  | S2Eexi (_, _, s2e) => let
      val s2e = s2exp_whnf (s2e) in s2exp_is_non_tyrec s2e
    end // end of [S2Eexi]
  | _ => true
// end of [s2exp_is_non_tyrec]

implement
s2exp_is_wth (s2e) = case+ s2e.s2exp_node of
  | S2Eexi (_, _, s2e) => s2exp_is_wth s2e | S2Ewth _ => true | _ => false
// end of [s2exp_is_wth]

(* ****** ****** *)

implement
s2exp_get_head (s2e0) = let
  fun loop (s2e: s2exp): s2exp =
    case+ s2e.s2exp_node of S2Eapp (s2e, _) => loop s2e | _ => s2e
  // end of [loop]
in
  loop (s2exp_whnf s2e0)
end // end of [s2exp_get_head]

(* ****** ****** *)

fun lte_s2explst_s2rtlst
  (s2es: s2explst, s2ts: s2rtlst): bool =
  case+ (s2es, s2ts) of
  | (s2e :: s2es, s2t :: s2ts) => begin
(*
      print "lte_s2explst_s2rtlst: srt = ";
      print s2t; print_newline ();
      print "lte_s2explst_s2rtlst: s2e.s2exp_srt = ";
      print s2e.s2exp_srt; print_newline ();
*)
      if s2e.s2exp_srt <= s2t then
        lte_s2explst_s2rtlst (s2es, s2ts)
      else false
    end // end of [::, ::]
  | (nil (), nil ()) => true
  | (_, _) => false
// end of [lte_s2explst_s2rtlst]

implement
s2cst_select_s2explstlst (s2cs, s2ess) = let
  fun test (s2t_fun: s2rt, s2ess: s2explstlst): bool =
    case+ s2ess of
    | s2es :: s2ess => begin case+ un_s2rt_fun s2t_fun of
      | ~Some_vt s2ts_s2t => begin
          if lte_s2explst_s2rtlst (s2es, s2ts_s2t.0) then test (s2ts_s2t.1, s2ess)
          else false
        end // end of [Some]
      | ~None_vt () => false
      end
    | nil () => true
  fun filter (s2cs: s2cstlst, s2ess: s2explstlst): s2cstlst =
    case+ s2cs of
    | S2CSTLSTcons (s2c, s2cs) => begin
(*
        print "s2cst_select_s2explstlst: filter: s2c = ";
        print s2c;
        print_newline ();
        print "s2cst_select_s2explstlst: filter: s2c_s2t = ";
        print (s2cst_get_srt s2c);
        print_newline ();
*)
        if test (s2cst_get_srt s2c, s2ess) then begin
          S2CSTLSTcons (s2c, filter (s2cs, s2ess))
        end else begin
          filter (s2cs, s2ess)
        end (* end of [if] *)
      end // end of [S2CSTLSTcons]
    | S2CSTLSTnil () => S2CSTLSTnil ()
in
  filter (s2cs, s2ess)
end // end of [s2cst_select_s2explstlst]

(* ****** ****** *)

implement
s2rt_lin_prg_boxed
  (lin, prg, boxed) =
  if lin > 0 then begin
    if prg > 0 then
      if boxed > 0 then s2rt_viewtype else s2rt_viewt0ype
    else s2rt_view
  end else begin
    if prg > 0 then
      if boxed > 0 then s2rt_type else s2rt_t0ype
    else s2rt_prop
  end (* end of [if] *)
// end of [s2rt_lin_prg_boxed]

fn labs2explst_is_singleton (
  npf: int, ls2es: labs2explst
) : Option_vt s2exp = let
  fun aux0 (npf: int, ls2es: labs2explst): Option_vt s2exp =
    if npf > 0 then begin case+ ls2es of
      | LABS2EXPLSTcons (_, _, ls2es) => aux0 (npf - 1, ls2es)
      | LABS2EXPLSTnil () => None_vt ()
    end else begin case+ ls2es of
      | LABS2EXPLSTcons (_, s2e, ls2es) => begin
          if s2exp_is_proof s2e then aux0 (0, ls2es) else aux1 (s2e, ls2es)
        end // end of [LABS2EXPLSTcons]
      | LABS2EXPLSTnil () => None_vt ()
    end // end of [if]
  // end of [aux0]
  and aux1 (s2e0: s2exp, ls2es: labs2explst): Option_vt s2exp =
    case+ ls2es of
    | LABS2EXPLSTcons (_, s2e, ls2es) => begin
        if s2exp_is_proof s2e then aux1 (s2e0, ls2es) else None_vt ()
      end // endof [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => Some_vt s2e0
  // end of [aux1]
in
  aux0 (npf, ls2es)
end (* end of [labs2explst_is_singleton] *)

implement
s2rt_lin_prg_boxed_npf_labs2explst
  (lin, prg, boxed, npf, ls2es) = let
  val s2t = s2rt_lin_prg_boxed (lin, prg, boxed)
in
  if prg > 0 then
    if boxed > 0 then s2t else let
      val os2e = labs2explst_is_singleton (npf, ls2es)
    in
      case+ os2e of
      | ~Some_vt s2e => let
          val s2t = s2e.s2exp_srt
        in
          if lin > 0 then s2rt_linearize s2t else s2t
        end // end of [Some_vt]
      | ~None_vt () => s2t // end of [None_vt]
    end // end of [if]
  else s2t // end of [if]
end // end of [s2rt_lin_prg_boxed_npf_labs2explst]

(* ****** ****** *)

implement
s2exp_tyrec (recknd, npf, ls2es) = let
  val tyrecknd: tyreckind = case+ recknd of
    | 0 => TYRECKINDflt0 () | _ => TYRECKINDbox ()
  var lin: int = 0 and prg: int = 0
  fun aux01
    (i: int, npf: int, ls2es: labs2explst, lin: &int, prg: &int): void =
    case+ ls2es of
    | LABS2EXPLSTcons (_(*lab*), s2e, ls2es) => let
        val s2t = s2e.s2exp_srt
        val () = if s2rt_is_linear s2t then (lin := lin+1)
        val () = begin
          if i >= npf then (if ~(s2rt_is_proof s2t) then (prg := prg+1))
        end
      in
        aux01 (i+1, npf, ls2es, lin, prg)
      end // end of [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => ()
  // end of [aux01]
  val s2t_rec = (case+ recknd of
    | 0 => let
        val () = aux01 (0, npf, ls2es, lin, prg)
      in
        s2rt_lin_prg_boxed_npf_labs2explst (lin, prg, 0, npf, ls2es)
      end
    | 1 => let
        val () = aux01 (0, npf, ls2es, lin, prg)
      in
        s2rt_lin_prg_boxed (lin, prg, 1)
      end
    | 2 => s2rt_type // $rec_t/$tup_t
    | 3 => s2rt_viewtype // $rec_vt/$tup_vt
    | _ => begin
        prerr_interror ();
        prerr ": s2exp_tyrec: recknd = "; prerr recknd; prerr_newline ();
        $Err.abort {s2rt} ()
      end // end of [_]
  ) : s2rt
in
  s2exp_tyrec_srt (s2t_rec, tyrecknd, npf, ls2es)
end // end of [s2exp_tyrec]

implement
s2exp_union (
  isbox, stamp, s2i, ls2es
) = let
  fun aux1 (ls2es: labs2explst, lin: &int): void =
    case+ ls2es of
    | LABS2EXPLSTcons (_, s2e, ls2es) => begin
        if s2rt_is_linear (s2e.s2exp_srt) then (lin := 1 + lin);
        aux1 (ls2es, lin)
      end // end of [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => ()
  // end of [aux1]
  fun aux2 (ls2es: labs2explst, i: int): s2expopt_vt =
    case+ ls2es of
    | LABS2EXPLSTcons (_, s2e, ls2es) =>
        if i = 0 then Some_vt (s2e) else aux2 (ls2es, i-1)
      // end of [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => None_vt ()
  // end of [aux2]
  var lin: int = 0
  val () = (case+ s2i.s2exp_node of
    | S2Eint i => begin
       if i >= 0 then begin case+ aux2 (ls2es, i) of
          | ~Some_vt s2e => begin
              if s2exp_is_linear s2e then lin := 1 else lin := 0
            end
          | ~None_vt () => (lin := 0)
        end else (lin := 0)
      end // end of [S2Eint]
    | _ => aux1 (ls2es, lin)
  ) : void
  val s2t_union = (
    if lin > 0 then begin
      if isbox then s2rt_viewtype else s2rt_viewt0ype
    end else begin
      if isbox then s2rt_type else s2rt_t0ype
    end // end of [if]
  ) : s2rt
in
  s2exp_union_srt (s2t_union, stamp, s2i, ls2es)
end // end of [s2exp_union]

(* ****** ****** *)

implement
s2kexp_make_s2exp (s2e0) = let
//
  fun aux_s2var (
    s2vss: s2varlstlst, s2v0: s2var_t
  ) : s2kexp =
    case+ s2vss of
    | list_cons (s2vs, s2vss) => let
        fun test (s2vs: s2varlst, s2v0: s2var_t): bool =
          case+ s2vs of
          | list_cons (s2v, s2vs) => begin
              if s2v = s2v0 then true else test (s2vs, s2v0)
            end // end of [list_cons]
          | list_nil () => false
      in
        if test (s2vs, s2v0) then S2KEany () else aux_s2var (s2vss, s2v0)
      end // end of [list_cons]
    | list_nil () => S2KEvar s2v0
  // end of [aux_s2var]
//
  fun aux_s2exp (
    pol: int, s2vss: s2varlstlst, s2e0: s2exp
  ) : s2kexp = let
    val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
      | S2Eapp (s2e, s2es) => let
          val s2ke = aux_s2exp (0, s2vss, s2e)
          val s2kes = aux_s2explst_arg (0, s2vss, s2es)
        in
          case+ s2kes of
          | list_cons _ => S2KEapp (s2ke, s2kes) | list_nil _ => s2ke
        end // end of [S2Eapp]
      | S2Ecst s2c => S2KEcst s2c
      | S2Eexi (s2vs, _, s2e) => aux_s2exp (pol, s2vs :: s2vss, s2e)
      | S2Efun (fc, _, _, _, s2es_arg, s2e_res) => let
          val s2kes_arg = aux_s2explst (0, s2vss, s2es_arg)
          val s2ke_res = aux_s2exp (0, s2vss, s2e_res)
        in
          S2KEfun (fc, s2kes_arg, s2ke_res)
        end // end of [S2Efun]
(*
// HX-2010-12-04: inadequate design
      | S2Enamed (_(*name*), s2e) => aux_s2exp (pol, s2vss, s2e)
*)
      | S2Eread (_(*view*), s2e_vt) => aux_s2exp (pol, s2vss, s2e_vt)
      | S2Erefarg (_(*knd*), s2e) => aux_s2exp (pol, s2vss, s2e)
      | S2Etyarr _ => S2KEtyarr ()
      | S2Etyrec (knd, npf, ls2es) => let
          val ls2kes = aux_labs2explst (pol, s2vss, ls2es)
        in
          S2KEtyrec (knd, ls2kes)
        end // end of [S2Etyrec]
      | S2Euni (s2vs, _, s2e) => aux_s2exp (pol, s2vs :: s2vss, s2e)
      | S2Evar s2v => aux_s2var (s2vss, s2v)
      | S2EVar s2V => aux_s2Var (pol, s2vss, s2V)
      | S2Ewth (s2e, _(*wths2es*)) => aux_s2exp (pol, s2vss, s2e)
      | _ => S2KEany ()
   end // end of [aux_s2exp]
//
  and aux_s2explst (
    pol: int, s2vss: s2varlstlst, s2es: s2explst
  ) : s2kexplst = case+ s2es of
    | list_cons (s2e, s2es) => list_cons
        (aux_s2exp (pol, s2vss, s2e), aux_s2explst (pol, s2vss, s2es))
      // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux_s2explst]
//
  and aux_s2Varboundlst (
    pol: int, s2vss: s2varlstlst, s2Vbs: s2Varboundlst
  ) : s2kexplst =
    case+ s2Vbs of
    | list_cons (s2Vb, s2Vbs) => let
        val s2ke = aux_s2exp (pol, s2vss, s2Varbound_get_val s2Vb)
      in
        list_cons (s2ke, aux_s2Varboundlst (pol, s2vss, s2Vbs))
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux_s2Varboundlst]
//
  and aux_labs2explst (
    pol: int, s2vss: s2varlstlst, ls2es: labs2explst
  ) : labs2kexplst =
    case+ ls2es of
    | LABS2EXPLSTcons (l, s2e, ls2es) => LABS2KEXPLSTcons
        (l, aux_s2exp (pol, s2vss, s2e), aux_labs2explst (pol, s2vss, ls2es))
    | LABS2EXPLSTnil () => LABS2KEXPLSTnil ()
  // end of [aux_labs2explst]
//
  and aux_s2explst_arg (
    pol: int, s2vss: s2varlstlst, s2es: s2explst
  ) : s2kexplst = case+ s2es of
    | list_cons (s2e, s2es) => begin
        if s2exp_is_impredicative s2e then list_cons
          (aux_s2exp (pol, s2vss, s2e), aux_s2explst (pol, s2vss, s2es))
        else aux_s2explst (pol, s2vss, s2es)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux_s2explst_arg]
//
  and aux_s2Var (
    pol: int, s2vss: s2varlstlst, s2V: s2Var_t
  ) : s2kexp =
    if pol > 0 then
      S2KEunion (aux_s2Varboundlst (pol, s2vss, s2Var_get_lbs s2V))
    else S2KEany ()
  // end of [aux_s2Var]
//
in
  aux_s2exp (1, list_nil (), s2e0)
end // end of [s2kexp_make]

(* ****** ****** *)

fun s2kexp_match_union_approx (
  s2kes1: s2kexplst, s2ke2: s2kexp, approx: &int
) : bool = begin
  case+ s2kes1 of
  | list_cons (s2ke1, s2kes1) => begin
      if s2kexp_match_approx (1, s2ke1, s2ke2, approx) then
        s2kexp_match_union_approx (s2kes1, s2ke2, approx)
      else false
    end (* end of [list_cons] *)
  | list_nil () => true
end // end of [s2kexp_match_union]

fun s2kexp_match_union
  (s2kes1: s2kexplst, s2ke2: s2kexp): bool = let
  var approx: int = 0 in
  s2kexp_match_union_approx (s2kes1, s2ke2, approx)
end // end of [s2kexp_match_union]

implement
s2kexp_match_approx
  (pol, s2ke1, s2ke2, approx) = let
(*
  val () = begin
    print "s2kexp_match_approx: s2ke1 = "; print s2ke1; print_newline ();
    print "s2kexp_match_approx: s2ke2 = "; print s2ke2; print_newline ();
  end // end of [val]
*)
  val ret = (case+ (s2ke1, s2ke2) of
  | (S2KEany (), _) => true // no information
  | (_, S2KEany ()) => true // no information
  | (_, S2KEunion _) => true // no information
  | (S2KEapp (s2ke11, s2kes12), S2KEapp (s2ke21, s2kes22)) => begin
      if s2kexp_match_approx (0, s2ke11, s2ke21, approx)
        then s2kexplst_match_approx (0, s2kes12, s2kes22, approx)
      else false
    end // end of [S2KEapp, S2KEapp]
  | (S2KEcst s2c1, S2KEcst s2c2) => begin
      if s2c1 = s2c2 then true else begin
        if pol > 0 then
          if s2cst_is_eqsup (s2c1, s2c2) then (approx := approx + 1; true)
          else false
        else false
      end // end of [if]
    end // end of [S2KEcst, S2KEcst]
  | (S2KEfun (fc1, _, _), S2KEfun (fc2, _, _)) => begin
       $Syn.eq_funclo_funclo (fc1, fc2)
    end // end of [S2KEfun, S2KEfun]
  | (S2KEtyarr _, S2KEtyarr _) => true
  | (S2KEtyrec (knd1, ls2kes1), S2KEtyrec (knd2, ls2kes2)) => begin
      if knd1 = knd2 then
        labs2kexplst_match_approx (pol, ls2kes1, ls2kes2, approx)
      else false
    end // end of [S2KEtyrec, S2KEtyrec]
  | (S2KEvar s2v1, S2KEvar s2v2) => eq_s2var_s2var (s2v1, s2v2)
  | (S2KEunion s2kes1, _) => s2kexp_match_union (s2kes1, s2ke2)
  | (_, _) => false
  ) : bool
(*
  val () = begin
    print "s2kexp_match_approx: ret = "; print ret; print_newline ();
  end // end of [val]
*)
in
  ret // return value
end // end of [s2kexp_match_approx]

implement
s2kexplst_match_approx
  (pol, s2kes1, s2kes2, approx) = let
  val ret = (case+ (s2kes1, s2kes2) of
    | (s2ke1 :: s2kes1, s2ke2 :: s2kes2) => (
        if s2kexp_match_approx (pol, s2ke1, s2ke2, approx)
          then s2kexplst_match_approx (pol, s2kes1, s2kes2, approx) else false
        // end of [if]
      ) // end of [::, ::]
    | (nil _, nil _) => true
    | (_, _) => false
  ) : bool // end of [val]
in
  ret // return value
end // end of [s2kexplst_match_approx]

implement
labs2kexplst_match_approx
  (pol, ls2kes1, ls2kes2, approx) = begin
  case+ (ls2kes1, ls2kes2) of
  | (LABS2KEXPLSTcons (l1, s2ke1, ls2kes1),
     LABS2KEXPLSTcons (l2, s2ke2, ls2kes2)) => begin
       if l1 = l2 then
         if s2kexp_match_approx (pol, s2ke1, s2ke2, approx) then
           labs2kexplst_match_approx (pol, ls2kes1, ls2kes2, approx)
         else false
       else false
    end // end of [LABS2KEXPLSTcons, LABS2KEXPLSTcons]
  | (LABS2KEXPLSTnil _, LABS2KEXPLSTnil _) => true
  | (_, _) => false
end // end of [labs2kexplst_match_approx]

implement
s2kexp_match_fun_arg
  (s2ke_fun, s2kes_arg) = begin
  case+ s2ke_fun of
  | S2KEfun (_(*fc*), s2kes1_arg, s2ke1_res) => let
      var approx: int = 0
      val ans = begin
        s2kexplst_match_approx (1, s2kes_arg, s2kes1_arg, approx)
      end
    in
      if ans then Some_vt @(s2ke1_res, approx)
(*
      else if $Lst.list_length_compare (s2kes_arg, s2kes1_arg) = 0 then
        Some_vt @(s2ke1_res, ~1) // [~1] means infinity: only arity match
*)
      else None_vt ()
    end // end of [S2KEfun]
  | _ => None_vt () // end of [_]
end // end of [s2kexp_match_fun_arg]

(* ****** ****** *)

fun s2cst_get_root
  (s2c: s2cst_t): s2cst_t = case+ s2cst_get_sup s2c of
  | S2CSTLSTcons (s2c, _) => s2cst_get_root s2c | S2CSTLSTnil () => s2c
// end of [s2cst_get_root]

fn s2zexp_make_s2cst (s2c: s2cst_t): s2zexp = S2ZEcst s2c

implement
s2zexp_make_s2exp (s2e0) = let
//
  fun aux_s2exp (
      s2vss: s2varlstlst, s2e0: s2exp
    ) : s2zexp = let
(*
    val () = (print "s2zexp_make_s2exp: aux_s2exp: s2e0 = "; print s2e0; print_newline ())
*)
    val s2e0 = s2exp_whnf s2e0 in
      case+ s2e0.s2exp_node of
      | S2Eapp (s2e_fun, s2es_arg) =>
          aux_s2exp_app (s2vss, s2e0.s2exp_srt, s2e_fun, s2es_arg)
        // end of [S2Eapp]
//
      | S2Ecst s2c => let
          val isabs = s2cst_get_isabs (s2c) in
          case+ isabs of
          | Some (Some s2e) => aux_s2exp (s2vss, s2e) | _ => s2zexp_make_s2cst (s2c)
        end // end of [S2Ecst]
//
      | S2Eclo (knd, _) => if knd <> 0 then S2ZEptr () else S2ZEbot ()
      | S2Edatconptr (d2c, _) => s2zexp_make_s2cst (d2con_get_scst d2c)
      | S2Edatcontyp (d2c, _) => s2zexp_make_s2cst (d2con_get_scst d2c)
      | S2Eexi (s2vs, _(*s2ps*), s2e) => aux_s2exp (s2vs :: s2vss, s2e)
      | S2Eextype (name, _(*arglst*)) => S2ZEextype (name)
      | S2Efun _ => S2ZEptr ()
(*
      | S2Eout s2e => S2ZEout (s2zexp_make_s2exp s2e)
*)
      | S2Eread (_, s2e) => s2zexp_make_s2exp s2e
      | S2Esize s2ze => s2ze
      | S2Etop (_(*knd*), s2e) => s2zexp_make_s2exp s2e
      | S2Etyarr (s2e_elt, s2ess_dim) => begin
          S2ZEtyarr (aux_s2exp (s2vss, s2e_elt), s2ess_dim)
        end // end of [S2Etyarr]
      | S2Etyrec (knd, npf, ls2es) => begin case+ knd of
        | TYRECKINDbox () => S2ZEptr ()
        | TYRECKINDflt_ext (name) => S2ZEextype (name)
        | _ => S2ZEtyrec (knd, aux_labs2explst (s2vss, ls2es))
        end // end of [S2Etyrec]
      | S2Euni (s2vs, _(*s2ps*), s2e) => aux_s2exp (s2vs :: s2vss, s2e)
      | S2Eunion (stamp, _(*s2i*), ls2es) => begin
          S2ZEunion (stamp, aux_labs2explst (s2vss, ls2es))
        end // end of [S2Eunion]
      | S2Evar s2v => aux_s2var (s2vss, s2v)
      | S2EVar s2V => aux_s2Var (s2vss, s2V)
      | _ => S2ZEbot ()
  end // end of [aux_s2exp]
//
  and aux_s2exp_app ( // [s2e_fun] is normalized
      s2vss: s2varlstlst, s2t: s2rt, s2e_fun: s2exp, s2es_arg: s2explst
    ) : s2zexp =
    case+ s2e_fun.s2exp_node of
    | S2Ecst s2c => let
        val isabs = s2cst_get_isabs (s2c) in
        case+ isabs of
        | Some (Some s2e_fun) => let
            val s2e = s2exp_app_srt (s2t, s2e_fun, s2es_arg) in aux_s2exp (s2vss, s2e)
          end // end of [Some (Some _)]
        | _ => s2zexp_make_s2cst (s2cst_get_root s2c) // incorrect for certain constructors
      end (* end of [S2Ecst] *)
    | _ => S2ZEbot () (* HX: ??? *)
  // end of [aux_s2exp_app]
//  
  and aux_s2explst
    (s2vss: s2varlstlst, s2es: s2explst): s2zexplst = case+ s2es of
    | list_cons (s2e, s2es) => let
        val s2ze = aux_s2exp (s2vss, s2e) in list_cons (s2ze, aux_s2explst (s2vss, s2es))
      end // end of [S2EXPLSTcons]
    | list_nil () => list_nil ()
  // end of [aux_s2explst]
//
  and aux_labs2explst (
    s2vss: s2varlstlst, ls2es: labs2explst
  ) : labs2zexplst = case+ ls2es of
    | LABS2EXPLSTcons (l, s2e, ls2es) =>
        if s2exp_is_proof (s2e) then
          aux_labs2explst (s2vss, ls2es)
        else let
          val s2ze = aux_s2exp (s2vss, s2e)
          val ls2zes = aux_labs2explst (s2vss, ls2es)
        in
          LABS2ZEXPLSTcons (l, s2ze, ls2zes)
        end // end of [if]
      // end of [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => LABS2ZEXPLSTnil ()
  // end of [aux_labs2explst]
//
  and aux_s2var (s2vss: s2varlstlst, s2v0: s2var_t): s2zexp =
    case+ s2vss of
    | list_cons (s2vs, s2vss) => let
        fun f (s2vs: s2varlst, s2v0: s2var_t): bool = case+ s2vs of
          | list_cons (s2v, s2vs) =>
              if s2v0 = s2v then true else f (s2vs, s2v0)
          | list_nil () => false
      in
        if f (s2vs, s2v0) then S2ZEbot () else aux_s2var (s2vss, s2v0)
      end // end of [list_cons]
    | list_nil () => S2ZEvar s2v0
  // end of [aux_s2var]
//
  and aux_s2Var
    (s2vss: s2varlstlst, s2V0: s2Var_t): s2zexp = let
    val lbs = s2Var_get_lbs s2V0
  in
    case+ lbs of
    | list_cons (lb, _) => let
        val s2e = s2Varbound_get_val (lb) in aux_s2exp (s2vss, s2e)
      end // end of [list_cons]
    | list_nil () => let
        val ubs = s2Var_get_ubs s2V0 in
        case+ ubs of
        | list_cons (ub, _) => let
            val s2e = s2Varbound_get_val (ub) in aux_s2exp (s2vss, s2e)
          end // end of [list_cons]
        | list_nil () => S2ZEbot () // no information
      end // end of [list_nil]
  end // end of [aux_s2Var]
in
  aux_s2exp (list_nil (), s2e0)
end // end of [s2zexp_make_s2exp]

(* ****** ****** *)

implement
s2cstlst_length (xs) = loop (xs, 0) where {
  fun loop (xs: s2cstlst, j: Nat): Nat = case+ xs of
    | S2CSTLSTcons (_, xs) => loop (xs, j+1) | S2CSTLSTnil () => j
} // end of [s2cstlst_length]

implement
s2cstlst_append (xs, ys) = case+ xs of
  | S2CSTLSTcons (x, xs) => S2CSTLSTcons (x, s2cstlst_append (xs, ys))
  | S2CSTLSTnil () => ys
// end of [s2cstlst_append]

implement
s2cstlst_reverse (xs) = let
  fun loop (xs: s2cstlst, ys: s2cstlst): s2cstlst =
    case+ xs of
    | S2CSTLSTcons (x, xs) => loop (xs, S2CSTLSTcons (x, ys))
    | S2CSTLSTnil () => ys
  // end of [loop]
in
  loop (xs, S2CSTLSTnil ())
end // end of [s2cstlst_reverse]

implement
s2qualst_reverse (xs) = let
  fun loop (xs: s2qualst, ys: s2qualst): s2qualst =
    case+ xs of x :: xs => loop (xs, x :: ys) | list_nil () => ys
  // end of [loop]
in
  loop (xs, list_nil ())
end // end of [s2qualst_reverse]

(* ****** ****** *)

typedef stasub = List @(s2var_t, s2exp)
assume stasub_t = stasub

implement stasub_nil = list_nil ()
implement stasub_add (sub, s2v, s2e) = @(s2v, s2e) :: sub
implement
stasub_addlst (sub, s2vs, s2es) = let
  fun loop (
    sub: stasub_t, s2vs: s2varlst, s2es: s2explst
  ) : stasub_t =
    case+ (s2vs, s2es) of
    | (list_cons (s2v, s2vs), list_cons (s2e, s2es)) => let
        val sub = stasub_add (sub, s2v, s2e) in loop (sub, s2vs, s2es)
      end // end of [list_cons, list_cons]
    | (_, _) => sub
  // end of [loop]
in
  loop (sub, s2vs, s2es)
end // end of [stasub_addlst]

implement
stasub_get_domain
  (sub) = case+ sub of
  | list_cons (s2vs2e, sub) =>
      list_cons (s2vs2e.0, stasub_get_domain sub)
  | list_nil () => list_nil ()
// end of [stasub_get_domain]

implement
stasub_get_codomain_whnf
  (sub) = case+ sub of
  | list_cons (s2vs2e, sub) => let
      val s2e = s2exp_whnf s2vs2e.1 in
      list_cons (s2e, stasub_get_codomain_whnf sub)
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [stasub_get_codomain_whnf]

(* ****** ****** *)

implement
stasub_extend_svarlst (sub, s2vs) = let
  fun loop (
    sub: stasub, s2vs1: s2varlst, s2vs: s2varlst
  ) : @(stasub, s2varlst) =
    case+ s2vs of
    | list_cons (s2v, s2vs) => let
        val s2v1 = s2var_copy s2v
        val s2e1 = s2exp_var s2v1 in
        loop ((s2v, s2e1) :: sub, s2v1 :: s2vs1, s2vs)
      end // end of [list_cons]
    | list_nil () => (sub, $Lst.list_reverse s2vs1)
  // end of [loop]
in
  loop (sub, nil (), s2vs)
end // end of [stasub_extend_svarlst]

implement
stasub_extend_sarglst_svarlst
  (loc0, sub, s2as, s2vs) = let
//  
  fn err1 (loc0: loc_t, s2t: s2rt, s2a: s2arg): s2rt = begin
    prerr_loc_error2 loc0;
    prerr ": the static argument [";
    prerr s2a.s2arg_sym;
    prerr "] is expected to be of sort ["; prerr s2t; prerr "].";
    prerr_newline ();
    $Err.abort {s2rt} ()
  end // end of [err1]
//
  fn err2 (loc0: loc_t): @(stasub, s2varlst) = begin
    prerr_loc_error2 loc0;
    prerr ": the static application is expected to have fewer arguments.";
    prerr_newline ();
    $Err.abort ()
  end // end of [err2]
//
  fn err3 (loc0: loc_t): @(stasub, s2varlst) = begin
    prerr_loc_error2 loc0;
    prerr ": the static application is expected to have more arguments.";
    prerr_newline ();
    $Err.abort ()
  end // end of [err3]
//
  fun aux (
    loc0: loc_t, sub: stasub
  , s2vs1: s2varlst, s2as: s2arglst, s2vs: s2varlst
  ) : @(stasub, s2varlst) =
    case+ (s2as, s2vs) of
    | (nil (), nil ()) => (sub, $Lst.list_reverse s2vs1)
    | (s2a :: s2as, s2v :: s2vs) => let
        val s2t_s2v = s2var_get_srt s2v
        val s2t = (case+ s2a.s2arg_srt of
          | Some s2t => begin
              if s2t_s2v <= s2t then s2t else err1 (loc0, s2t_s2v, s2a)
            end // end of [Some]
          | None () => s2t_s2v
        ) : s2rt
        val s2v1 = s2var_make_id_srt (s2a.s2arg_sym, s2t)
        val sub = list_cons (@(s2v, s2exp_var s2v1), sub)
      in
        aux (loc0, sub, list_cons (s2v1, s2vs1), s2as, s2vs)
      end // end of [::, ::]
    | (list_cons _, list_nil _) => err2 (loc0)
    | (list_nil _, list_cons _) => err3 (loc0)
  // end of [aux]
in
  aux (loc0, sub, nil (), s2as, s2vs)
end (* end of [stasub_extend_sarg] *)

(* ****** ****** *)

fun s2var_subst (
  sub: stasub, s2v0: s2var_t
) : Option_vt s2exp = begin
  case+ sub of
  | s2vs2e :: sub => begin
      if s2v0 = s2vs2e.0 then Some_vt s2vs2e.1 else s2var_subst (sub, s2v0)
    end // end of [::]
  | nil () => None_vt ()
end (* end of [s2var_subst] *)

fun s2Var_subst .<>. (
  sub: stasub, s2V0: s2Var_t
) : Option_vt (s2exp) = begin
  case+ s2Var_get_link s2V0 of
  | Some s2e => Some_vt (s2exp_subst (sub, s2e))
  | None () => None_vt () where {
      fun aux (
        s2V0: s2Var_t, sub: stasub
      ) : void = case+ sub of
        | s2vs2e :: sub => let
            val s2v = s2vs2e.0; val sVs = s2var_get_sVarset s2v
            val () = s2var_set_sVarset (s2v, s2Varset_add (sVs, s2V0))
          in
            aux (s2V0, sub)
          end // end of [::]
        | list_nil () => ()
      // end of [aux]
      val () = aux (s2V0, sub)
    } // end of [None]
end (* end of [s2Var_subst] *)

(* ****** ****** *)

local

fun s2exp_subst_flag
  (sub: stasub, s2e0: s2exp, flag: &int): s2exp = begin
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => let
      val flag0 = flag
      val s2e_fun = s2exp_subst_flag (sub, s2e_fun, flag)
      val s2es_arg = s2explst_subst_flag (sub, s2es_arg, flag)
    in
      if flag > flag0 then
        s2exp_app_srt (s2e0.s2exp_srt, s2e_fun, s2es_arg)
      else s2e0
    end // end of [S2Eapp]
  | S2Echar _ => s2e0
  | S2Eclo (knd, s2e_fun) => let
      val flag0 = flag
      val s2e_fun = s2exp_subst_flag (sub, s2e_fun, flag)
    in
      if flag > flag0 then
        s2exp_clo_srt (s2e_fun.s2exp_srt, knd, s2e_fun)
      else s2e0
    end // end of [S2Eclo]
  | S2Ecrypt s2e => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then s2exp_crypt (s2e) else s2e0
    end // end of [S2Ecrypt]
  | S2Ecst s2c  => s2e0
  | S2Edatconptr (d2c, s2es) => let
      val flag0 = flag
      val s2es = s2explst_subst_flag (sub, s2es, flag)
    in
      if flag > flag0 then s2exp_datconptr (d2c, s2es) else s2e0
    end // end of [S2Edatconptr]
  | S2Edatcontyp (d2c, s2es) => let
      val flag0 = flag
      val s2es = s2explst_subst_flag (sub, s2es, flag)
    in
      if flag > flag0 then s2exp_datcontyp (d2c, s2es) else s2e0
    end // end of [S2Edatcontyp]
  | S2Eeff s2fe => let
      val flag0 = flag
      val s2fe = s2eff_subst_flag (sub, s2fe, flag)
    in
      if flag > flag0 then s2exp_eff (s2fe) else s2e0
    end // end of [S2Eeff]
  | S2Eeqeq (s2e1, s2e2) => let
      val flag0 = flag
      val s2e1 = s2exp_subst_flag (sub, s2e1, flag)
      val s2e2 = s2exp_subst_flag (sub, s2e2, flag)
    in
      if flag > flag0 then s2exp_eqeq (s2e1, s2e2) else s2e0
    end // end of [S2Eeqeq]
  | S2Eexi (s2vs, s2ps, s2e_body) => let
      val flag0 = flag
      val @(sub, s2vs) = stasub_extend_svarlst (sub, s2vs)
      val s2ps = s2explst_subst_flag (sub, s2ps, flag)
      val s2e_body = s2exp_subst_flag (sub, s2e_body, flag)
    in
      if flag > flag0 then s2exp_exi (s2vs, s2ps, s2e_body) else s2e0
    end // end of [S2Eexi]
  | S2Eextype (name, _arg) => let
      val flag0 = flag
      val _arg = s2explstlst_subst_flag (sub, _arg, flag)
    in
      if flag > flag0 then
        s2exp_extype_srt (s2e0.s2exp_srt, name, _arg)
      else s2e0 // end of [if]
    end // end of [S2Eextype]
  | S2Efun (fc, lin, s2fe, npf, s2es_arg, s2e_res) => let
      val flag0 = flag
      val s2fe = s2eff_subst_flag (sub, s2fe, flag)
      val s2es_arg = s2explst_subst_flag (sub, s2es_arg, flag)
      val s2e_res = s2exp_subst_flag (sub, s2e_res, flag)
    in
      if flag > flag0 then
        s2exp_fun_srt (s2e0.s2exp_srt, fc, lin, s2fe, npf, s2es_arg, s2e_res)
      else s2e0 // end of [if]
    end // end of [S2Efun]
  | S2Eint _ => s2e0
  | S2Eintinf _ => s2e0
  | S2Elam (s2vs, s2e_body) => let
      val flag0 = flag
      val (sub, s2vs) = stasub_extend_svarlst (sub, s2vs)
      val s2e_body = s2exp_subst_flag (sub, s2e_body, flag)
    in
      if flag > flag0 then
        s2exp_lam_srt (s2e0.s2exp_srt, s2vs, s2e_body)
      else s2e0 // end of [if]
    end // end of [S2Elam]
  | S2Emetfn (d2v (*stamp*), s2es_met, s2e_fun) => let
      val flag0 = flag
      val s2es_met = s2explst_subst_flag (sub, s2es_met, flag)
      val s2e_fun = s2exp_subst_flag (sub, s2e_fun, flag)
    in
      if flag > flag0 then
        s2exp_metfn (d2v, s2es_met, s2e_fun)
      else s2e0 // end of [if]
    end // end of [S2Emetfn]
  | S2Emetlt (s2es1, s2es2) => let
      val flag0 = flag
      val s2es1 = s2explst_subst_flag (sub, s2es1, flag)
      val s2es2 = s2explst_subst_flag (sub, s2es2, flag)
    in
      if flag > flag0 then s2exp_metlt (s2es1, s2es2) else s2e0
    end // end of [S2Emetlt]
(*
// HX-2010-12-04: inadequate design
  | S2Enamed _ => s2e0 // a named type must be closed!
*)
  | S2Eout s2e => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then s2exp_out (s2e) else s2e0
    end // end of [S2Eout]
  | S2Eproj (s2e, s2l) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
      val s2l = s2lab_subst_flag (sub, s2l, flag)
    in
      if flag > flag0 then s2exp_proj (s2e, s2l) else s2e0
    end // end of [S2Eproj]
  | S2Eread (_v, s2e) => let
      val flag0 = flag
      val _v = s2exp_subst_flag (sub, _v, flag)
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then
        s2exp_read_srt (s2e0.s2exp_srt, _v, s2e)
      else s2e0
    end // end of [S2Eread]
  | S2Erefarg (refval, s2e) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then s2exp_refarg (refval, s2e) else s2e0
    end // end of [S2Erefarg]
  | S2Esel (s2e_tup, i) => let
      val flag0 = flag
      val s2e_tup = s2exp_subst_flag (sub, s2e_tup, flag)
    in
      if flag > flag0 then
        s2exp_sel_srt (s2e0.s2exp_srt, s2e_tup, i)
      else s2e0 // end of [if]
    end // end of [S2Esel]
  | S2Esize s2ze => let
      val flag0 = flag
      val s2ze = s2zexp_subst_flag (sub, s2ze, flag)
    in
      if flag > flag0 then s2exp_size s2ze else s2e0
    end // end of [S2Esize]
  | S2Esizeof s2e => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then s2exp_sizeof s2e else s2e0
    end // end of [S2Esizeof]
  | S2Etop (knd, s2e) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then
        s2exp_top_srt (s2e0.s2exp_srt, knd, s2e)
      else s2e0 // end of [if]
    end // end of [S2Etop]
  | S2Etup s2es => let
      val flag0 = flag
      val s2es = s2explst_subst_flag (sub, s2es, flag)
    in
      if flag > flag0 then
        s2exp_tup_srt (s2e0.s2exp_srt, s2es)
      else s2e0 // end of [if]
    end // end of [S2Etup]
  | S2Etyarr (s2e_elt, s2ess_dim) => let
      val flag0 = flag
      val s2e_elt = s2exp_subst_flag (sub, s2e_elt, flag)
      val s2ess_dim = s2explstlst_subst_flag (sub, s2ess_dim, flag)
    in
      if flag > flag0 then s2exp_tyarr (s2e_elt, s2ess_dim) else s2e0
    end // end of [S2Etyarr]
  | S2Etyleq (knd, s2e1, s2e2) => let
      val flag0 = flag
      val s2e1 = s2exp_subst_flag (sub, s2e1, flag)
      val s2e2 = s2exp_subst_flag (sub, s2e2, flag)
    in
      if flag > flag0 then s2exp_tyleq (knd, s2e1, s2e2) else s2e0
    end // end of [S2Etyleq]
  | S2Etylst s2es => let
      val flag0 = flag
      val s2es = s2explst_subst_flag (sub, s2es, flag)
    in
      if flag > flag0 then s2exp_tylst s2es else s2e0
    end // end of [S2Etylst]
  | S2Etyrec (k, npf, ls2es) => let
      val flag0 = flag
      val ls2es = labs2explst_subst_flag (sub, ls2es, flag)
    in
      if flag > flag0 then
        s2exp_tyrec_srt (s2e0.s2exp_srt, k, npf, ls2es)
      else s2e0 // end of [if]
    end // end of [S2Etyrec]
  | S2Euni (s2vs, s2ps, s2e_body) => let
      val flag0 = flag
      val @(sub, s2vs) = stasub_extend_svarlst (sub, s2vs)
      val s2ps = s2explst_subst_flag (sub, s2ps, flag)
      val s2e_body = s2exp_subst_flag (sub, s2e_body, flag)
    in
      if flag > flag0 then s2exp_uni (s2vs, s2ps, s2e_body) else s2e0
    end // end of [S2Euni]
  | S2Eunion (stamp, s2e_ind, ls2es) => let
      val flag0 = flag
      val s2e_ind = s2exp_subst_flag (sub, s2e_ind, flag)
      val ls2es = labs2explst_subst_flag (sub, ls2es, flag)
    in
      if flag > flag0 then
        s2exp_union_srt (s2e0.s2exp_srt, stamp, s2e_ind, ls2es)
      else s2e0
    end // end of [S2Eunion]
  | S2Evar s2v => begin
      case+ s2var_subst (sub, s2v) of
      | ~Some_vt s2e => (flag := flag + 1; s2e) | ~None_vt () => s2e0
    end // end of [S2Evar]
  | S2EVar s2V => begin
      case+ s2Var_subst (sub, s2V) of
      | ~Some_vt s2e => s2e | ~None_vt () => s2e0
    end // end of [S2EVar]
  | S2Evararg s2e => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then s2exp_vararg (s2e) else s2e0
    end // end of [S2Evararg]
  | S2Ewth (s2e, wths2es) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
      val wths2es = wths2explst_subst_flag (sub, wths2es, flag)
    in
      if flag > flag0 then s2exp_wth (s2e, wths2es) else s2e0
    end // end of [S2Ewth]
end // end of [s2exp_subst_flag]

and s2explst_subst_flag {n:nat}
  (sub: stasub, s2es0: s2explst n, flag: &int): s2explst n =
  case+ s2es0 of
  | list_cons (s2e, s2es) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
      val s2es = s2explst_subst_flag (sub, s2es, flag)
    in
      if flag > flag0 then list_cons (s2e, s2es) else s2es0
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [s2explst_subst_flag]

and s2explstlst_subst_flag
  (sub: stasub, s2ess0: s2explstlst, flag: &int): s2explstlst =
  case+ s2ess0 of
  | list_cons (s2es, s2ess) => let
      val flag0 = flag
      val s2es = s2explst_subst_flag (sub, s2es, flag)
      val s2ess = s2explstlst_subst_flag (sub, s2ess, flag) 
    in
      if flag > flag0 then list_cons (s2es, s2ess) else s2ess0
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [s2explstlst_subst_flag]

and labs2explst_subst_flag
  (sub: stasub, ls2es0: labs2explst, flag: &int): labs2explst =
  case+ ls2es0 of
  | LABS2EXPLSTcons (l, s2e, ls2es) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
      val ls2es = labs2explst_subst_flag (sub, ls2es, flag)
    in
      if flag > flag0 then LABS2EXPLSTcons (l, s2e, ls2es) else ls2es0
    end // end of [LABS2EXPLSTcons]
  | LABS2EXPLSTnil () => LABS2EXPLSTnil ()
// end of [labs2explst_subst_flag]

and wths2explst_subst_flag
  (sub: stasub, wths2es0: wths2explst, flag: &int): wths2explst = begin
  case+ wths2es0 of
  | WTHS2EXPLSTcons_some (refval, s2e, wths2es) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
      val wths2es = wths2explst_subst_flag (sub, wths2es, flag)
    in
      if flag > flag0 then WTHS2EXPLSTcons_some (refval, s2e, wths2es)
      else wths2es0
    end // end of [WTHS2EXPLSTcons_some]
  | WTHS2EXPLSTcons_none (wths2es) => let
      val flag0 = flag
      val wths2es = wths2explst_subst_flag (sub, wths2es, flag)
    in
      if flag > flag0 then WTHS2EXPLSTcons_none wths2es else wths2es0
    end
  | WTHS2EXPLSTnil () => WTHS2EXPLSTnil ()
end // end of [wths2explst_subst_flag]

and s2eff_subst_flag
  (sub: stasub, s2fe0: s2eff, flag: &int): s2eff = begin
  case+ s2fe0 of
  | S2EFFset (efs, s2es) => let
      val flag0 = flag
      val s2es = s2explst_subst_flag (sub, s2es, flag)
    in
      if flag > flag0 then S2EFFset (efs, s2es) else s2fe0
    end // end of [S2EFFset]
  | _ => s2fe0 // end of [_]
end // end of s2eff_subst_flag

and s2lab_subst_flag
  (sub: stasub, s2l0: s2lab, flag: &int): s2lab = begin
  case+ s2l0 of
  | S2LAB0lab _ => s2l0
  | S2LAB0ind (s2ess(*ind*)) => let
      val flag0 = flag
      val s2ess = s2explstlst_subst_flag (sub, s2ess, flag)
    in
      if flag > flag0 then S2LAB0ind (s2ess) else s2l0
    end // end of [S2LAB0ind]
  | S2LAB1lab (l, s2e) => let
      val flag0 = flag
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then S2LAB1lab (l, s2e) else s2l0
    end // end of [S2LAB1lab]
  | S2LAB1ind (s2ess(*ind*), s2e(*elt*)) => let
      val flag0 = flag
      val s2ess = s2explstlst_subst_flag (sub, s2ess, flag)
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > flag0 then S2LAB1ind (s2ess, s2e) else s2l0
    end // end of [S2LAB1ind]
end // end of [s2lab_subst_flag]

and s2zexp_subst_flag
  (sub: stasub, s2ze0: s2zexp, flag: &int): s2zexp = begin
  case+ s2ze0 of
  | S2ZEapp (s2ze_fun, s2zes_arg) => let
      val flag0 = flag
      val s2ze_fun = s2zexp_subst_flag (sub, s2ze_fun, flag)
      val s2zes_arg = s2zexplst_subst_flag (sub, s2zes_arg, flag)
    in
      if flag > flag0 then S2ZEapp (s2ze_fun, s2zes_arg) else s2ze0
    end
  | S2ZEbot _ => s2ze0
  | S2ZEcst _  => s2ze0
  | S2ZEextype _ => s2ze0
  | S2ZEptr () => s2ze0
  | S2ZEtyarr (s2ze_elt, s2ess_ind) => let
      val flag0 = flag
      val s2ze_elt = s2zexp_subst_flag (sub, s2ze_elt, flag)
      val s2ess_ind = s2explstlst_subst_flag (sub, s2ess_ind, flag)
    in
      if flag > flag0 then  S2ZEtyarr (s2ze_elt, s2ess_ind) else s2ze0
    end // end of[S2ZEtyarr]
  | S2ZEtyrec (knd, ls2zes) => let
      val flag0 = flag
      val ls2zes = labs2zexplst_subst_flag (sub, ls2zes, flag)
    in
      if flag > flag0 then S2ZEtyrec (knd, ls2zes) else s2ze0
    end // end of [S2ZEtyrec]
  | S2ZEunion (stamp, ls2zes) => let
      val flag0 = flag
      val ls2zes = labs2zexplst_subst_flag (sub, ls2zes, flag)
    in
      if flag > flag0 then S2ZEunion (stamp, ls2zes) else s2ze0
    end // end of [S2ZEunion]
  | S2ZEvar s2v => begin
      case+ s2var_subst (sub, s2v) of
      | ~Some_vt s2e => (flag := flag + 1; s2zexp_make_s2exp s2e)
      | ~None_vt () => s2ze0
    end // end of [S2ZEvar]
end // end of [s2zexp_subst_flag]

and s2zexplst_subst_flag
  (sub: stasub, s2zes0: s2zexplst, flag: &int): s2zexplst =
  case+ s2zes0 of
  | list_cons (s2ze, s2zes) => let
      val flag0 = flag
      val s2ze = s2zexp_subst_flag (sub, s2ze, flag)
      val s2zes = s2zexplst_subst_flag (sub, s2zes, flag)
    in
      if flag > flag0  then list_cons (s2ze, s2zes) else s2zes0
    end // end of [list_cons]
  | list_nil () => list_nil () // end of [list_nil]
// end of [s2zexplst_subst_flag]

and labs2zexplst_subst_flag
  (sub: stasub, ls2zes0: labs2zexplst, flag: &int): labs2zexplst =
  case+ ls2zes0 of
  | LABS2ZEXPLSTcons (l, s2ze, ls2zes) => let
      val flag0 = flag
      val s2ze = s2zexp_subst_flag (sub, s2ze, flag)
      val ls2zes = labs2zexplst_subst_flag (sub, ls2zes, flag)
    in
      if flag > flag0 then LABS2ZEXPLSTcons (l, s2ze, ls2zes) else ls2zes0
    end // end of [LABS2ZEXPLSTcons]
  | LABS2ZEXPLSTnil () => LABS2ZEXPLSTnil ()
// end of [labs2zexplst_subst_flag]

in

implement
s2explst_subst (sub, s2es0) =
  let var flag: int = 0 in s2explst_subst_flag (sub, s2es0, flag) end
// end of [s2explst_subst]

implement
s2explstlst_subst (sub, s2ess0) =
  let var flag: int = 0 in s2explstlst_subst_flag (sub, s2ess0, flag) end
// end of [s2explstlst_subst]

implement
s2expopt_subst
  (sub, os2e) = case+ os2e of
  | Some (s2e) => let
      var flag: int = 0
      val s2e = s2exp_subst_flag (sub, s2e, flag)
    in
      if flag > 0 then Some s2e else os2e
    end // end of [Some]
  | None () => None ()
// end of [s2expopt_subst]

implement
s2exp_subst (sub, s2e0) =
  let var flag: int = 0 in s2exp_subst_flag (sub, s2e0, flag) end
// end of [s2exp_subst]

end // end of [local]

implement
s2exp_alpha (s1v, s1v1, s2e) = let
  val sub = list_cons ((s1v, s2exp_var s1v1), list_nil ()) in
  s2exp_subst (sub, s2e)
end // end of [s2exp_alpha]

implement
s2explst_alpha (s1v, s1v1, s2es) = let
  val sub = list_cons ((s1v, s2exp_var s1v1), list_nil ()) in
  s2explst_subst (sub, s2es)
end // end of [s2explst_alpha]

(* ****** ****** *)

local

fun aux_s2exp (
  s2e0: s2exp, fvs: &s2varset_t
) : void =
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
      aux_s2exp (s2e_fun, fvs); aux_s2explst (s2es_arg, fvs)
    end
  | S2Echar _ => ()
  | S2Eclo (_, _fun) => aux_s2exp (_fun, fvs)
  | S2Ecrypt (s2e) => aux_s2exp (s2e, fvs)
  | S2Ecst _ => ()
  | S2Edatconptr (d2c, _arg) => aux_s2explst (_arg, fvs)
  | S2Edatcontyp (d2c, _arg) => aux_s2explst (_arg, fvs)
  | S2Eeff s2fe => aux_s2eff (s2fe, fvs)
  | S2Eeqeq (s2e1, s2e2) => begin
      aux_s2exp (s2e1, fvs); aux_s2exp (s2e2, fvs)
    end // end of [S2Eeqeq]
  | S2Eexi (s2vs, s2ps, s2e) => let
      var fvs1 = s2varset_nil
      val () = aux_s2explst (s2ps, fvs1)
      val () = aux_s2exp (s2e, fvs1)
      val () = fvs1 := s2varset_dels (fvs1, s2vs)
    in
      fvs := s2varset_union (fvs, fvs1)
    end // end of [S2Eexi]
  | S2Eextype (_(*name*), _arg) => aux_s2explstlst (_arg, fvs)
  | S2Efun (
      _(*funclo*), _(*lin*), s2fe, _(*npf*), _arg, _res
    ) => begin
      aux_s2eff (s2fe, fvs); aux_s2explst (_arg, fvs); aux_s2exp (_res, fvs)
    end // end of [S2Efun]
  | S2Eint _ => ()
  | S2Eintinf _ => ()
  | S2Elam (s2vs, s2e) => let
      var fvs1 = s2varset_nil
      val () = aux_s2exp (s2e, fvs1)
      val () = fvs1 := s2varset_dels (fvs1, s2vs)
    in
      fvs := s2varset_union (fvs, fvs1)
    end // end of [S2Elam]
  | S2Emetfn (_(*d2vopt*), s2es, s2e) => begin
      aux_s2explst (s2es, fvs); aux_s2exp (s2e, fvs)
    end
  | S2Emetlt (s2es1, s2es2) => begin
      aux_s2explst (s2es1, fvs); aux_s2explst (s2es2, fvs)
    end // end of [metlt]
(*
// HX-2010-12-04: inadequate design
  | S2Enamed _ => () // a named type must be closed
*)
  | S2Eout s2e => aux_s2exp (s2e, fvs)
  | S2Eproj (s2e(*ptr*), s2l(*lab*)) => begin
      aux_s2exp (s2e, fvs); aux_s2lab (s2l, fvs)
    end
  | S2Eread (_v, s2e) => begin
      aux_s2exp (_v, fvs); aux_s2exp (s2e, fvs)
    end // end of [S2Eread]
  | S2Erefarg (_, s2e) => aux_s2exp (s2e, fvs)
  | S2Esel (s2e, _) => aux_s2exp (s2e, fvs)
  | S2Esize s2ze => aux_s2zexp (s2ze, fvs)
  | S2Esizeof s2e => aux_s2exp (s2e, fvs)
  | S2Etop (_(*knd*), s2e) => aux_s2exp (s2e, fvs)
  | S2Etup s2es => aux_s2explst (s2es, fvs)
  | S2Etyarr (s2e_elt, s2ess_dim) => begin
      aux_s2exp (s2e_elt, fvs); aux_s2explstlst (s2ess_dim, fvs)
    end // end of [S2Etyarr]
  | S2Etyleq (_(*knd*), s2e1, s2e2) => begin
      aux_s2exp (s2e1, fvs); aux_s2exp (s2e2, fvs)
    end // end of [S2Etyleq]
  | S2Etylst s2es => aux_s2explst (s2es, fvs)
  | S2Etyrec (_(*knd*), _(*npf*), ls2es) => aux_labs2explst (ls2es, fvs)
  | S2Euni (s2vs, s2ps, s2e) => let
      var fvs1 = s2varset_nil
      val () = aux_s2explst (s2ps, fvs1)
      val () = aux_s2exp (s2e, fvs1)
      val () = fvs1 := s2varset_dels (fvs1, s2vs)
    in
      fvs := s2varset_union (fvs, fvs1)
    end // end of [S2Euni]
  | S2Eunion (_(*stamp*), s2e_ind, ls2es) => begin
      aux_s2exp (s2e_ind, fvs); aux_labs2explst (ls2es, fvs)
    end
  | S2Evar s2v => (fvs := s2varset_add (fvs, s2v))
  | S2EVar s2V => aux_s2Var (s2V, fvs)
  | S2Evararg s2e => aux_s2exp (s2e, fvs)
  | S2Ewth (s2e, wths2es) => begin
      aux_s2exp (s2e, fvs); aux_wths2explst (wths2es, fvs)
    end // end of [S2Ewth]
// end of [aux_s2exp]

and aux_s2explst (
  s2es: s2explst, fvs: &s2varset_t
) : void =
  case+ s2es of
  | list_cons (s2e, s2es) => begin
      aux_s2exp (s2e, fvs); aux_s2explst (s2es, fvs)
    end // end of [list_cons]
  | list_nil () => ()
// end of [aux_s2explst]

and aux_s2explstlst (
  s2ess: s2explstlst, fvs: &s2varset_t
) : void =
  case+ s2ess of
  | list_cons (s2es, s2ess) => begin
      aux_s2explst (s2es, fvs); aux_s2explstlst (s2ess, fvs)
    end // end of [list_cons]
  | list_nil () => ()
// end of [aux_s2explstlst]

and aux_labs2explst (
  ls2es: labs2explst, fvs: &s2varset_t
) : void =
  case+ ls2es of
  | LABS2EXPLSTcons (_(*lab*), s2e, ls2es) => begin
      aux_s2exp (s2e, fvs); aux_labs2explst (ls2es, fvs)
    end // end of [LABS2EXPLSTcons]
  | LABS2EXPLSTnil () => ()
// end of [aux_labs2explst]

and aux_wths2explst (
  wths2es: wths2explst, fvs: &s2varset_t
) : void =
  case+ wths2es of
  | WTHS2EXPLSTcons_some (_(*refval*), s2e, wths2es) => begin
      aux_s2exp (s2e, fvs); aux_wths2explst (wths2es, fvs)
    end // end of [WTHS2EXPLSTcons_some]
  | WTHS2EXPLSTcons_none (wths2es) => aux_wths2explst (wths2es, fvs)
  | WTHS2EXPLSTnil () => ()
// end of [aux_wths2explst]

and aux_s2eff (
  s2fe: s2eff, fvs: &s2varset_t
) : void = case+ s2fe of
  | S2EFFall _ => ()
  | S2EFFnil _ => ()
  | S2EFFset (_, s2es) => aux_s2explst (s2es, fvs)
// end of [aux_s2eff]

and aux_s2lab (
  s2l: s2lab, fvs: &s2varset_t
) : void = case+ s2l of
  | S2LAB0lab _ => ()
  | S2LAB0ind s2ess_ind => aux_s2explstlst (s2ess_ind, fvs)
  | S2LAB1lab (_, s2e) => aux_s2exp (s2e, fvs)
  | S2LAB1ind (s2ess_ind, s2e_elt) => begin
      aux_s2explstlst (s2ess_ind, fvs); aux_s2exp (s2e_elt, fvs)
    end // end of [S2LAB1ind]
// end of [aux_s2lab]

and aux_s2Var
  (s2V: s2Var_t, fvs: &s2varset_t): void =
  case+ s2Var_get_link s2V of
  | Some s2e => aux_s2exp (s2e, fvs) | None () => begin
      prerr_loc_interror (s2Var_get_loc s2V);
      prerr ": s2exp_freevars: s2V = "; prerr s2V; prerr_newline ();
      $Err.abort {void} ()
    end // end of [None]
// end of [aux_s2Var]

and aux_s2zexp
  (s2ze: s2zexp, fvs: &s2varset_t): void =
  case+ s2ze of
  | S2ZEapp (s2ze, s2zes) => begin
      aux_s2zexp (s2ze, fvs); aux_s2zexplst (s2zes, fvs)
    end // end of [S2ZEapp]
  | S2ZEbot () => ()
  | S2ZEcst _ => ()
  | S2ZEextype _ => ()
  | S2ZEptr () => ()
  | S2ZEtyarr (s2ze_elt, s2ess_dim) => begin
      aux_s2zexp (s2ze_elt, fvs); aux_s2explstlst (s2ess_dim, fvs)
    end // end of [S2ZEtyarr]
  | S2ZEtyrec (_(*knd*), ls2zes) => aux_labs2zexplst (ls2zes, fvs)
  | S2ZEunion (_(*stamp*), ls2zes) => aux_labs2zexplst (ls2zes, fvs)
  | S2ZEvar s2v => (fvs := s2varset_add (fvs, s2v))
// end of [aux_s2zexp]

and aux_s2zexplst
  (s2zes: s2zexplst, fvs: &s2varset_t): void =
  case+ s2zes of
  | list_cons (s2ze, s2zes) => begin
      aux_s2zexp (s2ze, fvs); aux_s2zexplst (s2zes, fvs)
    end // end of [list_cons]
  | list_nil () => ()
// end of [aux_s2zexplst]

and aux_labs2zexplst
  (ls2zes: labs2zexplst, fvs: &s2varset_t): void =
  case+ ls2zes of
  | LABS2ZEXPLSTcons (_(*lab*), s2ze, ls2zes) => begin
      aux_s2zexp (s2ze, fvs); aux_labs2zexplst (ls2zes, fvs)
    end // end of [LABS2ZEXPLSTcons]
  | LABS2ZEXPLSTnil () => ()
// end of [aux_labs2zexplst]

in

implement
s2exp_freevars (s2e) =
  let var fvs: s2varset_t = s2varset_nil in aux_s2exp (s2e, fvs); fvs end
// end of [s2exp_freevars]

end // end of [local]

(* ****** ****** *)

local

fun aux_s2exp
  (s2V0: s2Var_t, s2e: s2exp,
   ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst): void =
  case+ s2e.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
      aux_s2exp (s2V0, s2e_fun, ans, s2cs, s2vs);
      aux_s2explst (s2V0, s2es_arg, ans, s2cs, s2vs)
    end // end of [S2Eapp]
  | S2Echar _ => ()
  | S2Eclo (_(*knd*), s2e_fun) =>
      aux_s2exp (s2V0, s2e_fun, ans, s2cs, s2vs)
  | S2Ecrypt s2e => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Ecst s2c => let
      val sVs = s2cst_get_sVarset s2c in
      if s2Varset_ismem (sVs, s2V0) then (s2cs := S2CSTLSTcons (s2c, s2cs))
    end // end of [S2Ecst]
  | S2Edatconptr (d2c, s2es_arg) => begin
      aux_s2explst (s2V0, s2es_arg, ans, s2cs, s2vs)
    end
  | S2Edatcontyp (d2c, s2es_arg) => begin
      aux_s2explst (s2V0, s2es_arg, ans, s2cs, s2vs)
    end // end of [S2Edatcontyp]
  | S2Eeff s2fe => aux_s2eff (s2V0, s2fe, ans, s2cs, s2vs)
  | S2Eeqeq (s2e1, s2e2) => () where {
      val () = aux_s2exp (s2V0, s2e1, ans, s2cs, s2vs)
      val () = aux_s2exp (s2V0, s2e2, ans, s2cs, s2vs)
    } // end of [S2Eeqeq]
  | S2Eexi (_, s2ps, s2e) => () where {
      val () = aux_s2explst (s2V0, s2ps, ans, s2cs, s2vs)
      val () = aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
    } // end of [S2Eexi]
  | S2Eextype (_(*name*), _arg) =>
      aux_s2explstlst (s2V0, _arg, ans, s2cs, s2vs)
    // end of [S2Eextype]
  | S2Efun (
      _(*funclo*), _(*lin*), s2fe, _(*npf*), _arg, _res
    ) => () where {
      val () = aux_s2eff (s2V0, s2fe, ans, s2cs, s2vs)
      val () = aux_s2explst (s2V0, _arg, ans, s2cs, s2vs)
      val () = aux_s2exp (s2V0, _res, ans, s2cs, s2vs)
    } // end of [S2Efun]
  | S2Eint _ => ()
  | S2Eintinf _ => ()
  | S2Elam (_, s2e) => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Emetfn (
      _(*d2vopt*), s2es, s2e
    ) => () where {
      val () = aux_s2explst (s2V0, s2es, ans, s2cs, s2vs)
      val () = aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
    } // end of [S2Emetfn]
  | S2Emetlt (s2es1, s2es2) => begin
      aux_s2explst (s2V0, s2es1, ans, s2cs, s2vs);
      aux_s2explst (s2V0, s2es2, ans, s2cs, s2vs)
    end // end of [S2Emetlt]
(*
// HX-2010-12-04: inadequate design
  | S2Enamed _ => () // a named type should be closed
*)
  | S2Eout s2e => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Eproj (s2e, s2l) => begin
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs);
      aux_s2lab (s2V0, s2l, ans, s2cs, s2vs)
    end // end of [S2Eproj]
  | S2Eread (_v, s2e) => begin
      aux_s2exp (s2V0, _v, ans, s2cs, s2vs);
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
    end // end of [S2Eread]
  | S2Erefarg (_, s2e) => begin
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
    end // end of [S2Erefarg]
  | S2Esel (s2e, _) => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Esize s2ze => aux_s2zexp (s2V0, s2ze, ans, s2cs, s2vs)
  | S2Esizeof s2e => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Etop (_knd, s2e) => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Etup s2es => aux_s2explst (s2V0, s2es, ans, s2cs, s2vs)
  | S2Etyarr (s2e_elt, s2ess_dim) => begin
      aux_s2exp (s2V0, s2e_elt, ans, s2cs, s2vs);
      aux_s2explstlst (s2V0, s2ess_dim, ans, s2cs, s2vs)
    end // end of [S2Etyarr]
  | S2Etyleq (_knd, s2e1, s2e2) => begin
      aux_s2exp (s2V0, s2e1, ans, s2cs, s2vs);
      aux_s2exp (s2V0, s2e2, ans, s2cs, s2vs)
    end // end of [S2Etyleq]
  | S2Etylst s2es => aux_s2explst (s2V0, s2es, ans, s2cs, s2vs)
  | S2Etyrec (_knd, _npf, ls2es) => begin
      aux_labs2explst (s2V0, ls2es, ans, s2cs, s2vs)
    end // end of [S2Etyrec]
  | S2Euni (_, s2ps, s2e) => begin
      aux_s2explst (s2V0, s2ps, ans, s2cs, s2vs);
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
    end // end of [S2Euni]
  | S2Eunion (_stamp, s2e_ind, ls2es) => begin
      aux_s2exp (s2V0, s2e_ind, ans, s2cs, s2vs);
      aux_labs2explst (s2V0, ls2es, ans, s2cs, s2vs)
    end // end of [S2Eunion]
  | S2Evar s2v => aux_s2var (s2V0, s2v, ans, s2cs, s2vs)
  | S2EVar s2V => aux_s2Var (s2V0, s2V, ans, s2cs, s2vs)
  | S2Evararg s2e => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2Ewth (s2e, wths2es) => begin
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs);
      aux_wths2explst (s2V0, wths2es, ans, s2cs, s2vs)
    end // end of [S2Ewth]
// end of [aux_s2exp]

and aux_s2explst (
    s2V0: s2Var_t
  , s2es: s2explst
  , ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
  ) : void = begin case+ s2es of
  | list_cons (s2e, s2es) => begin
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs);
      aux_s2explst (s2V0, s2es, ans, s2cs, s2vs)
    end (* end of [list_cons] *)
  | list_nil () => ()
end // end of [aux_s2explst]

and aux_s2explstlst (
    s2V0: s2Var_t
  , s2ess: s2explstlst
  , ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
  ) : void = begin
  case+ s2ess of
  | list_cons (s2es, s2ess) => begin
      aux_s2explst (s2V0, s2es, ans, s2cs, s2vs);
      aux_s2explstlst (s2V0, s2ess, ans, s2cs, s2vs)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [aux_s2explstlst]

and aux_labs2explst (
    s2V0: s2Var_t
  , ls2es: labs2explst
  , ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
  ) : void = begin
  case+ ls2es of
  | LABS2EXPLSTcons (_(*lab*), s2e, ls2es) => begin
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs);
      aux_labs2explst (s2V0, ls2es, ans, s2cs, s2vs)
    end // end of [LABS2EXPLSTcons]
  | LABS2EXPLSTnil () => ()
end // end of [aux_labs2explst]

and aux_wths2explst
  (s2V0: s2Var_t, wths2es: wths2explst,
   ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst): void =
  case+ wths2es of
  | WTHS2EXPLSTcons_some (_(*refval*), s2e, wths2es) => begin
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs);
      aux_wths2explst (s2V0, wths2es, ans, s2cs, s2vs)
    end
  | WTHS2EXPLSTcons_none wths2es => begin
      aux_wths2explst (s2V0, wths2es, ans, s2cs, s2vs)
    end
  | WTHS2EXPLSTnil () => ()
// end of [aux_wths2explst]

and aux_s2eff (
  s2V0: s2Var_t
, s2fe: s2eff
, ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
) : void = begin case+ s2fe of
  | S2EFFall _ => ()
  | S2EFFnil _ => ()
  | S2EFFset (_, s2es) => aux_s2explst (s2V0, s2es, ans, s2cs, s2vs)
end // end of [aux_s2eff]

and aux_s2lab (
    s2V0: s2Var_t
  , s2l: s2lab
  , ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
  ) : void = begin
  case+ s2l of
  | S2LAB0lab _ => ()
  | S2LAB0ind (s2ess(*ind*)) => begin
      aux_s2explstlst (s2V0, s2ess, ans, s2cs, s2vs)
    end // end of [S2LAB0ind]
  | S2LAB1lab (_, s2e) => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | S2LAB1ind (s2ess(*ind*), s2e(*elt*)) => begin
      aux_s2explstlst (s2V0, s2ess, ans, s2cs, s2vs);
      aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
    end (* end of [S2LAB1ind] *)
end // end of [aux_s2lab]

and aux_s2var (
    s2V0: s2Var_t
  , s2v: s2var_t
  , ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
  ) : void = let
  val sVs = s2var_get_sVarset s2v in
  if s2Varset_ismem (sVs, s2V0)
    then (s2vs := list_cons (s2v, s2vs))
  // end of [if]
end // end of [aux_s2var]

and aux_s2Var (
    s2V0: s2Var_t
  , s2V: s2Var_t
  , ans: &int
  , s2cs: &s2cstlst
  , s2vs: &s2varlst
  ) : void = begin case+ s2Var_get_link s2V of
  | Some s2e => aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
  | None () => let
      val tst = eq_s2Var_s2Var (s2V0, s2V) in
      if tst then
        (ans := ans + 1)
      else let
        val sVs = s2Var_get_sVarset s2V in
        if s2Varset_ismem (sVs, s2V0) then (ans := ans + 1)
      end // end of [if]
    end (* end of [None] *)
end // end of [aux_s2Var]

and aux_s2zexp (
    s2V0: s2Var_t
  , s2ze: s2zexp
  , ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst
  ) : void = begin case+ s2ze of
  | S2ZEapp (s2ze_fun, s2zes_arg) => begin
      aux_s2zexp (s2V0, s2ze_fun, ans, s2cs, s2vs);
      aux_s2zexplst (s2V0, s2zes_arg, ans, s2cs, s2vs)
    end
  | S2ZEbot () => ()
  | S2ZEcst _ => ()
  | S2ZEextype _ => ()
  | S2ZEptr () => ()
  | S2ZEtyarr (s2ze_elt, s2ess_dim) => begin
      aux_s2zexp (s2V0, s2ze_elt, ans, s2cs, s2vs);
      aux_s2explstlst (s2V0, s2ess_dim, ans, s2cs, s2vs)
    end
  | S2ZEtyrec (_(*knd*), ls2zes) => begin
      aux_labs2zexplst (s2V0, ls2zes, ans, s2cs, s2vs)
    end
  | S2ZEunion (_(*stamp*), ls2zes) => begin
      aux_labs2zexplst (s2V0, ls2zes, ans, s2cs, s2vs)
    end
  | S2ZEvar s2v => aux_s2var (s2V0, s2v, ans, s2cs, s2vs)
end // end of [aux_s2zexp]

and aux_s2zexplst
  (s2V0: s2Var_t, s2zes: s2zexplst,
   ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst): void =
  case+ s2zes of
  | list_cons (s2ze, s2zes) => begin
      aux_s2zexp (s2V0, s2ze, ans, s2cs, s2vs);
      aux_s2zexplst (s2V0, s2zes, ans, s2cs, s2vs)
    end // end of [list_cons]
  | list_nil () => ()
// end of [aux_s2zexplst]

and aux_labs2zexplst
  (s2V0: s2Var_t, ls2zes: labs2zexplst,
   ans: &int, s2cs: &s2cstlst, s2vs: &s2varlst): void =
  case+ ls2zes of
  | LABS2ZEXPLSTcons (_(*lab*), s2ze, ls2zes) => begin
      aux_s2zexp (s2V0, s2ze, ans, s2cs, s2vs);
      aux_labs2zexplst (s2V0, ls2zes, ans, s2cs, s2vs)
    end (* end of [LABS2ZEXPLSTcons] *)
  | LABS2ZEXPLSTnil () => ()
// end of [aux_labs2zexplst]

in // in of [local]

implement
s2Var_s2exp_occurs
  (s2V0, s2e, s2cs, s2vs) = ans where {
  var ans: int = 0; val () = aux_s2exp (s2V0, s2e, ans, s2cs, s2vs)
} // end of [s2Var_s2exp_occurs]

end // end of [local]

(* ****** ****** *)

(* end of [ats_staexp2_util1.dats] *)
