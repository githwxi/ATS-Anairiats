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
// Time: February 2008
//
(* ****** ****** *)

staload Err = "ats_error.sats"

staload Lab = "ats_label.sats"

staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

staload SymEnv = "ats_symenv.sats"
staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_symenv.dats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

fn prerr_loc_error2 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(2)")
// end of [prerr_loc_error2]

fn prerr_interror () =
  prerr ": INTERNAL ERROR (ats_dynexp2_util)"
// end of [prerr_interror]

(* ****** ****** *)

implement
d2var_readize (s2e_v, d2v) = let
  val () = d2var_set_lin (d2v, ~1) // nonlinear
  val () = d2var_set_mastyp (
    d2v, s2expopt_readize (s2e_v, d2var_get_mastyp (d2v))
  ) // end of [val]
  val () = d2var_set_typ (
    d2v, s2expopt_readize (s2e_v, d2var_get_typ (d2v))
  ) // end of [val]
in
  (* nothing *)
end // end of [d2var_readize]

implement
d2varlst_readize
  (s2e_v, d2vs) = begin
  case+ d2vs of
  | list_cons (d2v, d2vs) => begin
      d2var_readize (s2e_v, d2v); d2varlst_readize (s2e_v, d2vs)
    end (* end of [list_cons] *)
  | list_nil () => ()
end // end of [d2varlst_readize]

(* ****** ****** *)

implement
d2exp_is_varlamcst
  (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Evar _ => true
  | D2Elam_dyn _ => true
  | D2Echar _ => true
  | D2Eint _ => true
  | D2Efloat _ => true
  | D2Estring _ => true
  | D2Etop _ => true
  | _ => false
end // end of [d2exp_is_varlamcst]

(* ****** ****** *)

implement
d2exp_var_cst_is_ptr (d2e) = begin
  case+ d2e.d2exp_node of
  | D2Evar d2v => let
      val os2e = d2var_get_typ d2v in case+ os2e of
      | Some s2e => begin
          s2cstref_equ_exp (Ptr_addr_type, s2exp_whnf s2e)
        end // end of [Some]
      | None () => false
    end // end of [D2Evar]
  | D2Ecst d2c => let
      val s2e = d2cst_get_typ d2c in
      s2cstref_equ_exp (Ptr_addr_type, s2exp_whnf s2e)
    end // end of [D2Ecst]
  | _ => begin
      $Loc.prerr_location d2e.d2exp_loc;
      prerr_interror ();
      prerr ": d2exp_var_cst_is_ptr: d2e = "; prerr d2e; prerr_newline ();
      $Err.abort {bool} ()
    end // end of [_]
end // end of [d2exp_var_cst_is_ptr]

(* ****** ****** *)

fn d2exp_seq_is_raised
  (d2es: d2explst): bool = let
  fun loop (
    d2e: d2exp, d2es: d2explst
  ) : bool = case+ d2es of
    | list_cons (d2e, d2es) => loop (d2e, d2es)
    | list_nil () => d2exp_is_raised d2e
  // end of [loop]
in
  case+ d2es of
  | list_cons (d2e, d2es) => loop (d2e, d2es)
  | list_nil () => false
end // end of [d2exp_seq_is_raised]

fun c2laulst_is_raised
  (c2ls: c2laulst): bool = begin
  case+ c2ls of
  | list_cons (c2l, c2ls) => begin
      if c2lau_is_raised c2l then c2laulst_is_raised c2ls else false
    end // end of [list_cons]
  | list_nil () => true // end of [list_nil]
end // end of [c2laulst_is_raised]

implement
d2exp_is_raised (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eann_type (d2e, _) => d2exp_is_raised d2e
  | D2Eann_seff (d2e, _) => d2exp_is_raised d2e
  | D2Ecaseof (_, _, _, _, c2ls) => c2laulst_is_raised c2ls
  | D2Eif (_(*inv*), _(*cond*), d2e1, od2e2) => begin case+ od2e2 of
    | Some d2e2 => begin
        if d2exp_is_raised d2e1 then d2exp_is_raised d2e2 else false
      end // end of [Some]
    | None () => false // end of [None]
    end // end of [D2Eif]
  | D2Elet (d2cs, d2e) => d2exp_is_raised d2e
  | D2Eloopexn i => true
  | D2Eraise _ => true
  | D2Eseq d2es => d2exp_seq_is_raised d2es
  | D2Ewhere (d2e, _) => d2exp_is_raised d2e
  | _ => false
end // end of [d2exp_is_raise]

implement c2lau_is_raised (c2l) = begin
  if c2l.c2lau_neg > 0 then true else d2exp_is_raised c2l.c2lau_exp
end // end of [c2lau_is_raised]

(* ****** ****** *)

(* end of [ats_dynexp2_util.dats] *)
