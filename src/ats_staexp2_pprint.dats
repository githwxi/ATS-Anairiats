(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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
// Start Time: September 2009
//
(* ****** ****** *)
//
// HX: pretty printing for static expressions
//
(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_staexp2_pprint.sats"

(* ****** ****** *)

fun _fpprint_s2exp {m:file_mode} (
    pf_mod: file_mode_lte (m, w) | out: &FILE m, s2e0: s2exp, n: int
  ) : void = let
  macdef prstr (s) = fprint1_string (pf_mod | out, ,(s))
in
  case+ s2e0.s2exp_node of
  | S2EVar s2V when n > 0 => let
      val os2e = s2Var_get_link s2V in case+ os2e of
      | Some s2e => _fpprint_s2exp (pf_mod | out, s2e, n-1)
      | None () => begin
          prstr "S2EVar("; fprint_s2Var (pf_mod | out, s2V); prstr ")"
        end // end of [None]
    end // end of [S2EVar when ...]
  | S2EVar s2V => begin
      prstr "S2EVar?("; fprint_s2Var (pf_mod | out, s2V); prstr ")"
    end // end of [S2EVar]
  | S2Evararg s2e => begin
      prstr "S2Evararg("; _fpprint_s2exp (pf_mod | out, s2e, n); prstr ")"
    end // end of [S2Evararg]
  | _ => fprint_s2exp (pf_mod | out, s2e0)
end // end of [_fpprint_s2exp]

(* ****** ****** *)

#define FPPRINT_S2EXP_DEPTH 99

implement fpprint_s2exp (out, s2e) = let
  val [l:addr] (vbox pf_fil | p_fil) = __cast (out) where {
    extern castfn __cast (x: FILEref): [l:addr] (vbox (FILE w @ l) | ptr l)
  } // end of [val]
in
  $effmask_ref (_fpprint_s2exp (file_mode_lte_w_w | !p_fil, s2e, FPPRINT_S2EXP_DEPTH))
end // end of [_]

implement pprint_s2exp (s2e) = fpprint_s2exp (stdout_ref, s2e)
implement pprerr_s2exp (s2e) = fpprint_s2exp (stderr_ref, s2e)

(* ****** ****** *)

(* end of [ats_staexp2_pprint.dats] *)
