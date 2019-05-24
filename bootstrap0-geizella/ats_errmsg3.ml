(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

open Ats_syntax
open Ats_staexp2
open Ats_staexp2_util
open Ats_dynexp2

module P = Printf

module Cnt = Ats_counter
module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location

(* ****** ****** *)

type loc = Loc.location
type lab = Lab.label
type stamp = Cnt.count

(* ****** ****** *)

let arity_errmsg loc (i: int) = match i with
  | _ when i > 0 -> begin
      P.fprintf stderr "%a: too many function arguments.\n" Loc.fprint loc;
      Err.abort ();
    end
  | _ -> begin
      P.fprintf stderr "%a: too few function arguments.\n" Loc.fprint loc;
      Err.abort ();
    end

(* ****** ****** *)

let tyrec_kind_errmsg loc (k1: tyrec_kind) (k2: tyrec_kind) = begin
  P.fprintf stderr "%a: record kind mismatch.\n" Loc.fprint loc;
  Err.abort ();
end

let flatness_errmsg loc (k: tyrec_kind) = begin
  P.fprintf stderr "%a: flatness mismatch.\n" Loc.fprint loc;
  Err.abort ();
end

let pfarity_errmsg loc = begin
  P.fprintf stderr "%a: proof arity mismatch.\n" Loc.fprint loc;
  Err.abort ();
end

(* ****** ****** *)

let occur_check_errmsg loc (s2V: sVar2) (s2e: sexp2): 'a = begin
  P.fprintf stderr "%a: failure of occurrence check: <%a> in <%a>.\n"
    Loc.fprint loc fprint_sVar2 s2V fprint_sexp2 s2e;
  Err.abort ();
end

(* ****** ****** *)

let labdexp2_label_errmsg loc (l1: Lab.label) (l2: Lab.label) = begin
  P.fprintf stderr "%a: label mismatch: %a <> %a\n"
    Loc.fprint loc Lab.fprint l1 Lab.fprint l2;
  Err.abort ();
end

let labdexp2_length_errmsg loc (i: int) =
  if i > 0 then begin
    P.fprintf stderr "%a: too many labeled expressions.\n" Loc.fprint loc;
    Err.abort ();
  end else begin
    P.fprintf stderr "%a: too few labeled expressions.\n" Loc.fprint loc;
    Err.abort ();
  end

let labdexp2_vararg_length_errmsg loc (i: int) =
  if i > 0 then begin
    P.fprintf stderr "%a: too many variable arguments.\n" Loc.fprint loc;
    Err.abort ();
  end else begin
    P.fprintf stderr "%a: too few variable arguments.\n" Loc.fprint loc;
    Err.abort ();
  end

(* ****** ****** *)

let cla2_tr_errmsg loc (i: int) =
  if i > 0 then begin
    P.fprintf stderr "%a: too many patterns.\n" Loc.fprint loc;
    Err.abort ();
  end else begin
    P.fprintf stderr "%a: too few patterns.\n" Loc.fprint loc;
    Err.abort ();
  end

(* ****** ****** *)

let dvar2_nonlocal_errmsg loc (d2v: dvar2) =
  begin
    P.fprintf stderr
      "%a: the dynamic variable <%a> is nonlocal.\n"
      Loc.fprint loc fprint_dvar2 d2v;
    Err.abort ();
  end

(* ****** ****** *)

let deref_lintype_duplicate_errmsg loc (s2e: sexp2) =
  begin
    P.fprintf stderr
      "%a: a linear value of the type <%a> cannot be duplicated.\n"
      Loc.fprint loc fprint_sexp2 s2e;
    Err.abort ();
  end

(* ****** ****** *)

let assgn_lintype_discard_errmsg loc (s2e: sexp2) =
  begin
    P.fprintf stderr
      "%a: a linear value of the type <%a> cannot be discarded.\n"
      Loc.fprint loc fprint_sexp2 s2e;
    Err.abort ();
  end

let assgn_nontype_discard_errmsg loc (s2e: sexp2) =
  begin
    P.fprintf stderr
      "%a: a value of the view <%a> cannot be discarded.\n"
      Loc.fprint loc fprint_sexp2 s2e;
    Err.abort ();
  end

(* ****** ****** *)

let addr_assgn_no_viewat_errmsg loc (s2r: sexp2) (s2labs: slab2 list) =
  begin
    P.fprintf stderr
      "%a: there is no view at <%a%a> for assignment.\n"
      Loc.fprint loc fprint_sexp2 s2r fprint_slab2_list s2labs;
    Err.abort ();
  end

let dvar2_mut_assgn_no_viewat_errmsg loc (d2v_view: dvar2) =
  begin
    P.fprintf stderr
      "%a: there is no view in <%a> for assignment.\n"
      Loc.fprint loc fprint_dvar2 d2v_view;
    Err.abort ();
  end

(* ****** ****** *)

let addr_deref_no_viewat_errmsg loc (s2r: sexp2) (s2labs: slab2 list) =
  begin
    P.fprintf stderr
      "%a: there is no view at <%a%a> for dereference.\n"
      Loc.fprint loc fprint_sexp2 s2r fprint_slab2_list s2labs;
    Err.abort ();
  end

let dvar2_mut_deref_no_viewat_errmsg loc (d2v_view: dvar2) =
  begin
    P.fprintf stderr
      "%a: there is no view in <%a> for dereference.\n"
      Loc.fprint loc fprint_dvar2 d2v_view;
    Err.abort ();
  end

let dvar2_mut_deref_nontype_errmsg loc (d2v_view: dvar2) =
  begin
    P.fprintf stderr
      "%a: there is no view in <%a> for dereference.\n"
      Loc.fprint loc fprint_dvar2 d2v_view;
    Err.abort ();
  end

(* ****** ****** *)

let addr_probe_no_viewat_errmsg loc (s2r: sexp2) (s2labs: slab2 list) =
  begin
    P.fprintf stderr
      "%a: there is no view at <%a%a> for probe.\n"
      Loc.fprint loc fprint_sexp2 s2r fprint_slab2_list s2labs;
    Err.abort ();
  end

let dvar2_mut_probe_no_viewat_errmsg loc (d2v_view: dvar2) =
  begin
    P.fprintf stderr
      "%a: there is no view in <%a> for probe.\n"
      Loc.fprint loc fprint_dvar2 d2v_view;
    Err.abort ();
  end

(* ****** ****** *)

let pattern_match_is_redundant_errmsg loc =
  begin
    P.fprintf stderr
      "%a: error: redundant pattern match.\n" Loc.fprint loc;
    Err.abort ();
 end

let pattern_match_is_redundant_warnmsg loc =
  begin
    P.fprintf stderr
      "%a: warning: redundant pattern match.\n" Loc.fprint loc;
  end

(* ****** ****** *)

(* end of [ats_errmsg3.ml] *)
