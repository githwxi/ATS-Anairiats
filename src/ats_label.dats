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
// Time: July 2007
//
(* ****** ****** *)

(* ats_label: handling labels *)

(* ****** ****** *)

staload "ats_symbol.sats"

(* ****** ****** *)

staload "ats_label.sats"

(* ****** ****** *)

datatype label = LABint of int | LABsym of symbol_t
assume label_t = label

(* ****** ****** *)

implement label_make_int i = LABint i
implement label_make_string s = LABsym (symbol_make_string s)
implement label_make_sym s = LABsym s

(* ****** ****** *)

implement label_get_sym (l) = case+ l of
  | LABsym s => Some_vt s | LABint _ => None_vt ()
// end of [label_get_sym]
 
implement label_get_int (l) = case+ l of
  | LABint i => Some_vt i | LABsym _ => None_vt ()
// end of [label_get_int]

(* ****** ****** *)

implement lt_label_label (lab1, lab2) = compare (lab1, lab2) < 0
implement lte_label_label (lab1, lab2) = compare (lab1, lab2) <= 0
implement gt_label_label (lab1, lab2) = compare (lab1, lab2) > 0
implement gte_label_label (lab1, lab2) = compare (lab1, lab2) >= 0

(* ****** ****** *)

implement
eq_label_label (lab1, lab2) =
  case+ (lab1, lab2) of
  | (LABint i1, LABint i2) => i1 = i2
  | (LABsym s1, LABsym s2) => s1 = s2
  | (_, _) => false
// end of [eq_label_label]

implement
neq_label_label (lab1, lab2) =
  case+ (lab1, lab2) of
  | (LABint i1, LABint i2) => i1 <> i2
  | (LABsym s1, LABsym s2) => s1 <> s2
  | (_, _) => true
// end of [neg_label_label]

(* ****** ****** *)

implement
compare_label_label (lab1, lab2) =
  case+ (lab1, lab2) of
  | (LABint i1, LABint i2) => compare (i1, i2)
  | (LABsym s1, LABsym s2) => compare (s1, s2)
  | (LABint _, LABsym _) => ~1
  | (LABsym _, LABint _) =>  1
// end of [compare_label_label]

(* ****** ****** *)

implement
fprint_label (pf | fil, lab) = begin
  case+ lab of
  | LABint i => fprint1_int (pf | fil, i)
  | LABsym s => fprint_symbol (pf | fil, s)
end // end of [fprint_label]

implement print_label (lab) = print_mac (fprint_label, lab)
implement prerr_label (lab) = prerr_mac (fprint_label, lab)

(* ****** ****** *)

(* end of [ats_label.dats] *)
