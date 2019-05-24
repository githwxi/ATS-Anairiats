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
 * Copyright (C) 2002-2009 Hongwei Xi, Boston University
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

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "token.sats"
staload "symbol.sats"
staload "grammar.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

implement symbol_rulerhslst_postpend (x, rhss_new) = let
  val rhss0 = symbol_rulerhslst_get x
  val rhss1 = list_append (rhss0, rhss_new)
in
  symbol_rulerhslst_set (x, rhss1)
end // end of [symbol_rulerhslst_postpend]

(* ****** ****** *)

implement the_nrulerhs_get () = let
  val xs = the_rulelhslst_get ()
  fun loop1 (xs: List symbol_t, n: int): int =
    case+ xs of
    | list_cons (x, xs) => let
        val n = loop2 (rhss, n) where {
          val rhss = symbol_rulerhslst_get x
          fun loop2 (rhss: rulerhslst, n: int): int =
            case+ rhss of
            | list_cons (rhs, rhss) => loop2 (rhss, n+1)
            | list_nil () => n
          // end of [loop2]
        } // end of [val]
      in
        loop1 (xs, n)
      end // end of [list_cons]
    | list_nil () => n
  // end of [loop1]
in
  loop1 (xs, 0)
end // end of [the_nrulerhs_get]

(* ****** ****** *)

local

assume rulerhs_t (n: int) = '{
  rulerhs_num= int
, rulerhs_nsym= int n
, rulerhs_symarr= array (symbol_t, n)
, rulerhs_prec= tokenopt
, rulerhs_extcode= tokenopt
} // end of [rulerhs]

in // end of [local]

implement rulerhs_num_get (rhs) = rhs.rulerhs_num

implement rulerhs_nsym_get (rhs) = rhs.rulerhs_nsym

implement rulerhs_symarr_get (rhs) = rhs.rulerhs_symarr

//

implement rulerhs_make {n} (num, nsym, symarr, prec, ext) = '{
  rulerhs_num= num
, rulerhs_nsym= nsym
, rulerhs_symarr= symarr
, rulerhs_prec= prec
, rulerhs_extcode= ext
} // end of [rulerhs_make]

end // end of [local]

(* ****** ****** *)

local

typedef symopt = Option (symbol_t)

val theStartSymRef = ref_make_elt<symopt> (None)

in // in of [local]

implement the_start_symbol_get () = case+ !theStartSymRef of
  | Some sym => sym | None () => begin
      prerr "error(ATSYACC): the start symbol of the grammar is unspecified.";
      prerr_newline ();
      exit {symbol_t} (1)
    end
// end of [the_start_symbol_get]

implement the_start_symbol_set (sym) = !theStartSymRef := Some sym

end // end of [local]

(* ****** ****** *)

local

typedef symlst = List (symbol_t)

val theRulelhslstRef = ref_make_elt<symlst> (list_nil)

in // in of [local]

implement the_rulelhslst_add (x) = 
  !theRulelhslstRef := list_cons (x, !theRulelhslstRef)

implement the_rulelhslst_get () = !theRulelhslstRef
implement the_rulelhslst_set (xs) = !theRulelhslstRef := xs

end // end of [local]

(* ****** ****** *)

implement the_start_rule_set () = let
  val lhs = the_accept_symbol
  val num = 0
  val nsym = 2
  val X0 = the_start_symbol_get ()
  val X1 = the_end_symbol
  val symarr = array_make_arrsz $arrsz (X0, X1)
  val prec = None ()
  val ext = None ()
  val rhs = rulerhs_make (num, nsym, symarr, prec, ext)
  val rhss = list_cons (rhs, list_nil ())
in
  symbol_rulerhslst_set (lhs, rhss)
end // end of [the_start_rule_set]

(* ****** ****** *)

implement fprint_rulerhs (pf_mod | out, rhs) = let
  val nsym = rulerhs_nsym_get (rhs)
  val symarr = rulerhs_symarr_get (rhs)
  var i: Nat // uninitialized
in
  for (i := 0; i < nsym; i := i + 1) let
    val () = if i > 0 then fprint_char (pf_mod | out, ' ')
  in
    fprint_symbol (pf_mod | out, symarr[i])
  end // end of [for]
end // end of [fprint_rulerhs]

//

fun fprint_indent {m:file_mode} {n:nat} (
    pf_mod: file_mode_lte (m, w) | out: &FILE m, nspace: int n
  ) : void = let
  var i: Nat (* uninitialized *) in
  for (i := 0; i < nspace; i := i+1) fprint_char (pf_mod | out, ' ')
end // end of [fprint_indent]

implement fprint_rulelhsrhss {m} (pf_mod | out, x) = let
  val nspace = int1_of_size1 (string1_length name) where {
    val name = symbol_name_get x; val name = string1_of_string (name)
  }
  fun loop (
      out: &FILE m
    , lhs: symbol_t, rhss: rulerhslst
    , i: int
    ) :<cloref1> void = begin case+ rhss of
    | list_cons (rhs, rhss) => let
        val () = if i = 0 then
          fprint_symbol (pf_mod | out, lhs)
        else
          fprint_indent (pf_mod | out, nspace)
        // end of [if]
        val () = if i = 0 then
          fprint1_string (pf_mod | out, "\t:\t")
        else
          fprint1_string (pf_mod | out, "\t|\t")
        // end of [if]
        val () = fprint_rulerhs (pf_mod | out, rhs)
        val () = fprint_char (pf_mod | out, '\n')
      in
        loop (out, lhs, rhss, i+1)
      end // end of [list_cons]
    | list_nil () => () where {
        val () = fprint_string (pf_mod | out, ";\n")
      } // end of [list_nil]
  end // end of [loop]
in
  loop (out, lhs, rhss, 0) where {
    val lhs = x and rhss = symbol_rulerhslst_get (x)
  } // end of [loop]
end // end of [fprint_rulelhsrhss]

//

implement fprint_rulelhsrhsslst {m}
  (pf_mod | out, xs) = loop (out, xs, 0) where {
  fun loop (out: &FILE m, xs: List symbol_t, i: int): void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_newline (pf_mod | out)
        val () = fprint_rulelhsrhss (pf_mod | out, x)
      in
        loop (out, xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [fprint_rulelhsrhsslst]

(* ****** ****** *)

(* end of [atsyacc_grammar.dats] *)
