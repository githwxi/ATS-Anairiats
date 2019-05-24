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

staload "atsyacc_top.sats"

(* ****** ****** *)

staload Sym = "symbol.sats"
staload Gra = "grammar.sats"

typedef symbol = $Sym.symbol_t
typedef rulerhs = $Gra.rulerhs_t
typedef rulerhslst = $Gra.rulerhslst

(* ****** ****** *)

implement theLHSarr_emit (out, xs) = let
  val () = fprint_string (out,  "\
val atsyacc_theLHSarr = array_make_arraysize $arrsz {int} (\n\
")

  val () = loop1 (xs, 0) where {
    typedef T = @(symbol, rulerhslst)
    fun loop1 (xs: List T, n: int):<cloref1> void =
      case+ xs of
      | list_cons (x, xs) => let
          val lhs = x.0 and rhss = x.1
(*
          val () = begin
            print "loop1: lhs = "; $Sym.print_symbol lhs; print_newline ()
          end // end of [val]
*)
          val ind = $Sym.symbol_index_get (lhs)
          val n = loop2 (rhss, n) where {
            fun loop2 
              (rhss: rulerhslst, n: int):<cloref1> int =
              case+ rhss of
              | list_cons (rhs, rhss) => let
                  val () = begin
                    if (n = 0) then fprint (out, "  ") else fprint (out, ", ")
                  end // end of [val]
                  val () = (fprint (out, ind); fprint (out, "\n"))
                in
                  loop2 (rhss, n+1)
                end // end of [list_cons]
              | list_nil () => n
            // end of [loop2]
          }
        in
          loop1 (xs, n)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop1]
  }

  val () = fprint_string (out, ") // end of [atsyacc_theLHSarr]\n")
in
  // empty
end // end of [theLHSarr_emit]

(* ****** ****** *)

implement theLENarr_emit (out, xs) = let
  val () = fprint_string (out,  "\
val atsyacc_theLENarr = array_make_arraysize $arrsz {int} (\n\
")

  val () = loop1 (xs, 0) where {
    typedef T = @(symbol, rulerhslst)
    fun loop1 (xs: List T, n: int):<cloref1> void =
      case+ xs of
      | list_cons (x, xs) => let
          val rhss = x.1
          val n = loop2 (rhss, n) where {
            fun loop2 
              (rhss: rulerhslst, n: int):<cloref1> int =
              case+ rhss of
              | list_cons (rhs, rhss) => let
                  val () = begin
                    if (n = 0) then fprint (out, "  ") else fprint (out, ", ")
                  end // end of [val]
                  val len = $Gra.rulerhs_nsym_get (rhs)
                  val () = (fprint (out, len); fprint (out, "\n"))
                in
                  loop2 (rhss, n+1)
                end // end of [list_cons]
              | list_nil () => n
            // end of [loop2]
          }
        in
          loop1 (xs, n)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop1]
  }

  val () = fprint_string (out, ") // end of [atsyacc_theLENarr]\n")
in
  // empty
end // end of [theLENarr_emit]

(* ****** ****** *)


(* end of [atsyacc_emit.dats] *)
