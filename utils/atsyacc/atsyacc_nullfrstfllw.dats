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

staload "symbol.sats"
staload "grammar.sats"

(* ****** ****** *)

staload "atsyacc_top.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"

(* ****** ****** *)

fn test_nullability
  {n:int} {i0,ik:nat | i0 + ik <= n}
  (alpha: symarr n, i0: int i0, ik: int ik): bool = let
  fun loop {i:nat | i <= i0+ik} .<n-i>. (i: int i):<cloref1> bool =
    if i < i0 + ik then
      if symbol_nullable_get (alpha[i]) then loop (i+1) else false
    else begin
      true // loop returns
    end // end of [if]
in
  loop (i0)
end // end of [test_nullability]

(* ****** ****** *)

fun nullfrstfllw_process_rulerhs {n:nat}
  (lhs: symbol_t, rhs: rulerhs_t n, flag: &int): void = () where {
(*
  val () = begin
    print "nullfrstfllw_process_rule: rhs = "; print_rulerhs rhs; print_newline ()
  end // end of [val]
*)
  val x0 = lhs
  val n = rulerhs_nsym_get (rhs)
  val alpha = rulerhs_symarr_get (rhs)
(*
  val () = begin
    print "nullfrstfllw_process_rulerhs: lhs = "; print_symbol lhs; print_newline ()
  end // end of [val]
  val () = begin
    print "nullfrstfllw_process_rulerhs: nsym = "; print n; print_newline ()
  end // end of [val]
*)
  // part 1:
  val () = if ~(symbol_nullable_get lhs) then
    if test_nullability (alpha, 0, n) then let
      val () = flag := flag + 1 in symbol_nullable_set (x0, true)
    end // end of [if]
  // end of [if]
  // part 2:
  val () = loop1 (0, flag) where {
    fun loop1 {i:nat | i <= n}
      (i: int i, flag: &int):<cloref1> void = let
      // empty
    in
      if i < n then let
        val yi = alpha[i]
        val test = test_nullability (alpha, 0, i)
        // part 2.1:
        val () = if test then let
          val flag0 = flag
          val frstset_x0 = symbol_frstset_get (x0)
          val frstset_yi = symbol_frstset_get (yi)
        in
          symbolset_union_flag (frstset_x0, frstset_yi, flag)
        end // end of [if]
        // part 2.2:
        val test = test_nullability (alpha, i+1, n-i-1)
        val () = if test then let
          val flag0 = flag
          val fllwset_x0 = symbol_fllwset_get (x0)
          val fllwset_yi = symbol_fllwset_get (yi)
        in
          symbolset_union_flag (fllwset_yi, fllwset_x0, flag)
        end // end of [val]
        // part 2.3:
        val () = loop2 (i, i+1, flag) where {
          fun loop2 {i,j:nat | i < j; j <= n}
            (i: int i, j: int j, flag: &int):<cloref1> void = let
          in
            if j < n then let
              val test = test_nullability (alpha, i+1, j-i-1)
              val () = if test then let
                val flag0 = flag
                val yj = alpha[j]
                val fllwset_yi = symbol_fllwset_get (yi)
                val frstset_yj = symbol_frstset_get (yj)
              in
                symbolset_union_flag (fllwset_yi, frstset_yj, flag)
              end // end of [val]
            in
              loop2 (i, j+1, flag)
            end // end of [if]
          end // end of [loop2]
        } // end of [val]
      in
        loop1 (i+1, flag)
      end else begin
        () // loop1 exits
      end // end of [if]
    end // end of [loop1]
  } // end of [val]
} (* end of [nullfrstfllw_process_rulerhs] *)

fun nullfrstfllw_process_rulerhslst
  (lhs: symbol_t, rhss: rulerhslst, flag: &int): void =
  case+ rhss of
  | list_cons (rhs, rhss) => let
      val () = nullfrstfllw_process_rulerhs (lhs, rhs, flag)
    in
      nullfrstfllw_process_rulerhslst (lhs, rhss, flag)
    end // end of [list_cons]
  | list_nil () => ()
// end of [nullfrstfllw_process_rulerhslst]

(* ****** ****** *)

implement the_nullfrstfllw_table_gen () = let
  var flag: int? // uninitialized
  fun symlst_loop (xs: List symbol_t, flag: &int): void =
    case+ xs of
    | list_cons (x, xs) => let
        val rhss = symbol_rulerhslst_get (x)
        val () = nullfrstfllw_process_rulerhslst (x, rhss, flag)
      in
        symlst_loop (xs, flag)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [symlst_loop]
  val xs = the_rulelhslst_get ()
in
  while (true) let
    val () = flag := 0; val () = symlst_loop (xs, flag)
  in
    if flag = 0 then break
  end // end of [while]
end (* end of [the_nullfrstfllw_table_gen] *)

(* ****** ****** *)

(* end of [atsyacc_nullfrstfllw.dats] *)
