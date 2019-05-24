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
staload Sym = "symbol.sats"
staload Gra = "grammar.sats"

(* ****** ****** *)

dynload "location.dats"
dynload "token.dats"
dynload "grammar.dats"
dynload "symbol.dats"
dynload "symbolset.dats"

dynload "libats/lex/lexing.dats"
dynload "atsyacc_lexer_lats.dats"
dynload "atsyacc_parser.dats"

dynload "atsyacc_nullfrstfllw.dats"

dynload "atsyacc_lrtable.dats"

dynload "atsyacc_emit.dats"

(* ****** ****** *)

extern fun the_allsym_initialize (): void = "atsyacc_the_allsym_initialize"

(* ****** ****** *)

extern fun the_nullable_print (): void

implement the_nullable_print () = loop (xs) where {
  val xs = $Gra.the_rulelhslst_get ()
  fun loop (xs: List $Sym.symbol_t): void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = begin
          print "nullable(";
          $Sym.print_symbol (x);
          print ") = ";
          print ($Sym.symbol_nullable_get x);
          print_newline ()
        end // end of [val]
      in
        loop (xs)
      end // end of 
    | list_nil () => ()
  // end of [loop]
} // end of [nullable_print]

(* ****** ****** *)

extern fun the_frstset_print (): void

implement the_frstset_print () = loop (xs) where {
  val xs = $Gra.the_rulelhslst_get ()
  fun loop (xs: List $Sym.symbol_t): void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = begin
          print "frstset(";
          $Sym.print_symbol (x);
          print ") = ";
          $Sym.print_symbolset ($Sym.symbol_frstset_get x);
          print_newline ()
        end // end of [val]
      in
        loop (xs)
      end // end of 
    | list_nil () => ()
  // end of [loop]
} // end of [frstset_print]

(* ****** ****** *)

extern fun the_fllwset_print (): void

implement the_fllwset_print () = loop (xs) where {
  val xs = $Gra.the_rulelhslst_get ()
  fun loop (xs: List $Sym.symbol_t): void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = begin
          print "fllwset(";
          $Sym.print_symbol (x);
          print ") = ";
          $Sym.print_symbolset ($Sym.symbol_fllwset_get x);
          print_newline ()
        end // end of [val]
      in
        loop (xs)
      end // end of 
    | list_nil () => ()
  // end of [loop]
} // end of [fllwset_print]

(* ****** ****** *)

implement main (argc, argv) = let
(*
  val () = gc_chunk_count_limit_max_set (~1) // infinite
*)
  val () = parse_from_stdin ()
(*
  val () = () where {
    val nrhs = $Gra.the_nrulerhs_get ()
    val () = begin
      print "The total number of rules is "; print nrhs; print_newline ()
    end // end of [val]
  } // end of [val]
*)

  val () = the_allsym_initialize () // create the array of terminal symbols

  val () = let
    val sym = $Gra.the_start_symbol_get () in
    prerr "the start symbol is: "; $Sym.prerr_symbol sym; prerr_newline ()
  end // end of [val]

  val () = $Gra.the_start_rule_set ()
  val () = $Gra.the_rulelhslst_add ($Sym.the_accept_symbol)

(*
  val () = () where {
    val x0 = $Sym.the_accept_symbol
    val xs = $Gra.the_rulelhslst_get ()
    val (pf_stdout | p_stdout) = stdout_get ()
    val () = $Gra.fprint_rulelhsrhss (file_mode_lte_w_w | !p_stdout, x0)
    val () = fprint_newline (file_mode_lte_w_w | !p_stdout)
    val () = $Gra.fprint_rulelhsrhsslst (file_mode_lte_w_w | !p_stdout, xs)
    val () = stdout_view_set (pf_stdout | (*none*))
  }
*)

  val () = begin
    prerr "the_nullfrstfllw_table_gen: bef"; prerr_newline ()
  end // end of [val]
  val () = the_nullfrstfllw_table_gen ()
  val () = begin
    prerr "the_nullfrstfllw_table_gen: aft"; prerr_newline ()
  end // end of [val]

(*
  val () = print "The nullablity table is given as follows:\n"
  val () = the_nullable_print ()
  val () = print "The firstset table is given as follows:\n"
  val () = the_frstset_print ()
  val () = print "The followset table is given as follows:\n"
  val () = the_fllwset_print ()
*)

  val () = the_lrtable_gen ()
  val () = the_lrstatelst_initialize ()
  val () = loop (sts) where {
    // print out all the generated states
    val sts = the_lrstatelst_get ()
    fun loop (sts: lrstatelst): void = case+ sts of
      | list_cons (st, sts) => let
          val () = print_lrstate (st); val () = print_newline ()
        in
          loop (sts)
        end // end of [list_cons]
      | list_nil () => () // loop exists
  } // end of [val]

  val () = () where {
    val xs = the_rulelhsrhsslst_get ()
    val () = theLHSarr_emit (stdout_ref, xs)
    val () = fprint_string (stdout_ref, "\n")
    val () = theLENarr_emit (stdout_ref, xs)
    val () = fprint_string (stdout_ref, "\n")
  } // end of [val]

in
end // end of [main]

(* ****** ****** *)

(* end of [atsyacc_main.dats] *)
