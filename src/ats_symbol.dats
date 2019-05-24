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
// Time: August 2007

(* ****** ****** *)

(* ats_symbol: implementing symbol table facilities for ATS *)

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload "ats_counter.sats"

(* ****** ****** *)

staload "ats_symbol.sats"
staload "ats_symtbl.sats"

(* ****** ****** *)

typedef symbol = '{ name= string, code= count_t }
assume symbol_t = symbol

(* ****** ****** *)

#define SYMTBLSZHNT 512

implement symbol_name (sym) = sym.name

local

val counter = counter_make ()
val symtbl = symtbl_make (SYMTBLSZHNT)

in // in of [local]

implement symbol_make_string name = let
(*
  val () = begin
    print "symbol_make_string: name = "; print name; print_newline ()
  end // end of [val]
*)
  val symopt = symtbl_search (symtbl, name)
in
  case+ symopt of
  | Some sym => sym // end of [Some]
  | None () => let
      val cnt = counter_getinc (counter)
      val sym: symbol = '{ name= name, code= cnt }
(*
      val () = begin
        print "symbol_make_string: sym = ";
        print_symbol_code sym;
        print_newline ()
      end // end of [val]
*)
    in
      symtbl_insert (symtbl, name, sym); sym
    end // end of [None]
end // end of [symbol_make_string]
 
end // end of [local]

(* ****** ****** *)

implement symbol_empty = symbol_make_string ""

(* various symbols *)

implement symbol_ADD = symbol_make_string "+" 
implement symbol_AMPERSAND = symbol_make_string "&"
implement symbol_AT = symbol_make_string "@"
implement symbol_BACKSLASH = symbol_make_string "\\"
implement symbol_BANG = symbol_make_string "!"
implement symbol_COLONEQ = symbol_make_string ":="
implement symbol_DIV = symbol_make_string "/" 
implement symbol_EQ = symbol_make_string "="
implement symbol_EQEQ = symbol_make_string "=="
implement symbol_FUN = symbol_make_string "fun"
implement symbol_GT = symbol_make_string ">"
implement symbol_GTEQ = symbol_make_string ">="
implement symbol_GTGT = symbol_make_string ">>"
implement symbol_GTLT = symbol_make_string "><"
implement symbol_LAND = symbol_make_string "&&"
implement symbol_LOR = symbol_make_string "||" 
implement symbol_LRBRACKETS = symbol_make_string "[]"
implement symbol_LT = symbol_make_string "<"
implement symbol_LTEQ = symbol_make_string "<="
implement symbol_LTLT = symbol_make_string "<<"
implement symbol_MINUSGT = symbol_make_string "->"
implement symbol_MINUSLTGT = symbol_make_string "-<>"
implement symbol_MUL = symbol_make_string "*" 
implement symbol_NEQ = symbol_make_string "<>"
implement symbol_NEQEQ = symbol_make_string "!="
implement symbol_QMARK = symbol_make_string "?" 
implement symbol_QMARKBANG = symbol_make_string "?!" 
implement symbol_SUB = symbol_make_string "-" 
implement symbol_TILDE = symbol_make_string "~"
implement symbol_UNDERSCORE = symbol_make_string "_"

implement symbol_FALSE = symbol_make_string "false"
implement symbol_TRUE = symbol_make_string "true"

implement symbol_DO = symbol_make_string "do"
implement symbol_FOR = symbol_make_string "for"
implement symbol_IF = symbol_make_string "if"
implement symbol_IN = symbol_make_string "in"
implement symbol_R0EAD = symbol_make_string "r@ead"
implement symbol_SIZEOF = symbol_make_string "sizeof"
implement symbol_STDIN = symbol_make_string "stdin"
implement symbol_TUPZ = symbol_make_string "tupz"
implement symbol_UNION = symbol_make_string "union"
implement symbol_VBOX = symbol_make_string "vbox"
implement symbol_WHILE = symbol_make_string "while"

(* macro expansion *)

implement symbol_DEFINED = symbol_make_string "defined"
implement symbol_UNDEFINED = symbol_make_string "undefined"
implement symbol_EVALMAC = symbol_make_string "evalmac"
implement symbol_LIFTMAC = symbol_make_string "liftmac"

implement symbol_IS_NIL = symbol_make_string "is_nil"
implement symbol_IS_CONS = symbol_make_string "is_cons"
implement symbol_TUP_HEAD = symbol_make_string "tup_head"
implement symbol_TUP_TAIL = symbol_make_string "tup_tail"

(* base sorts *)

implement symbol_ADDR = symbol_make_string "addr"
implement symbol_BOOL = symbol_make_string "bool"
implement symbol_CHAR = symbol_make_string "char"
implement symbol_CLS = symbol_make_string "cls"
implement symbol_EFF = symbol_make_string "eff"
implement symbol_EXN = symbol_make_string "exn"
implement symbol_INT = symbol_make_string "int"

(* base impredicative sorts *)

implement symbol_PROP = symbol_make_string "prop"
implement symbol_TYPE = symbol_make_string "type"
implement symbol_T0YPE = symbol_make_string "t@ype"
implement symbol_VIEW = symbol_make_string "view"
implement symbol_VIEWTYPE = symbol_make_string "viewtype"
implement symbol_VIEWT0YPE = symbol_make_string "viewt@ype"
implement symbol_TYPES = symbol_make_string "types"

(* ****** ****** *)

(*
//
// special variables for OOP
//
implement
symbol_SELF = symbol_make_string "self"
implement
symbol_MYCLS = symbol_make_string "mycls"
*)

(* ****** ****** *)
//
// staloading at run-time is needed or not
implement
symbol_ATS_STALOADFLAG =
  symbol_make_string "ATS_STALOADFLAG"
//
// dynloading at run-time is needed or not
implement
symbol_ATS_DYNLOADFLAG =
  symbol_make_string "ATS_DYNLOADFLAG"
//
implement
symbol_ATS_DYNLOADFUN_NAME =
  symbol_make_string "ATS_DYNLOADFUN_NAME"
//
(* ****** ****** *)
//
implement
symbol_ATSOPT_NAMESPACE =
  symbol_make_string "ATSOPT_NAMESPACE"
//
(* ****** ****** *)
//
implement
lt_symbol_symbol (sym1, sym2) =
  lt_count_count (sym1.code, sym2.code)
//
implement
lte_symbol_symbol (sym1, sym2) =
  lte_count_count (sym1.code, sym2.code)
//
implement
gt_symbol_symbol (sym1, sym2) =
  gt_count_count (sym1.code, sym2.code)
//
implement
gte_symbol_symbol (sym1, sym2) =
  gte_count_count (sym1.code, sym2.code)
//
implement
eq_symbol_symbol (sym1, sym2) =
  eq_count_count (sym1.code, sym2.code)
//
implement
neq_symbol_symbol (sym1, sym2) =
  neq_count_count (sym1.code, sym2.code)
//
implement
compare_symbol_symbol (sym1, sym2) =
  compare_count_count (sym1.code, sym2.code)
//
(* ****** ****** *)

implement symbol_hash (sym) = count_hash (sym.code)

(* ****** ****** *)

implement fprint_symbol (pf | out, sym) =
  fprint_string (pf | out, sym.name)

implement print_symbol (sym) = print_mac (fprint_symbol, sym)
implement prerr_symbol (sym) = prerr_mac (fprint_symbol, sym)

(* ****** ****** *)

implement fprint_symbol_code (pf | out, sym) = begin
  fprint_string (pf | out, sym.name);
  fprint_char (pf | out, '\(');
  fprint_count (pf | out, sym.code);
  fprint_char (pf | out, ')')
end // end of [fprint_symbol_code]

implement print_symbol_code (sym) = print_mac (fprint_symbol_code, sym)
implement prerr_symbol_code (sym) = prerr_mac (fprint_symbol_code, sym)

(* ****** ****** *)

(* end of [ats_symbol.dats] *)
