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

(* ats_symbol: implementing symbol table facilities for ATS *)

(* ****** ****** *)

open Ats_misc

module H = Hashtbl

(* ****** ****** *)

type symbol = int * string

let count: int ref = ref 0

let size_hint = 1024

let the_symbol_tbl : (string, int) H.t = H.create size_hint

let make_with_string name =
  try (H.find the_symbol_tbl name, name)
  with Not_found -> let i = !count in
    begin
      count := i+1; H.add the_symbol_tbl name i; (i, name)
    end

let stamp_of ((i, _): symbol) = i
let string_of ((_, s): symbol) = s

let compare ((i1, _): symbol) ((i2, _): symbol): int =
  if i1 < i2 then -1 else if i1 > i2 then 1 else 0

let eq ((i1, _): symbol) ((i2, _): symbol): bool = i1 == i2
let neq ((i1, _): symbol) ((i2, _): symbol): bool = i1 <> i2
let lt ((i1, _): symbol) ((i2, _): symbol): bool = i1 < i2
let lte ((i1, _): symbol) ((i2, _): symbol): bool = i1 <= i2
let gt ((i1, _): symbol) ((i2, _): symbol): bool = i1 > i2
let gte ((i1, _): symbol) ((i2, _): symbol): bool = i1 >= i2

(* ****** ****** *)

let fprint (out: out_channel) ((_, s): symbol): unit = fprint_string out s
let fprint_list (out: out_channel) (ids: symbol list): unit =
  fprint_list_with_sep fprint out ids ","

let prerr (x: symbol): unit = fprint stderr x
let print (x: symbol): unit = fprint stdout x

(* ****** ****** *)

let empty: symbol = make_with_string ""

let symAMPER: symbol = make_with_string "&"
let symAMPERBANG: symbol = make_with_string "&!"
let symAT: symbol = make_with_string "@"
let symBANG: symbol = make_with_string "!"
let symBACKSLASH: symbol = make_with_string "\\"
let symDOT: symbol = make_with_string "."
let symEQ: symbol = make_with_string "="
let symQMARK: symbol = make_with_string "?"
let symTILDA: symbol = make_with_string "~"
let symUNDERSCORE : symbol = make_with_string "_"

let symCOLONEQ: symbol = make_with_string ":="
let symMINUSGT: symbol = make_with_string "->"

let symANY: symbol = make_with_string "any"

let symADDR: symbol = make_with_string "addr"
let symBOOL: symbol = make_with_string "bool"
let symCHAR: symbol = make_with_string "char"
let symEFF: symbol = make_with_string "eff"
let symEXN: symbol = make_with_string "exn"
let symINT: symbol = make_with_string "int"
let symPTR: symbol = make_with_string "ptr"
let symRAT: symbol = make_with_string "rat" (* rational sort *)
let symREF: symbol = make_with_string "ref"
let symREG: symbol = make_with_string "reg"
let symSTRING: symbol = make_with_string "string"

let symDOUBLE: symbol = make_with_string "double"
let symFLOAT: symbol = make_with_string "float"

let symPROP: symbol = make_with_string "prop"

let symTYPE: symbol = make_with_string "type"
let symT0YPE: symbol = make_with_string "t@ype"

let symVIEW: symbol = make_with_string "view"

let symVIEWTYPE: symbol = make_with_string "viewtype"
let symVIEWT0YPE: symbol = make_with_string "viewt@ype"

let symTYPES: symbol = make_with_string "types"

let symSIZEOF : symbol = make_with_string "sizeof"
let symTOP : symbol = make_with_string "top"
let symVBOX : symbol = make_with_string "vbox"
let symVOID : symbol = make_with_string "void"

let symADD: symbol =  make_with_string "+"
let symSUB: symbol =  make_with_string "-"
let symMUL: symbol =  make_with_string "*"
let symDIV: symbol =  make_with_string "/"

let symLT: symbol =  make_with_string "<"
let symLTE: symbol =  make_with_string "<="
let symGT: symbol =  make_with_string ">"
let symGTE: symbol =  make_with_string ">="
let symEQEQ: symbol =  make_with_string "=="
let symLTGT: symbol =  make_with_string "<>"
let symGTLT: symbol =  make_with_string "><"

let symLTLT: symbol =  make_with_string "<<"
let symGTGT: symbol =  make_with_string ">>"

let symTRUE : symbol = make_with_string "true"
let symFALSE : symbol = make_with_string "false"
let symNULL : symbol = make_with_string "null"

let symAND: symbol =  make_with_string "&&"
let symOR: symbol =  make_with_string "||"

let symNAMESPACE: symbol = make_with_string "NAMESPACE"

let symBRACKETS: symbol =  make_with_string "[]"

(* ****** ****** *)

let symDEFINED: symbol = make_with_string "defined"
let symUNDEFINED: symbol = make_with_string "undefined"

(* ****** ****** *)

let symDYNLOADFLAG: symbol = make_with_string "ATS_DYNLOADFLAG"

(* ****** ****** *)

let staload_symbol (s: symbol): symbol =
  let (_(*name*), n) = s in make_with_string ("$" ^ n)

(* ****** ****** *)

module SymOrd: Map.OrderedType with type t = symbol = struct
  type t = symbol
  let compare = compare
end

module SymMap: Map.S with type key = SymOrd.t = Map.Make (SymOrd)

let sym_find k t = try Some (SymMap.find k t) with Not_found -> None

(* ****** ****** *)

(* end of [ats_symbol.ml] *)
