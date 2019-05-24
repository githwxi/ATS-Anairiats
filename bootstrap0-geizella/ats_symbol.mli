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

type symbol

val make_with_string : string -> symbol
val stamp_of : symbol -> int
val string_of : symbol -> string

val compare : symbol -> symbol -> int

val eq : symbol -> symbol -> bool
val neq : symbol -> symbol -> bool
val lt : symbol -> symbol -> bool
val lte : symbol -> symbol -> bool
val gt : symbol -> symbol -> bool
val gte : symbol -> symbol -> bool

val fprint : out_channel -> symbol -> unit
val fprint_list : out_channel -> symbol list -> unit

val prerr : symbol -> unit
val print : symbol -> unit

val empty : symbol

val symAMPER : symbol (* & *)
val symAMPERBANG : symbol (* &! *)
val symAT : symbol (* @ *)
val symBACKSLASH : symbol (* \ *)
val symBANG : symbol (* ! *)
val symDOT : symbol (* . *)
val symEQ : symbol (* = *)
val symQMARK : symbol (* ? *)
val symTILDA : symbol (* ~ *)
val symUNDERSCORE : symbol (* _ *)

val symCOLONEQ : symbol (* := *)
val symMINUSGT : symbol (* -> *)

val symANY : symbol

val symADDR : symbol
val symBOOL : symbol
val symCHAR : symbol
val symEXN : symbol
val symEFF : symbol
val symINT : symbol
val symPTR : symbol
val symRAT : symbol
val symREF : symbol
val symREG : symbol
val symSTRING : symbol

val symFLOAT : symbol
val symDOUBLE : symbol

val symPROP : symbol
val symTYPE : symbol
val symT0YPE : symbol
val symVIEW : symbol
val symVIEWTYPE : symbol
val symVIEWT0YPE : symbol

val symTYPES : symbol

val symSIZEOF : symbol
val symTOP : symbol
val symVBOX : symbol
val symVOID : symbol

val symADD : symbol
val symSUB : symbol
val symMUL : symbol
val symDIV : symbol
val symLT : symbol
val symLTE : symbol
val symGT : symbol
val symGTE : symbol
val symEQEQ : symbol
val symLTGT : symbol
val symGTLT : symbol

val symLTLT : symbol
val symGTGT : symbol

val symTRUE : symbol
val symFALSE : symbol
val symNULL : symbol

val symAND : symbol
val symOR : symbol

val symNAMESPACE : symbol

val symBRACKETS: symbol

(* ****** ****** *)

val symDEFINED: symbol
val symUNDEFINED: symbol

(* ****** ****** *)

val symDYNLOADFLAG: symbol

(* ****** ****** *)

val staload_symbol : symbol -> symbol

(* ****** ****** *)

module SymOrd: Map.OrderedType with type t = symbol

module SymMap: Map.S with type key = SymOrd.t

val sym_find : symbol -> 'a SymMap.t -> 'a option

(* end of [ats_symbol.mli] *)
