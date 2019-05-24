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

open Ats_grammar

(* ****** ****** *)

let ats_keywords: (string * token) list = [

  (* symbolic keywords *)
  "&", AMPER;
  "`", BACKQUOTE;
  "!", BANG;
  "|", BAR;
  ":", COLON;
  "$", DOLLAR;
  ".", DOT;
  "=", EQ;
  "#", HASH;
  "~", TILDA;
  "..", DOTDOT;
  "...", DOTDOTDOT;
  "=>", EQGT; (* implication without decoration *)
  "=<", EQLT; (* implication decoration *)
  "=<>", EQLTGT; (* implication with empty decoration *)
  "=/=>", EQSLASHEQGT;
  "=>>", EQGTGT;
  "=/=>>", EQSLASHEQGTGT;
  "<", LT;
  ">", GT;
  "><", GTLT;
  ".<", DOTLT;
  ">.", GTDOT; (* .<...>. : metric *)
  ".<>.", DOTLTGTDOT;
  "->", MINUSGT; (* implication *)
  "-<", MINUSLT; (* -<...> : decorated implication *)
  "-<>", MINUSLTGT;
  ":<", COLONLT; (* :<...> : decorated implication *)
  ":<>", COLONLTGT;

  (* alphanumeric keywords *)
  "absprop", ABSPROP;
  "abstype", ABSTYPE;
  "absview", ABSVIEW;
  "absviewtype", ABSVIEWTYPE;
  "and", AND;
  "as", AS;
  "assume", ASSUME;
  "begin", BEGIN;
  "break", BREAK;
  "case", CASE;
  "castfn", CASTFN;
  "class", CLASS;
  "continue", CONTINUE;
  "datasort", DATASORT;
  "dataprop", DATAPROP;
  "datatype", DATATYPE;
  "dataview", DATAVIEW;
  "dataviewtype", DATAVIEWTYPE;
  "dyn", DYN;
  "dynload", DYNLOAD;
  "else", ELSE;
  "end", END;
  "exception", EXCEPTION;
  "export", EXPORT;
  "extern", EXTERN;
  "fix", FIX;
  "fn", FN;
  "for", FOR;
  "fun", FUN;
  "if", IF;
  "implement", IMPLEMENT;
  "in", IN;
  "infix", INFIX;
  "infixl", INFIXL;
  "infixr", INFIXR;
  "lam", LAM;
  "lampara", LAMPARA;
  "lazycase", LAZYCASE;
  "lazyif", LAZYIF;
  "lazyval", LAZYVAL;
  "let", LET;
  "llam", LLAM;
  "load", LOAD;
  "local", LOCAL;
  "macdef", MACDEF;
  "macrodef", MACRODEF;
  "method", METHOD;
  "modprop", MODPROP;
  "modtype", MODTYPE;
  "module", MODULE;
  "nonfix", NONFIX;
  "overload", OVERLOAD;
  "par", PAR;
  "postfix", POSTFIX;
  "praxi", PRAXI;
  "prefix", PREFIX;
  "prfn", PRFN;
  "prfun", PRFUN;
  "prval", PRVAL;
  "object", OBJECT;
  "of", OF;
  "op", OP;
  "propdef", PROPDEF;
  "rec", REC;
  "sif", SIF;
  "sortdef", SORTDEF;
  "staload", STALOAD;
  "sta", STA;
  "stadef", STADEF;
  "stavar", STAVAR;
  "struct", STRUCT;
  "symelim", SYMELIM;
  "symintr", SYMINTR;
  "then", THEN;
  "try", TRY;
  "typedef", TYPEDEF;
  "union", UNION;
  "val", VAL;
  "var", VAR;
  "viewdef", VIEWDEF;
  "viewtypedef", VIEWTYPEDEF;
  "when", WHEN;
  "where", WHERE;
  "while", WHILE;
  "with", WITH;
  "withprop", WITHPROP;
  "withtype", WITHTYPE;
  "withview", WITHVIEW;
  "withviewtype", WITHVIEWTYPE;
]

(* ****** ****** *)

let
ats_keyword_table
  : (string, token) Hashtbl.t =
  let tbl = Hashtbl.create 127 in
  let () = List.iter
    (function (kwd, tok) -> Hashtbl.add tbl kwd tok)
    ats_keywords in tbl
(* end of [ats_keyword_table] *)

(* ****** ****** *)

let
ats_keyword_find
  (s: string): token option =
  try Some (Hashtbl.find ats_keyword_table s)
  with Not_found -> None
(* end of [ats_keyword_find] *)

(* ****** ****** *)

(* end of [ats_keywords.ml] *)
