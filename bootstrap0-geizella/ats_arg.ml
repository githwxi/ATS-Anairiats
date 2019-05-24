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

(* ats_arg: simple lexer for handling command line arguments *)

type arg_t = Key of int * string | Separator of int

let arg_parse (s: string): arg_t =
  let n = String.length s in
  let rec loop (i: int): arg_t = 
    if i < n then
      if (String.get s i == '-') then loop (i+1)
      else begin
        if i > 0 then Key (i, String.sub s i (n-i))
        else Key (0, s)
      end
    else Separator n in
    loop 0

let args_parse (argv: string array): arg_t list =
  let rec aux (i: int) (res: arg_t list): arg_t list =
    if i > 0 then (* the command name needs to be skipped *)
      aux (i-1) (arg_parse (Array.get argv (i-1)) :: res)
    else res in
    aux (Array.length argv) []

let arg_unparse (arg: arg_t): string = match arg with
  | Key (n, s) -> if n > 0 then (String.make n '-') ^ s else s
  | Separator n -> String.make n '-'

(* ****** ****** *)

(* end of [ats_arg.ml] *)
