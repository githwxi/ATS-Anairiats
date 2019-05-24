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

(* miscellanenous functions *)

(* ****** ****** *)

module BI = Big_int
module PR = Printf

(* ****** ****** *)

type intinf = BI.big_int

let intinf_zero = BI.zero_big_int
let intinf_unit = BI.unit_big_int
let intinf_neg_unit = BI.big_int_of_int (-1)
let intinf_of_int = BI.big_int_of_int

let intinf_is_zero i = BI.eq_big_int i BI.zero_big_int
let intinf_is_unit i = BI.eq_big_int i BI.unit_big_int

let intinf_is_pos i = BI.gt_big_int i BI.zero_big_int
let intinf_is_neg i = BI.lt_big_int i BI.zero_big_int

let string_of_intinf = BI.string_of_big_int
let int_of_intinf (i: intinf) = int_of_string (BI.string_of_big_int i)

let intinf_lt i1 i2 = BI.lt_big_int i1 i2
let intinf_lte i1 i2 = BI.le_big_int i1 i2
let intinf_gt i1 i2 = BI.gt_big_int i1 i2
let intinf_gte i1 i2 = BI.ge_big_int i1 i2

let intinf_eq i1 i2 = BI.eq_big_int i1 i2
let intinf_neq i1 i2 = not (BI.eq_big_int i1 i2)

(* ****** ****** *)

(* n1 and n2 are natural numbers *)
let rec gcd_nat (n1: int) (n2: int) =
  if n1 > 0 then gcd_nat (n2 mod n1) n1 else n2

(* i1 and i2 are integers *)
let gcd_int (i1: int) (i2: int) =
  if i1 >= 0 then begin
    if i2 >= 0 then gcd_nat i1 i2 else gcd_nat i1 (-i2)
  end else begin
    if i2 >= 0 then gcd_nat (-i1) i2 else gcd_nat (-i1) (-i2)
  end
(* end of [gcd_int] *)

(* ****** ****** *)

let is_digit (c: char) = ('0' <= c && c <= '9')
let is_lower (c: char) = ('a' <= c && c <= 'z')
let is_upper (c: char) = ('A' <= c && c <= 'Z')

let string_of_char_list (cs: char list): string =
  let n = List.length cs in
  let s = String.create n in
  let rec aux i cs = match cs with
    | [] -> s | c :: cs -> (String.set s i c; aux (i+1) cs) in
    aux 0 cs

(* ****** ****** *)

let string_explode s =
  let rec aux res k =
    if k >= 0 then aux (s.[k] :: res) (k-1) else res
  in aux [] (String.length s - 1)

(* ****** ****** *)

let char_is_digit (c: char): bool =
  '0' <= c && c <= '9'

let char_is_letter (c: char): bool =
  ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let char_is_underscore (c: char): bool = ('_' = c)

let hexdigit_of_int (i: int): char =
  if i >= 10 then Char.chr (Char.code 'a' + i - 10)
  else Char.chr (Char.code '0' + i)

let string_identifize (s: string): string =
  let n = String.length s in
  let sb = Buffer.create (3 * n) in
  let f c = match c with
    | _ when char_is_letter c -> Buffer.add_char sb c
    | _ when char_is_digit c -> Buffer.add_char sb c
    | _ when char_is_underscore c -> Buffer.add_char sb c
    | _ -> begin
      let i = Char.code c in
      let c1 = hexdigit_of_int (i / 16) in
      let c2 = hexdigit_of_int (i mod 16) in
	(Buffer.add_char sb '_';
	 Buffer.add_char sb c1;
	 Buffer.add_char sb c2)
    end in
  let () = String.iter f s in Buffer.contents sb

(* ****** ****** *)

let fprint_bool (out: out_channel) (b: bool) = PR.fprintf out "%b" b

let fprint_char (out: out_channel) (c: char) = output_char out c

let fprint_int (out: out_channel) (i: int) = PR.fprintf out "%i" i

let fprint_intinf
  (out: out_channel) (i: intinf) = begin
  PR.fprintf out "%s" (string_of_intinf i)
end (* end of [fprint_intinf] *)

let fprint_string (out: out_channel) (s: string) = output_string out s

let prerr_line (s: string): unit = (prerr_string s; prerr_newline ())

let fprint_list_with_sep f out xs sep =
  let rec aux x xs = match xs with
    | [] -> f out x | x' :: xs' ->
	(f out x; fprint_string out sep; aux x' xs') in
    match xs with [] -> () | x :: xs -> aux x xs

let fprint_intlist
  (out: out_channel) (ns: int list) =
  fprint_list_with_sep fprint_int out ns ","

(* ****** *)

let list_is_empty (xs: 'a list): bool =
  match xs with [] -> true | _ :: _ -> false

(* ****** *)

let opt_map (f: 'a -> 'b) (x: 'a option): 'b option =
  match x with None -> None | Some x -> Some (f x)

(* ****** *)

let rec list_nth (xs: 'a list) (i: int): 'a option =
  let rec aux xs i = match xs with
    | [] -> None
    | x :: xs -> if i > 0 then aux xs (i-1) else Some x in
    if i < 0 then None else aux xs i

let rec list_find_first
  (p: 'a -> bool) (xs: 'a list): 'a option = match xs with
    | [] -> None
    | x :: xs -> if p x then Some x else list_find_first p xs
(* end of [list_find_first] *)

(* ****** *)

exception UnavailabilityException

let error_of_unavailability (msg: string): 'a = begin
  prerr_string msg; prerr_newline (); raise UnavailabilityException
end (* end of [error_of_unavailability] *)
  
(* ****** *)

exception DeadCodeException

(* the function <deadcode> should never be executed at run-time! *)

let error_of_deadcode (msg: string): 'a = begin
  prerr_string msg; prerr_newline (); raise DeadCodeException
end (* end of [error_of_deadcode] *)

(* ****** ****** *)

(* end of [ats_misc.ml] *)
