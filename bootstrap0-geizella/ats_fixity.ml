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

(* ats_fixity: for handing prefix, infix and postfix operators *)

open Ats_misc

module Err = Ats_error
module Loc = Ats_location
module Sym = Ats_symbol

(* ****** ****** *)

let error (s: string): 'a = begin
  fprint_string stderr "ats_fixity: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

type prec = int
type assoc = L | R | N

type fixity =
  | Nonfix
  | Infix of prec * assoc
  | Prefix of prec
  | Postfix of prec

let prec_of_int i = i

let app_prec = 70
let app_assoc = L

let backslash_prec = app_prec + 1

let select_prec = 80 (* .label is a postfix operator *)

let static_amper_prec = 1
let static_amper_fixity = Prefix static_amper_prec

let static_amperbang_prec = 1
let static_amperbang_fixity = Prefix static_amperbang_prec

let static_bang_prec = 1
let static_bang_fixity = Prefix static_bang_prec

let static_qmark_prec = app_prec - 1
let static_qmark_fixity = Postfix static_qmark_prec

let static_trans_prec = 0
let static_trans_fixity = Infix (static_trans_prec, N)

let dynamic_bang_prec = 100
let dynamic_bang_fixity = Prefix dynamic_bang_prec

type 'a oper = 
  | Prefixop of prec * ('a -> 'a item)
  | Infixop of prec * assoc * ('a -> 'a -> 'a item)
  | Postfixop of prec * ('a -> 'a item)
        
and 'a item = Atm of 'a | Opr of 'a oper

let app_item f = Opr (Infixop (app_prec, app_assoc, f))

let make_backslash_opr locf appf =
  let f (x: 'a): 'a item =
    let f' (x1: 'a) (x2: 'a): 'a item =
      let loc = Loc.combine (locf x1) (locf x2) in
        Atm (appf loc x [x1; x2]) in
      Opr (Infixop (0, N, f')) in
    Opr (Prefixop (backslash_prec, f))
(* end of [make_backslash_opr] *)

let make_opr locf appf opr fx =
  let loc = locf opr in

  let prefx (opr: 'a) (p: prec): 'a item =
    let f (x: 'a): 'a item =
      let loc = Loc.combine loc (locf x) in
        Atm (appf loc opr [x]) in
      Opr (Prefixop (p, f))

  and postfx (opr: 'a) (p: prec): 'a item =
    let f (x: 'a): 'a item =
      let loc = Loc.combine (locf x) loc in
        Atm (appf loc opr [x]) in
      Opr (Postfixop (p, f))

  and infx (opr: 'a) (p: prec) (a: assoc): 'a item =
    let f (x1: 'a) (x2: 'a): 'a item =
      let loc = Loc.combine (locf x1) (locf x2) in
        Atm (appf loc opr [x1; x2]) in
      Opr (Infixop (p, a, f)) in
    
    match fx with
       | Prefix p -> prefx opr p
       | Infix (p, a) -> infx opr p a
       | Postfix p -> postfx opr p
       | Nonfix -> Atm (opr)
(* end of [make_opr] *)

let associativity opr = match opr with
  | Prefixop _ -> N
  | Infixop (_, a, _) -> a
  | Postfixop _ -> N
        
let precedence opr = match opr with
  | Prefixop (p, _) -> p
  | Infixop (p, _, _) -> p
  | Postfixop (p, _) -> p

let resolve loc app xs =
  let err (): 'a = begin
    prerr_string Err.prompt; Loc.prerr loc;
    prerr_string ": fixity cannot be resolved.";
    prerr_newline (); Err.abort ();
  end in

  let rec res xs m ys = match (xs, m, ys) with
    | (xs, Atm _, ys) -> begin match ys with
        | Atm _ :: _ -> resapp xs m ys
        | _ -> nxt xs (m :: ys)
      end

    | (xs, Opr opr, ys) -> begin match (opr, ys) with
        | (Prefixop _, ys) -> nxt xs (m :: ys)
        | (Infixop _, _ :: Opr opr' :: _) ->
            let p = precedence opr and p' = precedence opr' in
              if (p > p') then nxt xs (m :: ys)
              else if (p' > p) then red (m :: xs) ys
              else begin match (associativity opr, associativity opr') with
                | (L, L) -> red (m :: xs) ys
		| (R, R) -> nxt xs (m :: ys)
		| (_, _) -> err ()
              end
        | (Infixop _, [_]) -> nxt xs (m :: ys)
        | (Postfixop _, _ :: Opr opr' :: _) ->
            let p = precedence opr
            and p' = precedence opr' in
              if (p > p') then red xs (m :: ys)
              else if (p' > p) then red (m :: xs) ys
              else err ()

        | (Postfixop _, [_]) -> red (xs) (m :: ys)
        | (_, _) -> err ()
      end

  and resapp xs m ys = match ys with
    | _ :: Opr opr' :: _ ->
        let p' = precedence opr' in
          if (app_prec > p') then nxt xs (m :: app :: ys)
            else if (p' > app_prec) then red (m :: xs) ys
            else begin match associativity opr' with
              | L -> red (m :: xs) ys
              | _ -> err ()
            end
    | [_] -> nxt xs (m :: app :: ys)
    | _ -> err ()
              
  and red xs ys = match (xs, ys) with
    | (xs, Atm t :: Opr (Prefixop (_, f)) :: ys) -> nxt ((f t) :: xs) ys
    | (xs, Atm t1 :: Opr (Infixop (_, _, f)) :: Atm t2 :: ys) -> nxt (f t2 t1 :: xs) ys
    | (xs, Opr (Postfixop (_, f)) :: Atm t :: ys) -> nxt xs (f t :: ys)
    | (_, _) -> err ()
          
  and nxt xs ys = match (xs, ys) with
    | ([], [Atm t]) -> t
    | ([], ys) -> red [] ys
    | (x :: xs, ys) -> res xs x ys in

    nxt xs []
(*end of [resolve] *)

(* ****** ****** *)

(* end of [ats_fixity.ml] *)
