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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2007
//
(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_trans1_env.sats"
staload "ats_e1xp_eval.sats"

(* ****** ****** *)

typedef loc_t = $Loc.location_t
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

#define nil list_nil
#define cons list_cons

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol
overload prerr with $Loc.prerr_location

(* ****** ****** *)

fn is_debug (): bool = $Deb.debug_flag_get () > 0

(* ****** ****** *)

implement
v1al_is_true (v) = begin
  case+ v of
  | V1ALint i => i <> 0 // most common
  | V1ALstring s => string_isnot_empty s // 2nd most common
  | V1ALfloat f => f <> 0.0
  | V1ALchar c => c <> '\000'
  | V1ALcstsp _ => true // HX: always true
end // end of [v1al_is_true]

implement v1al_is_false (v) = ~v1al_is_true(v)

(* ****** ****** *)

fn e1xp_eval_errmsg_app
  (loc: loc_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval";
  prerr ": an identifier is expected here.";
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_errmsg_app]

fn e1xp_eval_errmsg_id
  (loc: loc_t, id: sym_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval";
  prerr ": unrecognized identifier: ";
  $Sym.prerr_symbol id;
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_errmsg_id]

fn e1xp_eval_errmsg_list
  (loc: loc_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval";
  prerr ": illegal list expression is used here.";
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_errmsg_list]

fn e1xp_eval_appid_errmsg_arity
  (loc: loc_t, opr: sym_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval_appid";
  prerr ": the arity of [";
  $Sym.prerr_symbol opr;
  prerr "] is mismatched.";
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_appid_errmsg_arity]

fn e1xp_eval_appid_errmsg_opr
  (loc: loc_t, opr: sym_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval_appid";
  prerr ": unrecognized operation: [";
  $Sym.prerr_symbol opr; prerr "]";
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_appid_errmsg_opr]

fn e1xp_eval_opr_errmsg
  (loc: loc_t, opr: sym_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval";
  prerr ": illegal argument(s) for [";
  $Sym.prerr_symbol opr; prerr "]";
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_opr_errmsg]

fn e1xp_eval_errmsg_undef
  (loc: loc_t): v1al = begin
  prerr loc;
  if is_debug () then prerr ": e1xp_eval";
  prerr ": undefined expression is used here.";
  prerr_newline ();
  $Err.abort ()
end // end of [e1xp_eval_errmsg_undef]

(* ****** ****** *)
//
// HX: it is assumed that [s] represents a valid integer
//
fun e1xp_eval_int (s: string): int = let
(*
  val () = begin
    print "e1xp_eval_int s = "; print s; print_newline ()
  end // end of [val]
*)
  val [n:int] s = string1_of_string (s) // no-op casting
//
  fun loop1 {i:nat | i <= n} .<n-i>.
    (sgn: int, s: string n, i: size_t i): int =
    if string_isnot_atend (s, i) then let
      val c0 = s[i]
    in
      if c0 <> '0' then begin
        sgn * loop2 (10(*base*), s, i+1, c0 - '0') // s = [1-9]...
      end else begin
        if string_isnot_atend (s, i+1) then let
          val c1 = s[i+1]
        in
          if char_isdigit (c1) then
            sgn * loop2 (8(*base*), s, i+2, c1 - '0') // s = 0...
          else
            sgn * loop2 (16(*base*), s, i+2, 0) // s = 0x... or s = 0X...
          // end of [if]
        end else begin
          0 // s = 0
        end // end of [if]
      end // end of [if]
    end else begin
      0 // empty string
    end // end of [if]
  // end of [loop1]
//
  and loop2 {i:nat | i <= n} .<n-i>. (
      base: int, s: string n, i: size_t i, res: int
    ) : int =
    if string_isnot_atend (s, i) then let
      val c = s[i]; val d = begin
        if char_isdigit c then c - '0' else
          10 + (if char_isupper c then c - 'A' else c - 'a' : int)
        // end of [if]
      end : int
    in
      loop2 (base, s, i+1, res * base + d)
    end else begin
      res (* loop2 returns *)
    end // end of [if]
  // end of [loop2]
//
in
//
  if string_isnot_atend (s, 0) then let
    val c0 = s[0]
  in
    if c0 <> '~' then loop1 (1(*sgn*), s, 0) else loop1 (~1(*sgn*), s, 1)
  end else begin
    0 // empty string represents 0
  end // end of [if]
//
end (* end of [e1xp_eval_int] *)

(* ****** ****** *)

fun e1xp_eval_defined
  (loc: loc_t, e: e1xp): v1al = begin
  case+ e.e1xp_node of
  | E1XPide id => V1ALint (i) where {
      val i = (case+ the_e1xpenv_find id of
        | ~Some_vt e => (case+ e.e1xp_node of E1XPundef () => 0 | _ => 1)
        | ~None_vt () => 0
      ) : int // end of [val]
    } // end of [E1XPide]
  | _ => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_DEFINED)
    end // end of [_]
end // end of [e1xp_eval_defined]

and e1xp_eval_undefined
  (loc: loc_t, e: e1xp): v1al = begin
  case+ e.e1xp_node of
  | E1XPide id => V1ALint (i) where {
      val i = (case+ the_e1xpenv_find id of
        | ~Some_vt e => (case+ e.e1xp_node of E1XPundef () => 1 | _ => 0)
        | ~None_vt () => 1
      ) : int // end of [val]
    } // end of [E1XPide]
  | _ => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_UNDEFINED)
    end // end of [_]
end // end of [e1xp_eval_undefined]
  
fun e1xp_eval_add (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) => V1ALfloat (f1 + f2)
  | (V1ALint i1, V1ALint i2) => V1ALint (i1 + i2)
  | (V1ALstring s1, V1ALstring s2) => V1ALstring (s1 + s2)
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_ADD)
    end // end of [(_, _)]
end // end of [e1xp_eval_add]

and e1xp_eval_sub (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) => V1ALfloat (f1 - f2)
  | (V1ALint i1, V1ALint i2) => V1ALint (i1 - i2)
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_SUB)
    end // end of [(_, _)]
end // end of [e1xp_eval_sub]

and e1xp_eval_mul (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) => V1ALfloat (f1 * f2)
  | (V1ALint i1, V1ALint i2) => V1ALint (i1 * i2)
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_MUL)
    end // end of [(_, _)]
end // end of [e1xp_eval_mul]

and e1xp_eval_div (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) => V1ALfloat (f1 / f2)
  | (V1ALint i1, V1ALint i2) => V1ALint (i1 / i2)
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_DIV)
    end // end of [(_, _)]
end // end of [e1xp_eval_div]

fun e1xp_eval_lt (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) =>
      if f1 < f2 then V1ALint 1 else V1ALint 0
  | (V1ALint i1, V1ALint i2) =>
      if i1 < i2 then V1ALint 1 else V1ALint 0
  | (V1ALstring s1, V1ALstring s2) =>
      if s1 < s2 then V1ALint 1 else V1ALint 0
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_LT)
    end // end of [(_, _)]
end // end of [e1xp_eval_lt]

and e1xp_eval_lteq (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) =>
      if f1 <= f2 then V1ALint 1 else V1ALint 0
  | (V1ALint i1, V1ALint i2) =>
      if i1 <= i2 then V1ALint 1 else V1ALint 0
  | (V1ALstring s1, V1ALstring s2) =>
      if s1 <= s2 then V1ALint 1 else V1ALint 0
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_LTEQ)
    end // end of [(_, _)]
end // end of [e1xp_eval_lteq]

and e1xp_eval_gt (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) =>
      if f1 > f2 then V1ALint 1 else V1ALint 0
  | (V1ALint i1, V1ALint i2) =>
      if i1 > i2 then V1ALint 1 else V1ALint 0
  | (V1ALstring s1, V1ALstring s2) =>
      if s1 > s2 then V1ALint 1 else V1ALint 0
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_GT)
    end // end of [(_, _)]
end // end of [e1xp_eval_gt]

and e1xp_eval_gteq (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALfloat f1, V1ALfloat f2) =>
      if f1 >= f2 then V1ALint 1 else V1ALint 0
  | (V1ALint i1, V1ALint i2) =>
      if i1 >= i2 then V1ALint 1 else V1ALint 0
  | (V1ALstring s1, V1ALstring s2) =>
      if s1 >= s2 then V1ALint 1 else V1ALint 0
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_GTEQ)
    end // end of [(_, _)]
end // end of [e1xp_eval_gteq]

and e1xp_eval_eq (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALint i1, V1ALint i2) =>
      if i1 = i2 then V1ALint 1 else V1ALint 0
  | (V1ALstring s1, V1ALstring s2) =>
      if s1 = s2 then V1ALint 1 else V1ALint 0
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_EQ)
    end // end of [(_, _)]
end // end of [e1xp_eval_eq]

and e1xp_eval_neq (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALint i1, V1ALint i2) =>
      if i1 <> i2 then V1ALint 1 else V1ALint 0
  | (V1ALstring s1, V1ALstring s2) =>
      if s1 <> s2 then V1ALint 1 else V1ALint 0
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_NEQ)
    end // end of [(_, _)]
end // end of [e1xp_eval_neq]

fun e1xp_eval_and (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALint i1, V1ALint i2) => begin
      if i1 = 0 then V1ALint 0
      else if i2 = 0 then V1ALint 0
      else V1ALint 1
    end // end of [V1ALint, V1ALint]
  | (V1ALstring s1, V1ALstring s2) => let
      val s1 = string1_of_string s1 and s2 = string1_of_string s2
    in
      if string_is_empty s1 then V1ALint 0
      else if string_is_empty s1 then V1ALint 0
      else V1ALint 1
    end // end of [V1ALstring, V1ALstring]
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_LAND)
    end // end of [(_, _)]
end // end of [e1xp_eval_and]

and e1xp_eval_or (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALint i1, V1ALint i2) => begin
      if i1 <> 0 then V1ALint 1
      else if i2 <> 0 then V1ALint 1
      else V1ALint 0
    end // end of [V1ALint, V1ALint]
  | (V1ALstring s1, V1ALstring s2) => let
      val s1 = string1_of_string s1 and s2 = string1_of_string s2
    in
      if string_isnot_empty s1 then V1ALint 1
      else if string_isnot_empty s2 then V1ALint 1
      else V1ALint 0
    end // end of [V1ALstring, V1ALstring]
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_LOR)
    end // end of [_, _]
end // end of [e1xp_eval_or]

(* arithmetic shift to the left *)
fun e1xp_eval_asl (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALint i1, V1ALint i2) => let
      val i2 = int1_of_int i2
      val () = // checking for nonnegativeness
        if (i2 < 0) then begin
          $Loc.prerr_location (loc);
          if is_debug () then prerr ": e1xp_eval";
          prerr ": the second argument of [<<] must be a natural number.";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [if]
      // end of [val]
      val () = assert (i2 >= 0) // redundant at run-time
    in
       V1ALint (i1 << i2)
    end // end of [(V1ALint _, V1ALint _)]
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_LTLT)
    end // end of [(_, _)]
end // end of [e1xp_eval_asl]

(* arithmetic shift to the right *)
and e1xp_eval_asr (
  loc: loc_t, e1: e1xp, e2: e1xp
) : v1al = let
  val v1 = e1xp_eval e1; val v2 = e1xp_eval e2
in
  case+ (v1, v2) of
  | (V1ALint i1, V1ALint i2) => let
      val i2 = int1_of_int i2
      val () = // checking for nonnegativeness
        if (i2 < 0) then begin
          $Loc.prerr_location (loc);
          if is_debug () then prerr ": e1xp_eval";
          prerr ": the second argument of [<<] must be a natural number.";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [if]
      // end of [val]
      val () = assert (i2 >= 0) // redundant at run-time
    in
      V1ALint (i1 >> i2)
    end // end of [(V1ALint _, V1ALint _)]
  | (_, _) => begin
      e1xp_eval_opr_errmsg (loc, $Sym.symbol_GTGT)
    end // end of [(_, _)]
end // end of [e1xp_eval_asr]

(* ****** ****** *)

fun e1xp_eval_appid
  (loc: loc_t, id: sym_t, es: e1xplst): v1al = let
(*
  val () = begin
    print "e1xp_eval_appid: id = "; $Sym.print_symbol id; print_newline ()
  end // end of [val]
*)
in
  if id = $Sym.symbol_DEFINED then begin case+ es of
    | cons (e, nil ()) => e1xp_eval_defined (loc, e)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_UNDEFINED then begin case+ es of
    | cons (e, nil ()) => e1xp_eval_undefined (loc, e)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_ADD then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_add (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_SUB then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_sub (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_MUL then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_mul (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_DIV then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_div (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_LT then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_lt (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_LTEQ then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_lteq (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_GT then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_gt (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_GTEQ then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_gteq (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_EQ then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_eq (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_EQEQ then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_eq (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_NEQ then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_neq (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_NEQEQ then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_neq (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_LAND then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_and (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_LOR then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_or (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_LTLT then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_asl (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else if id = $Sym.symbol_GTGT then begin case+ es of
    | cons (e1, cons (e2, nil ())) => e1xp_eval_asr (loc, e1, e2)
    | _ => e1xp_eval_appid_errmsg_arity (loc, id)
  end else begin
    e1xp_eval_appid_errmsg_opr (loc, id)
  end // end of [if]
end // end of [e1xp_eval_appid]

(* ****** ****** *)

implement
e1xp_eval (e0) = let
(*
  val () = begin
    print "e1xp_eval: e0 = "; print e0; print_newline ()
  end // end of [val]
*)
in
  case+ e0.e1xp_node of
  | E1XPapp (e, _(*loc_arg*), es) => (
      case+ e.e1xp_node of
      | E1XPide id => e1xp_eval_appid (e.e1xp_loc, id, es)
      | _ => e1xp_eval_errmsg_app e.e1xp_loc
    ) // end of [E1XPapp]
  | E1XPchar c => V1ALchar c
  | E1XPfloat f(*string*) => V1ALfloat (double_of f)
  | E1XPint (int: string) => V1ALint (e1xp_eval_int int)
  | E1XPide id => begin case+ the_e1xpenv_find id of
    | ~Some_vt e => e1xp_eval e
    | ~None_vt () => e1xp_eval_errmsg_id (e0.e1xp_loc, id)
    end // end of [E1XPide]
  | E1XPlist es => begin case+ es of
    | cons (e, nil ()) => e1xp_eval e
    | _ => e1xp_eval_errmsg_list (e0.e1xp_loc)
    end // end of [E1XPlist]
  | E1XPnone () => V1ALint 0
  | E1XPstring (s, _) => V1ALstring s
  | E1XPundef () => e1xp_eval_errmsg_undef (e0.e1xp_loc)
  | E1XPcstsp (cst) => V1ALcstsp (e0.e1xp_loc, cst)
end // end of [e1xp_eval]

(* ****** ****** *)

implement
e1xp_eval_if (knd, e) = begin
  case+ knd of $Syn.SRPIFKINDif _ => e1xp_eval (e)
  | $Syn.SRPIFKINDifdef _ => e1xp_eval_defined (e.e1xp_loc, e)
  | $Syn.SRPIFKINDifndef _ => e1xp_eval_undefined (e.e1xp_loc, e)
end // end of [e1xp_eval_if]

(* ****** ****** *)

implement
e1xp_make_v1al (loc, v) = // turning a value into an expr
  case+ v of
  | V1ALchar c => e1xp_char (loc, c)
  | V1ALfloat f =>
      let val s = tostring_double f in e1xp_float (loc, s) end
    // end of [V1ALfloat]
  | V1ALint i => let val s = tostring_int i in e1xp_int (loc, s) end
  | V1ALstring s => let
      val n = int_of_size (string_length s) in e1xp_string (loc, s, n)
    end // end of [V1ALstring]
  | V1ALcstsp (_(*loc*), cst) => e1xp_cstsp (loc, cst)
// end of [e1xp_make_v1al]

(* ****** ****** *)

(* end of [ats_e1xp_eval.dats] *)
