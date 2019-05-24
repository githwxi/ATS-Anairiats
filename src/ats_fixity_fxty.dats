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
// Time: July 2007
//
(* ****** ****** *)

(* ats_fixity: for handing prefix, infix and postfix operators *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_fixity.sats"

(* ****** ****** *)

implement fprint_fxty
  (pf | out, fxty) = begin
  case+ fxty of
  | FXTYnon () => begin
      fprint1_string (pf | out, "FXTYnon()")
    end // end of [FXTYnon]
  | FXTYinf (p, a) => begin
      fprint1_string (pf | out, "FXTYinf(");
      fprint1_int (pf | out, (int_of_prec)p);
      fprint1_string (pf | out, ")")
    end // end of [FXTYinf]
  | FXTYpre (p) => begin
      fprint1_string (pf | out, "FXTYpre(");
      fprint1_int (pf | out, (int_of_prec)p);
      fprint1_string (pf | out, ")")
    end // end of [FXTYpre]
  | FXTYpos (p) => begin
      fprint1_string (pf | out, "FXTYpos(");
      fprint1_int (pf | out, (int_of_prec)p);
      fprint1_string (pf | out, ")")
    end // end of [FXTYpos]
end // end of [fprint_fxty]

implement print_fxty (fxty) = print_mac (fprint_fxty, fxty)
implement prerr_fxty (fxty) = prerr_mac (fprint_fxty, fxty)

(* ****** ****** *)

implement
fixity_get_prec
  (fxty) = case+ fxty of
  | FXTYnon () => None_vt ()
  | FXTYinf (p, _) => Some_vt (p)
  | FXTYpre p => Some_vt (p)
  | FXTYpos p => Some_vt (p)
// end of [fixity_get_prec]

implement fxty_non = FXTYnon ()
implement fxty_inf (p, a) = FXTYinf (p, a)
implement fxty_pre (p) = FXTYpre p
implement fxty_pos (p) = FXTYpos p

(* ****** ****** *)

implement
selptr_fixity_dyn = FXTYinf (select_prec, ASSOClft)

implement deref_fixity_dyn = FXTYpre (deref_prec_dyn)

(* ****** ****** *)

local

val app_assoc = ASSOClft (* left association *)

in // in of [local]

implement item_app f = ITEMopr (OPERinf (app_prec, app_assoc, f))

end // end of [local]

(* ****** ****** *)

implement
oper_make_backslash
  {a} (locf, appf) = let
  fn f1 (x: a):<cloref1> item a = let
    fn f2 (x1: a, x2: a):<cloref1> item a = let
      val loc = $Loc.location_combine (locf x1, locf x2)
    in
      ITEMatm (appf (loc, x, loc, '[x1, x2]))
    end // end of [f2]
  in
    ITEMopr (OPERinf (infixtemp_prec, ASSOCnon, f2))
  end // end of [f1]
in
  ITEMopr (OPERpre (backslash_prec, f1))
end // end of [oper_make_backslahsh]

(* ****** ****** *)

implement
oper_make {a}
  (locf, appf, opr, fx) = let
//
  val loc_opr = locf opr
//
  fn aux_inf
    (opr: a, p: prec_t, a: assoc):<cloref1> item a = let
    fn f (x1: a, x2: a):<cloref1> item a = let
      val loc = $Loc.location_combine (locf x1, locf x2)
    in
      ITEMatm (appf (loc, opr, loc, '[x1, x2]))
    end // end of [f]
  in
    ITEMopr (OPERinf (p, a, f))
  end // end of [aux_inf]
//
  fn aux_pre (opr: a, p: prec_t):<cloref1> item a = let
    fn f (x: a):<cloref1> item a = let
      val loc_x = locf x
      val loc = $Loc.location_combine (loc_opr, loc_x)
    in
      ITEMatm (appf (loc, opr, loc_x, '[x]))
    end // end of [f]
  in
    ITEMopr (OPERpre (p, f))
  end // end of [aux_pre]
//
  fn aux_pos (opr: a, p: prec_t):<cloref1> item a = let
    fn f (x: a):<cloref1> item a = let
      val loc_x = locf x
      val loc = $Loc.location_combine (loc_x, loc_opr)
    in
      ITEMatm (appf (loc, opr, loc_x, '[x]))
    end // end of [f]
  in
    ITEMopr (OPERpos (p, f))
  end // end of [aux_pos]
//
in 
//
  case+ fx of
  | FXTYnon () => ITEMatm (opr)
  | FXTYinf (p, a) => aux_inf (opr, p, a)
  | FXTYpre p => aux_pre (opr, p)
  | FXTYpos p => aux_pos (opr, p)
//
end // end of [oper_make]

(* ****** ****** *)

implement
oper_associativity opr = begin
  case+ opr of OPERinf (_, a, _) => a | _ => ASSOCnon ()
end // end of [oper_associativity]
        
implement
oper_precedence opr = begin case+ opr of
  | OPERinf (p, _, _) => p | OPERpre (p, _) => p | OPERpos (p, _) => p
end // end of [oper_precedence]

(* ****** ****** *)

(*
** HX: this is some code I originally wrote for implementing DML
*)

implement
fixity_resolve
  {a} (loc0, app, xs) = let
//
#define nil list_nil
#define cons list_cons
#define :: list_cons
//
fn err (
  loc: $Loc.location_t
) : a = let
  val () = $Loc.prerr_location (loc)
  val () = prerr ": error(1)"
  val () = prerr ": fixity cannot be resolved."
  val () = prerr_newline ()
in
  $Err.abort {a} ()
end // end of [err]
//
typedef I = item a and IS = List (item a)
//
(*
** HX: [fn*] for mutual tail-recursion
*)
fn* resolve (xs: IS, m: I, ys: IS)
  :<cloref1> a = begin case+ (xs, m, ys) of
  | (_, ITEMatm _, _) => begin case+ ys of
    | ITEMatm _ :: _ => resolve_app (xs, m, ys)
    | _ => pushup (xs, m :: ys)
    end // end of [begin]
  | (_, ITEMopr opr, _) => begin case+ (opr, ys) of
    | (OPERpre _, _) => pushup (xs, m :: ys)
    | (OPERinf _, _ :: nil ()) => pushup (xs, m :: ys)
    | (OPERinf _, _ :: ITEMopr opr1 :: _) => let
        val p = oper_precedence opr and p1 = oper_precedence opr1
      in
        case+ compare (p, p1) of
        |  1 => pushup (xs, m :: ys)
        | ~1 => reduce (m :: xs, ys)
        |  _ (* 0 *) => let
             val assoc = oper_associativity opr
             and assoc1 = oper_associativity opr1
           in
             case+ (assoc, assoc1) of
             | (ASSOClft (), ASSOClft ()) => reduce (m :: xs, ys)
             | (ASSOCrgt (), ASSOCrgt ()) => pushup (xs, m :: ys)
             | (_, _) => err (loc0)
           end // end of [_ (* 0 *)]
      end // end of [let]
    | (OPERpos _, _ :: ITEMopr opr1 :: _) => let
        val p = oper_precedence opr and p1 = oper_precedence opr1
      in
        case+ compare (p, p1) of
        |  1 => reduce (xs, m :: ys) | ~1 => reduce (m :: xs, ys)
        |  _ (* 0 *) => err (loc0)
      end // end of [let]
    | (OPERpos _, _ :: nil ()) => reduce (xs, m :: ys)
    | (_, _) => err (loc0)
    end // end of [_, ITEMopr, _]
end // end of [resolve]
//
and resolve_app
  (xs: IS, m: I, ys: IS):<cloref1> a = case+ ys of
  | _ :: ITEMopr opr1 :: _ => let
      val p1 = oper_precedence opr1
      val sgn = compare (app_prec, p1): Sgn
    in
      case+ sgn of
      | 1 => pushup (xs, m :: app :: ys) | ~1 => reduce (m :: xs, ys)
      | _ (*0*) => let
           val assoc1 = oper_associativity opr1 in case+ assoc1 of
             | ASSOClft () => reduce (m :: xs, ys) | _ => err (loc0)
         end // end of [_]
    end // end of [_ :: ITERMopr :: _]
  | _ :: nil () => pushup (xs, m :: app :: ys)
  | _ => err (loc0)
(* end of [resolve_app] *)
//
and reduce
  (xs: IS, ys: IS):<cloref1> a = case+ ys of
  | ITEMatm t :: ITEMopr (OPERpre (_, f)) :: ys =>
    pushup (f t :: xs, ys)
  | ITEMatm t1 :: ITEMopr (OPERinf (_, _, f)) :: ITEMatm t2 :: ys =>
    pushup (f (t2, t1) :: xs, ys)
  | ITEMopr (OPERpos (_, f)) :: ITEMatm t :: ys =>
    pushup (xs, f t :: ys)
  | _ => err (loc0)
(* end of [reduce] *)
//
and pushup (xs: IS, ys: IS):<cloref1> a = case+ (xs, ys) of
  | (nil (), ITEMatm t :: nil ()) => t
  | (nil (), ys) => reduce (nil (), ys)
  | (x :: xs, ys) => resolve (xs, x, ys)
(* end of [pushup] *)
//
in
//
pushup (xs, nil ())
//
end // end of [fixity_resolve]

(* ****** ****** *)

(* end of [ats_fixity_fxty.dats] *)
