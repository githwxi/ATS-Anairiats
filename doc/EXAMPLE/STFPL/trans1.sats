(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

//
// A typechecker for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//

(* ****** ****** *)

staload SYMBOL = "symbol.sats"
typedef sym = $SYMBOL.symbol_t

(* ****** ****** *)

staload POSLOC = "contrib/parcomb/SATS/posloc.sats"
typedef loc = $POSLOC.location_t

(* ****** ****** *)

staload ABSYN = "absyn.sats"

(* ****** ****** *)

datatype t1yp =
  | T1YPbase of sym
  | T1YPfun of (t1yp, t1yp)
  | T1YPtup of t1yplst
// end of [t1yp]

where t1yplst = List t1yp
  and t1ypopt = Option t1yp

fun fprint_t1yp (out: FILEref, t: t1yp): void 
fun fprint_t1yplst (out: FILEref, t: t1yplst): void 

fun print_t1yp (t: t1yp): void 
fun prerr_t1yp (t: t1yp): void 

overload print with print_t1yp
overload prerr with prerr_t1yp

(* ****** ****** *)

datatype e1xp_node =
  | E1XPann of (e1xp, t1yp)
  | E1XPapp of (e1xp, e1xp)
  | E1XPbool of bool
  | E1XPfix of (v1ar, v1arlst, e1xp)
  | E1XPif of (e1xp, e1xp, e1xpopt)
  | E1XPint of int
  | E1XPlam of (v1arlst, e1xp)
  | E1XPlet of (d1eclst, e1xp)
  | E1XPopr of ($ABSYN.opr, e1xplst)
  | E1XPproj of (e1xp, int)
  | E1XPstr of string
  | E1XPtup of e1xplst
  | E1XPvar of v1ar

and d1ec_node =
  | D1ECval of (bool(*isrec*), v1aldeclst)
// end of [d1ec_node]

where e1xp = '{
  e1xp_loc= loc
, e1xp_node= e1xp_node
, e1xp_typ= t1yp
} // end of [e1xp]

and e1xplst = List (e1xp)
and e1xpopt = Option (e1xp)

and v1ar = '{
  v1ar_loc= loc
, v1ar_nam= sym
, v1ar_typ= t1yp
, v1ar_def= e1xpopt
} // end of [v1ar]
and v1arlst = List (v1ar)

and d1ec = '{
  d1ec_loc= loc, d1ec_node= d1ec_node
}
and d1eclst = List (d1ec)

and v1aldec = '{
  v1aldec_loc= loc
, v1aldec_var= v1ar
, v1aldec_def= e1xp
}
and v1aldeclst = List (v1aldec)

(* ****** ****** *)

fun fprint_v1ar (out: FILEref, v: v1ar): void

fun fprint_e1xp (out: FILEref, e: e1xp): void

(* ****** ****** *)

fun v1ar_make (_: loc, _: sym, _: t1yp): v1ar

fun eq_v1ar_v1ar (x1: v1ar, x2: v1ar): bool = "eq_v1ar_v1ar"
overload = with eq_v1ar_v1ar

fun v1ar_def_set (x: v1ar, def: e1xpopt): void = "v1ar_def_set"

(* ****** ****** *)

fun e1xp_make_ann (_: loc, e: e1xp, t: t1yp): e1xp
fun e1xp_make_app (_: loc, e1: e1xp, e2: e1xp, t: t1yp): e1xp
fun e1xp_make_bool (_: loc, b: bool): e1xp
fun e1xp_make_fix (_: loc, f: v1ar, xs: v1arlst, body: e1xp, t: t1yp): e1xp
fun e1xp_make_if (_: loc, e1: e1xp, e2: e1xp, oe3: e1xpopt, t: t1yp): e1xp
fun e1xp_make_int (_: loc, i: int): e1xp
fun e1xp_make_lam (_: loc, xs: v1arlst, body: e1xp, t: t1yp): e1xp
fun e1xp_make_let (_: loc, decs: d1eclst, body: e1xp, t: t1yp): e1xp
fun e1xp_make_opr (_: loc, opr: $ABSYN.opr, es: e1xplst, t: t1yp): e1xp
fun e1xp_make_proj (_: loc, e: e1xp, i: int, t: t1yp): e1xp
fun e1xp_make_str (_: loc, s: string): e1xp
fun e1xp_make_tup (_: loc, es: e1xplst, t: t1yp): e1xp
fun e1xp_make_var (_: loc, x: v1ar): e1xp

fun v1aldec_make (_: loc, x: v1ar, def: e1xp): v1aldec
fun d1ec_make_val (_: loc, isrec: bool, vds: v1aldeclst): d1ec

(* ****** ****** *)

fun trans1_typ (_: $ABSYN.t0yp): t1yp
fun trans1_exp (_: $ABSYN.e0xp): e1xp

(* ****** ****** *)

(* end of [trans1.sats] *)
