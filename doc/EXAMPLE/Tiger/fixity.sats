(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "PARCOMB/posloc.sats"

(* ****** ****** *)

datatype assoc = LeftAssoc | RightAssoc | NonAssoc

(* ****** ****** *)

local

typedef loc = location_t

in // in of [local]

datatype fixopr (a: type) =
  | Prefix (a) of (loc, int(*prec*), a -<cloref> a)
  | Infix (a) of (loc, int(*prec*), assoc, (a, a) -<cloref> a)
  | Postfix (a) of (loc, int(*prec*), a -<cloref> a)

end // end of [local]

(* ****** ****** *)

datatype fixitm (a: type) = 
  | FIXITMatm (a) of a | FIXITMopr (a) of fixopr a

(* ****** ****** *)

fun fixopr_loc_get {a:type} (opr: fixopr a):<> location_t

(* ****** ****** *)

fun fixity_resolve {a:type}
  (xs: List (fixitm a)): Option_vt a

(* ****** ****** *)

(* end of [fixity.sats] *)
