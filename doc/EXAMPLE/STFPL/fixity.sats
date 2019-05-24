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

staload "contrib/parcomb/SATS/posloc.sats"

(* ****** ****** *)

datatype assoc = LeftAssoc | RightAssoc | NonAssoc

(* ****** ****** *)

local

typedef loc = location_t

in // in of [local]

datatype fixopr (a:type) =
  | Prefix (a) of (loc, int(*prec*), a -<cloref> a)
  | Infix (a) of (loc, int(*prec*), assoc, (a, a) -<cloref> a)
  | Postfix (a) of (loc, int(*prec*), a -<cloref> a)
// end of [fixopr]

end // end of [local]

fun fprint_fixopr {a:type} (out: FILEref, opr: fixopr a): void

(* ****** ****** *)

datatype fixitm (a:type) = 
  | FIXITMatm (a) of a | FIXITMopr (a) of fixopr a
// end of [fixitm]

fun fprint_fixitm {a:type} (out: FILEref, itm: fixitm a): void
fun fprint_fixitmlst {a:type} (out: FILEref, itms: List (fixitm a)): void

(* ****** ****** *)

fun fixopr_loc_get {a:type} (opr: fixopr a):<> location_t

(* ****** ****** *)

fun fixitm_make_app {a:type} (app: (a, a) -<cloref> a): fixitm a

(* ****** ****** *)

fun fixity_resolve {a:type}
  (app: fixitm a, xs: List (fixitm a)): Option_vt a
// end of [fixity_resolve]

(* ****** ****** *)

(* end of [fixity.sats] *)
