(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software, Inc.
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
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: August, 2011
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload
LOC = "libatsdoc/SATS/libatsdoc_location.sats"
typedef location = $LOC.location
overload fprint with $LOC.fprint_location

(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_lexbuf.sats"

(* ****** ****** *)

staload "atsdoc_translate.sats"

(* ****** ****** *)

implement
docerr_make (loc, node) = '{
  docerr_loc= loc, docerr_node= node
} // end of [docerr_make]

(* ****** ****** *)

viewtypedef docerrlst_vt = List_vt (docerr)

(* ****** ****** *)

extern
fun the_docerrlst_get (n: &int? >> int): docerrlst_vt

(* ****** ****** *)

local

#define MAXLEN 100
#assert (MAXLEN > 0)
val the_length = ref<int> (0)
val the_docerrlst = ref<docerrlst_vt> (list_vt_nil)

in // in of [local]

implement
the_docerrlst_length () = !the_length

implement
the_docerrlst_clear
  () = () where {
  val () = !the_length := 0
  val () = () where {
    val (vbox pf | p) = ref_get_view_ptr (the_docerrlst)
    val () = list_vt_free (!p)
    val () = !p := list_vt_nil ()
  } // end of [val]
} // end of [the_docerrlst_clear]

implement
the_docerrlst_add
  (err) = () where {
  val n = let
    val (vbox pf | p) = ref_get_view_ptr (the_length)
    val n = !p
    val () = !p := n + 1
  in n end // end of [val]
  val () = if n < MAXLEN then let
    val (vbox pf | p) = ref_get_view_ptr (the_docerrlst)
  in
    !p := list_vt_cons (err, !p)
  end // end of [val]
} // end of [the_docerrlst_add]

implement
the_docerrlst_get
  (n) = xs where {
  val () = n := !the_length
  val () = !the_length := 0
  val (vbox pf | p) = ref_get_view_ptr (the_docerrlst)
  val xs = !p
  val xs = list_vt_reverse (xs)
  val () = !p := list_vt_nil ()
} // end of [the_docerrlst_get]

end // end of [local]

(* ****** ****** *)

extern
fun fprint_docerr (out: FILEref, err: docerr): void

implement
fprint_docerr
  (out, x) = let
  val loc = x.docerr_loc
  val () = fprint (out, loc)
in
//
case+ x.docerr_node of
//
| DE_EXTCODE_unclose () => () where {
    val () = fprintf (out, ": error(atsdoc)", @())
    val () = fprintf (out, ": the external code block is unclosed.", @())
    val () = fprint_newline (out)
  }
//
| DE_STRING_unclose () => () where {
    val () = fprintf (out, ": error(atsdoc)", @())
    val () = fprintf (out, ": the string argument is unclosed.", @())
    val () = fprint_newline (out)
  }
//
| DE_FUNARGLST_unclose () => () where {
    val () = fprintf (out, ": error(atsdoc)", @())
    val () = fprintf (out, ": the funarg list is not properly closed.", @())
    val () = fprint_newline (out)
  }
| DE_FUNRES_none () => () where {
    val () = fprintf (out, ": error(atsdoc)", @())
    val () = fprintf (out, ": the funres identifier is ill-formed.", @())
    val () = fprint_newline (out)
  }
| DE_FUNRES_unclose () => () where {
    val () = fprintf (out, ": error(atsdoc)", @())
    val () = fprintf (out, ": the optional funres is not properly closed.", @())
    val () = fprint_newline (out)
  }
(*
| _ => () where {
    val () = fprintf (out, ": error(lexing): unspecified", @())
    val () = fprint_newline (out)
  }
*)
//
end // end of [fprint_docerr]

implement
fprint_the_docerrlst
  (out) = let
  var n: int?
  val xs = the_docerrlst_get (n)
  fun loop (
    out: FILEref, xs: docerrlst_vt, n: int
  ) : int =
    case+ xs of
    | ~list_vt_cons (x, xs) => (
        fprint_docerr (out, x); loop (out, xs, n-1)
      ) // end of [list_vt_cons]
    | ~list_vt_nil () => n
  // end of [loop]
in
//
case+ xs of
| list_vt_cons _ => let
    prval () = fold@ (xs)
    val n = loop (out, xs, n)
    val () = if n > 0 then {
      val () = fprint_string
        (out, "There are possibly some additional errors.")
      val () = fprint_newline (out)
    } // end of [if]
  in
    // nothing
  end // end of [list_vt_cons]
| ~list_vt_nil () => ()
//
end // end of [fprint_the_docerrlst]

(* ****** ****** *)

implement
lexbufpos2_docerr (
  buf, pos0, pos1, node
) = let
  val loc = $LOC.location_make_pos_pos (pos0, pos1)
  val () = the_docerrlst_add (docerr_make (loc, node))
in
  // nothing
end // end of [lexbufpos2_docerr]

(* ****** ****** *)

(* end of [atsdoc_translate_error.dats] *)
