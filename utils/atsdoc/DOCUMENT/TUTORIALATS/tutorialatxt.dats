(*
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Time: August, 2011
**
*)
(* ****** ****** *)
//
// For write the TUTORIALATS book
//
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"
//
(* ****** ****** *)

#include "utils/atsdoc/HATS/docbookatxt.hats"

(* ****** ****** *)

macdef stacode (x) = xmltagging ("code", ,(x))
macdef dyncode (x) = xmltagging ("code", ,(x))

(* ****** ****** *)

macdef filename(x) =
  xmltagging ("filename", ,(x)) // italic
// end of [filename]

(* ****** ****** *)
//
macdef LI (x) = xmltagging ("listitem", ,(x))
//
fun itemizedlist
  (xs: atextlst): atext = let
  val sep = atext_newline ()
  val _itms = atext_concatxtsep (xs, sep)
  val _beg = atext_strcst "<itemizedlist>\n"
  val _end = atext_strcst "\n</itemizedlist>"
in
  atext_apptxt3 (_beg, _itms, _end)
end // end of [itemizedlist]
//
(* ****** ****** *)

#define MYDOCROOT "http://www.ats-lang.org/DOCUMENT"
(*
#define MYDOCROOT "http://www.cs.bu.edu/~hwxi/ATS/DOCUMENT"
*)

(* ****** ****** *)

fun mydoclink (
  path: string, linkname: string
) : atext = let
  val res = sprintf (
    "<ulink url=\"%s/TUTORIALATS/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  atext_strcst (res)
end // end of [mydoclink]

fun mycodelink (
  path: string, linkname: string
) : atext = let
  val res = sprintf (
    "<ulink url=\"%s/TUTORIALATS/CODE/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  atext_strcst (res)
end // end of [mydoclink]

fun myatsdoclink (
  path: string, linkname: string
) : atext = let
  val res = sprintf (
    "<ulink url=\"%s/ANAIRIATS/%s\">%s</ulink>", @(MYDOCROOT, path, linkname)
  ) // end of [val]
  val res = string_of_strptr (res)
in
  atext_strcst (res)
end // end of [myatsdoclink]

(* ****** ****** *)

local

val theCodeLst = ref<atextlst> (list_nil)

in // in of [local]

fun theCodeLst_add (x: atext) =
  !theCodeLst := list_cons (x, !theCodeLst)

fun theCodeLst_get (): atextlst = let
  val xs = list_reverse (!theCodeLst) in list_of_list_vt (xs)
end // end of [theCodeLst_get]

fun fprint_theCodeLst
  (out: FILEref): void = let
  fun loop (xs: atextlst, i: int):<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_newline (out)
        val () = fprint_atext (out, x)
      in
        loop (xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
in
  loop (theCodeLst_get (),  0)
end // end of [fprint_theCodeLst]

end // end of [local]

(* ****** ****** *)

fn atscode_extract
  (x: string): atext = let
  val () = theCodeLst_add (atext_strcst (x)) in atscode (x)
end // end of [atscode_extract]

(* ****** ****** *)

(* end of [tutorialatxt.dats] *)
