(*
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Time: August, 2011
**
*)
//
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"
//
(* ****** ****** *)
//
#include "utils/atsdoc/HATS/xhtmlatxt.hats"
//
macdef para (x) = xmltagging ("p", ,(x))
macdef emph (x) = xmltagging ("em", ,(x))
//
(* ****** ****** *)
//
staload _(*anon*) = "libatsdoc/DATS/atsdoc_text.dats"
//
(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

#define s2s string_of_strptr

(* ****** ****** *)
//
macdef strcst (x) = TEXTstrcst ,(x)
macdef strsub (x) = TEXTstrsub ,(x)
//
fun strcst_of_strptr (x: strptr1): text = TEXTstrcst ((s2s)x)
fun strsub_of_strptr (x: strptr1): text = TEXTstrsub ((s2s)x)
//
(* ****** ****** *)

macdef command(x) = xmltagging ("pre", ,(x)) // <pre> ... </pre>

fn filename (x: string): text = let
  val opn = strcst"<span style=\"text-decoration: underline;\">"
  val cls = strcst"</span>"
in
  TEXTapptxt3 (opn, strsub(x), cls)
end // end of [filename]

(* ****** ****** *)

fn menu
  (itmlst: string): text = xmltagging ("ul", itmlst)
// end of [menu]

fn lisub
  (x: string): text = xmltagging ("li", x)
// end of [lisub]

fn litxt (x: text): text =
  TEXTapptxt3 (strcst"<li>", x, strcst"</li>")
// end of [litxt]

(* ****** ****** *)

fn HR (sz: int) =
  strcst_of_strptr (sprintf ("<hr style=\"background-color: #E0E0E0; height: %ipx;\"></hr>", @(sz)))
// end of [HR]

(* ****** ****** *)

fun uid (id: string, name: string): text =
  strcst_of_strptr (sprintf ("<a id=\"%s\">%s</a>", @(id, name)))
// end of [uid]

fun ulink (link: string, name: string): text =
  strcst_of_strptr (sprintf ("<a href=\"%s\">%s</a>", @(link, name)))
// end of [ulink]

fun ulink1 (link: string, name: string): text =
  strsub_of_strptr (sprintf ("<a href=\"%s\">%s</a>", @(link, name)))
// end of [ulink1]

(* ****** ****** *)

(* end of [pagenatxt.dats] *)
