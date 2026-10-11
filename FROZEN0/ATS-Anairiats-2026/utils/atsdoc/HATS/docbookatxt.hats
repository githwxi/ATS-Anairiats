(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
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
// Start Time: September, 2011
//
(* ****** ****** *)

(*
** HX: help functions for writing docbook documents via [atsdoc]
*)

(* ****** ****** *)

#ifndef ATSDOC_DOCBOOKATXT
#define ATSDOC_DOCBOOKATXT 1

(* ****** ****** *)

#include "utils/atsdoc/HATS/xhtmlatxt.hats"

(* ****** ****** *)

macdef
bookinfo (x) = xmltagging ("bookinfo", ,(x))

macdef
articleinfo (x) = xmltagging ("articleinfo", ,(x))

(* ****** ****** *)

macdef title (x) = xmltagging ("title", ,(x))
macdef subtitle (x) = xmltagging ("subtitle", ,(x))

(* ****** ****** *)

macdef author (x) = xmltagging ("author", ,(x))
macdef firstname (x) = xmltagging ("firstname", ,(x))
macdef surname (x) = xmltagging ("surname", ,(x))

(* ****** ****** *)

macdef email (x)  = xmltagging ("email", ,(x))
macdef address (x)  = xmltagging ("address", ,(x))
macdef affiliation (x)  = xmltagging ("affiliation", ,(x))

(* ****** ****** *)

macdef copyright (x) = xmltagging ("copyright", ,(x))

(* ****** ****** *)

macdef abstract (x) = xmltagging ("abstract", ,(x))

(* ****** ****** *)
//
macdef code (x) = xmltagging ("code", ,(x))
macdef command (x) = xmltagging ("command", ,(x))
macdef emph (x) = xmltagging ("emphasis", ,(x))
macdef filename (x) = xmltagging ("filename", ,(x))
//
macdef para (x) = xmltagging ("para", ,(x))
macdef simplesect (x) = xmltagging ("simplesect", ,(x))
//
(* ****** ****** *)
//
macdef sub (x) = xmltagging ("subscript", ,(x))
macdef sup (x) = xmltagging ("superscript", ,(x))
//
(* ****** ****** *)

macdef member (x) = xmltagging ("member", ,(x))
macdef simplelist (x) = xmltagging ("simplelist", ,(x))

(* ****** ****** *)

macdef listitem (x) = xmltagging ("listitem", ,(x))
macdef orderedlist (x) = xmltagging ("orderedlist", ,(x))
macdef itemizedlist (x) = xmltagging ("itemizedlist", ,(x))

(* ****** ****** *)

macdef programlisting (x) = xmltagging ("programlisting", ,(x))
macdef informalexample (x) = xmltagging ("informalexample", ,(x))

(* ****** ****** *)

fun
ulink
  (link: string, name: string): atext = let
  val res = sprintf ("<ulink url=\"%s\">%s</ulink>", @(link, name))
in
  atext_strptr (res)
end // end of [ulink]

(* ****** ****** *)
//
local
//
val _opn = "\
<informalexample><programlisting><![CDATA[\
" // end of [val]
val _cls =
  "]]></programlisting></informalexample>\n"
// end of [val]
in
//
fun atscode
  (x: string): atext = atext_appstr3 (_opn, x, _cls)
//
fun atscodefil
  (path: string): atext = let
  val _opn = atext_strcst(_opn)
  val _code = atext_filepath (path)
  val _cls = atext_strcst(_cls)
in
  atext_apptxt3 (_opn, _code, _cls)
end // end of [atscodefil]
//
end // end of [local]
//
(* ****** ****** *)

#endif // end of [#ifndef(ATSDOC_DOCBOOKATXT)]

(* end of [docbookatxt.dats] *)
