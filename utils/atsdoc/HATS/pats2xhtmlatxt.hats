(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustful Software, Inc.
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

#ifndef ATSDOC_PATS2XHTMLATXT
#define ATSDOC_PATS2XHTMLATXT 1

(* ****** ****** *)

#include "utils/atsdoc/HATS/xhtmlatxt.hats"

(* ****** ****** *)

fn patsyntax_style (): atext = atext_strcst("\
<style type=\"text/css\">\n\
  .patsyntax {color:#808080;background-color:#E0E0E0;}\n\
  .patsyntaxkeyword {color:#000000;font-weight:bold;}\n\
  .patsyntaxcomment {color:#787878;font-style:italic;}\n\
  .patsyntaxextcode {color:#A52A2A;}\n\
  .patsyntaxneuexp  {color:#800080;}\n\
  .patsyntaxstaexp  {color:#0000F0;}\n\
  .patsyntaxprfexp  {color:#603030;}\n\
  .patsyntaxdynexp  {color:#F00000;}\n\
  .patsyntaxstalab  {color:#0000F0;font-style:italic}\n\
  .patsyntaxdynlab  {color:#F00000;font-style:italic}\n\
  .patsyntaxdynstr  {color:#008000;font-style:normal}\n\
  .patsyntaxstacstdec  {text-decoration:none;}\n\
  .patsyntaxstacstuse  {color:#0000CF;text-decoration:underline;}\n\
  .patsyntaxdyncstdec  {text-decoration:none;}\n\
  .patsyntaxdyncstuse  {color:#B80000;text-decoration:underline;}\n\
  .patsyntaxdyncst_implement  {color:#B80000;text-decoration:underline;}\n\
  .patsyntax span.keyword {color:#000000;font-weight:bold;}\n\
  .patsyntax span.comment {color:#787878;font-style:italic;}\n\
  .patsyntax span.extcode {color:#A52A2A;}\n\
  .patsyntax span.neuexp  {color:#800080;}\n\
  .patsyntax span.staexp  {color:#0000F0;}\n\
  .patsyntax span.prfexp  {color:#603030;}\n\
  .patsyntax span.dynexp  {color:#F00000;}\n\
  .patsyntax span.stalab  {color:#0000F0;font-style:italic}\n\
  .patsyntax span.dynlab  {color:#F00000;font-style:italic}\n\
  .patsyntax span.dynstr  {color:#008000;font-style:normal}\n\
  .patsyntax span.stacstdec  {text-decoration:none;}\n\
  .patsyntax span.stacstuse  {color:#0000CF;text-decoration:underline;}\n\
  .patsyntax span.dyncstdec  {text-decoration:none;}\n\
  .patsyntax span.dyncstuse  {color:#B80000;text-decoration:underline;}\n\
  .patsyntax span.dyncst_implement  {color:#B80000;text-decoration:underline;}\n\
</style>\n\
")

(* ****** ****** *)

fn patscode_jquery_min_js (): atext = atext_strcst("\
<script\n\
type=\"text/javascript\"\n\
src=\"https://ajax.googleapis.com/ajax/libs/jquery/1.7.2/jquery.min.js\"\n\
></script>\n\
")

(* ****** ****** *)

fn patscode_tryit_bind_all_js (): atext = atext_strcst("\
<script\n\
type=\"text/javascript\"\n\
src=\"http://www.ats-lang.org/scripts/patscode_tryit_bind_all.js\"\n\
></script>\n\
")

(* ****** ****** *)

macdef para (x) = xmltagging ("p", ,(x))

(* ****** ****** *)

fn HR (sz: int): atext = let
  val str = sprintf ("<hr style=\"background-color: #E0E0E0; height: %ipx;\"></hr>", @(sz))
in
  atext_strptr (str)
end // end of [HR]

(* ****** ****** *)

fn sizeof
  (type: string): atext =
  atext_appstr3 ("sizeof&lt;", type, "&gt;")
// end of [tszof]

fn stacode
  (x: string): atext = let
  val _beg = atext_strcst"<span class=\"patsyntaxstaexp\">"
  val _end = atext_strcst"</span>"
in
  atext_apptxt3 (_beg, atext_strsub(x), _end)
end // end of [stacode]

fn prfcode
  (x: string): atext = let
  val _beg = atext_strcst"<span class=\"patsyntaxprfexp\">"
  val _end = atext_strcst"</span>"
in
  atext_apptxt3 (_beg, atext_strsub(x), _end)
end // end of [prfcode]

fn dyncode
  (x: string): atext = let
  val _beg = atext_strcst"<span class=\"patsyntaxdynexp\">"
  val _end = atext_strcst"</span>"
in
  atext_apptxt3 (_beg, atext_strsub(x), _end)
end // end of [dyncode]

(* ****** ****** *)

local

val theCount = ref<int> (0)

in // in of [local]

fn patscode_count_getinc (): int = let
  val n = !theCount in !theCount := n+1; n
end // end of [getinc]

fn patscode_count_reset (): void = !theCount := 0

end // end of [local]

(* ****** ****** *)

local

val thePrefix = ref<string> ("")

in // in of [local]

fn patscode_prefix_get (): string = !thePrefix
fn patscode_prefix_set (x: string): void = !thePrefix := x

end // end of [local]

(* ****** ****** *)

fn patscode_save (
  stadyn: int, code: string
) : Option (string) = let
//
val prfx = patscode_prefix_get ()
//
in
//
if prfx != "" then let
  val cnt = patscode_count_getinc ()
  val path = sprintf ("%s_%i", @(prfx, cnt))
  val path = string_of_strptr (path)
  val ext = (
    if stadyn = 0 then "sats" else "dats"
  ) : string // end of [val]
  val pathext = sprintf ("%s.%s", @(path, ext))
  val pathext = string_of_strptr (pathext)
  val out = open_file_exn (pathext, file_mode_w)
  val () = fprint_string (out, code)
  val () = close_file_exn (out)
in
  Some (path)
end else None () // end of [if]
//
end // end of [patscoded_save]

(* ****** ****** *)

fn pats2xhtmls
  (code: string): atext = let
//
val _beg = atext_strcst ("<pre class=\"patsyntax\">")
val _code = atext_strptr (string_pats2xhtmlize_bground (0(*stadyn*), code))
val _end = atext_strcst ("</pre>\n")
//
in
  atext_apptxt3 (_beg, _code, _end)
end // end of [pats2xhtmls]

fn pats2xhtmld
  (code: string): atext = let
//
val _beg = atext_strcst ("<pre class=\"patsyntax\">")
val _code = atext_strptr (string_pats2xhtmlize_bground (1(*stadyn*), code))
val _end = atext_strcst ("</pre>\n")
in
  atext_apptxt3 (_beg, _code, _end)
end // end of [pats2xhtmld]

(* ****** ****** *)

fn pats2xhtmld_save
  (code: string): atext = let
//
val _(*path*) =
  patscode_save (1(*stadyn*), code)
//
in
  pats2xhtmld (code)
end // end of [pats2xhtmld_save]

(* ****** ****** *)

fn pats2xhtmld_tryit
  (code: string): atext = let
val opt =
  patscode_save (1(*stadyn*), code)
val name = (
  case+ opt of
  | Some path => let
      val x = sprintf ("%s.dats", @(path)) in string_of_strptr (x)
    end // end of [Some]
  | None () => "TRYIT/patscode_tryit_nameless.dats"
) : string // end of [val]
//
val _beg = let
  val x = sprintf (
    "<pre class=\"patsyntax patscode_tryit\" name=\"%s\">", @(name)
  ) // end of [val]
in
  atext_strptr (x)
end // end of [val]
val _code = atext_strptr (string_pats2xhtmlize_bground (1(*stadyn*), code))
val _end = atext_strcst ("</pre>\n")
//
in
  atext_apptxt3 (_beg, _code, _end)
end // end of [pats2xhtmld_tryit]

(* ****** ****** *)

#endif // end of [ATSDOC_PATS2XHTMLATXT]

(* ****** ****** *)

(* end of [pats2xhtmlatxt.hats] *)
