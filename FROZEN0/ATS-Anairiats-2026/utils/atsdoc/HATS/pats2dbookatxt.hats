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

#ifndef ATSDOC_PATS2DBOOKATXT
#define ATSDOC_PATS2DBOOKATXT 1

(* ****** ****** *)

fn sizeof
   (type: string): atext = atext_strcst (type)
// end of [sizeof]

fn stacode (x: string): atext = atext_strcst (x)
fn prfcode (x: string): atext = atext_strcst (x)
fn dyncode (x: string): atext = atext_strcst (x)

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

fn pats2xhtmls
  (code: string): atext = let
  val _beg =
    atext_strcst ("<programlisting><![CDATA[\n")
  val _code = atext_strcst (code)
  val _end = atext_strcst ("]]></programlisting>")
in
  atext_apptxt3 (_beg, _code, _end)
end // end of [pats2xhtmls]

fn pats2xhtmld
  (code: string): atext = let
  val _beg =
    atext_strcst ("<programlisting><![CDATA[\n")
  val _code = atext_strcst (code)
  val _end = atext_strcst ("]]></programlisting>")
in
  atext_apptxt3 (_beg, _code, _end)
end // end of [pats2xhtmld]

(* ****** ****** *)

fn pats2xhtmls_save
  (code: string): atext = pats2xhtmls (code)

(* ****** ****** *)

fn pats2xhtmls_tryit
  (code: string): atext = pats2xhtmls (code)
fn pats2xhtmld_tryit
  (code: string): atext = pats2xhtmld (code)

(* ****** ****** *)

#endif // end of [ATSDOC_PATS2DBOOKATXT]

(* ****** ****** *)

(* end of [pats2dbookatxt.hats] *)
