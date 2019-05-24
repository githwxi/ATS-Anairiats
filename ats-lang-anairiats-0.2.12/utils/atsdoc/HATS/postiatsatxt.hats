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

#ifndef ATSDOC_POSTIATSATXT
#define ATSDOC_POSTIATSATXT 1

(* ****** ****** *)
//
staload UN = "prelude/SATS/unsafe.sats"
staload _(*anon*) = "prelude/DATS/unsafe.dats"
//
staload
STDIO = "libc/SATS/stdio.sats"
staload TIME = "libc/SATS/time.sats"
//
dynload "libatsdoc/dynloadall.dats"
//
staload "libatsdoc/SATS/libatsdoc_atext.sats"
//
(* ****** ****** *)

fun comment
  (x: string): atext = let
  val _beg = "(*\n" and _end = "\n*)"
in
  atext_appstr3 (_beg, x, _end)
end // end of [comment]

fun ignoretxt (x: atext): atext = atext_nil ()

(* ****** ****** *)

fun timestamp
  (): atext = let
  var time = $TIME.time_get ()
  val (fpf | x) = $TIME.ctime (time)
  val x1 = sprintf ("%s", @($UN.castvwtp1{string}(x)))
  prval () = fpf (x)
  val x1 = string_of_strptr (x1)
  val x1 = string1_of_string (x1)
//
  fun loop
    {n,i:nat | i <= n} (
    str: string n, i: size_t i
  ) : sizeLte (n) =
    if string_isnot_atend (str, i) then let
      val c = str[i]
    in
      if c <> '\n' then loop (str, i+1) else i
    end else i // end of [if]
  // end of [loop]
//
  val ofs = loop (x1, 0)
  val p_ofs = $UN.cast2ptr(x1) + ofs
  val [l:addr] p_ofs = ptr1_of_ptr (p_ofs)
  prval () = __assert () where {
    extern praxi __assert (): [l > null] void
  } // end of [prval]
  val () = $UN.ptrset<char> (p_ofs, '\0')
//
in
  atext_strcst (x1)
end // end of [timestamp]

(* ****** ****** *)

fun atscode_banner
  (): atext = atext_strcst ("\
(***********************************************************************)\n\
(*                                                                     *)\n\
(*                         Applied Type System                         *)\n\
(*                                                                     *)\n\
(***********************************************************************)\n\
") // end of [atscode_banner]

fun atscode_banner_for_C
  (): atext = atext_strcst ("\
/***********************************************************************/\n\
/*                                                                     */\n\
/*                         Applied Type System                         */\n\
/*                                                                     */\n\
/***********************************************************************/\n\
") // end of [atscode_banner_for_C]

(* ****** ****** *)

fun atscode_copyright_GPL
  (): atext = atext_strcst ("\
(*\n\
** ATS/Postiats - Unleashing the Potential of Types!\n\
** Copyright (C) 2010-2015 Hongwei Xi, ATS Trustful Software, Inc.\n\
** All rights reserved\n\
**\n\
** ATS is free software;  you can  redistribute it and/or modify it under\n\
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the\n\
** Free Software Foundation; either version 3, or (at  your  option)  any\n\
** later version.\n\
**\n\
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY\n\
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or\n\
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License\n\
** for more details.\n\
**\n\
** You  should  have  received  a  copy of the GNU General Public License\n\
** along  with  ATS;  see the  file COPYING.  If not, please write to the\n\
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA\n\
** 02110-1301, USA.\n\
*)\
") // end of [atscode_copyright_GPL]

fun atscode_copyright_LGPL
  (): atext = atext_strcst ("\
(*\n\
** ATS/Postiats - Unleashing the Potential of Types!\n\
** Copyright (C) 2011-2015 Hongwei Xi, ATS Trustful Software, Inc.\n\
** All rights reserved\n\
**\n\
** ATS is free software;  you can  redistribute it and/or modify it under\n\
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the\n\
** Free Software Foundation; either version 2.1, or (at your option)  any\n\
** later version.\n\
**\n\
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY\n\
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or\n\
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License\n\
** for more details.\n\
**\n\
** You  should  have  received  a  copy of the GNU General Public License\n\
** along  with  ATS;  see the  file COPYING.  If not, please write to the\n\
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA\n\
** 02110-1301, USA.\n\
*)\
") // end of [atsode_copyright_LGPL)

(* ****** ****** *)

fun atscode_copyright_GPL_for_C
  (): atext = atext_apptxt3 (
  atext_strcst "/* ", atscode_copyright_GPL (), atext_strcst " */"
) // end of [atscode_copyright_GPL_for_C]

fun atscode_copyright_LGPL_for_C
  (): atext = atext_apptxt3 (
  atext_strcst "/* ", atscode_copyright_LGPL (), atext_strcst " */"
) // end of [atscode_copyright_LGPL_for_C]

(* ****** ****** *)

fun atscode_author
  (x: string): atext = atext_appstr3 ("(* Author: ", x, " *)")
fun atscode_authoremail
  (x: string): atext = atext_appstr3 ("(* Authoremail: ", x, " *)")

(* ****** ****** *)

fun atscode_start_time
  (x: string): atext = atext_appstr3 ("(* Start time: ", x, " *)")
// end of [atscode_start_time]

(* ****** ****** *)

fun atscode_separator
  (): atext = atext_strcst ("(* ****** ****** *)")
// end of [atscode_separator]

fun atscode_separator_for_C
  (): atext = atext_strcst ("/* ****** ****** */")
// end of [atscode_separator_for_C]

(* ****** ****** *)

fun atscode_decl_strcst (x: string): atext = atext_strcst (x)
fun atscode_decl_strsub (x: string): atext = atext_strsub (x)

(* ****** ****** *)

fun atscode_eof_strsub
  (x: string): atext = atext_apptxt3
  (atext_strcst"(* end of [", atext_strsub(x), atext_strcst"] *)")
// end of [atscode_eof_strsub]

fun atscode_eof_strsub_for_C
  (x: string): atext = atext_apptxt3
  (atext_strcst"/* end of [", atext_strsub(x), atext_strcst"] */")
// end of [atscode_eof_strsub_for_C]

(* ****** ****** *)

fun macextval
  (tname: string, vname: string): atext = let
//
val x = sprintf (
  "macdef %s = $extval (%s, \"%s\")", @(vname, tname, vname)
) (* end of [val] *)
//
in
  atext_strptr (x)
end // end of[macextval]

(* ****** ****** *)

#endif // end of [ATSDOC_POSTIATSATXT]

(* ****** ****** *)

(* end of [postiatsatxt_txt.hats] *)
