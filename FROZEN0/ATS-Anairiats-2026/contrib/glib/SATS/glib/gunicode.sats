(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December, 2011
//
(* ****** ****** *)

%{#
#include "contrib/glib/CATS/glib/gunicode.cats"
%} // end of [%{#]

(* ****** ****** *)

staload "contrib/glib/SATS/glib/gtypes.sats"

(* ****** ****** *)

abst@ype gunichar = guint32
abst@ype gunichar2 = guint16

(* ****** ****** *)
//
abst@ype GUnicodeType = int
//
macdef G_UNICODE_CONTROL = $extval (GUnicodeType, "G_UNICODE_CONTROL")
macdef G_UNICODE_FORMAT = $extval (GUnicodeType, "G_UNICODE_FORMAT")
macdef G_UNICODE_UNASSIGNED = $extval (GUnicodeType, "G_UNICODE_UNASSIGNED")
macdef G_UNICODE_PRIVATE_USE = $extval (GUnicodeType, "G_UNICODE_PRIVATE_USE")
macdef G_UNICODE_SURROGATE = $extval (GUnicodeType, "G_UNICODE_SURROGATE")
macdef G_UNICODE_LOWERCASE_LETTER = $extval (GUnicodeType, "G_UNICODE_LOWERCASE_LETTER")
macdef G_UNICODE_MODIFIER_LETTER = $extval (GUnicodeType, "G_UNICODE_MODIFIER_LETTER")
macdef G_UNICODE_OTHER_LETTER = $extval (GUnicodeType, "G_UNICODE_OTHER_LETTER")
macdef G_UNICODE_TITLECASE_LETTER = $extval (GUnicodeType, "G_UNICODE_TITLECASE_LETTER")
macdef G_UNICODE_UPPERCASE_LETTER = $extval (GUnicodeType, "G_UNICODE_UPPERCASE_LETTER")
macdef G_UNICODE_COMBINING_MARK = $extval (GUnicodeType, "G_UNICODE_COMBINING_MARK")
macdef G_UNICODE_ENCLOSING_MARK = $extval (GUnicodeType, "G_UNICODE_ENCLOSING_MARK")
macdef G_UNICODE_NON_SPACING_MARK = $extval (GUnicodeType, "G_UNICODE_NON_SPACING_MARK")
macdef G_UNICODE_DECIMAL_NUMBER = $extval (GUnicodeType, "G_UNICODE_DECIMAL_NUMBER")
macdef G_UNICODE_LETTER_NUMBER = $extval (GUnicodeType, "G_UNICODE_LETTER_NUMBER")
macdef G_UNICODE_OTHER_NUMBER = $extval (GUnicodeType, "G_UNICODE_OTHER_NUMBER")
macdef G_UNICODE_CONNECT_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_CONNECT_PUNCTUATION")
macdef G_UNICODE_DASH_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_DASH_PUNCTUATION")
macdef G_UNICODE_CLOSE_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_CLOSE_PUNCTUATION")
macdef G_UNICODE_FINAL_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_FINAL_PUNCTUATION")
macdef G_UNICODE_INITIAL_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_INITIAL_PUNCTUATION")
macdef G_UNICODE_OTHER_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_OTHER_PUNCTUATION")
macdef G_UNICODE_OPEN_PUNCTUATION = $extval (GUnicodeType, "G_UNICODE_OPEN_PUNCTUATION")
macdef G_UNICODE_CURRENCY_SYMBOL = $extval (GUnicodeType, "G_UNICODE_CURRENCY_SYMBOL")
macdef G_UNICODE_MODIFIER_SYMBOL = $extval (GUnicodeType, "G_UNICODE_MODIFIER_SYMBOL")
macdef G_UNICODE_MATH_SYMBOL = $extval (GUnicodeType, "G_UNICODE_MATH_SYMBOL")
macdef G_UNICODE_OTHER_SYMBOL = $extval (GUnicodeType, "G_UNICODE_OTHER_SYMBOL")
macdef G_UNICODE_LINE_SEPARATOR = $extval (GUnicodeType, "G_UNICODE_LINE_SEPARATOR")
macdef G_UNICODE_PARAGRAPH_SEPARATOR = $extval (GUnicodeType, "G_UNICODE_PARAGRAPH_SEPARATOR")
macdef G_UNICODE_SPACE_SEPARATO = $extval (GUnicodeType, "G_UNICODE_SPACE_SEPARATO")
//
(* ****** ****** *)
//
abst@ype GUnicodeBreakType = int
//
macdef G_UNICODE_BREAK_MANDATORY = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_MANDATORY")
macdef G_UNICODE_BREAK_CARRIAGE_RETURN = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_CARRIAGE_RETURN")
macdef G_UNICODE_BREAK_LINE_FEED = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_LINE_FEED")
macdef G_UNICODE_BREAK_COMBINING_MARK = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_COMBINING_MARK")
macdef G_UNICODE_BREAK_SURROGATE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_SURROGATE")
macdef G_UNICODE_BREAK_ZERO_WIDTH_SPACE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_ZERO_WIDTH_SPACE")
macdef G_UNICODE_BREAK_INSEPARABLE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_INSEPARABLE")
macdef G_UNICODE_BREAK_NON_BREAKING_GLUE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_NON_BREAKING_GLUE")
macdef G_UNICODE_BREAK_CONTINGENT = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_CONTINGENT")
macdef G_UNICODE_BREAK_SPACE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_SPACE")
macdef G_UNICODE_BREAK_AFTER = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_AFTER")
macdef G_UNICODE_BREAK_BEFORE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_BEFORE")
macdef G_UNICODE_BREAK_BEFORE_AND_AFTER = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_BEFORE_AND_AFTER")
macdef G_UNICODE_BREAK_HYPHEN = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_HYPHEN")
macdef G_UNICODE_BREAK_NON_STARTER = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_NON_STARTER")
macdef G_UNICODE_BREAK_OPEN_PUNCTUATION = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_OPEN_PUNCTUATION")
macdef G_UNICODE_BREAK_CLOSE_PUNCTUATION = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_CLOSE_PUNCTUATION")
macdef G_UNICODE_BREAK_QUOTATION = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_QUOTATION")
macdef G_UNICODE_BREAK_EXCLAMATION = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_EXCLAMATION")
macdef G_UNICODE_BREAK_IDEOGRAPHIC = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_IDEOGRAPHIC")
macdef G_UNICODE_BREAK_NUMERIC = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_NUMERIC")
macdef G_UNICODE_BREAK_INFIX_SEPARATOR = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_INFIX_SEPARATOR")
macdef G_UNICODE_BREAK_SYMBOL = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_SYMBOL")
macdef G_UNICODE_BREAK_ALPHABETIC = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_ALPHABETIC")
macdef G_UNICODE_BREAK_PREFIX = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_PREFIX")
macdef G_UNICODE_BREAK_POSTFIX = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_POSTFIX")
macdef G_UNICODE_BREAK_COMPLEX_CONTEXT = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_COMPLEX_CONTEXT")
macdef G_UNICODE_BREAK_AMBIGUOUS = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_AMBIGUOUS")
macdef G_UNICODE_BREAK_UNKNOWN = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_UNKNOWN")
macdef G_UNICODE_BREAK_NEXT_LINE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_NEXT_LINE")
macdef G_UNICODE_BREAK_WORD_JOINER = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_WORD_JOINER")
macdef G_UNICODE_BREAK_HANGUL_L_JAMO = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_HANGUL_L_JAMO")
macdef G_UNICODE_BREAK_HANGUL_V_JAMO = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_HANGUL_V_JAMO")
macdef G_UNICODE_BREAK_HANGUL_T_JAMO = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_HANGUL_T_JAMO")
macdef G_UNICODE_BREAK_HANGUL_LV_SYLLABLE = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_HANGUL_LV_SYLLABLE")
macdef G_UNICODE_BREAK_HANGUL_LVT_SYLLABL = $extval (GUnicodeBreakType, "G_UNICODE_BREAK_HANGUL_LVT_SYLLABL")
//
(* ****** ****** *)

fun g_unichar_isalnum (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isalnum"
fun g_unichar_isalpha (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isalpha"
fun g_unichar_iscntrl (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_iscntrl"
fun g_unichar_isdigit (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isdigit"
fun g_unichar_isgraph (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isgraph"
fun g_unichar_islower (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_islower"
fun g_unichar_isprint (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isprint"
fun g_unichar_ispunct (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_ispunct"
fun g_unichar_isspace (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isspace"
fun g_unichar_isupper (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isupper"
fun g_unichar_isxdigit (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isxdigit"
fun g_unichar_istitle (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_istitle"
fun g_unichar_isdefined (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_isdefined"
fun g_unichar_iswide (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_iswide"
fun g_unichar_iswide_cjk (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_iswide_cjk"
fun g_unichar_iszerowidth (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_iszerowidth"
fun g_unichar_ismark (c: gunichar):<> gboolean = "mac#atsctrb_g_unichar_ismark"

(* ****** ****** *)

fun g_utf8_strlen_cstr (
  x: string
) : glong = "atsctrb_g_utf8_strlen_cstr"
// end of [g_utf8_strlen_cstr]

fun g_utf8_strlen_carr {n:nat} (
  x: &READ(@[gchar][n]), n: gsize(n)
) : glong = "mac#atsctrb_g_utf8_strlen_carr"
// end of [g_utf8_strlen_carr]

(* ****** ****** *)

(* end of [gunicode.sats] *)
