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
// Start Time: July, 2011
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload
STDIO = "libc/SATS/stdio.sats"
macdef fputc_err = $STDIO.fputc_err

(* ****** ****** *)
//
staload
SYM = "libatsdoc/SATS/libatsdoc_symbol.sats"
//
staload
FIL = "libatsdoc/SATS/libatsdoc_filename.sats"
//
staload
LOC = "libatsdoc/SATS/libatsdoc_location.sats"
//
macdef posincby1
  (pos) = $LOC.position_incby_count (,(pos), 1u)
macdef posincbyc
  (pos, i) = $LOC.position_incby_char (,(pos), ,(i))
//
(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_lexbuf.sats"

(* ****** ****** *)

staload "atsdoc_translate.sats"

(* ****** ****** *)

#define i2c char_of_int

#define i2u uint_of_int
#define u2i int_of_uint
#define sz2i int1_of_size1

(* ****** ****** *)

macdef
neof (i) = (,(i) != EOF)

(* ****** ****** *)

local

val the_funres_prefix = ref<string> ("__tok")

in (* in-of-local *)

implement
funres_get_prfx () = !the_funres_prefix
implement
funres_set_prfx (prfx) = !the_funres_prefix := prfx

end // end of [local]

(* ****** ****** *)

local

val cntref = ref<int> (1)

fun funres_get_count (): int = let
  val n = !cntref; val () = !cntref := n + 1 in n
end // end of [funres_count]

in (* in-of-local *)

implement
funcall_get_fres () = let
  val prfx = funres_get_prfx ()
  val count = funres_get_count ()
  val fres = sprintf ("%s%i", @(prfx, count))
in
  string_of_strptr (fres)
end // end of [funcall_get_fres]

end // end of [local]

(* ****** ****** *)

implement
tranitm_make (loc, node) = '{
  tranitm_loc= loc, tranitm_node= node
}

(* ****** ****** *)

implement
fprint_tranitm
  (out, itm) =
  case+ itm.tranitm_node of
  | EXTCODE (code) => (
      fprint_string (out, code)
    ) // end of [EXTCODE]
  | FUNCALL (fnam, knd, xs, fres) => let
      val () = fprintf (out, "val %s = %s", @(fres, fnam))
      val () = if knd > 0 then fprint_string (out, "$lst")
      val () = fprint_funarglst (out, xs)
      val () = fprint_newline (out)
      val () = fprintf (
        out, "val () = theAtextMap_insert_str (\"%s\", %s)", @(fres, fres)
      ) // end of [val]
      val () = fprint_newline (out)
    in
      // nothing
    end // end of [FUNCALL]
// end of [fprint_tranitm]

(* ****** ****** *)

fun SPACE_test (c: char): bool = char_isspace (c)

(* ****** ****** *)

implement
DIGIT_test (c) = char_isdigit (c)

implement
IDENTFST_test (c) = case+ 0 of
  | _ when ('a' <= c andalso c <= 'z') => true
  | _ when ('A' <= c andalso c <= 'Z') => true
  | _ when c = '_' => true
  | _ => false
// end of [IDENTFST_test]

implement
IDENTRST_test (c) = case+ 0 of
  | _ when ('a' <= c andalso c <= 'z') => true
  | _ when ('A' <= c andalso c <= 'Z') => true
  | _ when ('0' <= c andalso c <= '9') => true
  | _ when c = '_' => true
  | _ when c = '\'' => true
  | _ => false
// end of [IDENTRST_test]

(* ****** ****** *)

implement
ftesting_seq0
  (buf, pos, f) = diff where {
  fun loop (
    buf: &lexbuf, nchr: uint, f: char -> bool
  ) : uint = let
    val i = lexbuf_get_char (buf, nchr)
  in
    if neof(i) then
      if f ((i2c)i)
        then loop (buf, succ(nchr), f) else nchr
      // end of [if]
    else nchr // end of [if]
  end // end of [loop]
  val nchr0 = lexbufpos_diff (buf, pos)
  val nchr1 = loop (buf, nchr0, f)
  val diff = nchr1 - nchr0
  val () = if diff > 0u 
    then $LOC.position_incby_count (pos, diff) else ()
  // end of [val]
} // end of [ftesting_seq0]

(* ****** ****** *)

implement
testing_spaces
  (buf, pos) = let
  fun loop (
    buf: &lexbuf, pos: &position, k: uint
  ) : uint = let
    val i = lexbufpos_get_char (buf, pos)
  in
    if neof(i) then (
      if SPACE_test ((i2c)i) then let
        val () = posincbyc (pos, i) in loop (buf, pos, k+1u)
      end else k // end of [if]
    ) else k // end of [if]
  end // end of [loop]
in
  loop (buf, pos, 0u)
end // end of [testing_spaces]

(* ****** ****** *)
//
// HX: [lit] contains no '\n'!
//
implement testing_literal
  (buf, pos, lit) = res where {
//
val [n:int] lit = string1_of_string (lit)
//
fun loop
  {k:nat | k <= n} (
  buf: &lexbuf, nchr: uint, lit: string n, k: size_t k
) : int = let
  val notatend =
    string_isnot_atend (lit, k)
  // end of [val]
in
  if notatend then let
    val i = lexbuf_get_char (buf, nchr)
  in
    if neof(i) then
      if ((i2c)i = lit[k])
        then loop (buf, succ(nchr), lit, k+1) else ~1
      // end of [if]
    else ~1 // end of [if]
  end else (sz2i)k // end of [if]
end // end of [loop]
//
val nchr0 = lexbufpos_diff (buf, pos)
val res = loop (buf, nchr0, lit, 0)
val () = if res >= 0
  then $LOC.position_incby_count (pos, (i2u)res) else ()
// end of [if] // end of [val]
//
} // end of [testing_literal]

(* ****** ****** *)

implement
testing_ident
  (buf, pos) = let
  val i = lexbufpos_get_char (buf, pos)
in
//
if neof(i) then (
  if IDENTFST_test ((i2c)i) then let
    val () = posincby1 (pos)
    val nchr = ftesting_seq0 (buf, pos, IDENTRST_test)
  in
    (u2i)nchr + 1
  end else ~1 // end of [if]
) else ~1 // end of [if]
//
end // end of [testing_ident]

(* ****** ****** *)

local

viewtypedef
tranitmlst_vt = List_vt (tranitm)
val theList = ref<tranitmlst_vt> (list_vt_nil)

in // in of [local]

implement
the_tranitmlst_add (x) = let
  val (vbox pf | p) = ref_get_view_ptr (theList)
in
  !p := list_vt_cons (x, !p)
end // end of [the_tranitmlst_add]

implement
the_tranitmlst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theList)
  val xs = !p
  val () = !p := list_vt_nil
in
  list_vt_reverse (xs)
end // end of [the_tranitmlst_add]

end // end of [local]

(* ****** ****** *)

extern
fun trans_top_PERCENT
  (out: FILEref, buf: &lexbuf, pos: &position): void
// end of [trans_PERCENT]

extern
fun trans_top_SHARP
  (out: FILEref, buf: &lexbuf, pos: &position): void
// end of [trans_SHARP]

extern
fun trans_top_SLASH
  (out: FILEref, buf: &lexbuf, pos: &position): void
// end of [trans_SLASH]

(* ****** ****** *)

implement
trans_top
  (out, buf) = let
//
  var pos: position
  val () = lexbuf_get_position (buf, pos)
//
  val i0 = lexbuf_get_char (buf, 0u)
//
in
//
if neof(i0) then let
  val c = (i2c)i0 // the first character
  val () = posincbyc (pos, i0)
in
  case+ c of
  | '%' => let
      val () = trans_top_PERCENT (out, buf, pos)
      val () = lexbuf_reset_position (buf, pos)
    in
      trans_top (out, buf)
    end
  | '#' => let
      val () = trans_top_SHARP (out, buf, pos)
      val () = lexbuf_reset_position (buf, pos)
    in
      trans_top (out, buf)
    end
  | '\\' => let
      val () = trans_top_SLASH (out, buf, pos)
      val () = lexbuf_reset_position (buf, pos)
    in
      trans_top (out, buf)
    end
  | _ => let
      val err = fputc_err (c, out)
      val () = lexbuf_reset_position (buf, pos)
    in
      trans_top (out, buf)
    end // end of [_]
//
end else () // end of [if]
//
end // end of [trans_top]

(* ****** ****** *)

implement
trans_top_PERCENT
  (out, buf, pos) = let
  val i = lexbufpos_get_char (buf, pos)
  val c = (i2c)i
in
  case+ c of 
  | '\{' when // '%{' at the beginning
      $LOC.position_get_ncol (pos) = 1 => let
      var pos0: position
      val () = lexbuf_get_position (buf, pos0)
      val () = posincby1 (pos)
    in
      trans_extcode (buf, pos0, pos)
    end // end of ['\{']
  | _ => let
      val () = posincbyc (pos, i)
      val err = fputc_err ('%', out); val err = fputc_err (c, out)
    in
      // nothing
    end // end of [_]
end // end of [trans_PERCENT]

(* ****** ****** *)

implement
trans_top_SHARP
  (out, buf, pos) = let
  var pos0: position
  val () = $LOC.position_copy (pos0, pos)
  val opt = trans_funcall (buf, pos0, pos)
in
//
case+ opt of
| ~Some_vt (fres) => fprintf (out, "#%s$", @(fres)) // HX: '$' is a separator!
| ~None_vt () => let
    val err = fputc_err ('#', out) in (*nothing*)
  end // end of [if]
//
end // end of [trans_top_SHARP]

(* ****** ****** *)

implement
trans_top_SLASH
  (out, buf, pos) = let
  val i = lexbufpos_get_char (buf, pos)
in
//
if neof(i) then let
  val c = (i2c)i in
  case+ c of
  | '\n' => let
      val () = posincbyc (pos, i)
    in
      // nothing
    end // end of ['\n']
  | '#' => let
      val () = posincby1 (pos); val err = fputc_err (c, out)
    in
      // nothing
    end // end of ['\\']
  | '\\' => let
      val () = posincby1 (pos); val err = fputc_err (c, out)
    in
      // nothing
    end // end of ['\\']
  | '%' => let
      val () = posincby1 (pos); val err = fputc_err (c, out)
    in
      // nothing
    end // end of ['\\']
  | _ => let
      val () = posincby1 (pos)
      val err = fputc_err ('\\', out); val err = fputc_err (c, out)
    in
      // nothing
    end // end of [_]
end else let
  val err = fputc_err ('\\', out)
in
  // nothing
end // end of [if]
//
end // end of [trans_top_SLASH]

(* ****** ****** *)

implement
trans_top_from_stdin
  (tout) = () where {
  var buf: lexbuf
  val () = lexbuf_initialize_getc (buf, lam () =<cloptr1> $STDIO.getchar ())
  val () = trans_top (tout, buf)
  val () = lexbuf_uninitialize (buf)
//
  val () = fprint_the_docerrlst (stderr_ref)
//
} // end of [trans_top_from_stdin]

implement
trans_top_from_filename
  (tout, fil) = let
//
  prval pfmod = file_mode_lte_r_r
  val fullname = $FIL.filename_get_full (fil)
  val fullname = $SYM.symbol_get_name (fullname)
  val (pffil | filp) = $STDIO.fopen_exn (fullname, file_mode_r)
  var buf: lexbuf
  val () = lexbuf_initialize_filp (file_mode_lte_r_r, pffil | buf, filp)
//
  val (pfpush | ()) = $FIL.the_filenamelst_push (fil)
  val () = trans_top (tout, buf)
  val () = $FIL.the_filenamelst_pop (pfpush | (*none*))
//
  val () = lexbuf_uninitialize (buf)
//
in
  fprint_the_docerrlst (stderr_ref)
end // end of [trans_top_from_filename]

implement
trans_top_from_basename
  (tout, basename) = let
  val filopt = $FIL.filenameopt_make_relative (basename)
in
//
case+ filopt of
| ~Some_vt (fil) => trans_top_from_filename (tout, fil)
| ~None_vt () => let
    val () = prerrf ("The file [%s] cannot be opened for read.\n", @(basename))
  in
    // nothing
  end // end of [if]
// end of [case]
//
end // end of [trans_top_from_filename]

(* ****** ****** *)

(* end of [atsdoc_translate.dats] *)
