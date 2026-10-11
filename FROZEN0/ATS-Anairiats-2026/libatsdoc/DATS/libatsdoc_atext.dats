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
//
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: July, 2011
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)
//
staload
UN = "prelude/SATS/unsafe.sats"
//
staload
STDIO = "libc/SATS/stdio.sats"
sortdef fm = $STDIO.fm
stadef FILE_v = $STDIO.FILE_v
macdef SEEK_SET = $STDIO.SEEK_SET
macdef feof = $STDIO.feof
macdef fopen_err = $STDIO.fopen_err
macdef fclose_err = $STDIO.fclose_err
macdef fflush_err = $STDIO.fflush_err
macdef fgetc_err = $STDIO.fgetc_err
macdef fputc_err = $STDIO.fputc_err
macdef fseek_err = $STDIO.fseek_err
//
staload
FCNTL = "libc/SATS/fcntl.sats"
staload
STDLIB = "libc/SATS/stdlib.sats"
staload
UNISTD = "libc/SATS/unistd.sats"
staload
WAIT = "libc/sys/SATS/wait.sats"
//
(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_symbol.sats"
staload "libatsdoc/SATS/libatsdoc_symmap.sats"

(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_atext.sats"

(* ****** ****** *)

macdef neof (i) = (,(i) != EOF)

(* ****** ****** *)

datatype atext =
//
  | ATEXTnil of () // empty text
//
  | ATEXTstrcst of string // string constants
  | ATEXTstrsub of string // strings containing marked tokens
//
  | ATEXTapptxt2 of (atext, atext) // text concatenation
  | ATEXTappstr2 of (string, string) // string concatenation
//
  | ATEXTapptxt3 of (atext, atext, atext) // text concatenation
  | ATEXTappstr3 of (string, string, string) // string concatenation
//
  | ATEXTconcatxt of atextlst // text concatenation
  | ATEXTconcatxtsep of (atextlst, atext(*sep*)) // text concatenation with separator
// end of [atext]

where stringlst = List (string)

(* ****** ****** *)

assume atext_type = atext

(* ****** ****** *)

implement atext_nil () = ATEXTnil ()
implement atext_strcst (x) = ATEXTstrcst (x)
implement atext_strsub (x) = ATEXTstrsub (x)
implement atext_apptxt2 (x1, x2) = ATEXTapptxt2 (x1, x2)
implement atext_appstr2 (x1, x2) = ATEXTappstr2 (x1, x2)
implement atext_apptxt3 (x1, x2, x3) = ATEXTapptxt3 (x1, x2, x3)
implement atext_appstr3 (x1, x2, x3) = ATEXTappstr3 (x1, x2, x3)
implement atext_concatxt (xs) = ATEXTconcatxt (xs)
implement atext_concatxtsep (xs, sep) = ATEXTconcatxtsep (xs, sep)

(* ****** ****** *)

implement atext_newline () = ATEXTstrcst ("\n")

(* ****** ****** *)
//
implement
atext_strptr (x) = ATEXTstrcst ((string_of_strptr)x)

implement
atext_strptr0 (x) = let
  val notnull = strptr_isnot_null (x)
in
  if notnull then
    atext_strptr (x)
  else let
    val () = strptr_free (x) in atext_nil ()
  end // end of [if]
end // end of [atext_strptr0]
//
implement atext_strcstptr (x) = ATEXTstrcst ((string_of_strptr)x)
implement atext_strsubptr (x) = ATEXTstrsub ((string_of_strptr)x)
//
(* ****** ****** *)

local

staload
S = "libc/SATS/stdlib.sats"
staload
UNI = "libc/SATS/unistd.sats"

in // in of [local]

%{$
ats_ptr_type
libatsdoc_file2strptr
  (ats_int_type fd) {
  int err = 0 ;
  int nerr = 0 ;
  char* sbp = (char*)0 ;
//
  long int ofs_beg, ofs_end, nbyte ;
//
  ofs_beg = lseek (fd, 0L, SEEK_CUR) ;
  if (ofs_beg < 0) nerr += 1 ;
  ofs_end = lseek (fd, 0L, SEEK_END) ;
  if (ofs_end < 0) nerr += 1 ;
  ofs_beg = lseek (fd, ofs_beg, SEEK_SET) ;
  if (ofs_beg < 0) nerr += 1 ;
  nbyte = ofs_end - ofs_beg ;
//
  if (nerr == 0) { sbp = ATS_MALLOC(nbyte + 1) ; }
  if (sbp == NULL) nerr += 1 ;
//
  if (nerr == 0) {
    err = atslib_fildes_read_all_err (fd, sbp, nbyte) ;
  }
  if (err < 0) { nerr += 1 ; }
//
  if (nerr == 0) {
    sbp[ofs_end] = '\0'; return sbp ;
  }
//
  if (sbp) free (sbp) ; return NULL ;
} // end of [libatsdoc_file2strptr]
%} // end of [%{$]

(* ****** ****** *)

implement{a}
tostring_fprint (prfx, fpr, x) = let
  val tmp = sprintf ("%sXXXXXX", @(prfx))
  val [m,n:int] tmp = strbuf_of_strptr (tmp)
  prval () = __assert () where {
    extern prfun __assert (): [n >= 6] void
  }
  prval pfstr = tmp.1
  val (pfopt | fd) = $S.mkstemp !(tmp.2) // create it!
  prval () = tmp.1 := pfstr
  val tmp = strptr_of_strbuf (tmp)
in
//
if fd >= 0 then let
  prval $F.open_v_succ (pffil) = pfopt
  val (fpf | out) = fdopen (pffil | fd, file_mode_w) where {
    extern fun fdopen {fd:nat} (
      pffil: !fildes_v fd | fd: int fd, mode: file_mode
    ) : (fildes_v fd -<lin,prf> void | FILEref) = "mac#fdopen"
  } // end of [out]
  val () = fpr (out, x)
  val _err = fflush_err (out)
  val _err = fseek_err (out, 0L, SEEK_SET)
  val res = file2strptr (pffil | fd)
  prval () = fpf (pffil)
  val _err = fclose_err (out)
  val _err = $UNI.unlink ($UN.castvwtp1 (tmp))
  val () = strptr_free (tmp)
in
  res (*strptr*)
end else let
  prval $F.open_v_fail () = pfopt; val () = strptr_free (tmp) in strptr_null ()
end // end of [if]
//
end // end of [tostring_fprint]

(* ****** ****** *)

implement
tostring_strsub (sub) = 
  tostring_fprint<string> ("libatsdoc_tostring_strsub", fprint_strsub, sub)
// end of [tostring_strsub]

(* ****** ****** *)

local

fun filepath2string
  (path: string): strptr0 = let
  val [l:addr] (pfopt | filp) = fopen_err (path, file_mode_r)
in
  if filp > null then let
    prval Some_v (pffil) = pfopt
    val filr = __cast (pffil | filp) where {
      extern castfn __cast {m:fm} (pffil: FILE_v (m, l) | p: ptr l): FILEref
    } // end of [val]
    val cs = char_list_vt_make_file (filr)
    val _err = fclose_err (filr)
    val cs1 = $UN.castvwtp1 {List(char)} (cs)
    val n = list_length (cs1)
    val sbf = string_make_list_int (cs1, n)
    val () = list_vt_free (cs)
  in
    strptr_of_strbuf (sbf)
  end else let
    prval None_v () = pfopt in strptr_null ()
  end // end of [if]
end // end of [filepath2string]

in // in of [local]

implement
atext_filepath (path) = let
  val [l:addr]
    str = filepath2string (path)
  prval () = addr_is_gtez {l} ()
  val isnotnull = strptr_isnot_null (str)
in
  if isnotnull then
    atext_strptr (str)
  else let
    prval () = strptr_free_null (str) in atext_nil ()
  end // end of [if]
end // end of [atext_filepath]

end // end of [local]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

local

viewtypedef
atextmap = symmap (atext)

val map0 = symmap_make_nil ()
val theAtextMap = ref<atextmap> (map0)

in // in of [local]

implement
theAtextMap_search (s) = let
  val (vbox pf | p) = ref_get_view_ptr (theAtextMap)
in
  symmap_search (!p, s)
end // end of [theAtextMap_search]

implement
theAtextMap_insert (s, x) = let
  val (vbox pf | p) = ref_get_view_ptr (theAtextMap)
in
  symmap_insert (!p, s, x)
end // end of [theAtextMap_insert]

implement
theAtextMap_insert_str (s, x) = let
  val s = symbol_make_string (s) in theAtextMap_insert (s, x)
end // end of [theAtextMap_insert_str]

end // end of [local]

(* ****** ****** *)

implement
fprint_atext (out, x) = (
  case+ x of
//
  | ATEXTnil () => ()
//
  | ATEXTstrcst (str) => fprint_string (out, str)
  | ATEXTstrsub (sub) => fprint_strsub (out, sub)
//
  | ATEXTapptxt2 (x1, x2) => {
      val () = fprint_atext (out, x1)
      val () = fprint_atext (out, x2)
    }
  | ATEXTappstr2 (x1, x2) => {
      val () = fprint_string (out, x1)
      val () = fprint_string (out, x2)
    }
//
  | ATEXTapptxt3 (x1, x2, x3) => {
      val () = fprint_atext (out, x1)
      val () = fprint_atext (out, x2)
      val () = fprint_atext (out, x3)
    }
  | ATEXTappstr3 (x1, x2, x3) => {
      val () = fprint_string (out, x1)
      val () = fprint_string (out, x2)
      val () = fprint_string (out, x3)
    }
//
  | ATEXTconcatxt (xs) => fprint_atextlst (out, xs)
  | ATEXTconcatxtsep (xs, sep) => fprint_atextlst_sep (out, xs, sep)
//
) (* end of [fprint_atext] *)

implement
fprint_atextlst (out, xs) =
  list_app_cloptr<atext> (xs, lam (x) =<1> fprint_atext (out, x))
// end of [fprint_atextlst]

implement
fprint_atextlst_sep
  (out, xs, sep) = let
  fun loop (
    xs: atextlst, i: int
  ) :<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_atext (out, sep)
        val () = fprint_atext (out, x)
      in
        loop (xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (xs, 0)
end // end of [fprint_atextlst]

(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_reader.sats"
extern fun fprsub_reader (out: FILEref, inp: &reader): void

(* ****** ****** *)

local

#define i2c char_of_int

fun
IDENTFST_test
  (c: char): bool = case+ 0 of
  | _ when ('a' <= c andalso c <= 'z') => true
  | _ when ('A' <= c andalso c <= 'Z') => true
  | _ when c = '_' => true
  | _ => false
// end of [IDENTFST_test]

fun
IDENTRST_test
  (c: char): bool = case+ 0 of
  | _ when ('a' <= c andalso c <= 'z') => true
  | _ when ('A' <= c andalso c <= 'Z') => true
  | _ when ('0' <= c andalso c <= '9') => true
  | _ when c = '_' => true
  | _ when c = '\'' => true
  | _ => false
// end of [IDENTRST_test]

fun ident_get (
  inp: &reader, cur: &int
) : List_vt (char) = let
  val fst = (i2c)cur
in
  if IDENTFST_test (fst) then let
    val () = cur := reader_get_char (inp)
  in
    list_vt_cons (fst, identrst_get (inp, cur))
  end else
    list_vt_nil ()
  // end of [if]
end // end of [ident_get]

and identrst_get (
  inp: &reader, cur: &int
) : List_vt (char) = let
  val fst = (i2c)cur
in
  if IDENTRST_test (fst) then let
    val () = cur := reader_get_char (inp)
  in
    list_vt_cons (fst, identrst_get (inp, cur))
  end else
    list_vt_nil ()
  // end of [if]
end // end of [identrst_get]

fun fprsub_ident {n:nat} (
  out: FILEref, cs: list_vt (char, n)
) : void = let
  val n = list_vt_length (cs)
in
  if n > 0 then let
    val cs1 = $UN.castvwtp1(cs)
    val id =
      string_make_list_int (cs1, n)
    val id = string_of_strbuf (id)
    val sym = symbol_make_string (id)
    val ans = theAtextMap_search (sym)
    val () = (case+ ans of
      | ~Some_vt xt => fprint_atext (out, xt)
      | ~None_vt () => fprintf (out, "#%s$", @(id))
    ) // end of [val]
//
    val () = list_vt_free<char> (cs)
//
  in
    // nothing
  end else let
    val ~list_vt_nil () = cs in (*nothing*)
  end // end of [if]
end // end of [fprsub_ident]

in // in of [local]

implement
fprsub_reader (out, inp) = let
//
fun aux (
  out: FILEref, inp: &reader, cur: &int
) : void =
  if neof(cur) then let
    val fst = (i2c)cur
    val () = cur := reader_get_char (inp)
  in 
    case+ fst of
    | '#' => aux_SHARP (out, inp, cur)
    | '\\' => aux_SLASH (out, inp, cur)
    | _ => let
        val err = fputc_err (fst, out) in aux (out, inp, cur)
      end // end of [_]
  end // end of [if]
//
and aux_SHARP (
  out: FILEref, inp: &reader, cur: &int
) : void =
  if neof(cur) then let
    val cs = ident_get (inp, cur)
    val dlrend = (cur = int_of('$')): bool
//
    fun loop (out: FILEref, cs: List_vt (char)): void =
      case+ cs of
      | ~list_vt_cons (c, cs) => let
          val err = fputc_err (c, out) in loop (out, cs)
        end // end of [list_cons]
      | ~list_vt_nil () => ()
    (* end of [loop] *)
//
    val () =
      if dlrend then let
        val () = cur := reader_get_char (inp)
      in
        fprsub_ident (out, cs) // valid identifier
      end else let
        val err = fputc_err ('#', out) in loop (out, cs)
      end // end of [if]
    // end of [val]
  in
    aux (out, inp, cur)
  end else let
    val err = fputc_err ('#', out) in (*nothing*)
  end // end of [if]
//
and aux_SLASH (
  out: FILEref, inp: &reader, cur: &int
) : void =
  if neof(cur) then let
    val fst = (i2c)cur
    val () = cur := reader_get_char (inp)
  in
    case+ fst of
    | '#' => let
        val err = fputc_err ('#', out) in aux (out, inp, cur)
      end // end of ['#']
    | '\\' => let
        val err = fputc_err ('\\', out) in aux (out, inp, cur)
      end // end of ['\\']
    | _ => let
        val err = fputc_err ('\\', out); val err = fputc_err (fst, out)
      in
        aux (out, inp, cur)
      end // end of [_]
  end else let
    val err = fputc_err ('\\', out) in (*nothing*)
  end // end of [if]
//
  var cur: int
  val () = cur := reader_get_char (inp)
in
  aux (out, inp, cur)
end // end of [fprsub_reader]

end // end of [local]

(* ****** ****** *)

implement
fprint_strsub
  (out, sub) = let
  var inp: reader
  val () = reader_initialize_string (inp, sub)
  val () = fprsub_reader (out, inp)
  val () = reader_uninitialize (inp)
in
  // nothing
end // end of [fprint_strsub]

(* ****** ****** *)

implement
fprint_filsub (out, path) = let
  val (pfopt | filp) = fopen_err (path, file_mode_r)
in
//
if filp > null then let
  prval Some_v (pffil) = pfopt
  var inp: reader
  val () = reader_initialize_filp (file_mode_lte_r_r, pffil | inp, filp)
  val () = fprsub_reader (out, inp)
  val () = reader_uninitialize (inp)
in
  // nothing
end else let
  prval None_v () = pfopt
  val () = fprintf (stderr_ref, "fprint_filsub: [%s] cannot be opened!\n", @(path))
  val () = exit (1)
in
  // nothing
end // end of [if]
//
end // end of [fprint_filsub]

(* ****** ****** *)

(* end of [libatsdoc_atext.dats] *)
