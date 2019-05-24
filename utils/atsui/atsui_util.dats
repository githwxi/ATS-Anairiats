(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2010-201? Hongwei Xi, Boston University
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May 2010

(* ****** ****** *)

staload STDIO = "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload "atsui_util.sats"

(* ****** ****** *)

%{^

#define DIRSEP '/'

ats_ptr_type
atsui_filename_get_basename
  (ats_ptr_type x0) {
  char *x1 ;
  x1 = strrchr ((char*)x0, DIRSEP) ;
  return (x1 == NULL ? x0 : x1 + 1) ;
} // end of [atsui_filename_get_basename]

%} // end of [%{^]

(* ****** ****** *)

implement
gtk_text_buffer_clear (tb) = () where {
(*
  // HX: this does not seem natural
  val p1 = GINT_TO_POINTER ((gint)1)
  val [l1:addr] p1 = __cast (p1) where {
    extern castfn __cast (x: gpointer): Ptr
  } // end of [val]
  viewdef V = array_v (gchar, 0, l1) 
  prval (fpf, pf) = __assert () where {
    extern prfun __assert (): (V -<> void, V)
  } // end of [prval]
  val () = gtk_text_buffer_set_text (tb, !p1, (gint)0)
  prval () = fpf (pf)
*)
  var _beg: GtkTextIter and _end: GtkTextIter
  val () = gtk_text_buffer_get_bounds (tb, _beg, _end)
  val () = gtk_text_buffer_delete (tb, _beg, _end)
} // end of [gtk_text_buffer_clear]

(* ****** ****** *)

implement
gtk_text_buffer_load_file
  (pfmod | txtbuf, src) = let
  val () = gtk_text_buffer_clear (txtbuf)
  #define BUFSZ 4096
  var !p_buf with pf_buf = @[byte][BUFSZ]()
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  stadef l_buf = p_buf
  var iter: GtkTextIter?
  val () = while (true) let
    val () = if $STDIO.feof (src) <> 0 then break
    val () = gtk_text_buffer_get_end_iter (txtbuf, iter)
    val [n:int] nread = $STDIO.fread_byte (pfmod | !p_buf, BUFSZ, src)
    viewdef V = array_v (gchar, n, l_buf)
    prval (fpf, pf) = __assert () where {
      extern prfun __assert (): (V -<lin,prf> void, V)
    } // end of [prval]
    val nread = int1_of_size1 (nread)
    val () = gtk_text_buffer_insert (txtbuf, iter, !p_buf, (gint)nread)
    prval () = fpf (pf)
  in
    // nothing
  end // end of [val]
  val () = gtk_text_buffer_get_start_iter (txtbuf, iter)
  val () = gtk_text_buffer_place_cursor (txtbuf, iter)
in
  // nothing
end // end of [gtk_text_buffer_load_file]

(* ****** ****** *)

implement
gtk_text_buffer_store_file
  (pfmod | txtbuf, dst) = let
  var _beg: GtkTextIter and _end: GtkTextIter
  val () = gtk_text_buffer_get_bounds (txtbuf, _beg, _end)
  val [l:addr] gstr = gtk_text_buffer_get_text (txtbuf, _beg, _end, GFALSE(*hidden*))
  val _err = $STDIO.fputs_err
    (pfmod | __cast (gstr), dst) where {
    extern castfn __cast (x: !gstring l): string
  } // end of [val]
  val () = gstring_free (gstr)
in
  // nothing
end // end of [gtk_text_buffer_store_file]

(* ****** ****** *)

(* end of [atsui_util.dats] *)
