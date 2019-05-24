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

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload "atsui_srcwinlst.sats"

(* ****** ****** *)

viewtypedef srcwinlst = GList_ptr0 (srcwin1)

var the_srcwinlst: srcwinlst

stadef l_the_srcwinlst = the_srcwinlst

val p_the_srcwinlst = &the_srcwinlst

val (pf_the_srcwinlst | ()) =
  vbox_make_view_ptr (view@ the_srcwinlst | p_the_srcwinlst)
// end of [val]

extern
prfun the_srcwinlst_takeout ()
  : (srcwinlst @ l_the_srcwinlst, srcwinlst @ l_the_srcwinlst -<lin,prf> void)
// end of [the_srcwinlst_takeout]

(* ****** ****** *)

%{^

typedef struct {
  gchar *name ; // linear
  int nsaved ; // initially: -1 for a new file and 0 for one that is loaded
  GtkTextBuffer *textbuf ; // linear
  GtkMenuItem *menuitm ; // linear
} srcwin_struct ;
// 
// typedef srcwin_struct *srcwin ;
//

ats_ptr_type
atsui_srcwin_get_name
  (ats_ptr_type p) {
  return ((srcwin_struct*)p)->name ;
} // end of [atsui_srcwin_get_name]

ats_ptr_type
atsui_srcwin_getref_name
  (ats_ptr_type p) {
  return &((srcwin_struct*)p)->name ;
} // end of [atsui_srcwin_getref_name]

ats_int_type
atsui_srcwin_get_nsaved
  (ats_ptr_type p) {
  return ((srcwin_struct*)p)->nsaved ;
} // end of [atsui_srcwin_get_nsaved]

ats_void_type
atsui_srcwin_set_nsaved
  (ats_ptr_type p, ats_int_type nsaved) {
  ((srcwin_struct*)p)->nsaved = nsaved ; return ;
} // end of [atsui_srcwin_set_nsaved]

ats_ptr_type
atsui_srcwin_get_textbuf
  (ats_ptr_type p) {
  return ((srcwin_struct*)p)->textbuf ;
} // end of [atsui_srcwin_get_textbuf]

ats_ptr_type
atsui_srcwin_get_menuitm
  (ats_ptr_type p) {
  return ((srcwin_struct*)p)->menuitm ;
} // end of [atsui_srcwin_get_menuitm]

/* ****** ****** */

ats_ptr_type
atsui_srcwin_make (
  ats_ptr_type name
, ats_ptr_type textbuf
, ats_ptr_type menuitm
) {
  srcwin_struct *p ;
  p = g_new (srcwin_struct, 1) ;
  p->name = (gchar*)name ;
  p->nsaved = -1 ; // default: a new file
  p->textbuf= (GtkTextBuffer*)textbuf ;
  p->menuitm= (GtkMenuItem*)menuitm ;
  return p ;
} // end of [atsui_srcwin_make]

ats_ptr_type
atsui_srcwin_free
  (ats_ptr_type p) {
  g_free (((srcwin_struct*)p)->name) ;
  g_object_unref (((srcwin_struct*)p)->textbuf) ;
  g_object_unref (((srcwin_struct*)p)->menuitm) ;
  return ;
} // end of [atsui_srcwin_make]

/* ****** ****** */

ats_ptr_type
atsui_srcwinlst_search (
  ats_ptr_type xs0
, ats_fun_ptr_type f, ats_ptr_type env
) {
  GList *xs = xs0 ;
  srcwin_struct *x = 0 ;
  int test ;
  while (xs) {
    test = ((int(*)(gpointer, gpointer))f)(xs->data, env) ;
    if (test) { x = xs->data ; break ; }
    xs = g_list_next (xs) ;
  } // end of [while]
  return x ;
} // end of [atsui_srcwinlst_search]

%} // end of [%{^]

(* ****** ****** *)

extern
fun srcwin_make (
    name: gstring1
  , textbuf: GtkTextBuffer_ref1
  , menuitm: GtkMenuItem_ref1
  ) : srcwin1
  = "atsui_srcwin_make"
// end of [srcwin_make]

(* ****** ****** *)

implement
srcwin_set_menuitm_label (x, name) = let
  val (fpf_menuitm | menuitm) = srcwin_get_menuitm (x)
  val () = gtk_menu_item_set_label (menuitm, name)
  prval () = minus_addback (fpf_menuitm, menuitm | x)
in
  // nothing
end // end of [srcwin_set_menuitm_label]

(* ****** ****** *)

implement 
the_srcwinlst_append (srcwin) = let
  prval (pf, fpf) = the_srcwinlst_takeout ()
  val () = !p_the_srcwinlst := g_list_append (!p_the_srcwinlst, srcwin)
  prval () = fpf (pf)
in
  // nothing
end // end of [the_srcwinlst_append]

(* ****** ****** *)

%{^

ats_ptr_type
atsui_srcwinlst_remove (
  ats_ptr_type p_xs, GtkTextBuffer *tb, int *p_n
) {
  srcwin_struct *x ;
  GList *xs = *(GList**)p_xs ;
  *p_n = 0 ;
  while (xs) {
    x = (srcwin_struct*)(xs->data) ;
    if (x->textbuf == tb) {
      if (*p_n == 0)
        *(GList**)p_xs = xs->next ;
      else {
        (xs->prev)->next = xs->next ;
      } // end of [if]
      if (xs->next) (xs->next)->prev = xs->prev ;
      g_list_free1 (xs);
      return x ;
    } else {
      *p_n += 1 ; xs = xs->next ;
    }
  } // end of [while]
  *p_n = -1 ; // notremoved
  return (srcwin_struct*)0 ;
} // end of [atsui_srcwinlst_remove]

%} // end of [%{^]

implement
the_srcwinlst_remove (tb, n) = let
  prval (pf, fpf) = the_srcwinlst_takeout ()
  val srcwin = srcwinlst_remove (!p_the_srcwinlst, tb, n) where {
    extern fun srcwinlst_remove {l:agz}
      (xs: &srcwinlst, tb: !GtkTextBuffer_ref l, n: &int? >> int): srcwin0
      = "mac#atsui_srcwinlst_remove"
  } // end of [val]
  prval () = fpf (pf)
in
  srcwin
end // end of [the_srcwinlst_remove]

(* ****** ****** *)

//
// HX-2010-05-06:
// if the next is not available then try the prev
//
implement
the_srcwinlst_getnext (n) = let
  prval (pf, fpf) = the_srcwinlst_takeout ()
  extern fun nth {n:nat}
    (xs: !srcwinlst, n: int n): [l:addr] (srcwin l -<lin,prf> void | srcwin l)
    = "mac#atsctrb_g_list_nth_data"
  // end of [nth]
  val (fpf_x | x) = nth (!p_the_srcwinlst, n)
  val px = ptr_of_srcwin (x)
in
  if px > null then let
    prval () = fpf (pf) in (fpf_x | x)
  end else if n = 0 then let
    prval () = fpf (pf) in (fpf_x | x) // no need to try again
  end else let
    prval () = fpf_x (x)
    val (fpf_x | x) = nth (!p_the_srcwinlst, n-1)
    prval () = fpf (pf)
  in
    (fpf_x | x)    
  end // end of [if]
end (* end of [the_srcwinlst_getnext] *)

(* ****** ****** *)

extern
fun srcwinlst_search {vt:viewtype} (
    xs: !srcwinlst, f: {l:agz} (!srcwin l, !vt) -<fun> bool, env: !vt
  ) : [l1:addr] (srcwin l1 -<lin,prf> void | srcwin l1)
  = "atsui_srcwinlst_search"
// end of [srcwinlst_search]

implement
the_srcwinlst_search_name
  {l0} (name0) = res where {
  viewtypedef VT = gstring l0
  prval (pf, fpf) = the_srcwinlst_takeout ()
  val f = lam {l:agz}
    (x: !srcwin l, name0: !VT): bool =<fun> let
    val (fpf_name | name) = srcwin_get_name (x)
    extern castfn __cast {l:agz} (x: !gstring l):<> string
    val str = __cast name
    prval () = minus_addback (fpf_name, name | x)
    val str0 = __cast name0
  in
    str = str0
  end // end of [val]
  val res = srcwinlst_search {VT} (!p_the_srcwinlst, f, name0)
  prval () = fpf (pf)
} // end of [the_srcwinlst_search_name]

implement
the_srcwinlst_search_textbuf
  {c0} {l0} (tb0) = res where {
  typedef VT = ptr l0
  val p0 = ptr_of_gobjref (tb0)
  prval (pf, fpf) = the_srcwinlst_takeout ()
  val f = lam {l:agz}
    (x: !srcwin l, p0: !VT): bool =<fun> let
    val (fpf_tb | tb) = srcwin_get_textbuf (x)
    val p = ptr_of_gobjref (tb)
    prval () = minus_addback (fpf_tb, tb | x)
  in
    p = p0
  end // end of [val]
  val res = srcwinlst_search {VT} (!p_the_srcwinlst, f, p0)
  prval () = fpf (pf)
} // end of [the_srcwinlst_search_textbuf]

(* ****** ****** *)

staload TE = "atsui_topenv.sats"

implement
the_srcwinlst_get_current () = let
  val tvflag = $TE.topenv_get_textview_source_initset_flag ()
in
  if tvflag > 0 then let
    val (fpf_tv | tv) = $TE.topenv_get_textview_source ()
    val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
    val (fpf_x | x) = the_srcwinlst_search_textbuf (tb)
    prval () = minus_addback (fpf_tb, tb | tv)
    prval () = fpf_tv (tv)
  in
    (fpf_x | x)
  end else let
    val x = srcwin_make_null (null)
    prval fpf_x = lam (x: srcwin null)
      : void =<lin,prf> () where { val _null = srcwin_free_null x }
    // end of [prval
  in
    (fpf_x | x)
  end // end of [if]
end // end of [the_srcwinlst_get_current]

(* ****** ****** *)

(* end of [atsui_srcwinlst.dats] *)
