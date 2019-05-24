(*
**
** A simple GTK example: a window
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)
//
staload "contrib/glib/SATS/glib-object.sats"
//
staload "contrib/GTK/SATS/gtk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
//
(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_widget_show {GtkWindow} (window)
  val () = gtk_main ()
  val () = gtk_widget_destroy0 (window) // can never be reached!!!
} // end of [main1]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [gtk-test01.dats] *)
