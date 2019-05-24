(*
**
** A simple GTK example: file selection
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun file_ok_sel (
    fs: !GtkFileSelection_ref1
  ) : void = () where {
  val [l:addr] (fpf_name | name) =
    gtk_file_selection_get_filename (fs)
  val () = printf
    ("%s\n", @(__cast name)) where {
    extern castfn __cast (x: !gstring l): string
  } // end of [val]
  prval () = minus_addback (fpf_name, name | fs)
} // end of [file_ok_sel]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val (fpf_x | x) = (gs)"File Selection Test"
  val filew = gtk_file_selection_new (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (filew, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)
//
  val (fpf_btn | btn) = gtk_file_selection_get_ok_button (filew)
  val _sid = g_signal_connect_swapped
    (btn, (gsignal)"clicked", G_CALLBACK(file_ok_sel), filew)
  prval () = minus_addback (fpf_btn, btn | filew)
//
  val (fpf_btn | btn) = gtk_file_selection_get_cancel_button (filew)
  val _sid = g_signal_connect_swapped
    (btn, (gsignal)"clicked", G_CALLBACK(gtk_widget_destroy), filew)
  prval () = minus_addback (fpf_btn, btn | filew)
//
  val (fpf_x | x) = gstring_of_string "penguin.png"
  val () = gtk_file_selection_set_filename (filew, x)
  prval () = fpf_x (x)
//
  val () = gtk_widget_show_unref (filew) // ref-count becomes 1!
//
  val () = gtk_main ()
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

(* end of [gtk-test15.dats] *)
