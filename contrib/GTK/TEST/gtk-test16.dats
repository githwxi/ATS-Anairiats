(*
**
** A simple GTK example: text view
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

%{^
//
extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;
//
%} // end of [%{^]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
//
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)
  val (fpf_x | x) = (gs)"TextView"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
  val () = gtk_window_set_position (window, GTK_WIN_POS_CENTER)
  val () = gtk_window_set_default_size (window, (gint)200, (gint)250)
  val () = gtk_window_set_resizable (window, GTRUE)
  val () = gtk_container_set_border_width (window, (guint)5)
//
  val vbox0 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, vbox0)
  val textview = gtk_text_view_new ()
  val () = gtk_box_pack_start (vbox0, textview, GTRUE, GTRUE, (guint)0)
  val (fpf_buffer | buffer) = gtk_text_view_get_buffer (textview)
//
  var iter: GtkTextIter // uninitialized
  val () = gtk_text_buffer_get_iter_at_offset (buffer, iter, (gint)0)
  val (fpf_x | x) = (gs)"Plain text\n"
  val () = gtk_text_buffer_insertall (buffer, iter, x)
  prval () = fpf_x (x)
//
  prval () = minus_addback (fpf_buffer, buffer | textview)
  val () = g_object_unref (textview)
  val () = g_object_unref (vbox0)
//
  val () = gtk_widget_show_all (window)
  val () = g_object_unref (window) // ref-count becomes 1!
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

(* end of [gtk-test16.dats] *)
