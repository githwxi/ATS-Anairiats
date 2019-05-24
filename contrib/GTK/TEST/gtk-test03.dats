(*
**
** A simple GTK example: two buttons in a box
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

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun callback {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), data: string): void =
  printf ("Hello again: %s was pressed\n", @(data))
// end of [callback]

fun delete_event {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // deletion 
end // end of [delete_event]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val (fpf_x | x) = (gs)"Hello Buttons!"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)delete_event, (gpointer)null
  ) // end of [val]
//
  val () = gtk_container_set_border_width (window, (guint)10U)
//
  val box1 = gtk_hbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, box1)
//
  val (fpf_x | x) = (gs)"Button 1"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(callback), (gpointer)"button 1")
  val () = gtk_box_pack_start (box1, button, GTRUE, GTRUE, (guint)0U)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val (fpf_x | x) = (gs)"Button 2"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(callback), (gpointer)"button 2")
  val () = gtk_box_pack_start (box1, button, GTRUE, GTRUE, (guint)0U)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val () = gtk_widget_show (box1)
  val () = g_object_unref (box1)
//
  val () = gtk_widget_show_unref (window) // HX: ref-count decreases to 1!
  val () = gtk_main ()
//
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

(* end of [gtk-test03.dats] *)
