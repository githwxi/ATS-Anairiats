(*
**
** A simple GTK example: various buttons
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

fun close_application
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), event: &GdkEvent, data: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // deletion 
end // end of [close_application]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)close_application, (gpointer)null
  ) // end of [val]
  val (fpf_x | x) = (gs)"radio buttons"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val () = gtk_container_set_border_width (window, (guint)0)
//
  val box1 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, box1)
//
  val box2 = gtk_vbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GTRUE, GTRUE, (guint)0)
//
  val G_SLIST_NULL = g_slist_new_nil ()
  val (fpf_x | x) = (gs)"button1"
  val button1 = gtk_radio_button_new_with_label (G_SLIST_NULL, x)
  prval () = fpf_x (x)
  val () = g_slist_free_nil (G_SLIST_NULL)
  val () = gtk_box_pack_start (box2, button1, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button1)
  val (fpf_group | group) = gtk_radio_button_get_group (button1)
  val (fpf_x | x) = (gs)"button2"
  val button2 = gtk_radio_button_new_with_label (group, x)
  prval () = fpf_x (x)
  prval () = minus_addback (fpf_group, group | button1)
  val () = g_object_unref (button1)
  val () = gtk_toggle_button_set_active (button2, GTRUE)
  val () = gtk_box_pack_start (box2, button2, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button2)
//
  val (fpf_x | x) = (gs)"button3"
  val button3 = gtk_radio_button_new_with_label_from_widget (button2, x)
  prval () = fpf_x (x)
  val () = g_object_unref (button2)
  val () = gtk_box_pack_start (box2, button3, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button3)
  val () = g_object_unref (button3)
//
  val () = gtk_widget_show (box2)
  val () = g_object_unref (box2)
//
  val sep = gtk_hseparator_new ()
  val () = gtk_box_pack_start (box1, sep, GFALSE, GTRUE, (guint)0)
  val () = gtk_widget_show (sep)
  val () = g_object_unref (sep)
//
  val box2 = gtk_vbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GFALSE, GTRUE, (guint)0)  
//
  val (fpf_x | x) = (gs)"close"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"clicked", G_CALLBACK(close_application), window)
  val () = gtk_box_pack_start (box2, button, GTRUE, GTRUE, (guint)0)
  val () = GTK_WIDGET_SET_FLAGS (button, GTK_CAN_DEFAULT)
  val () = gtk_widget_grab_default (button)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val () = gtk_widget_show (box2)
  val () = g_object_unref (box2)
//
  val () = gtk_widget_show (box1)
  val () = g_object_unref (box1)
//
  val () = gtk_widget_show_unref (window) // ref-count becomes 1!
//
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

(* end of [gtk-test06.dats] *)
