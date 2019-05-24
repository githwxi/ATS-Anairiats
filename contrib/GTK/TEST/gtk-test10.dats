(*
**
** A simple GTK example: horizontal and vertical rulers
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun delete_event {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = gtk_main_quit ()
in
  GFALSE // delivered!
end // end of [delete_event]

(* ****** ****** *)

%{^
#define EVENT_METHOD(x, event_name) GTK_WIDGET_GET_CLASS(x)->event_name
ats_ptr_type
motion_notify_event (ats_ptr_type x) { return EVENT_METHOD(x, motion_notify_event) ; }
%} // end of ...
extern fun motion_notify_event
  {c:cls | c <= GtkWidget} {l:agz} (x: !gobjref (c, l)): ptr = "motion_notify_event"
// end of [motion_notify_event]

(* ****** ****** *)

#define XSIZE 600
#define YSIZE 400

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)delete_event, (gpointer)null
  ) // end of [val]
  val () = gtk_container_set_border_width (window, (guint)10)
//
  val table = gtk_table_new ((guint)3, (guint)2, GFALSE)
  val () = gtk_container_add (window, table)
//
  val area = gtk_drawing_area_new ()
  val () = gtk_widget_set_size_request (area, (gint)XSIZE, (gint)YSIZE)
  val xopt = GTK_EXPAND lor GTK_FILL
  val yopt = GTK_FILL
  val () = gtk_table_attach (
    table, area, (guint)1, (guint)2, (guint)1, (guint)2, xopt, yopt, (guint)0, (guint)0
  ) // end of [val]
  val mask = GDK_POINTER_MOTION_MASK lor GDK_POINTER_MOTION_HINT_MASK
  val mask = gint_of_GdkEventMask (mask)
  val () = gtk_widget_set_events (area, mask)
  val () = gtk_widget_show (area)
//
  val xopt = GTK_EXPAND lor GTK_SHRINK lor GTK_FILL
  val yopt = GTK_FILL
//
  val hr = gtk_hruler_new ()
  val () = gtk_ruler_set_metric (hr, GTK_PIXELS)
  val () = gtk_ruler_set_range (hr, 7.0, 13.0, 0.0, 20.0)
  val _sid = g_signal_connect_swapped
    (area, (gsignal)"motion_notify_event", G_CALLBACK(motion_notify_event(hr)), hr)
  val () = gtk_table_attach (
    table, hr, (guint)1, (guint)2, (guint)0, (guint)1, xopt, yopt, (guint)0, (guint)0
  ) // end of [val]
  val () = gtk_widget_show (hr)
  val () = g_object_unref (hr)
//
  val vr = gtk_vruler_new ()
  val () = gtk_ruler_set_metric (vr, GTK_PIXELS)
  val () = gtk_ruler_set_range (vr, 0.0, (double_of)YSIZE, 10.0, (double_of)YSIZE)
  val _sid = g_signal_connect_swapped
    (area, (gsignal)"motion_notify_event", G_CALLBACK(motion_notify_event(vr)), vr)
  val () = gtk_table_attach (
    table, vr, (guint)0, (guint)1, (guint)1, (guint)2, yopt, xopt, (guint)0, (guint)0
  ) // end of [val]
  val () = gtk_widget_show (vr)
  val () = g_object_unref (vr)
//
  val () = g_object_unref (area)
//
  val () = gtk_widget_show (table)
  val () = g_object_unref (table)
//
  val () = gtk_widget_show_unref (window) // ref-count becomes 1!
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

(* end of [gtk-test10.dats] *)
