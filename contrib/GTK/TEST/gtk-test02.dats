(*
**
** A simple GTK example: one button in a window
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

fun hw {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), _: gpointer): void = print ("Hello, world!\n")
// end of [hw]

fun delete_event {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = print ("delete event occurred\n")
in
  GTRUE // deletion ignored
end // end of [delete_event]

fun destroy {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), _: gpointer): void = gtk_main_quit ()
// end of [destroy]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)delete_event, (gpointer)null
  ) // end of [val]
  val _sid = g_signal_connect (
    window, (gsignal)"destroy", (G_CALLBACK)destroy, (gpointer)null
  ) // end of [val]
  val () = gtk_container_set_border_width (window, (guint)10U)
  val (fpf_x | x) = gstring_of_string "Hello, world!"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_widget_show (button)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", (G_CALLBACK)hw, (gpointer)null)
  val () = gtk_container_add (window, button)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"clicked", (G_CALLBACK)gtk_widget_destroy, window)
  val () = gtk_widget_show (window)
  val () = g_object_unref (button)
  val () = g_object_unref (window) // ref-count becomes 1!
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

(* end of [gtk-test02.dats] *)
