(*
**
** A simple GTK example: table packing
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

fun handle_delete_event {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), event: &GdkEvent, _: gpointer): gboolean = let
  val () = (print "this is from [handle_delete_event]"; print_newline ())
in
  GFALSE // deletion 
end // end of [handle_delete_event]

fun handle_destroy
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: gobjref (c, l)): void = () where {
  val () = (print "this is from [handle_destroy]"; print_newline ())
  val () = gtk_widget_destroy0 (widget)
  val () = gtk_main_quit ()
} // end of [handle_destroy]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val (fpf_x | x) = (gs)"Hello Buttons!"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect (
    window, (gsignal)"destroy", (G_CALLBACK)handle_destroy, (gpointer)null
  ) // end of [val]
  val _sid = g_signal_connect (
    window, (gsignal)"delete_event", (G_CALLBACK)handle_delete_event, (gpointer)null
  ) // end of [val]
//
  val () = gtk_container_set_border_width (window, (guint)10U)
//
  val table = gtk_table_new ((guint)2U, (guint)2U, GTRUE)
  val () = gtk_container_add (window, table)
//
  val (fpf_x | x) = (gs)"Button 1"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(callback), (gpointer)"button 1")
  val () = gtk_table_attach_defaults
    (table, button, (guint)0U, (guint)1U, (guint)0U, (guint)1U)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val (fpf_x | x) = (gs)"Button 2"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (button, (gsignal)"clicked", G_CALLBACK(callback), (gpointer)"button 2")
  val () = gtk_table_attach_defaults
    (table, button, (guint)1U, (guint)2U, (guint)0U, (guint)1U)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val (fpf_x | x) = (gs)"_Q_u_i_t"
  val button = gtk_button_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"clicked", G_CALLBACK(handle_destroy), window)
  val () = gtk_table_attach_defaults
    (table, button, (guint)0U, (guint)2U, (guint)1U, (guint)2U)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
//
  val () = gtk_widget_show (table)
  val () = g_object_unref (table)
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

(* end of [gtk-test04.dats] *)
