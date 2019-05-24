(*
**
** A simple GTK example: horizontal/vertical alignment
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

extern
fun gtk_label_new0
  (name: string): GtkLabel_ref1 = "mac#atsctrb_gtk_label_new"
// end of [gtk_label_new0]

(* ****** ****** *)

macdef gs = gstring_of_string

(* ****** ****** *)

extern
fun main1 (): void = "main1"
implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_position (window, GTK_WIN_POS_CENTER)
  val () = gtk_widget_set_size_request (window, (gint)300, (gint)250)
  val () = gtk_window_set_resizable (window, GFALSE)
  val () = gtk_container_set_border_width (window, (guint)15)
  val (fpf_x | x) = (gs)"Window Layout"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val table = gtk_table_new ((guint)8, (guint)4, GFALSE)
  val () = gtk_container_add (window, table)
//
  val () = gtk_table_set_col_spacings (table, (guint)3)
  val halign = gtk_alignment_new (0.0f, 0.0f, 0.0f, 0.0f)
  val title = gtk_label_new0 ("Windows")
  val () = gtk_container_add (halign, title)
  val () = gtk_table_attach
    (table, halign, 0U, 1U, 0U, 1U, GTK_FILL, GTK_FILL, 0U, 0U)
  // end of [gtk_table_attach]
  val () = g_object_unref (title)
  val () = g_object_unref (halign)
//
  val wins = gtk_text_view_new ()
  val () = gtk_text_view_set_editable (wins, GTRUE)
  val () = gtk_text_view_set_cursor_visible (wins, GFALSE)
  val xopt = GTK_FILL lor GTK_EXPAND
  val yopt = GTK_FILL lor GTK_EXPAND
  val () = gtk_table_attach
    (table, wins, 0U, 2U, 1U, 3U, xopt, yopt, 1U, 1U)
  // end of [gtk_table_attach]
  val () = g_object_unref (wins)
//
  val (fpf_x | x) = (gstring_of_string)"Activate"
  val activate = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_widget_set_size_request (activate, (gint)50, (gint)30)
  val () = gtk_table_attach
    (table, activate, 3U, 4U, 1U, 2U, GTK_FILL, GTK_SHRINK, 1U, 1U)
  // end of [gtk_table_attach]
  val () = g_object_unref (activate)
//
  val valign = gtk_alignment_new (0.0f, 0.0f, 0.0f, 0.0f)
  val (fpf_x | x) = (gstring_of_string)"Close"
  val close = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_container_add (valign, close)
  val () = gtk_widget_set_size_request (close, (gint)70, (gint)30)
  val () = gtk_table_set_row_spacing (table, (guint)1, (guint)3)
  val yopt = GTK_FILL lor GTK_EXPAND
  val () = gtk_table_attach
    (table, valign, 3U, 4U, 2U, 3U, GTK_FILL, yopt, 1U, 1U)
  // end of [gtk_table_attach]
  val () = g_object_unref (close)
  val () = g_object_unref (valign)
//
  val halign2 = gtk_alignment_new (0.0f, 1.0f, 0.0f, 0.0f)
  val (fpf_x | x) = (gstring_of_string)"Help"
  val help = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_container_add (halign2, help)
  val () = gtk_widget_set_size_request (help, (gint)70, (gint)30)
  val () = gtk_table_set_row_spacing (table, (guint)3, (guint)6)
  val () = gtk_table_attach
    (table, halign2, 0U, 1U, 4U, 5U, GTK_FILL, GTK_FILL, 0U, 0U)
  // end of [gtk_table_attach]
  val () = g_object_unref (help)
  val () = g_object_unref (halign2)
//
  val (fpf_x | x) = (gstring_of_string)"OK"
  val ok = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_widget_set_size_request (ok, (gint)70, (gint)30)
  val () = gtk_table_attach
    (table, ok, 3U, 4U, 4U, 5U, GTK_FILL, GTK_FILL, 0U, 0U)
  val () = g_object_unref (ok)
//
  val () = g_object_unref (table)
//
  val _sid = g_signal_connect
    (window, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)
  val () = gtk_widget_show_all (window)
  val () = g_object_unref (window) // ref-count becomes 1!
//
  val () = gtk_main ()
} // end of [main1]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

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

(* end of [gtk-test17.dats] *)
