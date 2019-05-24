(*
**
** A simple GTK example: various labels
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
%} // end of [%{^]

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

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"destroy", (G_CALLBACK)gtk_main_quit, (gpointer)null
  ) // end of [val]
  val (fpf_x | x) = (gs)"Label"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val hbox = gtk_hbox_new (GFALSE, (gint)5)
  val () = gtk_container_add (window, hbox)
//
  val vbox = gtk_vbox_new (GFALSE, (gint)5)
  val () = gtk_box_pack_start (hbox, vbox, GFALSE, GFALSE, (guint)0)
  val () = gtk_container_set_border_width (window, (guint)5)
//
  val (fpf_x | x) = (gs)"Normal Lable"
  val frame = gtk_frame_new (x)
  prval () = fpf_x (x)
  val label = gtk_label_new0 ("This is a Normal label")
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val (fpf_x | x) = (gs)"Multi-line Lable"
  val frame = gtk_frame_new (x)
  prval () = fpf_x (x)
  val label = gtk_label_new0 ("This is a Multi-line label.\nSecond line.\nThird line\n")
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val (fpf_x | x) = (gs)"Left-justified Lable"
  val frame = gtk_frame_new (x)
  prval () = fpf_x (x)
  val label = gtk_label_new0 ("This is a Left-justified\nMulti-line label.\nThird line\n")
  val () = gtk_label_set_justify (label, GTK_JUSTIFY_LEFT)
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val (fpf_x | x) = (gs)"Right-justified Lable"
  val frame = gtk_frame_new (x)
  prval () = fpf_x (x)
  val label = gtk_label_new0 ("This is a Right-justified\nMulti-line label.\nThird line, (j,k)\n")
  val () = gtk_label_set_justify (label, GTK_JUSTIFY_RIGHT)
  val () = gtk_container_add (frame, label)
  val () = g_object_unref label
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref frame
//
  val () = g_object_unref vbox
//
  val vbox = gtk_vbox_new (GFALSE, (gint)5)
  val () = gtk_box_pack_start (hbox, vbox, GFALSE, GFALSE, (guint)0)
  val (fpf_x | x) = (gs)"Line Wrapped Lable"
  val frame = gtk_frame_new (x)
  prval () = fpf_x (x)
  val label = gtk_label_new0 ("This is an example of a line-wrapped lable. It \
should not be taking up the entire \
width allocated to it, but automatically \
wraps the words to fit.\
")
  val () = gtk_label_set_line_wrap (label, GTRUE)
  val () = gtk_container_add (frame, label)
  val () = gtk_box_pack_start (vbox, frame, GFALSE, GFALSE, (guint)0)
  val () = g_object_unref label
  val () = g_object_unref frame
//
  val () = g_object_unref vbox
//
  val () = g_object_unref hbox
//
  val () = gtk_widget_show_all (window)
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

(* end of [gtk-test09.dats] *)
