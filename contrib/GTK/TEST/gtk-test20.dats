(*
**
** A simple GTK example: menubar, menu, menuitem
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(* ****** ****** *)

staload "libc/SATS/string.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun update_statusbar
  {c1,c2:cls | c1 <= GtkTextBuffer; c2 <= GtkStatusbar}
  {l1,l2:agz}
  (buf: !gobjref (c1, l1), bar: !gobjref (c2, l2)): void = () where {
  val () = gtk_statusbar_pop(bar, (guint)0)
  var iter: GtkTextIter
  val (fpf_tm | tm) = gtk_text_buffer_get_insert (buf)
  val () = gtk_text_buffer_get_iter_at_mark (buf, iter, tm)
  prval () = minus_addback (fpf_tm, tm | buf)
  val nrow = gtk_text_iter_get_line (iter)
  val nrow = int_of_gint (nrow)
  val ncol = gtk_text_iter_get_line_offset (iter)
  val ncol = int_of_gint (ncol)
  val msg = g_strdup_printf ("Col %d Ln %d", @(ncol+1, nrow+1))
  val _mid = gtk_statusbar_push(bar, (guint)0, msg)
  val () = gstring_free (msg)
} // end of [update_statusbar]

fun mark_set_callback
  {c1,c2:cls | c1 <= GtkTextBuffer; c2 <= GtkStatusbar}
  {l1,l2:agz} (
    buf: !gobjref (c1, l1)
  , _iter: ptr, _iter2: ptr
  , bar: !gobjref (c2, l2)
 ) : void = () where {
 val () = update_statusbar(buf, bar)
} // end of [mark_set_callback]

(* ****** ****** *)

extern
fun main1 (): void = "main1"
implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)
  val () = gtk_window_set_position(window, GTK_WIN_POS_CENTER)
  val () = gtk_window_set_default_size(window, (gint)250, (gint)200)
  val (fpf_x | x) = gstring_of_string ("lines & cols")
  val () = gtk_window_set_title(window, x)
  prval () = fpf_x (x)
  val vbox = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, vbox)
//
  val toolbar = gtk_toolbar_new()
  val () = gtk_toolbar_set_style (toolbar, GTK_TOOLBAR_ICONS)
  val (fpf_x | x) = gstring_of_string(GTK_STOCK_QUIT)
  val quit = gtk_tool_button_new_from_stock (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect(quit, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), (gpointer)null)
  val () = gtk_toolbar_insert(toolbar, quit, (gint)~1)
  val () = gtk_widget_show_unref (quit)
  val sep = gtk_separator_tool_item_new ()
  val () = gtk_toolbar_insert(toolbar, sep, (gint)~1)
  val () = gtk_widget_show_unref (sep)
  val () = gtk_box_pack_start(vbox, toolbar, GFALSE, GFALSE, (guint)5)
  val () = gtk_widget_show_unref (toolbar)
//
(*
  val (fpf_x | x) = (gstring_of_string)GTK_STOCK_QUIT
  val quit = gtk_button_new_from_stock(x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect(quit, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), (gpointer)null)
  val () = gtk_box_pack_start (vbox, quit, GFALSE, GFALSE, (guint)10)
  val () = gtk_widget_show_unref (quit)
*)
//
  val view = gtk_text_view_new()
  val () = gtk_box_pack_start(vbox, view, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_grab_focus (view) // HX: what does this do?
  val (fpf_buf | buf) = gtk_text_view_get_buffer (view)
  val bar = gtk_statusbar_new ()
  val () = gtk_box_pack_start(vbox, bar, GFALSE, GFALSE, (guint)0)
  val _sid = g_signal_connect(buf, (gsignal)"mark_set", G_CALLBACK(mark_set_callback), (gpointer_vt)bar)
  val () = update_statusbar(buf, bar)
  val () = gtk_widget_show_unref (bar)
  prval () = minus_addback (fpf_buf, buf | view)
  val () = gtk_widget_show_unref (view)
  val () = gtk_widget_show_unref (vbox)
  val () = gtk_widget_show_unref (window) // ref-count becomes 1!
  val () = gtk_main ()
} // end of [main1]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

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

(* end of [gtk-test20.dats] *)

////

#include <gtk/gtk.h>

update_statusbar(GtkTextBuffer *buffer,
    GtkStatusbar  *statusbar)
{
  gchar *msg;
  gint row, col;
  GtkTextIter iter;

  gtk_statusbar_pop(statusbar, 0); 

  gtk_text_buffer_get_iter_at_mark(buffer,
      &iter, gtk_text_buffer_get_insert(buffer));

  row = gtk_text_iter_get_line(&iter);
  col = gtk_text_iter_get_line_offset(&iter);

  msg = g_strdup_printf("Col %d Ln %d", col+1, row+1);

  gtk_statusbar_push(statusbar, 0, msg);

  g_free(msg);
}

static void
mark_set_callback(GtkTextBuffer *buffer,
    const GtkTextIter *new_location, GtkTextMark *mark,
    gpointer data)
{
  update_statusbar(buffer, GTK_STATUSBAR(data));
}


int main( int argc, char *argv[])
{

  GtkWidget *window;
  GtkWidget *vbox;

  GtkWidget *toolbar;
  GtkWidget *view;
  GtkWidget *statusbar;
  GtkToolItem *exit;
  GtkTextBuffer *buffer;

  gtk_init(&argc, &argv);

  window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
  gtk_window_set_position(GTK_WINDOW(window), GTK_WIN_POS_CENTER);
  gtk_window_set_default_size(GTK_WINDOW(window), 250, 200);
  gtk_window_set_title(GTK_WINDOW(window), "lines & cols");

  vbox = gtk_vbox_new(FALSE, 0);
  gtk_container_add(GTK_CONTAINER(window), vbox);

  toolbar = gtk_toolbar_new();
  gtk_toolbar_set_style(GTK_TOOLBAR(toolbar), GTK_TOOLBAR_ICONS);

  exit = gtk_tool_button_new_from_stock(GTK_STOCK_QUIT);
  gtk_toolbar_insert(GTK_TOOLBAR(toolbar), exit, -1);

  gtk_box_pack_start(GTK_BOX(vbox), toolbar, FALSE, FALSE, 5);

  view = gtk_text_view_new();
  gtk_box_pack_start(GTK_BOX(vbox), view, TRUE, TRUE, 0);
  gtk_widget_grab_focus(view);

  buffer = gtk_text_view_get_buffer(GTK_TEXT_VIEW(view));

  statusbar = gtk_statusbar_new();
  gtk_box_pack_start(GTK_BOX(vbox), statusbar, FALSE, FALSE, 0);

  g_signal_connect(G_OBJECT(exit), "clicked", 
        G_CALLBACK(gtk_main_quit), NULL);

  g_signal_connect(buffer, "changed",
        G_CALLBACK(update_statusbar), statusbar);

  g_signal_connect_object(buffer, "mark_set", 
        G_CALLBACK(mark_set_callback), statusbar, 0);

  g_signal_connect_swapped(G_OBJECT(window), "destroy",
        G_CALLBACK(gtk_main_quit), NULL);

  gtk_widget_show_all(window);

  update_statusbar(buffer, GTK_STATUSBAR (statusbar));

  gtk_main();

  return 0;
}
