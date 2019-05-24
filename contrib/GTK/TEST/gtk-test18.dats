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

fun cb_menuitem (_: ptr, str: string) = printf ("%s\n", @(str))

(* ****** ****** *)

staload PRINTF = "libc/SATS/printf.sats"

fun menu_add_item
  {c:cls | c <= GtkMenu} {l:agz}
  (menu: !gobjref (c, l), i: int): void = () where {
  #define BUFSZ 1024
  var !p_str with pf_str = @[byte][BUFSZ]()
  val _int = $PRINTF.snprintf (pf_str | p_str, BUFSZ, "Test-undermenu - %i", @(i))
  extern castfn __cast (_: ptr): [l:agz] (gstring l -<lin,prf> void | gstring l)
  val (fpf_x | x) = __cast (p_str)
  val item = gtk_menu_item_new_with_label (x)
  prval () = fpf_x (x)
  val (pf_gc, pf | p) = strdup_gc
    (__cast (p_str)) where { extern castfn __cast (x: ptr): String }
  // end of [val]
  val str = string1_of_strbuf @(pf_gc, pf | p)
  val _sid = g_signal_connect (
    item, (gsignal)"activate", G_CALLBACK(cb_menuitem), (gpointer)str
  ) // end of [val]
//
  prval () = clstrans {c,GtkMenu,GtkMenuShell} ()
//
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  prval () = pf_str := bytes_v_of_strbuf_v (pf_str)
} // end of [menu_add_item]

(* ****** ****** *)

fun cb_button_press
  (menu: !GtkMenu_ref1, event: &GdkEvent): gboolean = let
  val _type = event.type
in
  case+ 0 of
  | _ when _type = GDK_BUTTON_PRESS => let
      prval (pf, fpf) = GdkEventButton_castdn (view@ event)
      val button = (&event)->button
      val time = (&event)->time
      prval () = view@ event := fpf (pf)
      val () = gtk_menu_popup_null (menu, button, time)
    in
      GTRUE
    end // end of [GDK_BUTTON_PRESS]
  | _ => GFALSE
end // end of [cb_button_press]

(* ****** ****** *)

macdef gs = gstring_of_string

(* ****** ****** *)

extern
fun main1 (): void = "main1"
implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_widget_set_size_request (window, (gint)200, (gint)100)
  val (fpf_x | x) = (gs)"GTK menu test(1)"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val [l_menu:addr] menu = gtk_menu_new ()
//
  var i: int
  val () = for (i := 0; i < 3; i := i+1) menu_add_item (menu, i)
//
  val (fpf_x | x) = (gs)"Root Menu"
  val root_menu = gtk_menu_item_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_menu_item_set_submenu (root_menu, menu)
//
//
  val vbox = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, vbox)
//
  val mbar = gtk_menu_bar_new ()
  val () = gtk_box_pack_start (vbox, mbar, GFALSE, GFALSE, (guint)2)
  val () = gtk_menu_shell_append (mbar, root_menu)
//
  val (fpf_x | x) = (gs)"press me"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"event", G_CALLBACK(cb_button_press), menu)
  val () = gtk_box_pack_start (vbox, button, GTRUE, GTRUE, (guint)2)
//
  // val () = gtk_widget_show (menu) // never call [gtk_widget_show] on it!
  val () = g_object_unref (menu)
  val () = gtk_widget_show (button)
  val () = g_object_unref (button)
  val () = gtk_widget_show (root_menu)
  val () = g_object_unref (root_menu)
  val () = gtk_widget_show (mbar)
  val () = g_object_unref (mbar)
//
  val () = gtk_widget_show (vbox)
  val () = g_object_unref (vbox)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)  
  val () = gtk_widget_show_unref (window) // ref-count becomes 1!
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

(* end of [gtk-test18.dats] *)
