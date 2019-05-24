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

extern
fun gtk_image_menu_item_new_with_label0
  (name: string): GtkImageMenuItem_ref1 = "atsctrb_gtk_image_menu_item_new_with_label"
// end of [gtk_image_menu_item_new_with_label0]

(* ****** ****** *)

macdef gs = gstring_of_string

(* ****** ****** *)

extern
fun main1 (): void = "main1"
implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_position (window, GTK_WIN_POS_CENTER)
  val () = gtk_widget_set_size_request (window, (gint)250, (gint)200)
  val (fpf_x | x) = (gs)"GTK menu test(2)"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val vbox0 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_container_add (window, vbox0)
//
  val mbar = gtk_menu_bar_new ()
  val () = gtk_box_pack_start (vbox0, mbar, GFALSE, GFALSE, (guint)3)
//
  val aclgrp = gtk_accel_group_new ()
  val () = gtk_window_add_accel_group (window, aclgrp)
//
  val (fpf_x | x) = (gs)"_File"
  val item_file = gtk_menu_item_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val () = gtk_menu_shell_append (mbar, item_file)
  val filemenu = gtk_menu_new ()
  val () = gtk_menu_item_set_submenu (item_file, filemenu)
  val (fpf_x | x) = (gs)GTK_STOCK_NEW
  val item_new = gtk_image_menu_item_new_from_stock_null (x)
  prval () = fpf_x (x)
  val () = gtk_menu_shell_append (filemenu, item_new)
  val (fpf_x | x) = (gs)GTK_STOCK_OPEN
  val item_open = gtk_image_menu_item_new_from_stock_null (x)
  prval () = fpf_x (x)
  val () = gtk_menu_shell_append (filemenu, item_open)
  val item_sep = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (filemenu, item_sep)
  val (fpf_x | x) = (gs)GTK_STOCK_QUIT
  val item_quit = gtk_image_menu_item_new_from_stock (x, aclgrp)
  prval () = fpf_x (x)
  val () = gtk_menu_shell_append (filemenu, item_quit)
  val _sid = g_signal_connect
    (item_quit, (gsignal)"activate", G_CALLBACK(gtk_main_quit), (gpointer)null)
  val () = gtk_widget_add_accelerator
    (item_quit, (gsignal)"activate", aclgrp, (guint)GDK_q, GDK_CONTROL_MASK, GTK_ACCEL_VISIBLE)
  // end of [val]
  val () = g_object_unref (item_new)
  val () = g_object_unref (item_open)
  val () = g_object_unref (item_sep)
  val () = g_object_unref (item_quit)
  val () = g_object_unref (filemenu)
  val () = g_object_unref (item_file)
//
  val (fpf_x | x) = (gs)"_Family"
  val item_family = gtk_menu_item_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val () = gtk_menu_shell_append (mbar, item_family)
  val familymenu = gtk_menu_new ()
  val () = gtk_menu_item_set_submenu (item_family, familymenu)
//
  val item_zoe = gtk_image_menu_item_new_with_label0 ("Zoe")
  val () = gtk_menu_shell_append (familymenu, item_zoe)
  val () = g_object_unref (item_zoe)
  val item_mom = gtk_image_menu_item_new_with_label0 ("Mom")
  val () = gtk_menu_shell_append (familymenu, item_mom)
  val () = g_object_unref (item_mom)
  val item_dad = gtk_image_menu_item_new_with_label0 ("Dad")
  val () = gtk_menu_shell_append (familymenu, item_dad)
  val () = g_object_unref (item_dad)
  val item_grandma = gtk_image_menu_item_new_with_label0 ("Grandma")
  val () = gtk_menu_shell_append (familymenu, item_grandma)
  val () = g_object_unref (item_grandma)
  val item_grandpa = gtk_image_menu_item_new_with_label0 ("Grandpa")
  val () = gtk_menu_shell_append (familymenu, item_grandpa)
  val () = g_object_unref (item_grandpa)
//
  val () = g_object_unref (familymenu)
  val () = g_object_unref (item_family)
//
  val () = g_object_unref (mbar)
  val () = g_object_unref (aclgrp)
//
  val () = g_object_unref (vbox0)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy", G_CALLBACK(gtk_main_quit), (gpointer)null)  
  val () = gtk_widget_show_all (window)
  val () = g_object_unref (window) // ref-count becomes 1!
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

(* end of [gtk-test19.dats] *)
