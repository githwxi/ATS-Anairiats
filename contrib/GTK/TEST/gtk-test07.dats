(*
**
** A simple GTK example: adjustment, range, scale
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

%{^
GtkWidget *the_hscale = NULL;
ats_ptr_type
the_hscale_get () {
  g_object_ref (G_OBJECT(the_hscale)); return the_hscale ;
}
ats_void_type
the_hscale_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_hscale) g_object_unref (G_OBJECT(the_hscale));
  the_hscale = x ;
  return ;
} // end of [the_hscale_set]

GtkWidget *the_vscale = NULL;
ats_ptr_type
the_vscale_get () {
  g_object_ref (G_OBJECT(the_vscale)); return the_vscale ;
}
ats_void_type
the_vscale_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_vscale) g_object_unref (G_OBJECT(the_vscale));
  the_vscale = x ;
  return ;
} // end of [the_vscale_set]
%} // end of [%{^] 
extern fun the_hscale_get (): GtkHScale_ref1 = "the_hscale_get"
extern fun the_hscale_set (x: !GtkHScale_ref1): void = "the_hscale_set"
extern fun the_vscale_get (): GtkVScale_ref1 = "the_vscale_get"
extern fun the_vscale_set (x: !GtkVScale_ref1): void = "the_vscale_set"

(* ****** ****** *)

fun cb_pos_menu_select
  (_: ptr, pos: GtkPositionType): void = () where {
  val scale = the_hscale_get ()
  val () = gtk_scale_set_value_pos (scale, pos)
  val () = g_object_unref (scale)  
  val scale = the_vscale_get ()
  val () = gtk_scale_set_value_pos (scale, pos)
  val () = g_object_unref (scale)  
} // end of [cb_pos_menu_select]

(* ****** ****** *)

fun cb_update_menu_select
  (_: ptr, policy: GtkUpdateType): void = () where {
  val scale = the_hscale_get ()
  val () = gtk_range_set_update_policy (scale, policy)
  val () = g_object_unref (scale)  
  val scale = the_vscale_get ()
  val () = gtk_range_set_update_policy (scale, policy)
  val () = g_object_unref (scale)  
} // end of [cb_update_menu_select]

(* ****** ****** *)

fun cb_digits_scale
  {c:cls | c <= GtkAdjustment} {l:agz}
  (adj: !gobjref (c, l)): void = () where {
  val value = gtk_adjustment_get_value (adj)
  val n = gint(int_of((double_of(value))))
  val scale = the_hscale_get ()
  val () = gtk_scale_set_digits (scale, n)
  val () = g_object_unref (scale)  
  val scale = the_vscale_get ()
  val () = gtk_scale_set_digits (scale, n)
  val () = g_object_unref (scale)  
} // end of [cb_digits_scale]

(* ****** ****** *)

%{^
ats_void_type
cb_page_size (ats_ptr_type get0, ats_ptr_type set0) {
  GtkAdjustment *get = (GtkAdjustment*)get0 ;
  GtkAdjustment *set = (GtkAdjustment*)set0 ;
  set->page_size = get->value;
  set->page_increment = get->value;
  gtk_adjustment_set_value
    (set, CLAMP (set->value, set->lower, (set->upper - set->page_size)));
  return ;
} // end of [cb_page_size]
%} // end of [%{^]
extern fun cb_page_size
  {c1,c2:cls | c1 <= GtkAdjustment; c2 <= GtkAdjustment} {l1,l2:agz}
  (get: !gobjref (c1, l1), set: !gobjref (c2, l2)): void = "cb_page_size"
// end of [cb_page_size]

(* ****** ****** *)

fun cb_draw_value
  {c:cls | c <= GtkToggleButton} {l:agz}
  (button: !gobjref (c, l)): void = () where {
  val isactive = gtk_toggle_button_get_active (button)
  val scale = the_hscale_get ()
  val () = gtk_scale_set_draw_value (scale, isactive)
  val () = g_object_unref (scale)  
  val scale = the_vscale_get ()
  val () = gtk_scale_set_draw_value (scale, isactive)
  val () = g_object_unref (scale)  
} // end of [cb_draw_value]

(* ****** ****** *)

fun scale_set_default_values
  {c:cls | c <= GtkScale} {l:agz}
  (scale: !gobjref (c, l)): void = () where {
//
  prval () = clstrans {c,GtkScale,GtkRange} ()
//
  val () = gtk_range_set_update_policy (scale, GTK_UPDATE_CONTINUOUS)
  val () = gtk_scale_set_digits (scale, (gint)1)
  val () = gtk_scale_set_value_pos (scale, GTK_POS_TOP)
  val () = gtk_scale_set_draw_value (scale, GTRUE)
} // end of [scale_set_default_values]

(* ****** ****** *)

extern
fun gtk_label_new0
  (name: string): GtkLabel_ref1 = "mac#atsctrb_gtk_label_new"
// end of [gtk_label_new]

extern
fun gtk_menu_item_new_with_label0
  (name: string): GtkMenuItem_ref1 = "mac#atsctrb_gtk_menu_item_new_with_label"
// end of [gtk_menu_item_new_with_label]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val _sid = g_signal_connect (
    window, (gsignal)"destroy", (G_CALLBACK)gtk_main_quit, (gpointer)null
  ) // end of [val]
  val (fpf_x | x) = (gs)"Range Controls"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
// two scales: vertical and horizonal
//
  val box1 = gtk_vbox_new (GFALSE, (gint)0)
  val () = gtk_widget_show (box1)
  val () = gtk_container_add (window, box1)
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_widget_show (box2)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GTRUE, GTRUE, (guint)0)
//
  val adj1 = gtk_adjustment_new (0.0, 0.0, 101.0, 0.1, 1.0, 1.0)
//
  val vscale = gtk_vscale_new (adj1)
  val () = the_vscale_set (vscale)
  val () = scale_set_default_values (vscale)
  val () = gtk_box_pack_start (box2, vscale, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (vscale)
  val () = g_object_unref (vscale)
//
  val box3 = gtk_vbox_new (GFALSE, (gint)10)
  val () = gtk_widget_show (box3)
  val () = gtk_box_pack_start (box2, box3, GTRUE, GTRUE, (guint)0)
//
  val hscale = gtk_hscale_new (adj1)
  val () = the_hscale_set (hscale)
  val () = gtk_widget_set_size_request (hscale, (gint)200, (gint)~1)
  val () = gtk_box_pack_start (box3, hscale, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (hscale)
  val () = g_object_unref (hscale)
//
  val scrollbar = gtk_hscrollbar_new (adj1)
  val () = gtk_range_set_update_policy (scrollbar, GTK_UPDATE_CONTINUOUS)
  val () = gtk_box_pack_start (box3, scrollbar, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (scrollbar)
  val () = g_object_unref (scrollbar)
//
  val () = g_object_unref (box3)
  val () = g_object_unref (box2)
//
// A checkbutton control
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (box2)
  val (fpf_x | x) = (gstring_of_string)"Display value on scale widgets"
  val button = gtk_check_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (button, (gsignal)"toggled", G_CALLBACK(cb_draw_value), (gpointer)null)
  val () = gtk_toggle_button_set_active (button, GTRUE)
  val () = gtk_widget_show (button)
  val () = gtk_box_pack_start (box2, button, GTRUE, GTRUE, (guint)0)
  val () = g_object_unref (button)
  val () = g_object_unref (box2)
//
// An option menu for controlling value position
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (box2)
  val label = gtk_label_new0 ("Scale Value Position:")
  val () = gtk_box_pack_start (box2, label, GFALSE, GFALSE, (guint)0)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val opt = gtk_option_menu_new ()
  val menu = gtk_menu_new () 
  val () = gtk_option_menu_set_menu (opt, menu)
  val () = gtk_box_pack_start (box2, opt, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (opt)
  extern castfn __cast (x: GtkPositionType): gpointer
  // item: Top
  val item = gtk_menu_item_new_with_label0 ("Top")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_pos_menu_select), (__cast)GTK_POS_TOP)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // item: Bottom
  val item = gtk_menu_item_new_with_label0 ("Bottom")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_pos_menu_select), (__cast)GTK_POS_BOTTOM)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // item: Left
  val item = gtk_menu_item_new_with_label0 ("Left")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_pos_menu_select), (__cast)GTK_POS_LEFT)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // item: Right
  val item = gtk_menu_item_new_with_label0 ("Right")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_pos_menu_select), (__cast)GTK_POS_RIGHT)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // all of the items are added
  val () = g_object_unref (menu)
  val () = g_object_unref (opt)
  val () = g_object_unref (box2)
//
// An option menu for controlling update policy
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (box2)
  val label = gtk_label_new0 ("Scale Update Policy:")
  val () = gtk_box_pack_start (box2, label, GFALSE, GFALSE, (guint)0)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val opt = gtk_option_menu_new ()
  val menu = gtk_menu_new () 
  val () = gtk_option_menu_set_menu (opt, menu)
  val () = gtk_box_pack_start (box2, opt, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (opt)
  extern castfn __cast (x: GtkUpdateType): gpointer
  // item: Top
  val item = gtk_menu_item_new_with_label0 ("Continuous")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_update_menu_select), (__cast)GTK_UPDATE_CONTINUOUS)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // item: Bottom
  val item = gtk_menu_item_new_with_label0 ("Discontinuous")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_update_menu_select), (__cast)GTK_UPDATE_DISCONTINUOUS)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // item: Left
  val item = gtk_menu_item_new_with_label0 ("Delayed")
  val _sid = g_signal_connect
    (item, (gsignal)"activate", G_CALLBACK(cb_update_menu_select), (__cast)GTK_UPDATE_DELAYED)
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  val () = g_object_unref (item)
  // all of the items are added
  val () = g_object_unref (menu)
  val () = g_object_unref (opt)
  val () = g_object_unref (box2)
//
// A scale for adjusting the number of digits used in the previous scales
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GFALSE, GTRUE, (guint)0)  
  val () = gtk_widget_show (box2)
  val label = gtk_label_new0 ("Scale Digits:")
  val () = gtk_box_pack_start (box2, label, GFALSE, GFALSE, (guint)0)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val adj2 = gtk_adjustment_new (1.0, 0.0, 5.0, 1.0, 1.0, 0.0)
  val _sid = g_signal_connect
    (adj2, (gsignal)"value_changed", G_CALLBACK(cb_digits_scale), (gpointer)null)
  val scale = gtk_hscale_new (adj2)
  val () = gtk_scale_set_digits (scale, (gint)0)
  val () = gtk_box_pack_start (box2, scale, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (scale)
  val () = g_object_unref (scale)
  val () = g_object_unref (adj2)
  val () = g_object_unref (box2)
//
// A scale for adjusting the page size of the scrollbar
//
  val box2 = gtk_hbox_new (GFALSE, (gint)10)
  val () = gtk_container_set_border_width (box2, (guint)10)
  val () = gtk_box_pack_start (box1, box2, GFALSE, GTRUE, (guint)0)  
  val () = gtk_widget_show (box2)
  val label = gtk_label_new0 ("Scrollbar Page Size:")
  val () = gtk_box_pack_start (box2, label, GFALSE, GFALSE, (guint)0)
  val () = gtk_widget_show (label)
  val () = g_object_unref (label)
  val adj2 = gtk_adjustment_new (1.0, 1.0, 101.0, 1.0, 1.0, 0.0)
  val _sid = g_signal_connect
    (adj2, (gsignal)"value_changed", G_CALLBACK(cb_page_size), (gpointer_vt)adj1)
  val scale = gtk_hscale_new (adj2)
  val () = gtk_box_pack_start (box2, scale, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (scale)
  val () = g_object_unref (scale)
  val () = g_object_unref (adj2)
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
  val () = gtk_widget_show (box2)
  val (fpf_x | x) = (gs)"Quit"
  val button = gtk_button_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect_swapped
    (button, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), window)
  val () = gtk_box_pack_start (box2, button, GTRUE, GTRUE, (guint)0)
  val () = gtk_widget_show (button)
  val () = GTK_WIDGET_SET_FLAGS (button, GTK_CAN_DEFAULT)
  val () = gtk_widget_grab_default (button)
  val () = g_object_unref (button)
  val () = g_object_unref (box2)
//
  val () = g_object_unref (adj1)
  val () = g_object_unref (box1)
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

(* end of [gtk-test07.dats] *)
