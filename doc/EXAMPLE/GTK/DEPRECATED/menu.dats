%{^

#include "prelude/CATS/array.cats"

#include "gtk.cats"
#include "glib.cats"

extern void mainats (ats_int_type argc, ats_ptr_type argv) ;

%} // end of [%{^]

staload "gtk.sats"
staload "glib.sats"

(* ****** ****** *)

staload "prelude/DATS/array.dats"
staload "prelude/DATS/reference.dats"

(* ****** ****** *)

fn window_delete_event
  (wid: &gobj GtkWindow, evt: &gevent, data: &void): gboolean =
  (gtk_main_quit (); GBOOLEAN_FALSE)

extern fun menu_button_press_event
  (button: &gobj GtkButton, evt: &gevent, menu: &gobj GtkMenu): gboolean
  = "menu_button_press_event"

fn menu_button_press_event_ref
  (button: &gobj GtkButton, evt: &gevent, r_menu: gobjref GtkMenu)
  : gboolean =
  let
    val (pf_menu | p_menu) = g_objref_get r_menu
    val ans = menu_button_press_event (button, evt, !p_menu)
    val () = g_objref_set (pf_menu | r_menu, p_menu)
  in
    ans
  end

fn menu_item_response
  (mi: &gobj (GtkMenuItem), data: &(string, gobjref GtkButton)): void =
  let
    val (lab, r_button) = data
    val (pf_button | p_button) = g_objref_get r_button
    val () = gtk_button_set_label (GtkButtonIsGtkButton | !p_button, lab)
  in
    g_objref_set (pf_button | r_button, p_button)
  end

#define NMAX 10

val digits: array (string, 10) =
  array_make_arrpsz{string}$arrpsz("0", "1", "2", "3", "4", "5", "6", "7", "8", "9")

fun menu_items_append {i:nat | i <= NMAX}
  (menu: &gobj GtkMenu, i: int i, button: gobjref GtkButton): void =
  if i < NMAX then let
    val lab = digits[i]
    val (pf_mi | p_mi) = gtk_menu_item_new_with_label (lab)
    val () = gtk_widget_show (GtkMenuItemIsGtkWidget | !p_mi)
    val () = g_signal_connect_ref {@(string, gobjref GtkButton)}
      (!p_mi, GSIGNAL_ACTIVATE, menu_item_response, ref_make_elt @(lab, button))
    val () = gtk_menu_shell_append
      (GtkMenuIsGtkMenuShell, GtkMenuItemIsGtkMenuItem, pf_mi | menu, p_mi)
  in
    menu_items_append (menu, i + 1, button) 
  end

(* ****** ****** *)

implement main_dummy () = ()

extern fun main_menu (): void = "main_menu"
implement main_menu () = let

val dummy: ref void = ref_void_make ()

val (pf_window | p_window) = gtk_window_new (GTK_WINDOW_TOPLEVEL)
val () = g_signal_connect_event_ref {void}
  (!p_window, GSIGNAL_DELETE_EVENT, window_delete_event, dummy)
val () = gtk_widget_set_size_request
  (GtkWindowIsGtkWidget | !p_window, 100, 100)

val (pf_button | p_button) = gtk_button_new_with_label ("?")
val (pf_menu | p_menu) = gtk_menu_new ()

val r_menu = g_objref_make_some (pf_menu | p_menu)
val () = g_signal_connect_event
  (!p_button, GSIGNAL_EVENT, menu_button_press_event_ref, r_menu)

val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)

val () = gtk_container_add_ref
  (GtkWindowIsGtkContainer, GtkButtonIsGtkWidget | !p_window, !p_button)

val r_button = g_objref_make_some (pf_button | p_button)

val (pf_menu | p_menu) = g_objref_get r_menu
val () = menu_items_append (!p_menu, 0, r_button)
val () = g_objref_set (pf_menu | r_menu, p_menu)

val () = gtk_widget_show (GtkWindowIsGtkWidget | !p_window)
val () = gtk_toplevel_add (GtkWindowIsGtkWidget, pf_window | p_window)

in

gtk_main ()

end

(* ****** ****** *)

%{^

static gboolean menu_button_press_event
  (ats_ptr_type button, ats_ptr_type event, ats_ptr_type menu)
{
  GdkEventButton *bevent ;

  if ((((GdkEvent*)event)->type) == GDK_BUTTON_PRESS) {

    bevent = (GdkEventButton *) event ;

    gtk_menu_popup (menu, NULL, NULL, NULL, NULL, bevent->button, bevent->time) ;

    /* Tell calling code that we have handled this event; the buck stops here. */
    return TRUE;
  }

  /* Tell calling code that we have not handled this event; pass it on. */
  return FALSE;
}

%}

(* ****** ****** *)

%{

void mainats (ats_int_type argc, ats_ptr_type argv) {

gtk_init ((int*)&argc, (char***)&argv) ;
main_menu () ;
return ;

}

%}

(* ****** ****** *)

(* end of [menu.dats] *)
