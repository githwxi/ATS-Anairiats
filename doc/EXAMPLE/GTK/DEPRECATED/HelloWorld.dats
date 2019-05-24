%{^

#include "gtk.cats"
#include "glib.cats"

extern void mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "gtk.sats"
staload "glib.sats"

//

fn hello_world {c:gcls} (wid: &gobj c, data: &void): void =
  print ("Hello, world!\n")

fn delete_event {c:gcls} (wid: &gobj c, evt: &gevent, data: &void): gboolean =
  (print ("delete event occurred!\n"); GBOOLEAN_TRUE)

fn destroy {c:gcls} (wid: &gobj c, data: &void): void =
  begin print ("destroy signal occurred!\n"); gtk_main_quit () end

fn destroy_window {c:gcls}
  (wid: &gobj c, win: gobjref GtkWindow): void = let
  val (pf_win | p_win) = g_objref_get (win)
in
  gtk_widget_destroy (GtkWindowIsGtkWidget, pf_win | p_win)
end // end of [destroy_window]

(* ****** ****** *)

extern fun main_HelloWorld (): void = "main_HelloWorld"

implement main_HelloWorld () = let

val dummy: ref void = ref_void_make ()

val (pf_window | p_window) =
  gtk_window_new (GTK_WINDOW_TOPLEVEL)

val () = gtk_container_set_border_width
  (GtkWindowIsGtkContainer | !p_window, 10)
val () = g_signal_connect_ref {void}
  (!p_window, GSIGNAL_DESTROY, destroy, dummy)
val () = g_signal_connect_event_ref {void}
  (!p_window, GSIGNAL_DELETE_EVENT, delete_event, dummy)

val (pf_button | p_button) =
  gtk_button_new_with_label ("Hello, world!")

val () = gtk_widget_show (GtkButtonIsGtkWidget | !p_button)
val () = gtk_widget_show (GtkWindowIsGtkWidget | !p_window)

val () = gtk_container_add_ref
  (GtkWindowIsGtkContainer, GtkButtonIsGtkWidget | !p_window, !p_button)

val () = g_signal_connect_ref {void}
  (!p_button, GSIGNAL_CLICKED, hello_world, dummy)

val r_window = g_objref_make_some (pf_window | p_window)

val () = g_signal_connect
  (!p_button, GSIGNAL_CLICKED, destroy_window, r_window)

val () = g_object_unref (pf_button | p_button)

in

gtk_main ()

end // end of [main]

(* ****** ****** *)

implement main_dummy () = () // [mainats] is implemented in C

%{$

void mainats (ats_int_type argc, ats_ptr_type argv) {

gtk_init ((int*)&argc, (char***)&argv) ;
main_HelloWorld () ;
return ;

}

%} // end of [%{$]

(* ****** ****** *)

(* end of [HelloWorld.dats] *)
