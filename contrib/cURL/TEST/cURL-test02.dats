(*
**
** A cURL example using GTK to show a progress bar while downloading
** Based on libcurl example: http://curl.haxx.se/libcurl/c/curlgtk.html
*
** Author: Chris Double (chris.double AT double DOT co DOT nz)
** Time: June, 2010
**
*)

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload "contrib/cURL/SATS/curl.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload "libc/SATS/pthread.sats"

(* ****** ****** *)

fun my_progress_func {l:agz} (
  bar: !GtkProgressBar_ref l, 
  t:double,
  d:double,
  ultotal:double,
  ulnow:double): int = let
  val () = gtk_progress_bar_set_fraction (bar, (gdouble)(d/t))
in
  0
end

(* ****** ****** *)

extern fun my_thread
  (pf: CURLglobal_v 0 | bar: GtkProgressBar_ref1): void

implement my_thread (pf_gerr | bar) = () where {
  val curl  = curl_easy_init ()
  val () = assert_errmsg (curlptr_isnot_null curl, #LOCATION)
//
  val (pf_err | err) = curl_easy_setopt (curl, CURLOPT_URL, @("www.ats-lang.org"))
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
//
  val (pf_err | err) = curl_easy_setopt (curl, CURLOPT_NOPROGRESS, @(0))
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
//
  val (pf_err | err) = curl_easy_setopt (curl, CURLOPT_PROGRESSFUNCTION, @(my_progress_func))
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
//
  val p_bar = ptr_of (bar)
  val (pf_err | err) = curl_easy_setopt (curl, CURLOPT_PROGRESSDATA, @(p_bar))
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
//
  val (pf_err | err) = curl_easy_perform (curl)
  val () = assert_errmsg (err = CURLE_OK, #LOCATION)
  prval () = curlerr_elim_null (pf_err)
//
  val () = g_object_unref (bar)
  val () = curl_easy_cleanup (curl)
  val () = curl_global_cleanup (pf_gerr | (*none*))
} // end of [my_thread]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1(): void = "main1"

implement main1 () = () where {
//
  val (pf_gerr | gerr) = curl_global_init (CURL_GLOBAL_ALL)
  val () = assert_errmsg (gerr = CURLE_OK, #LOCATION)
//
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val (fpf_window | window_) = g_object_vref (window)
  val _sid = g_signal_connect0 (
    window_, (gsignal)"destroy", (G_CALLBACK)gtk_main_quit, (gpointer)null
  ) // end of [val]

  val (fpf_x | x) = (gs)"cURL and GTK";
  val frame = gtk_frame_new (x); 
  val () = gtk_frame_set_shadow_type (frame, GTK_SHADOW_OUT)
  val () = gtk_container_add (window, frame);
  prval () = fpf_x (x);

  val (fpf_x | x) = (gs)"Progress";
  val frame2 = gtk_frame_new (x);
  prval () = fpf_x (x);

  val () = gtk_frame_set_shadow_type (frame2, GTK_SHADOW_IN)
  val () = gtk_container_add (frame, frame2)
  val () = gtk_container_set_border_width (frame2, (guint)5)
  val adj = gtk_adjustment_new ((gdouble)0, (gdouble)0, (gdouble)100, (gdouble)0, (gdouble)0, (gdouble)0)
  val bar = gtk_progress_bar_new_with_adjustment (adj)
  val () = gtk_container_add (frame2, bar)
  val () = gtk_widget_show_all (window) 

  val () = pthread_create_detached_cloptr (llam () => my_thread (pf_gerr | bar))

  val () = g_object_unref adj
  val () = g_object_unref frame
  val () = g_object_unref frame2

  prval () = fpf_window (window);

  val () = gtk_main ();
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

(* end of [cURL-test02.dats] *)
