(*
**
** A simple GTK example: file selection
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

fun file_open {l:agz} (
    chooser: !gobjref (GtkFileChooser, l)
  ) : void = () where {
  val [l1:addr] gstr = gtk_file_chooser_get_filename (chooser)
  val () = printf ("%s\n", @(__cast gstr)) where {
    extern castfn __cast (x: !gstring l1): string
  } // end of [val]
  val () = gstring_free (gstr)
} // end of [file_open]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

overload gint with gint_of_GtkResponseType

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val filew = gtk_file_chooser_dialog_new
    (stropt_some "File Chooser Test", GTK_FILE_CHOOSER_ACTION_OPEN)
//
  val (fpf_x | x) = (gs)GTK_STOCK_CANCEL
  val (fpf_btn | btn) = gtk_dialog_add_button (filew, x, GTK_RESPONSE_CANCEL)
  prval () = fpf_x (x)
(*
  val isflt = g_object_is_floating (btn)
  val () = (print "isflt = "; print isflt; print_newline ())
  val refcnt = g_object_ref_count (btn)
  val () = (print "refcnt = "; print refcnt; print_newline ())
*)
  prval () = minus_addback (fpf_btn, btn | filew)
//
  val (fpf_x | x) = (gs)GTK_STOCK_OPEN
  val (fpf_btn | btn) = gtk_dialog_add_button (filew, x, GTK_RESPONSE_ACCEPT)
  prval () = fpf_x (x)
  prval () = minus_addback (fpf_btn, btn | filew)
//
  val _sid = g_signal_connect
    (filew, (gsignal)"destroy", G_CALLBACK(gtk_widget_destroy), (gpointer)null)
//
  val (fpf_chooser | chooser) = gtk_file_chooser_dialog_get_chooser (filew)
//
  // val _ret = gtk_file_chooser_set_filename (filew, "/tmp")
//
  val response = gtk_dialog_run (filew)
//
  val () = (case+ 0 of
    | _ when (response = (gint)GTK_RESPONSE_ACCEPT) => file_open (chooser)
    | _ => ()
  ) : void // end of [val]
//
  prval () = minus_addback (fpf_chooser, chooser | filew)
//
  val () = gtk_widget_destroy0 (filew)
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

(* end of [gtk-test15.dats] *)
