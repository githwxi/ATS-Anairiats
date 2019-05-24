(*
**
** A simple Clutter example: a window
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: June, 2010
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

staload "contrib/Clutter/SATS/clutter.sats"
staload "contrib/Clutter/SATS/clutterclassdec.sats"

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val (fpf_stage | stage) = clutter_stage_get_default ()
//
  var color: ClutterColor
  val (fpf_x | x) = (gs)"Spinny box ahoy!"
  val () = clutter_stage_set_title (stage, x)
  prval () = fpf_x (x)
  val () = color.red := (guint8)0
  val () = color.green := (guint8)0
  val () = color.blue := (guint8)0
  val () = color.alpha := (guint8)0xFF
  val () = clutter_stage_set_color (stage, color)
  val () = clutter_actor_set_size (stage, (gfloat)512, (gfloat)512)
  val () = clutter_actor_show (stage)
//
  val () = color.red := (guint8)0
  val () = color.green := (guint8)0xFF
  val () = color.blue := (guint8)0
  val () = color.alpha := (guint8)0x80
  val rect = clutter_rectangle_new_with_color (color);
  val () = clutter_actor_set_size (rect, (gfloat)100, (gfloat)100)
  val () = clutter_actor_set_position (rect, (gfloat)100, (gfloat)100)
  val (fpf_container | container) = CLUTTER_GROUP_GET_CONTAINER (stage)
  val () = clutter_container_add_actor (container, rect)
  prval () = minus_addback (fpf_container, container | stage)
  val () = clutter_actor_show (rect)
  val () = g_object_unref (rect)
//
  val () = clutter_main ()
//
  prval () = fpf_stage (stage)
} // end of [main1]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  int err = clutter_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [clutter-test01.dats] *)
