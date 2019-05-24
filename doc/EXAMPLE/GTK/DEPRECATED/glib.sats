(*******************************************************************)
(*                                                                 *)
(*                        Applied Type System                      *)
(*                                                                 *)
(*                          (c) Hongwei Xi                         *)
(*                                                                 *)
(*                            2002 - 2007                          *)
(*                                                                 *)
(*                         Boston University                       *)
(*                                                                 *)
(*                   Distributed by permission only.               *)
(*                                                                 *)
(*******************************************************************)

(* ****** ****** *)

abst@ype gboolean = $extype "gboolean"

macdef GBOOLEAN_TRUE = $extval (gboolean, "TRUE")
macdef GBOOLEAN_FALSE = $extval (gboolean, "FALSE")

abst@ype gchar = $extype "gchar"
abstype gchar_ptr // = gchar_ptr

abstype gsignal // gchar_ptr

macdef GSIGNAL_ACTIVATE = $extval (gsignal, "\"activate\"")
macdef GSIGNAL_CLICKED = $extval (gsignal, "\"clicked\"")
macdef GSIGNAL_DESTROY = $extval (gsignal, "\"destroy\"")

macdef GSIGNAL_EVENT = $extval (gsignal, "\"event\"")
macdef GSIGNAL_DELETE_EVENT = $extval (gsignal, "\"delete_event\"")

abst@ype guint = $extype "guint"

(* ****** ****** *)

datasort gcls = (* abstract *)

absviewt@ype gobj (c: gcls)

viewtypedef gobjptr (c: gcls, l:addr) = @(gobj c @ l | ptr l)
viewtypedef gobjptr (c: gcls) = [l:addr] gobjptr (c, l)
abstype gobjref (c: gcls)

absviewt@ype gevent

(* ****** ****** *)

fun g_object_ref {c:gcls} {l:addr}
  (pf: !gobj c @ l | p: ptr l): (gobj c @ l | ptr l)
  = "g_object_ref"

fun g_object_unref
  {c:gcls} {l:addr} (pf: gobj c @ l | p: ptr l): void
  = "g_object_unref"

(* ****** ****** *)

fun g_objref_make_some
  {c:gcls} {l:addr} (pf: gobj c @ l | p: ptr l): gobjref c
  = "ats_g_objref_make_some"

fun g_objref_make_none {c:gcls} (): gobjref c
  = "ats_g_objref_make_none"

fun g_objref_get {c:gcls}
  (_: gobjref c): [l:addr] (gobj c @ l | ptr l)
  = "ats_g_objref_get"

fun g_objref_set {c:gcls} {l:addr}
  (pf: gobj c @ l | r: gobjref c, p: ptr l): void
  = "ats_g_objref_set"

fun g_objref_get_opt {c:gcls}
  (r: gobjref c): [l:addr] (option_v (gobj c @ l, l <> null) | ptr l)
  = "ats_g_objref_get_err"

fun g_objref_set_opt {c:gcls} {l:addr}
  (pf: gobj c @ l | r: gobjref c, p: ptr l)
  : [i:nat] (option_v (gobj c @ l, i > 0) | int i)
  = "ats_g_objref_set_err"

(* ****** ****** *)

fun g_signal_connect {a:type} {c:gcls}
  (_: &gobj c, _: gsignal, _: (&gobj c, a) -<fun1> void, _: a): void
  = "ats_g_signal_connect"

fun g_signal_connect_ref {a:viewt@ype} {c:gcls}
  (_: &gobj c, _: gsignal, _: (&gobj c, &a) -<fun1> void, _: ref a)
  : void
  = "ats_g_signal_connect"

fun g_signal_connect_swapped {a:type} {c:gcls}
  (_: &gobj c, _: gsignal, _: (a, &gobj c) -<fun1> void, _: a): void
  = "ats_g_signal_connect_swapped"

fun g_signal_connect_swapped_ref {a:viewt@ype} {c:gcls}
  (_: &gobj c, _: gsignal, _: (&a, &gobj c) -<fun1> void, _: ref a): void
  = "ats_g_signal_connect_swapped"

fun g_signal_connect_event {a:type} {c:gcls}
  (_: &gobj c, _: gsignal, _: (&gobj c, &gevent, a) -<fun1> gboolean, _: a)
  : void
  = "ats_g_signal_connect_event"

fun g_signal_connect_event_ref {a:viewt@ype} {c:gcls}
  (_: &gobj c, _: gsignal, _: (&gobj c, &gevent, &a) -<fun1> gboolean, _: ref a): void
  = "ats_g_signal_connect_event"

(* ****** ****** *)

(* end of [glib.sats] *)

