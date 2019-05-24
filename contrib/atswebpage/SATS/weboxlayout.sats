(*
**
** Generating layouts for web pages
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Start Time: August, 2011
**
*)

(* ****** ****** *)
//
// License: GNU LESSER GENERAL PUBLIC LICENSE version 2.1
//
(* ****** ****** *)

typedef color_t = Option (string)
typedef display_t = Option (string)
typedef float_t = Option (string)

(* ****** ****** *)

datatype
tabstyle =
  | TSnone of () | TShbox of () | TSvbox of ()
// end of [tabstyle]

(* ****** ****** *)

fun randcolor (): color_t // random color generation for testing

(* ****** ****** *)

abstype webox_t
typedef webox = webox_t
typedef weboxlst = List (webox)
typedef weboxopt = Option (webox)

fun webox_get_id (x: webox): int // unique indentification
fun webox_get_name (x: webox): string // name given by the user
//
fun webox_get_width (x: webox): int
fun webox_set_width (x: webox, w: int): void
fun webox_get_pwidth (x: webox): int // percent-of
fun webox_set_pwidth (x: webox, w: int): void // percent-of
//
fun webox_get_height (x: webox): int
fun webox_set_height (x: webox, h: int): void
//
fun webox_get_color (x: webox): color_t
fun webox_set_color (x: webox, c: color_t): void
fun webox_get_bgcolor (x: webox): color_t
fun webox_set_bgcolor (x: webox, c: color_t): void
//
fun webox_get_display (x: webox): display_t
fun webox_set_display (x: webox, v: display_t): void
//
fun webox_get_float (x: webox): float_t
fun webox_set_float (x: webox, v: float_t): void
//
fun webox_is_root (x: webox): bool
fun webox_get_parent (x: webox): weboxopt
fun webox_get_parent_exn (x: webox): webox
fun webox_set_parent (x: webox, opt: weboxopt): void
//
fun webox_get_children (x: webox): weboxlst
fun webox_set_children (x: webox, cs: weboxlst): void
//
fun webox_get_tabstyle (x: webox): tabstyle
fun webox_set_tabstyle (x: webox, ts: tabstyle): void
//
// HX: 
// a list of percentages allocated to the children of
// a webox; a negative value is interpreted specially,
// often meaning that the percentage is not available.
//
fun get_percent_from {n:nat}
  (pcs: List (int), n: int n): int // -1 for stray subs
// end of [get_percent_from]
fun webox_get_percentlst (x: webox): List (int)
fun webox_set_percentlst (x: webox, rs: List (int)): void
//
(* ****** ****** *)

fun webox_make_name (name: string): webox
fun webox_make_name_width (name: string, width: int): webox

(* ****** ****** *)

fun fprint_webox_css_one (out: FILEref, x: webox): void
fun fprint_webox_css_all (out: FILEref, x: webox): void

(* ****** ****** *)

fun fprint_webox_html (out: FILEref, x: webox): void // recursive

(* ****** ****** *)

(* end of [weboxlayout.sats] *)
