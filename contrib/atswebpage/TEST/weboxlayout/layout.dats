(*
**
** Generating CSS for ATSLANGWEB layout
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Start Time: September, 2011
**
*)

(* ****** ****** *)

staload
"contrib/atswebpage/SATS/weboxlayout.sats"
dynload "contrib/atswebpage/dynloadall.dats"

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

#ifndef TESTING
#define TESTING 0
#endif // end of [#ifndef]

#if(TESTING) #then

fn webox_make_name
  (name: string): webox = let
  val res = webox_make_name (name) 
  val color = randcolor ()
  val () = webox_set_bgcolor (res, color)
in
  res
end // end of [webox_make_name]

fn webox_make_name_width
  (name: string, width: int): webox = let
  val res = webox_make_name_width (name, width)
  val color = randcolor ()
  val () = webox_set_bgcolor (res, color)
in
  res
end // end of [webox_make_name]

#endif // end of [#if(TESTING)]

(* ****** ****** *)

#ifndef RANDCOLOR
#define RANDCOLOR 0
#endif // end of [#ifndef]

#if(RANDCOLOR)
//
local
staload "libc/SATS/random.sats"
in
val () = srand48_with_time ()
end
//
#endif // end of [#if(RANDCOLOR)]

(* ****** ****** *)

val thePage =
  webox_make_name_width ("thePage", thePage_width)
// end of [thePage]

(* ****** ****** *)

val theSidebar =
  webox_make_name_width ("theSidebar", theSidebar_width)
// end of [theSidebar]

(* ****** ****** *)

val thePageHeader =
  webox_make_name_width ("thePageHeader", thePage_width)
// end of [thePageHeader]

val thePageHeaderTitle = 
  webox_make_name_width ("thePageHeaderTitle", thePage_width)
val () = webox_set_height (thePageHeaderTitle, thePageHeaderTitle_height)

val thePageHeaderSeparator = 
  webox_make_name_width ("thePageHeaderSeparator", thePage_width)

val () = webox_set_children (
  thePageHeader, $lst (thePageHeaderTitle, thePageHeaderSeparator)
) // end of [thePageHeader]

val () = webox_set_tabstyle (thePageHeader, TSvbox())

(* ****** ****** *)

val thePageBody =
  webox_make_name_width ("thePageBody", thePage_width)
// end of [thePageBody]
val () = webox_set_height (thePageBody, thePageBody_height)

(* ****** ****** *)

val thePageFooter =
  webox_make_name_width ("thePageFooter", thePage_width)

val thePageFooterSeparator =
  webox_make_name_width ("thePageFooterSeparator", thePage_width)
val thePageFooterRest =
  webox_make_name_width ("thePageFooterRest", thePage_width)
val () = webox_set_height (thePageFooterRest, thePageFooterRest_height)

val () = webox_set_children (
  thePageFooter, $lst (thePageFooterSeparator, thePageFooterRest)
) // end of [thePageFooter]

val () = webox_set_tabstyle (thePageFooter, TSvbox())

(* ****** ****** *)

val () = webox_set_children (
  thePage, $lst (thePageHeader, thePageBody, thePageFooter)
) // end of [thePage]

val () = webox_set_tabstyle (thePage, TSvbox())

(* ****** ****** *)

val theBodyProp =
  webox_make_name ("theBodyProp")
// end of [theBody]

val () = webox_set_children (
  theBodyProp, $lst (theSidebar, thePage)
) // end of [thePage]
val () = webox_set_tabstyle (theBodyProp, TShbox())
val () = webox_set_percentlst (theBodyProp, $lst (~1, 100))

(* ****** ****** *)

(*
implement
main (argc, argv) = let
  val cmd = argv.[0]
  val flag = (
    if argc >= 2 then argv.[1] else "-css"
  ) : string // end of [val]
in
//
case+ flag of
| "-css" => fprint_webox_css_all (stdout_ref, theBodyProp)
| "-html" => fprint_webox_html (stdout_ref, theBodyProp) // recursive
| _ => () where {
    val () = prerr ("The only supported flags are: -css and -html\n")
    val () = exit (1)
  }
//  
end // end of [main]
*)

(* ****** ****** *)

(* end of [layout.dats] *)
