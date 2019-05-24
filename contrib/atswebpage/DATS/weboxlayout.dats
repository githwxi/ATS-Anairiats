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

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "contrib/atswebpage/SATS/weboxlayout.sats"

(* ****** ****** *)

local
//
staload "libc/SATS/random.sats"
//
in

implement
randcolor
  () = let
//
  #define i2u uint_of_int
//
  val FF = 256
  val r = randint (FF)
  val b = randint (FF)
  val g = randint (FF)
  val name = sprintf ("#%x%x%x", @((i2u)r, (i2u)b, (i2u)g))
//
in
  Some (string_of_strptr (name))
end // end of [randcolor]

end // end of [local]

(* ****** ****** *)

typedef intlst = List (int)

abstype weboxlst_t
extern
castfn weboxlst_encode (xs: weboxlst): weboxlst_t
extern
castfn weboxlst_decode (xs: weboxlst_t): weboxlst

abstype weboxopt_t
extern
castfn weboxopt_encode (xs: weboxopt): weboxopt_t
extern
castfn weboxopt_decode (xs: weboxopt_t): weboxopt

typedef
webox = '{
  id= int
, name= string
, width= ref(int)
, pwidth= ref(int)
, height= ref(int)
, color= ref(color_t)
, bgcolor= ref(color_t)
, display= ref(display_t)
, float= ref(float_t)
, children= ref(weboxlst_t)
, parent= ref(weboxopt_t)
, tabstyle= ref(tabstyle)
, percentlst= ref(intlst)
} (* end of [webox] *)

(* ****** ****** *)

local

assume webox_t = webox

val theCount = ref<int> (0)
fun genNewId (): int = let
  val n = !theCount in !theCount := n+1; n
end // end of [genNewId]

in // in of [local]

implement
webox_get_id (x) = x.id
implement
webox_get_name (x) = x.name

implement
webox_get_width (x) = !(x.width)
implement
webox_set_width (x, w) = !(x.width) := w

implement
webox_get_pwidth (x) = !(x.pwidth)
implement
webox_set_pwidth (x, pw) = !(x.pwidth) := pw

implement
webox_get_height (x) = !(x.height)
implement
webox_set_height (x, h) = !(x.height) := h

(* ****** ****** *)

implement
webox_get_color (x) = !(x.color)
implement
webox_set_color (x, c) = !(x.color) := c

implement
webox_get_bgcolor (x) = !(x.bgcolor)
implement
webox_set_bgcolor (x, c) = !(x.bgcolor) := c

(* ****** ****** *)

implement
webox_get_display (x) = !(x.display)
implement
webox_set_display (x, v) = !(x.display) := v

(* ****** ****** *)

implement
webox_get_float (x) = !(x.float)
implement
webox_set_float (x, v) = !(x.float) := v

(* ****** ****** *)

implement
webox_get_children (x) = let
  val cs = !(x.children) in weboxlst_decode (cs)
end // end of [webox_get_children]
implement
webox_set_children
  (x, cs) = !(x.children) := weboxlst_encode (cs)
// end of [webox_set_children]

(* ****** ****** *)

implement
webox_get_parent (x) = let
  val opt = !(x.parent) in weboxopt_decode (opt)
end // end of [webox_get_parent]
implement
webox_set_parent
  (x, opt) = !(x.parent) := weboxopt_encode (opt)
// end of [webox_set_children]

(* ****** ****** *)

implement
webox_get_tabstyle (x) = !(x.tabstyle)
implement
webox_set_tabstyle (x, ts) = !(x.tabstyle) := ts

(* ****** ****** *)

implement
webox_get_percentlst (x) = !(x.percentlst)
implement
webox_set_percentlst (x, pcs) = !(x.percentlst) := pcs

(* ****** ****** *)

implement
webox_make_name
  (name) = let
  val id = genNewId ()
  val float_init = Some ("left")
in '{
  id= id
, name= name
, width= ref(~1)
, pwidth= ref(100) // HX: the most common case
, height= ref(~1)
, color= ref(None)
, bgcolor= ref(None)
, display= ref(None)
, float= ref(float_init)
, children= ref(weboxlst_encode(list_nil))
, parent= ref(weboxopt_encode(None))
, tabstyle= ref(TSnone())
, percentlst= ref(list_nil)
} end // end of [webox_make_name]

end // end of [local]

(* ****** ****** *)

typedef color = color_t
typedef webox = webox_t

(* ****** ****** *)

implement
webox_make_name_width
  (name, width) = x where {
  val x = webox_make_name (name)
  val () = webox_set_width (x, width)
} // end of [webox_make_name_width]

(* ****** ****** *)

implement
webox_get_parent_exn (x) = let
  val- Some (p) = webox_get_parent (x) in p
end // end of [webox_get_parent_exn]

(* ****** ****** *)

implement
get_percent_from (pcs, n) =
  case+ pcs of
  | list_cons (pc, pcs) =>
      if n > 0 then get_percent_from (pcs, n-1) else pc
  | list_nil () => ~1 (*special value*)
// end of [get_percent_from]

(* ****** ****** *)

extern
fun fprint_webox_css_one (out: FILEref, x: webox): void

implement
fprint_webox_css_one (out, x0) = {
  macdef prstr (s) = fprint_string (out, ,(s))
  val name = webox_get_name (x0)
  val () = fprintf (out, "#%s {\n", @(name))
//
  val () = fprint_string (out, "/*\nchildren: ")
  val xs = webox_get_children (x0)
  val () = loop (xs, 0) where {
    fun loop (
      xs: weboxlst, i: int
    ) :<cloref1> void =
      case+ xs of
      | list_cons (x, xs) => let
          val name = webox_get_name (x)
          val () = if i > 0 then fprint_string (out, ", ")
          val () = fprint_string (out, name)
        in
          loop (xs, i+1)
        end
      | list_nil () => ()
  } // end of [val]
  val () = fprint_string (out, "\n*/\n")
//
  val width = webox_get_width (x0)
  val pwidth = webox_get_pwidth (x0)
  val () = (
    case+ 0 of
    | _ when width >= 0 =>
        fprintf (out, "width: %ipx ;\n", @(width))
    | _ when pwidth >= 0 =>
        fprintf (out, "width: %i%% ;\n", @(pwidth))
    | _ => ()
  ) : void // end of [val]
//
  val height = webox_get_height (x0)
  val () = if height >= 0 then
    fprintf (out, "height: %ipx ;\n", @(height))
//
  val color = webox_get_color (x0)
  val () = (case+ color of
    | Some (v) => fprintf (out, "color: %s ;\n", @(v)) | None () => ()
  ) : void // end of [val]
//
  val color = webox_get_bgcolor (x0)
  val () = (case+ color of
    | Some (v) => fprintf (out, "background-color: %s ;\n", @(v)) | None () => ()
  ) : void // end of [val]
//
  val display = webox_get_display (x0)
  val () = (case+ display of
    | Some (v) => fprintf (out, "display: %s ;\n", @(v)) | None () => ()
  ) : void // end of [val]
//
  val float = webox_get_float (x0)
  val () = (case+ float of
    | Some (v) => fprintf (out, "float: %s ;\n", @(v)) | None () => ()
  ) : void // end of [val]
//
  val () = fprintf (out, "} /* %s */\n", @(name))
} // end of [fprint_webox_css_one]

(* ****** ****** *)

extern
fun fprint_weboxlst_css_all (out: FILEref, xs: weboxlst): void

implement
fprint_webox_css_all
  (out, x0) = let
  val xs = webox_get_children (x0)
in
  case+ xs of
  | list_cons _ => let
      val () = fprint_weboxlst_css_all (out, xs)
      val () = fprint_string (out, "\n")
    in
      fprint_webox_css_one (out, x0)
    end // end of [list_cons]
  | list_nil () => fprint_webox_css_one (out, x0)
end // end of [fprint_webox_css_all]

implement
fprint_weboxlst_css_all (out, xs) = let
  fun loop (xs: weboxlst, i: int):<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_string (out, "\n")
        val () = fprint_webox_css_all (out, x)
      in
        loop (xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (xs, 0)
end // end of [fprint_weboxlst_css_all]

(* ****** ****** *)

extern
fun fprint_weboxlst_html
  (out: FILEref, ts: tabstyle, pcs: intlst, xs: weboxlst): void
// end of [fprint_weboxlst_html]

implement
fprint_webox_html
  (out, x0) = let
  val name = webox_get_name (x0)
  val () = fprintf (out, "<div id=\"%s\">\n", @(name))
  val xs = webox_get_children (x0)
  val pcs = webox_get_percentlst (x0)
  val isnil = list_is_empty (xs)
  val () = if isnil then {
    val () = fprintf (out, "#%s$\n", @(name)) // HX: it to be interpreted!
  } else {
    val ts = webox_get_tabstyle (x0)
    val () = fprint_weboxlst_html (out, ts, pcs, xs)
  } // end of [val]
  val () = fprintf (out, "</div><!--%s-->\n", @(name))
in
  // nothing
end // end of [fprint_webox_html]

implement
fprint_weboxlst_html
  (out, ts, pcs, xs) = let
  val isbox = (case+ ts of
    | TSvbox () => true | TShbox () => true | _ => false
  ) : bool
  val ishbox = (
    case+ ts of TShbox () => true | _ => false
  ) : bool
  val isvbox = (
    case+ ts of TSvbox () => true | _ => false
  ) : bool
  fun loop {i:nat}
    (xs: weboxlst, i: int i):<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_string (out, "\n")
        val () = if isvbox then fprint_string (out, "<tr>\n")
//
        val () = if ishbox then let
          val pc = get_percent_from (pcs, i)
        in
          case+ 0 of
          | _ when pc >= 0 => fprintf (
              out, "<td style=\"vertical-align: top; width: %d%%;\">\n", @(pc)
            ) // end of [ pc >= 0]
          | _ => fprintf (out, "<td style=\"vertical-align: top;\">\n", @())
        end // end of [val]
        val () = if isvbox then fprint_string (out, "<td>\n") // HX: no [halign]!
//
        val () = fprint_webox_html (out, x)
        val () = if isbox then fprint_string (out, "</td>\n")
        val () = if isvbox then fprint_string (out, "</tr>\n")
      in
        loop (xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
  val () = if isbox then {
    val () = fprintf (
      out, "<table width=\"100%%\" border=\"0\" cellspacing=\"0\" cellpadding=\"0\">\n", @()
    ) // end of [val]
  } (* end of [if] *)
  val () = if ishbox then fprint_string (out, "<tr>\n")
  val () = loop (xs, 0)
  val () = if ishbox then fprint_string (out, "</tr>\n")
  val () = if isbox then fprintf (out, "</table>\n", @())
in
  // nothing
end // end of [fprint_weboxlst_html]

(* ****** ****** *)

(* end of [weboxlayout.dats] *)
