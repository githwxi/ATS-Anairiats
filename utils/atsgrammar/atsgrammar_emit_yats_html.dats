(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload "libc/SATS/time.sats"
staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

fun emit_sym_term
  (out: FILEref, x: symbol): void = let
  val name = symbol_get_name (x)
  val tname = symbol_get_tyname (x)
  val () = fprint_string (out, "%token ")
  val () = if
    tyname_is_some (tname) then let
    val () = fprint_string (out, "&lt;")
    val () = fprint_tyname (out, tname)
    val () = fprint_string (out, "&gt; ")
  in
    // nothing
  end // end of [val]
  val () = fprint_string (out, name)
  val () = fprint_newline (out)
in
  // nothing
end // end of [emit_sym_term]

fun emit_symall_term (
  out: FILEref, xs: !symlst_vt
) : void = let
  fun loop (out: FILEref, xs: !symlst_vt): void =
    case+ xs of
    | list_vt_cons (x, !p_xs1) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then () else emit_sym_term (out, x)
        val () = loop (out, !p_xs1)
      in
        fold@ (xs)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs) // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, xs)
end // end of [emit_symall_term]

(* ****** ****** *)

fun emit_sym_nonterm
  (out: FILEref, x: symbol): void = let
  val name = symbol_get_name (x)
  val tname = symbol_get_tyname (x)
  val () = fprint_string (out, "%type ")
  val () = if
    tyname_is_some (tname) then let
    val () = fprint_string (out, "&lt;")
    val () = fprint_tyname (out, tname)
    val () = fprint_string (out, "&gt; ")
  in
    // nothing
  end // end of [val]
  val () = fprint_string (out, name)
  val () = fprint_newline (out)
in
  // nothing
end // end of [emit_sym_nonterm]

fun emit_symall_nonterm (
  out: FILEref, xs: !symlst_vt
) : void = let
  fun loop (out: FILEref, xs: !symlst_vt): void =
    case+ xs of
    | list_vt_cons (x, !p_xs1) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then emit_sym_nonterm (out, x) else ()
        val () = loop (out, !p_xs1)
      in
        fold@ (xs)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs) // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, xs)
end // end of [emit_symall_nonterm]

(* ****** ****** *)

fun emit_symreg (
  out: FILEref, r: symreg
) : void = case+ r of
  | SYMREGlit (x) => let
      val isnt = symbol_get_nonterm (x)
      val clsname = (if isnt then "nonterm" else "term"): string
      val name = symbol_get_name (x)
      val () = if isnt then fprintf (out, "<a href=#%s>", @(name))
      val () = fprintf (out, "<span class=%s>%s</span>", @(clsname, name))
      val () = if isnt then fprintf (out, "</a>", @())
    in
      // nothing
    end // end of [SYMREGlit]
  | _ => fprintf (out, "<span class=ERROR>ERROR</span>", @())
// end of [emit_symreg]

fun emit_grmrule (
  out: FILEref, gr: grmrule
) : void = let
//
  fun loop (
    out: FILEref, xs: symreglst, i: int
  ) : void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if (i > 0) then fprint_string (out, " ")
        val () = emit_symreg (out, x)
      in
        loop (out, xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
//
  val xs = grmrule_get_symreglst (gr)
//
  val () = (case+ xs of
    | list_cons _ => loop (out, xs, 0)
    | list_nil () => fprint_string (out, "<span class=comment>/*(empty)*/</span>")
  ) : void // end of [val]
  val action = grmrule_get_action (gr)
//
  val () = if
    stropt_is_some (action) then let
    val action = stropt_unsome (action)
  in
    fprintf (out, " <span class=action>%s</span>", @(action))
  end // end of [val]
//
  val precval = grmrule_get_precval (gr)
  val () = if
    stropt_is_some (precval) then let
    val precval = stropt_unsome (precval)
  in
    fprintf (out, " <span class=precval>%s</span>", @(precval))
  end // end of [val]
//
in
  // nothing
end // end of [emit_grmrule]

(* ****** ****** *)

fun emit_sym_defn (
  out: FILEref, x: symbol
) : void = let
  fun loop (
    out: FILEref, grs: grmrulelst, i: &int
  ) : void =
    case+ grs of
    | list_cons (gr, grs) => let
        val knd = grmrule_get_kind (gr)
        val () = if knd = 0 then let
          val c = (
            if i = 0 then ':' else '|'
          ) : char // end of [val]
          val () = i := i+1
          val () = fprintf (out, "  %c ", @(c))
          val () = emit_grmrule (out, gr)
          val () = fprint_newline (out)
        in
          // nothing
        end // end of [val]
      in
        loop (out, grs, i)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
//
  val name = symbol_get_name (x)
  val () = fprintf (
    out, "<a name=\"%s\"><span class=nonterm>%s</span></a>\n", @(name, name)
  ) // end of [val]
  var i: int = 0
  val () = loop (out, symbol_get_grmrulelst (x), i)
  val () = fprintf (out, "; <span class=comment>/* %s */</span>\n\n", @(name))
//
in
  // nothing  
end // end of [emit_sym_defn]

(* ****** ****** *)

fun emit_symall_defn (
  out: FILEref, xs: !symlst_vt
) : void = let
  fun loop (out: FILEref, xs: !symlst_vt): void =
    case+ xs of
    | list_vt_cons (x, !p_xs1) => let
        val isnt = symbol_get_nonterm (x)
        val () = if isnt then emit_sym_defn (out, x)
        val () = loop (out, !p_xs1)
      in
        fold@ (xs)
      end // end of [list_vt_cons]
    | list_vt_nil () => fold@ (xs) // end of [list_vt_nil]
  // end of [loop]
in
  loop (out, xs)
end // end of [emit_symall_defn]

(* ****** ****** *)

val thePreamble = "\
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n\
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n\
<html xmlns=\"http://www.w3.org/1999/xhtml\">\n\
<head>\n\
  <title></title>\n\
  <meta http-equiv=\"Content-Type\" content=\"text/html;charset=utf-8\"/>\n\
  <style type=\"text/css\">\n\
    span.term {color:#000000}\n\
    span.nonterm {color:#0000FF}\n\
    span.action {color:#E80000}\n\
    span.precval {color:#009000}\n\
    span.comment {color:#787878;font-style:italic}
    body {color:#000000;background-color:#E0E0E0}\n\
  </style>\n\
</head>\n\
<body>\n\
<pre>\n\
" // end of [thePreamble]

val thePostamble = "\
<span class=comment>\
/* ****** ****** */\n\n\
/* end of [ats_grammar.yats] */\n\
</span>\n\
</pre>\n\
</body>\n\
</html>\n\
" // end of [thePostamble]

(* ****** ****** *)

val theATSGrammarHeader = "\
/************************************************************************/\n\
/*                                                                      */\n\
/*                         Applied Type System                          */\n\
/*                                                                      */\n\
/*                              Hongwei Xi                              */\n\
/*                                                                      */\n\
/************************************************************************/\n\
\n\
/*\n\
** ATS/Anairiats - Unleashing the Potential of Types!\n\
**\n\
** Copyright (C) 2002-2008 Hongwei Xi.\n\
**\n\
** All rights reserved\n\
**\n\
** ATS is free software;  you can  redistribute it and/or modify it under\n\
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the\n\
** Free Software Foundation; either version 3, or (at  your  option)  any\n\
** later version.\n\
** \n\
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY\n\
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or\n\
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License\n\
** for more details.\n\
** \n\
** You  should  have  received  a  copy of the GNU General Public License\n\
** along  with  ATS;  see the  file COPYING.  If not, please write to the\n\
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA\n\
** 02110-1301, USA.\n\
*/\n\
\n\
/* ****** ****** */\n\
//\n\
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)\n\
// Start time: July 2007\n\
//\n\
/* ****** ****** */\n\
\n\
/*\n\
** Grammar for ATS/Anairiats\n\
*/\
" // end of [theATSGrammarHeader]

(* ****** ****** *)

val thePrecedenceHeader = "\
%nonassoc PATAS\n\
%nonassoc PATFREE\n\
\n\
%nonassoc SEXPLAM\n\
%nonassoc DEXPLAM\n\
%nonassoc DEXPFIX\n\
\n\
%nonassoc CLAUS\n\
%nonassoc DEXPCASE\n\
%nonassoc DEXPIF\n\
\n\
%nonassoc DEXPRAISE\n\
%nonassoc DEXPTRY\n\
\n\
%nonassoc DEXPFOR\n\
%nonassoc DEXPWHILE\n\
\n\
%nonassoc ELSE\n\
%nonassoc WHERE\n\
\n\
%right COLON /* <d0exp> : <s0exp> : <s0rt> */\n\
\n\
%nonassoc BARCLAUSSEQNONE\n\
%nonassoc BAR\n\
\n\
%nonassoc GT\n\
%nonassoc TMPSEXP\n\
%nonassoc TMPSARG\n\
\n\
%nonassoc SARRIND\n\
%nonassoc LBRACKET\n\
\n\
%nonassoc SEXPDARGSEQEMPTY\n\
%nonassoc LBRACE\n\
" // end of [thePrecedenceHeader]

(* ****** ****** *)

implement
emit_yats_html (out) = let
  val () = fprint_string (out, thePreamble)
//
  val () = fprintf (
    out, "<span class=comment>%s</span>\n", @(theATSGrammarHeader)
  ) // end of [val]
//
  var time: time_t // uninitialized
  val () = assertloc (time_get_and_set (time))
  prval () = opt_unsome (time)
//
  val () = fprint_string (out, "\n<span class=comment>/* ****** ****** */\n\n")
  val () = fprint_string (out, "/*\n")
  val (fpf_str | p_str) = ctime (time)
  val () = fprintf (out, "** Time of Generation: %s", @($UN.castvwtp1 {string} (p_str)))
  prval () = fpf_str (p_str)
  val () = fprint_string (out, "*/</span>\n")
//
  val () = () where {
    val xs = theSymlst_get ()
    val xs = list_vt_reverse (xs)
//
    val () = fprint_string (out, "\n<span class=comment>/* ****** ****** */\n\n")
    val () = fprint_string (out, "/*\n")
    val () = fprint_string (out, "** terminals\n")
    val () = fprint_string (out, "*/</span>\n\n")
    val () = emit_symall_term (out, xs)
//
    val () = fprint_string (out, "\n<span class=comment>/* ****** ****** */\n\n")
    val () = fprint_string (out, "/*\n")
    val () = fprint_string (out, "** precedence\n")
    val () = fprint_string (out, "*/</span>\n\n")
    val () = fprint_string (out, thePrecedenceHeader)
//
    val () = fprint_string (out, "\n<span class=comment>/* ****** ****** */\n\n")
    val () = fprint_string (out, "/*\n")
    val () = fprint_string (out, "** nonterminals\n")
    val () = fprint_string (out, "*/</span>\n\n")
    val () = emit_symall_nonterm (out, xs)
//
    val () = fprint_string (out, "\n<span class=comment>/* ****** ****** */\n\n")
    val () = fprint_string (out, "/*\n")
    val () = fprint_string (out, "** production rules\n")
    val () = fprint_string (out, "*/</span>\n\n")
    val () = emit_symall_defn (out, xs)
//
    val () = list_vt_free (xs)
  } // end of [val]
//
  val () = fprint_string (out, thePostamble)
//
in
  // nothing
end // end of [emit_yats_html]

(* ****** ****** *)

(* end of [atsgrammar_emit_yats_html.dats] *)
