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

staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

fun symbol_get_descname
  (x: symbol): string = let
  val fname = symbol_get_fullname (x)
in
  if stropt_is_some (fname)
    then stropt_unsome (fname) else symbol_get_name (x)
  // end of [if]
end // end of [symbol_get_descname]

fun emit_symreg_desc (
  out: FILEref, r: symreg
) : void = let
//
#define PRECalt 10
#define PRECseq 20
(*
#define PRECopt 1000000 // infinity
#define PRECstar 1000000 // infinity
#define PRECplus 1000000 // infinity
*)
#define PRECini 1000000 // infinity
//
fun emit (p: int, r: symreg):<cloref1> void =
  case+ r of
  | SYMREGlit (x) => {
      val isnt = symbol_get_nonterm (x)
      val clsname = (if isnt then "nonterm" else "term"): string
      val name = symbol_get_name (x)
      val () = if isnt then fprintf (out, "<a href=#%s>", @(name))
      val fname = symbol_get_descname (x)
      val () = fprintf (out, "<span class=%s>%s</span>", @(clsname, fname))
      val () = if isnt then fprintf (out, "</a>", @())
    } // end of [SYMREGlit]
  | SYMREGseq (x1, x2) => let
      val () = if p > PRECseq then fprint (out, "(")
      val () = emit (PRECseq, x1)
      val () = fprint (out, " , ")
      val () = emit (PRECseq, x2)
      val () = if p > PRECseq then fprint (out, ")")
    in
      // nothing
    end // end of [SYMREGseq]
  | SYMREGalt (x1, x2) => let
      val () = if p > PRECalt then fprint (out, "(")
      val () = emit (PRECalt, x1)
      val () = fprint (out, " | ")
      val () = emit (PRECalt, x2)
      val () = if p > PRECalt then fprint (out, ")")
    in
      // nothing
    end // end of [SYMREGalt]
  | SYMREGopt (x) => let
      val () = fprint (out, "[")
      val () = emit (0, x)
      val () = fprint (out, "]")
    in
      // nothing
    end // end of [SYMREGopt]
  | SYMREGstar (x) => let
      val () = fprint (out, "{")
      val () = emit (0, x)
      val () = fprint (out, "}")
    in
      // nothing
    end // end of [SYMREGstar]
  | SYMREGplus (x) => let
      val () = fprint (out, "{")
      val () = emit (0, x)
      val () = fprint (out, "}+")
    in
      // nothing
    end // end of [SYMREGplus]
// end of [emit]
in
  emit (PRECini, r)
end // end of [emit_symreg_desc]

(* ****** ****** *)

fun emit_grmrule_desc (
  out: FILEref, gr: grmrule
) : void = let
  fun loop (
    out: FILEref, xs: symreglst, i: int
  ) : void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if (i > 0) then fprint_string (out, " ")
        val () = emit_symreg_desc (out, x)
      in
        loop (out, xs, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
  val xs = grmrule_get_symreglst (gr)
in
  case+ xs of
  | list_cons _ => loop (out, xs, 0)
  | list_nil () => fprint_string (out, "<span class=comment>/*(empty)*/</span>")
end // end of [emit_grmrule_desc]

(* ****** ****** *)

fun emit_sym_defn (
  out: FILEref, x: symbol
) : void = let
  fun loop (
    out: FILEref, grs: grmrulelst, i: &int
  ) : void =
    case+ grs of
    | list_cons (gr, grs) => let
        val ismrgd = grmrule_get_merged (gr)
        val () = if ismrgd = 0 then let
          val () = i := i + 1
          val () = fprintf (out, "  | ", @())
          val () = emit_grmrule_desc (out, gr)
          val () = fprint_newline (out)
        in
          // nothing
        end // end of [if]
      in
        loop (out, grs, i)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
//
  val name = symbol_get_name (x)
  val fname = symbol_get_descname (x)
  val () = fprintf (
    out, "<a name=\"%s\"><span class=nonterm>%s</span></a> ::= \n", @(name, fname)
  ) // end of [val]
  var i: int = 0
  val () = loop (out, symbol_get_grmrulelst (x), i)
  val () = fprintf (out, "; <span class=comment>/* %s */</span>\n\n", @(fname))
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
    | list_vt_nil () => (fold@ xs) // end of [list_vt_nil]
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
/* end of [ats_grammar.desc] */\n\
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
// This version is prepared together with\n\
// Sylvain Nahas (sylvain.nahas AT googlemail DOT com)\n\
//\n\
/* ****** ****** */\n\
" // end of [theATSGrammarHeader]

(* ****** ****** *)

val theTitle = "\
<H2>Grammar for ATS/Anairiats</H2>\n\
" // end of [theTitle]

(* ****** ****** *)

val theEBNFnotation = "\
<H3>Some Explanation on the EBNF Notation</H3>\n\
\"...\"   : terminal string<BR>\n\
::=     : nonterminal definition<BR>\n\
a , b   : concatenation<BR>\n\
(...)   : grouping<BR>\n\
{a}     : 0 or more a (Kleene's star closure)<BR>\n\
{a}+    : 1 or more a (this is an extension to the standard EBNF)<BR>\n\
[a]     : 0 or 1 a (option)<BR>\n\
a | b   : a or b (alternation)<BR>\n\
/*...*/ : comment<BR>\n\
" // end of [theEBNFnotation]

(* ****** ****** *)

implement
emit_desc_html (out) = let
  val () = fprint_string (out, thePreamble)
//
  val () = fprintf (
    out, "<span class=comment>%s</span>\n", @(theATSGrammarHeader)
  ) // end of [val]
//
  val () = fprintf (out, "<HR>\n", @())
  val () = fprint_string (out, theTitle)
  val () = fprintf (out, "<HR>\n", @())
//
  val () = fprint_string (out, theEBNFnotation)
  val () = fprintf (out, "<HR>\n", @())
//
  val xs = theSymlst_get ()
  val xs = list_vt_reverse (xs)
  val () = emit_symall_defn (out, xs)
//
  val () = fprint_string (out, thePostamble)
in
  list_vt_free (xs)
end // end of [emit_desc_html]

(* ****** ****** *)

(* end of [atsgrammar_emit_desc_html.dats] *)
