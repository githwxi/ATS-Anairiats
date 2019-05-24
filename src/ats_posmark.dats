(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2007
//
// Modification by Guillaume Brunerie (guillaume DOT brunerie AT gmail DOT com)
// for XHTML conformity
// Time: August, 2010
//
(* ****** ****** *)

%{^
#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"
%} // end of [%{^]

//
// staload "libc/SATS/stdio.sats"
//
extern
fun fopen_exn
  {m:file_mode} (
  s: string, m: file_mode m
) : [l:addr] (FILE m @ l | ptr l)
  = "atslib_fopen_exn"
// end of [fun]

extern
fun fclose_exn
  {m:file_mode} {l:addr} (
  pf: FILE m @ l | p: ptr l
) :<!exnref> void = "atslib_fclose_exn"

extern
fun fgetc_err
  {m:file_mode} (
  pf: file_mode_lte (m, r) | f: &FILE m
) : int = "mac#atslib_fgetc_err"

extern
fun fputc_exn {m:file_mode} (
  pf: file_mode_lte (m, w) | c: char, f: &FILE m
) : void = "atslib_fputc_exn"

//
// staload "libc/SATS/stdlib.sats"
//
extern fun qsort
  {a:viewt@ype} {n:nat} {f:eff} (
  base: &(@[a][n])
, nmemb: size_t n
, size: sizeof_t a
, compar: (&a, &a) -<f> int
) : void = "mac#atslib_qsort"

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Loc = "ats_location.sats"

(* ****** ****** *)

staload Arr = "ats_array.sats"
staload _(*anonymous*) = "ats_array.dats"

staload Lst = "ats_list.sats"
staload _(*anonymous*) = "ats_list.dats"

(* ****** ****** *)

staload "ats_posmark.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

datatype posmark = // 0/1 : begin/end
  | PMnone
  | PMcomment of int
  | PMextern of int
  | PMkeyword of int
  | PMneuexp of int
  | PMstaexp of int
  | PMprfexp of int
  | PMstacstdec of (int, loc_t(*dec*))
  | PMstacstuse of (int, loc_t(*dec*))
  | PMdyncstdec of (int, loc_t(*dec*))
  | PMdyncstimp of (int, loc_t(*dec*))
  | PMdyncstuse of (int, loc_t(*dec*))
// end of [posmark]

(* ****** ****** *)

#define NPOSMARK1 100
// please make sure that the values assigned to closing tags (i=1)
// are strictly less than the values assigned to opening tags (i=0)
fn int_of_posmark (pm: posmark): int =
  case+ pm of
  | PMnone () => 0
//
  | PMcomment i => if i > 0 then 1 else NPOSMARK1-1
//
  | PMextern  i => if i > 0 then 2 else NPOSMARK1-2
//
  | PMkeyword i => if i > 0 then 3 else NPOSMARK1-3
//
  | PMneuexp  i => if i > 0 then 4 else NPOSMARK1-4
//
  | PMstacstdec (i, _) => if i > 0 then 5 else NPOSMARK1-5
  | PMstacstuse (i, _) => if i > 0 then 6 else NPOSMARK1-6
//
  | PMstaexp  i => if i > 0 then 7 else NPOSMARK1-7
  | PMprfexp  i => if i > 0 then 8 else NPOSMARK1-8
//
  | PMdyncstdec (i, _) => if i > 0 then 20 else NPOSMARK1-20
  | PMdyncstimp (i, _) => if i > 0 then 21 else NPOSMARK1-21
  | PMdyncstuse (i, _) => if i > 0 then 22 else NPOSMARK1-22
// end of [int_of_posmark]

fn compare_posmark_posmark
  (pm1: posmark, pm2: posmark): Sgn =
  compare (int_of_posmark pm1, int_of_posmark pm2)
// end of [compare_posmark_posmark]

(* ****** ****** *)

typedef lintposmark = @(lint, posmark)
viewtypedef lintposmarklst = List_vt lintposmark
viewtypedef lintposmarklstlst = List_vt lintposmarklst

local

val the_posmark_flag = ref_make_elt<int> 0
val the_posmarklst =
  ref_make_elt<lintposmarklst> (list_vt_nil ())
val the_posmarklstlst =
  ref_make_elt<lintposmarklstlst> (list_vt_nil ())

in // in of [local]

implement posmark_enable () = (!the_posmark_flag := 1)
implement posmark_disable () = (!the_posmark_flag := 0)

implement posmark_pause_get () = let
  val flag = !the_posmark_flag in !the_posmark_flag := 0; flag
end // end of [posmark_pause_get]

implement posmark_resume_set
  (flag) = !the_posmark_flag := flag
// end of [posmark_resume_set]

fn the_posmarklst_get (): lintposmarklst = let
  val (vbox pf | p) = ref_get_view_ptr (the_posmarklst)
  val xs = !p
in
  !p := list_vt_nil (); xs
end // end of [the_posmarklst_get]

fn the_posmarklst_insert
  (p: lint, pm: posmark): void =
  if !the_posmark_flag > 0 then let
    val (vbox pf | p_ref) = ref_get_view_ptr (the_posmarklst)
  in
    !p_ref := list_vt_cons ((p, pm), !p_ref)
  end // end of [if]
// (* end of [posmark_insert] *)

implement posmark_pop () = let
  val xs = let
    val (vbox pf | p) = ref_get_view_ptr (the_posmarklstlst)
  in
    case+ !p of
    | ~list_vt_cons (xs, xss) => begin
        !p := (xss: lintposmarklstlst); xs
      end // end of [list_vt_cons]
    | ~list_vt_nil () => let
        val xs = $effmask_ref begin
          prerr "INTERNAL ERROR (ats_posmark)";
          prerr ": posmark_pop: empty stack"; prerr_newline ();
          $Err.abort {lintposmarklst} ()
        end // end of [val]
      in
        !p := list_vt_nil (); xs
      end // end of [list_vt_nil]
  end : lintposmarklst // end of [val]
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_posmarklst)
    val xs1 = !p; val () = !p := xs
  in
    $Lst.list_vt_free (xs1)
  end // end of [val]
in
  // empty
end // end of [posmark_pop]

implement posmark_push () = let
  val xs = let
    val (vbox pf | p) = ref_get_view_ptr (the_posmarklst)
    val xs = !p
  in
    !p := list_vt_nil (); xs
  end // end of [val]
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_posmarklstlst)
  in
    !p := list_vt_cons (xs, !p)
  end // end of [val]
in
  // empty
end // end of [posmark_push]

implement posmark_push_dup () = let
  val xs = let
    val (vbox pf | p) = ref_get_view_ptr (the_posmarklst)
  in
    $Lst.list_vt_copy (!p)
  end // end of [val]
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_posmarklstlst)
  in
    !p := list_vt_cons (xs, !p)
  end // end of [val]
in
  // empty
end // end of [posmark_push]

end // end of [local]

(* ****** ****** *)

implement
posmark_insert_comment_beg (p) = the_posmarklst_insert (p, PMcomment 0)
implement
posmark_insert_comment_end (p) = the_posmarklst_insert (p, PMcomment 1)

implement
posmark_insert_extern_beg (p) = the_posmarklst_insert (p, PMextern 0)
implement
posmark_insert_extern_end (p) = the_posmarklst_insert (p, PMextern 1)

//

implement
posmark_insert_keyword_beg (p) = let
(*
  val () = begin
    print "posmark_insert_keyword_beg"; print_newline ()
  end // end of [val]
*)
in
  the_posmarklst_insert (p, PMkeyword 0)
end // end of [posmark_insert_keyword_beg]

implement
posmark_insert_keyword_end (p) = let
(*
  val () = begin
    print "posmark_insert_keyword_end"; print_newline ()
  end // end of [val]
*)
in
  the_posmarklst_insert (p, PMkeyword 1)
end // end of [posmark_insert_keyword_end]

//

implement posmark_insert_neuexp_beg (p) =
  the_posmarklst_insert (p, PMneuexp 0)
implement posmark_insert_neuexp_end (p) =
  the_posmarklst_insert (p, PMneuexp 1)

implement posmark_insert_staexp_beg (p) =
  the_posmarklst_insert (p, PMstaexp 0)
implement posmark_insert_staexp_end (p) =
  the_posmarklst_insert (p, PMstaexp 1)

implement posmark_insert_prfexp_beg (p) =
  the_posmarklst_insert (p, PMprfexp 0)
implement posmark_insert_prfexp_end (p) =
  the_posmarklst_insert (p, PMprfexp 1)

//

implement posmark_insert_stacstdec_beg (p, loc) =
  the_posmarklst_insert (p, PMstacstdec (0, loc))
implement posmark_insert_stacstdec_end (p, loc) =
  the_posmarklst_insert (p, PMstacstdec (1, loc))

implement posmark_insert_stacstuse_beg (p, loc) =
  the_posmarklst_insert (p, PMstacstuse (0, loc))
implement posmark_insert_stacstuse_end (p, loc) =
  the_posmarklst_insert (p, PMstacstuse (1, loc))

//

implement posmark_insert_dyncstdec_beg (p, loc) =
  the_posmarklst_insert (p, PMdyncstdec (0, loc))
implement posmark_insert_dyncstdec_end (p, loc) =
  the_posmarklst_insert (p, PMdyncstdec (1, loc))

implement posmark_insert_dyncstimp_beg (p, loc) =
  the_posmarklst_insert (p, PMdyncstimp (0, loc))
implement posmark_insert_dyncstimp_end (p, loc) =
  the_posmarklst_insert (p, PMdyncstimp (1, loc))

implement posmark_insert_dyncstuse_beg (p, loc) =
  the_posmarklst_insert (p, PMdyncstuse (0, loc))
implement posmark_insert_dyncstuse_end (p, loc) =
  the_posmarklst_insert (p, PMdyncstuse (1, loc))

(* ****** ****** *)

local

// color= gray
// #define HTM_COMMENT_FONT_BEG "<FONT COLOR=\"#787878\">"
// #define HTM_COMMENT_FONT_END "</FONT>"

#define HTM_COMMENT_FONT_BEG "<span class=\"comment\">"
#define HTM_COMMENT_FONT_END "</span>"

// color= brown
// #define HTM_EXTERN_FONT_BEG "<FONT COLOR=\"#A52A2A\">"
// #define HTM_EXTERN_FONT_END "</FONT>"

#define HTM_EXTERN_FONT_BEG "<span class=\"extern\">"
#define HTM_EXTERN_FONT_END "</span>"

// color= black
// #define HTM_KEYWORD_FONT_BEG "<FONT COLOR=\"#000000\">"
// #define HTM_KEYWORD_FONT_END "</FONT>"

#define HTM_KEYWORD_FONT_BEG "<span class=\"keyword\">"
#define HTM_KEYWORD_FONT_END "</span>"

// color= pink
// #define HTM_NEUEXP_FONT_BEG "<FONT COLOR=\"#800080\">"
// #define HTM_NEUEXP_FONT_END "</FONT>"

#define HTM_NEUEXP_FONT_BEG "<span class=\"neuexp\">"
#define HTM_NEUEXP_FONT_END "</span>"

// color= blue
// #define HTM_STAEXP_FONT_BEG "<FONT COLOR=\"#0000FF\">"
// #define HTM_STAEXP_FONT_END "</FONT>"

#define HTM_STAEXP_FONT_BEG "<span class=\"staexp\">"
#define HTM_STAEXP_FONT_END "</span>"

// color= red
// #define HTM_DYNEXP_FONT_BEG "<FONT COLOR=\"#E80000\">"
// #define HTM_DYNEXP_FONT_END "</FONT>"

#define HTM_DYNEXP_FONT_BEG "<span class=\"dynexp\">"
#define HTM_DYNEXP_FONT_END "</span>"

// color= green
// #define HTM_PRFEXP_FONT_BEG "<FONT COLOR=\"#009000\">"
// #define HTM_PRFEXP_FONT_END "</FONT>"

#define HTM_PRFEXP_FONT_BEG "<span class=\"prfexp\">"
#define HTM_PRFEXP_FONT_END "</span>"

//

#define HTM_STACSTDEC_FONT_BEG "<span class=\"stacstdec\">"
#define HTM_STACSTDEC_FONT_END "</span>"

#define HTM_STACSTUSE_FONT_BEG "<span class=\"stacstuse\">"
#define HTM_STACSTUSE_FONT_END "</span>"

//

#define HTM_DYNCSTDEC_FONT_BEG "<span class=\"dyncstdec\">"
#define HTM_DYNCSTDEC_FONT_END "</span>"

#define HTM_DYNCSTIMP_FONT_BEG "<span class=\"dyncstimp\">"
#define HTM_DYNCSTIMP_FONT_END "</span>"

#define HTM_DYNCSTUSE_FONT_BEG "<span class=\"dyncstuse\">"
#define HTM_DYNCSTUSE_FONT_END "</span>"

//

// color= light gray
// #define HTM_POSMARK_FILE_BEG "<BODY BGCOLOR=\"#E0E0E0\" TEXT=\"#E80000\"><PRE>"
// #define HTM_POSMARK_FILE_END "</PRE></BODY>"

#define HTM_POSMARK_FILE_BEG "\
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n\
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n\
<html xmlns=\"http://www.w3.org/1999/xhtml\">\n\
<head>\n\
  <title></title>\n\
  <meta http-equiv=\"Content-Type\" content=\"text/html;charset=utf-8\"/>\n\
  <style type=\"text/css\">\n\
    .atsyntax {color:#E80000;background-color:#E0E0E0;}\n\
    .atsyntax span.comment {color:#787878;font-style:italic;}\n\
    .atsyntax span.extern  {color:#A52A2A;}\n\
    .atsyntax span.keyword {color:#000000;font-weight:bold;}\n\
    .atsyntax span.neuexp  {color:#800080;}\n\
    .atsyntax span.staexp  {color:#0000FF;}\n\
    .atsyntax span.dynexp  {color:#E80000;}\n\
    .atsyntax span.prfexp  {color:#009000;}\n\
    .atsyntax span.stacstdec  {text-decoration:none;}\n\
    .atsyntax span.stacstuse  {color:#0000CF;text-decoration:underline;}\n\
    .atsyntax span.dyncstdec  {text-decoration:none;}\n\
    .atsyntax span.dyncstimp  {color:#B80000;text-decoration:underline;}\n\
    .atsyntax span.dyncstuse  {color:#B80000;text-decoration:underline;}\n\
  </style>\n\
</head>\n\
<body class=\"atsyntax\">\n\
"
#define HTM_POSMARK_PRE_BEG "<pre class=\"atsyntax\">\n"
#define HTM_POSMARK_PRE_END "</pre>\n"

#define HTM_POSMARK_FILE_END "\
</body>\n\
</html>\n\
"
(* ****** ****** *)

fn posmarklst_sort (
  ppms: lintposmarklst
) : lintposmarklst = let
//
  typedef ppm = lintposmark
//
  fn cmp
    (x1: &ppm, x2: &ppm): Sgn = let
    val x10 = x1.0 and x20 = x2.0 in
    if x10 < x20 then ~1 else begin
      (if x10 > x20 then 1 else compare_posmark_posmark (x1.1, x2.1))
    end // end of [if]
  end // end of [cmp]
//
  fun loop
    {n,i:int | 0 <= i + 1; i + 1 <= n} (
    A: &(@[ppm][n]), i: int i, res: list_vt (ppm, n-i-1)
  ) : list_vt (ppm, n) =
    if i >= 0 then begin
      loop (A, i-1, list_vt_cons (A.[i], res))
    end else begin
      res // return value
    end // end of [if]
  // end of [loop]
//
  val n = $Lst.list_vt_length<ppm> (ppms)
  val (pf_gc, pf_arr | p_arr) =
    $Arr.array_ptr_make_lst_vt<ppm> (n, ppms)
  val () = qsort {ppm} (!p_arr, size1_of_int1 n, sizeof<ppm>, cmp)
  val res = loop (!p_arr, n-1, list_vt_nil ())
  val () = array_ptr_free {ppm?} (pf_gc, pf_arr | p_arr)
//
in
  res
end // end of [posmarklst_sort]
  
(* ****** ****** *)

fn posmark_file_file (
  isall: bool // header+body or body only
, proc: (&FILE w, lint, posmark) -<fun1> void
, fputchr: (char, &FILE w) -<fun1> void
, fil_s: &FILE r, fil_d: &FILE w
) : void = let
//
  typedef ppm =  lintposmark
//
  fun lpfin1 (
    fil_s: &FILE r
  , fil_d: &FILE w
  , p: lint, pm: posmark
  , ppms: List_vt ppm
  ) :<cloref1> void = let
    val () = proc (fil_d, p, pm)
  in
    case+ ppms of
    | ~list_vt_cons (ppm, ppms) =>
        lpfin1 (fil_s, fil_d, ppm.0, ppm.1, ppms)
    | ~list_vt_nil () => ()
  end // end of [lpfin1]
//
  fun lpfin2 (
    fil_s: &FILE r, fil_d: &FILE w
  ) :<cloref1> void = let
    val c = fgetc_err (file_mode_lte_r_r | fil_s)
  in
    if (c >= 0) then begin
      fputchr (char_of_int c, fil_d); lpfin2 (fil_s, fil_d)
    end // end of [if]
  end // end of [lpfin2]
//
  fn* loop1
    (fil_s: &FILE r, fil_d: &FILE w,
     i: lint, p: lint, pm: posmark, ppms: List_vt ppm)
    :<cloref1> void = let
    val c = fgetc_err (file_mode_lte_r_r | fil_s)
  in
    if (c >= 0) then begin
      loop2 (fil_s, fil_d, i, p, pm, ppms, c)
    end else begin
      lpfin1 (fil_s, fil_d, p, pm, ppms)
    end // end of [if]
  end (* end of [loop1] *)
//
  and loop2
    (fil_s: &FILE r, fil_d: &FILE w,
     i: lint, p: lint, pm: posmark, ppms: List_vt ppm, c: int)
    :<cloref1> void = begin
    if i < p then let
      val () = fputchr (char_of_int c, fil_d)
    in
      loop1 (fil_s, fil_d, succ i, p, pm, ppms)
    end else let
      val () = proc (fil_d, p, pm)
    in
      case+ ppms of
      | ~list_vt_cons (ppm, ppms) => begin
          loop2 (fil_s, fil_d, i, ppm.0, ppm.1, ppms, c)
        end // end of [list_vt_cons]
      | ~list_vt_nil () => begin
          fputchr (char_of_int c, fil_d); lpfin2 (fil_s, fil_d)
        end // end of [list_vt_nil]
    end // end of [if]
  end (* end of [loop2] *)
//
  val lint0 = lint_of_int 0 // 0L
  val ppms = posmarklst_sort (the_posmarklst_get ())
//
  prval pf_mod = file_mode_lte_w_w
  val () = if isall then
    fprint1_string (pf_mod | fil_d, HTM_POSMARK_FILE_BEG)
//
  val () = fprint1_string (pf_mod | fil_d, HTM_POSMARK_PRE_BEG)
  val () = loop1 (fil_s, fil_d, lint0, lint0, PMnone (), ppms)
  val () = fprint1_string (pf_mod | fil_d, HTM_POSMARK_PRE_END)
//
  val () = if isall then
    fprint1_string (pf_mod | fil_d, HTM_POSMARK_FILE_END)
//
in
  // empty
end // end of [posmark_file_file]

(* ****** ****** *)

fn posmark_process_htm (
  fil_d: &FILE w, p: lint, pm: posmark
): void = let
  fn fprint_stadyncstpos (
      pf_mod: file_mode_lte (w, w) | fil_d: &FILE w, name: string
    ) : void = let
    val name = string1_of_string (name)
    fun loop {n,i:nat | i <= n} .<n-i>.
      (fil_d: &FILE w, name: string n, i: size_t i): void =
      if string_isnot_atend (name, i) then let
        val c = name[i]; val () = case+ c of
          | _ when char_isalnum c => fprint_char (pf_mod | fil_d, c)
          | _ => let
              val () = fprint_char (pf_mod | fil_d, '_')
              val u = uint_of_char c
              val () = fprintf1_exn (pf_mod | fil_d, "%2x", @(u))
            in
              // empty
            end // end of [_]
      in
        loop (fil_d, name, i + 1)
      end else begin
        fprint1_string (pf_mod | fil_d, ".html")
      end // end of [if]
    // end of [loop]
    val () = () where {
      val flag = posmark_xref_flag_get () where { extern fun
        posmark_xref_flag_get (): Stropt = "ats_posmark_xref_flag_get"
      } // end of [flag]
      val () = if stropt_is_some flag then let
        val flag = stropt_unsome (flag) in fprint1_string (pf_mod | fil_d, flag)
      end // end of [val]
    } // end of [val]
    val () = loop (fil_d, name, 0)
  in
    // empty
  end // end of [fprint_dyncstpos]
  prval pf_mod = file_mode_lte_w_w
in
  case+ pm of
  | PMnone () => ()
  | PMcomment i => if i = 0 then begin
      fprint1_string (pf_mod | fil_d, HTM_COMMENT_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_COMMENT_FONT_END)
    end // end of [PMcomment]
  | PMextern i => if i = 0 then begin
      fprint1_string (pf_mod | fil_d, HTM_EXTERN_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_EXTERN_FONT_END)
    end // end of [PMextern]
  | PMkeyword i => if i = 0 then begin
      fprint1_string (pf_mod | fil_d, HTM_KEYWORD_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_KEYWORD_FONT_END)
    end // end of [PMkeyword]
  | PMneuexp i => if i = 0 then begin
      fprint1_string (pf_mod | fil_d, HTM_NEUEXP_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_NEUEXP_FONT_END)
    end // end of [PMneuexp]
  | PMstaexp i =>  if i = 0 then begin
      fprint1_string (pf_mod | fil_d, HTM_STAEXP_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_STAEXP_FONT_END)
    end // end of [PMstaexp]
  | PMprfexp i => if i = 0 then begin
      fprint1_string (pf_mod | fil_d, HTM_PRFEXP_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_PRFEXP_FONT_END)
    end // end of [PMprfexp]
  | PMstacstdec (i, loc(*dec*)) => if i = 0 then let
      val () = fprint1_string (pf_mod | fil_d, "<span id=\"loc")
      val () = fprint1_lint (pf_mod | fil_d, ofs) where {
        val ofs = $Loc.location_begpos_toff (loc)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "\">")
    in
      fprint1_string (pf_mod | fil_d, HTM_STACSTDEC_FONT_BEG)
    end else let // HX: closing
      val () = fprint1_string (pf_mod | fil_d, HTM_STACSTDEC_FONT_END)
      val () = fprint1_string (pf_mod | fil_d, "</span>")
    in
      // nothing
    end // end of [PMdyncstdec]
  | PMstacstuse (i, loc(*dec*)) => if i = 0 then let
      val () = fprint1_string (pf_mod | fil_d, "<a href=\"")
      val () = fprint_stadyncstpos (pf_mod | fil_d, name) where {
        val fil = $Loc.location_get_filename loc
        val name = $Fil.filename_full (fil)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "#loc") 
      val () = fprint1_lint (pf_mod | fil_d, ofs) where {
        val ofs = $Loc.location_begpos_toff (loc)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "\">")
    in
      fprint1_string (pf_mod | fil_d, HTM_STACSTUSE_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_STACSTUSE_FONT_END);
      fprint1_string (pf_mod | fil_d, "</a>")
    end // end of [PMstacstuse]
  | PMdyncstdec (i, loc(*dec*)) => if i = 0 then let
      val () = fprint1_string (pf_mod | fil_d, "<span id=\"loc")
      val () = fprint1_lint (pf_mod | fil_d, ofs) where {
        val ofs = $Loc.location_begpos_toff (loc)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "\">")
    in
      fprint1_string (pf_mod | fil_d, HTM_DYNCSTDEC_FONT_BEG)
    end else let // HX: closing
      val () = fprint1_string (pf_mod | fil_d, HTM_DYNCSTDEC_FONT_END);
      val () = fprint1_string (pf_mod | fil_d, "</span>")
    in
      // nothing
    end // end of [PMdyncstdec]
  | PMdyncstimp (i, loc(*dec*)) => if i = 0 then let
      val () = fprint1_string (pf_mod | fil_d, "<a href=\"")
      val () = fprint_stadyncstpos (pf_mod | fil_d, name) where {
        val fil = $Loc.location_get_filename loc
        val name = $Fil.filename_full (fil)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "#loc")
      val ofs = $Loc.location_begpos_toff (loc)
      val () = fprint1_lint (pf_mod | fil_d, ofs)
      val () = fprint1_string (pf_mod | fil_d, "\">")
    in
      fprint1_string (pf_mod | fil_d, HTM_DYNCSTIMP_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_DYNCSTIMP_FONT_END);
      fprint1_string (pf_mod | fil_d, "</a>")
    end // end of [PMdyncstimp]
  | PMdyncstuse (i, loc(*dec*)) => if i = 0 then let
      val () = fprint1_string (pf_mod | fil_d, "<a href=\"")
      val () = fprint_stadyncstpos (pf_mod | fil_d, name) where {
        val fil = $Loc.location_get_filename loc
        val name = $Fil.filename_full (fil)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "#loc") 
      val () = fprint1_lint (pf_mod | fil_d, ofs) where {
        val ofs = $Loc.location_begpos_toff (loc)
      } // end of [val]
      val () = fprint1_string (pf_mod | fil_d, "\">")
    in
      fprint1_string (pf_mod | fil_d, HTM_DYNCSTUSE_FONT_BEG)
    end else begin
      fprint1_string (pf_mod | fil_d, HTM_DYNCSTUSE_FONT_END);
      fprint1_string (pf_mod | fil_d, "</a>")
    end // end of [PMdyncstuse]
end // end of [posmark_process_htm]

fn fputchr_htm
  (c: char, out: &FILE w): void = let
  prval pf_mod = file_mode_lte_w_w in case+ c of
  | '<' => fprint1_string (pf_mod | out, "&lt;")
  | '>' => fprint1_string (pf_mod | out, "&gt;")
  | '&' => fprint1_string (pf_mod | out, "&amp;")
  | _ => fputc_exn (pf_mod | c, out)
end // end of [fputchr_htm]

in // in of [local]

extern fun posmark_htmlfilename_make
  (basename: string): string = "posmark_htmlfilename_make"
// end of [posmark_htmlfilename_make]

implement
posmark_file_make_htm
  (isall, in_name, out_name) = let
  val file_mode_r = $extval (file_mode r, "\"r\"")
  val (pf_in | p_in) = fopen_exn (in_name, file_mode_r)
  val file_mode_w = $extval (file_mode w, "\"w\"")
  val () = if stropt_is_some out_name then let
    val out_name = stropt_unsome (out_name)
    val (pf_out | p_out) = fopen_exn (out_name, file_mode_w)
    val () = posmark_file_file
      (isall, posmark_process_htm, fputchr_htm, !p_in, !p_out)
    // end of [val]
  in
    fclose_exn (pf_out | p_out)
  end else let
    val (pf_out | p_out) = stdout_get ()
    val () = posmark_file_file
      (isall, posmark_process_htm, fputchr_htm, !p_in, !p_out)
    // end of [val]
  in
    stdout_view_set (pf_out | (*none*))
  end // end of [val]
  val () = fclose_exn (pf_in | p_in)
in
  // empty
end // end of [posmark_file_make_htm]

end // end of [local]

(* ****** ****** *)

local

staload "ats_charlst.sats"

fn char_of_xdigit (i: int): char = let
  val i = (if i >= 10 then let
    val a = int_of_char 'a' in int_of_char 'a' + i - 10
  end else begin
    int_of_char '0' + i
  end) : int // end of [val]
in
  char_of_int (i)
end // end of [char_of_xdigit]

fun posmark_xref_testnot
  (flag: string, name: string): Stropt = let
  fun loop {n,i:nat | i <= n} .<n-i>.
    (name: string n, i: size_t i, cs: Charlst_vt): Charlst_vt =
    if string_isnot_atend (name, i) then let
      val c = name[i]
      val cs = (case+ c of
        | _ when char_isalnum c => CHARLSTcons (c, cs)
        | _ => let
            val cs = CHARLSTcons ('_', cs)
            val i = int_of_char (c)
            val i1 = i / 16 and i2 = i mod 16
            val c1 = char_of_xdigit i1 and c2 = char_of_xdigit i2
          in
            CHARLSTcons (c2, CHARLSTcons (c1, cs))
          end // end of [_]
      ) : Charlst_vt
    in
      loop (name, i+1, cs)
    end else begin
      charlst_add_string (cs, ".html") // loop returns
    end (* end of [if] *)
  val flag = string1_of_string (flag)
  val cs = charlst_add_string (CHARLSTnil (), flag) // [flag] ends with [dirsep]
  val name = string1_of_string (name)
  val cs = loop (name, 0, cs)
  val name1 = string_make_charlst_rev (cs)
in
  if test_file_exists (name1) then stropt_none else stropt_some (name1)
end // end of [posmark_xref_testnot]

extern fun posmark_xref_flag_get (): Stropt = "ats_posmark_xref_flag_get"

in // in of [local]

implement posmark_xref_testnot_if (name) = let
  val flag = posmark_xref_flag_get ()
in
  if stropt_is_some flag then let
    val flag = stropt_unsome (flag) in posmark_xref_testnot (flag, name)
  end else stropt_none
end // end of [posmark_xref_testnot_if]

end // end of [local]

(* ****** ****** *)

val () = ats_posmark_initialize () where {
  extern fun ats_posmark_initialize (): void = "ats_posmark_initialize"
} // end of [val]

(* ****** ****** *)

%{$

ats_ptr_type
posmark_htmlfilename_make (ats_ptr_type basename) {
  int n ; char c, *s ;
  n = strlen((char *)basename) ;
  s = (char*)ATS_MALLOC (n+6) ;
  s[n+5] = '\000' ;
  s[n+4] = 'l'; s[n+3] = 'm' ; s[n+2] = 't' ; s[n+1] = 'h' ;
  s[n] = '.' ; --n ;
  while (n >= 0) {
    c = ((char *)basename)[n] ;
    if (c == '.') { s[n] = '_' ; --n ; break ; }
    s[n] = c ; --n ;
  }
  while (n >= 0) { s[n] = ((char *)basename)[n] ; --n ; }
  return s ;
} /* posmark_htmlfilename_make */

/* ****** ****** */

static char* the_ats_posmark_xref_flag = 0 ;

ats_ptr_type
ats_posmark_xref_flag_get () { return the_ats_posmark_xref_flag ; }

ats_void_type
ats_posmark_xref_flag_set
  (ats_ptr_type flag) {
  the_ats_posmark_xref_flag = flag ; return ;
} // end of [ats_posmark_xref_flag_set]

ats_void_type
ats_posmark_initialize () {
  ATS_GC_MARKROOT (&the_ats_posmark_xref_flag, sizeof(ats_ptr_type)) ;
  return ;
} // end of [ats_posmark_initialize]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_posmark.dats] *)
