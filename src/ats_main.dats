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
// Time: July 2007
//
(* ****** ****** *)

%{^
//
#include "libc/CATS/stdio.cats"
#include "libc/CATS/stdlib.cats"
//
#include "ats_main.cats"
//
%} // end of [%{^]

(* ****** ****** *)
//
extern
fun fopen_exn
  {m:file_mode}
  (s: string, m: file_mode m)
: [l:addr] (FILE m @ l | ptr l) = "atslib_fopen_exn"
//
extern
fun fclose_exn
  {m:file_mode}{l:addr}
  (pf: FILE m @ l | p: ptr l):<!exnref> void = "atslib_fclose_exn"
// end of [fclose_exn]
//
(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

dynload "libats_lex_lexing.dats"

(* ****** ****** *)

dynload "ats_array.dats"
dynload "ats_charlst.dats"
dynload "ats_counter.dats"
dynload "ats_hashtbl.dats"
dynload "ats_intinf.dats"
dynload "ats_list.dats"
dynload "ats_map_lin.dats"
dynload "ats_set_fun.dats"
dynload "ats_symbol.dats"

(* ****** ****** *)
//
dynload "ats_comarg.dats"
dynload "ats_debug.dats"
dynload "ats_effect.dats"
dynload "ats_error.dats"
dynload "ats_filename.dats" // needs [ats_symbol.dats]
//
dynload "ats_fixity_prec.dats"
dynload "ats_fixity_fxty.dats" // needs the previous one
//
dynload "ats_global.dats"
dynload "ats_keyword.dats"
dynload "ats_label.dats"
//
dynload "ats_location.dats"
//
dynload "ats_stamp.dats"
//
dynload "ats_symenv.dats"
dynload "ats_symtbl.dats"
//
dynload "ats_syntax.dats"
dynload "ats_syntax_depgen.dats"
dynload "ats_syntax_taggen.dats"
//
dynload "ats_posmark.dats"
dynload "ats_syntax_posmark.dats"
//
dynload "ats_namespace.dats"
//
dynload "ats_lexer_lats.dats"
//
dynload "ats_parser.dats"
//
dynload "ats_staexp1.dats"
dynload "ats_staexp1_print.dats"
dynload "ats_dynexp1.dats"
dynload "ats_dynexp1_syndef.dats"
dynload "ats_dynexp1_print.dats"
dynload "ats_trans1_env.dats"
dynload "ats_e1xp_eval.dats"
dynload "ats_trans1_sta.dats"
dynload "ats_trans1_dyn.dats"
//
dynload "ats_staexp2.dats"
dynload "ats_staexp2_print.dats"
dynload "ats_staexp2_scst.dats"
dynload "ats_staexp2_svVar.dats"
dynload "ats_staexp2_dcon.dats"
dynload "ats_staexp2_util1.dats"
dynload "ats_staexp2_util2.dats"
dynload "ats_staexp2_pprint.dats"
//
dynload "ats_dynexp2.dats"
dynload "ats_dynexp2_print.dats"
dynload "ats_dynexp2_dcst.dats"
dynload "ats_dynexp2_dmac.dats"
dynload "ats_dynexp2_dvar.dats"
dynload "ats_dynexp2_util.dats"
dynload "ats_trans2_env.dats"
dynload "ats_stadyncst2.dats"
dynload "ats_trans2_sta.dats"
dynload "ats_trans2_dyn1.dats"
dynload "ats_trans2_dyn2.dats"
dynload "ats_macro2.dats"
dynload "ats_patcst2.dats"
dynload "ats_string_parse.dats"
dynload "ats_printf_c_lats.dats"
dynload "ats_staexp2_solve.dats"
dynload "ats_trans3_env_eff.dats"
dynload "ats_trans3_env_loop.dats"
dynload "ats_trans3_env_met.dats"
dynload "ats_trans3_env_scst.dats"
dynload "ats_trans3_env_state.dats"
dynload "ats_trans3_env.dats"
dynload "ats_trans3_env_print.dats"
dynload "ats_dynexp3.dats"
dynload "ats_dynexp3_print.dats"
dynload "ats_trans3_pat.dats"
dynload "ats_trans3_assgn.dats"
dynload "ats_trans3_deref.dats"
dynload "ats_trans3_view.dats"
dynload "ats_trans3_util.dats"
dynload "ats_trans3_exp_up.dats"
dynload "ats_trans3_exp_dn.dats"
dynload "ats_trans3_loop.dats"
dynload "ats_trans3_dec.dats"
//
dynload "ats_solver_fm.dats"
dynload "ats_constraint.dats"
dynload "ats_constraint_print.dats"
//
dynload "ats_hiexp.dats"
dynload "ats_hiexp_print.dats"
dynload "ats_hiexp_util.dats"
//
dynload "ats_trans4.dats"
//
dynload "ats_ccomp.dats"
dynload "ats_ccomp_env.dats"
dynload "ats_ccomp_print.dats"
dynload "ats_ccomp_util.dats"
dynload "ats_ccomp_trans.dats"
dynload "ats_ccomp_trans_clau.dats"
dynload "ats_ccomp_trans_tailcal.dats"
dynload "ats_ccomp_trans_temp.dats"
dynload "ats_ccomp_emit.dats"
dynload "ats_ccomp_main.dats"
//
(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Glo = "ats_global.sats"
staload Fil = "ats_filename.sats"
staload Par = "ats_parser.sats"
staload PM = "ats_posmark.sats"

(* ****** ****** *)

staload "ats_comarg.sats"

staload Loc = "ats_location.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"
staload SEXP1 = "ats_staexp1.sats"
staload DEXP1 = "ats_dynexp1.sats"
staload DEXP2 = "ats_dynexp2.sats"
staload DEXP3 = "ats_dynexp3.sats"
staload Trans1 = "ats_trans1.sats"
staload TransEnv1 = "ats_trans1_env.sats"
staload Trans2 = "ats_trans2.sats"
staload TransEnv2 = "ats_trans2_env.sats"
staload Trans3 = "ats_trans3.sats"
staload TransEnv3 = "ats_trans3_env.sats"
staload CSTR = "ats_constraint.sats"
staload Trans4 = "ats_trans4.sats"
staload CC = "ats_ccomp.sats"

(* ****** ****** *)
//
// HX: this is primarily for ATS developers
//
fn atsopt_usage (cmd: string): void = begin
  printf ("usage: %s <command> ... <command>\n\n", @(cmd));
  print "where a <command> is of one of the following forms:\n\n";
  print "  -s filenames (for statically loading (many) <filenames>)\n";
  print "  --static filenames (for statically loading (many) <filenames>)\n";
  print "  -d filenames (for dynamically loading (many) <filenames>)\n";
  print "  --dynamic filenames (for dynamically loading (many) <filenames>)\n";
  print "  --pervasive filenames (for pervasively loading (many) <filenames>)\n";
  print "  -o filename (output into <filename>)\n";
  print "  --output filename (output into <filename>)\n";
  print "  --output-w filename (output-write into <filename>)\n";
  print "  --output-a filename (output-append into <filename>)\n";
  print "  -dep (for generating dependencies only)\n";
  print "  --depgen (for generating dependencices only)\n";
  print "  -dep2 (for generating dependencies and then compiling)\n";
  print "  --depgen2 (for generating dependencies and then compiling)\n";
  print "  --taggen (for generating tagging information)\n";
  print "  -tc (for typechecking only)\n";
  print "  --typecheck (for typechecking only)\n";
  print "  --posmark_html (for generating html file depicting colored concrete syntax)\n";
  print "  --posmark_html_body (for generating html body depicting colored concrete syntax)\n";
  print "  --posmark_xref (for generating html file depicting some syntactic cross references)\n";
  print "  --xrefprelude (for generating cross-referencing prelude files)\n";
  print "  --gline (for generating line pragma information on source code)\n";
  print "  --debug=0 (for disabling the generation of debugging information)\n";
  print "  --debug=1 (for enabling the generation of debugging information)\n";
  print "  -h (for printing out this help usage)\n";
  print "  --help (for printing out this help usage)\n";
  print "  -v (for printing out the version)\n";
  print "  --version (for printing out the version)\n";
  print_newline ()
end // end of [atsopt_usage]

(* ****** ****** *)
//
// ATS_MAJOR_VERSION, ATS_MINOR_VERSION, ATS_MICRO_VERSION
// defined in [prelude/params.hats]
//
fn
atsopt_version (): void =
(
//
printf
(
  "ATS/Anairiats version %i.%i.%i with Copyright (c) 2002-2014 Hongwei Xi\n"
, @(ATS_MAJOR_VERSION, ATS_MINOR_VERSION, ATS_MICRO_VERSION)
) (* end of [printf] *)
//
) (* end of [atsopt_version] *)

(* ****** ****** *)

fn
parse_from_filename_d0eclst_sta
  (fil: $Fil.filename_t): $Syn.d0eclst =
  $Par.parse_from_filename_d0eclst (0(*static*), fil)
// end of [parse_from_filename_d0eclst_sta]

(* ****** ****** *)

fn e1xpenv_load () = () where {
  val () = $TransEnv1.the_e1xpenv_pervasive_add_topenv ()
} // end of [e1xpenv_load]

(* ****** ****** *)
//
// HX: load in built-in fixity declarations
//
fn fixity_load
   (ATSHOME: string): void = let
  val basename = "prelude/fixity.ats"
  val fullname =
    $Fil.filename_append (ATSHOME, basename)
  val filename = $Fil.filename_make_full (fullname)
  val () = $Fil.the_filenamelst_push filename
  val d0cs = parse_from_filename_d0eclst_sta (filename)
  val () = $Fil.the_filenamelst_pop ()
  val d1cs = $Trans1.d0eclst_tr (d0cs)
  val () = $TransEnv1.the_fxtyenv_pervasive_add_topenv ()
(*
  val () = begin
    print "[fixity_load] is finished."; print_newline ()
  end // end of [val]
*)
in
  // empty
end // end of [fixity_load]

(* ****** ****** *)

local

val xrefpreludeflag = ref_make_elt<int> (0)

in (* in of [local] *)

fn pervasive_load
  (ATSHOME: string, basename: string): void = let
  val fullname = $Fil.filename_append (ATSHOME, basename)
  val filename = $Fil.filename_make_full (fullname)
  val () = $Fil.the_filenamelst_push (filename)
(*
  val () = begin
    print "pervasive_load: parse: fullname = "; print fullname; print_newline ()
  end // end of [val]
*)
  val d0cs = parse_from_filename_d0eclst_sta (filename)
(*
  val () = begin
    print "pervasive_load: parse: after: fullname = "; print fullname; print_newline ()
  end // end of [val]
*)
  val () = $Fil.the_filenamelst_pop ()
  val d1cs = $Trans1.d0eclst_tr (d0cs)
//
  val () = if !xrefpreludeflag = 0 then
    $TransEnv1.staload_file_insert (fullname, 0(*loadflag*), list_nil)
  (* end of [val] *)
//
  val _(*d2cs*) = $Trans2.d1eclst_tr d1cs
in
  // empty
end // end of [pervasive_load]

fun prelude_load
  (pv: int, ATSHOME: string): void = let
//
  val () = e1xpenv_load ()
  val () = fixity_load (ATSHOME)
//
  val () = if (pv = ~1) then !xrefpreludeflag := 1
//
  val () = pervasive_load (ATSHOME, "prelude/basics_sta.sats")
  val () = pervasive_load (ATSHOME, "prelude/sortdef.sats")
  val () = pervasive_load (ATSHOME, "prelude/basics_dyn.sats")
  val () = pervasive_load (ATSHOME, "prelude/macrodef.sats")
(*
** [trans2_env_pervasive_add_topenv] needs to be called for the rest
*)
  val () = $TransEnv2.trans2_env_pervasive_add_topenv ()
(*
** these are all the .sats files in $ATSHOME/prelude
*)
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/arith.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/vsubrw.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/bool.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/char.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/byte.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/float.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/integer.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/integer_ptr.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/integer_fixed.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/sizetype.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/memory.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/pointer.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/reference.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/string.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/lazy.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/lazy_vt.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/printf.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/filebas.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/extern.sats") // for building external API's
//
(*
** these are here because they are so commonly needed
*)
  val () = pervasive_load (ATSHOME, "prelude/SATS/list.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/list0.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/list_vt.sats")
//
(*
  val () = pervasive_load (ATSHOME, "prelude/SATS/dlist_vt.sats")
*)
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/option.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/option0.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/option_vt.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/array.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/array0.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/matrix.sats")
  val () = pervasive_load (ATSHOME, "prelude/SATS/matrix0.sats")
//
  val () = pervasive_load (ATSHOME, "prelude/SATS/ptrarr.sats")
//
(*
  // HX-2010-04-09: is this a good idea?
  val () = pervasive_load (ATSHOME, "prelude/SATS/prelude_finish.sats") // miscellaneous
*)
//
  val () = if (pv = ~1) then !xrefpreludeflag := 0
//
  val () = $TransEnv2.trans2_env_pervasive_add_topenv ()
//
  val () = $TransEnv3.trans3_env_initize () // initializing the environment for trans3
//
in
  // empty
end // end of [prelude_load]

end // end of [local]

(* ****** ****** *)

datatype comkind =
  | COMKINDnone of ()
  | COMKINDinput of int (* 0: static; 1: dynamic *)
  | COMKINDpervasive of () // for pervasively loading static files
  | COMKINDoutput of ()
// end of [comkind]

fn comkind_is_input (knd: comkind): bool =
  case+ knd of COMKINDinput _ => true | _ => false
// end of [comkind_is_input]

fn comkind_is_pervasive (knd: comkind): bool =
  case+ knd of COMKINDpervasive _ => true | _ => false
// end of [comkind_is_pervasive]

fn comkind_is_output (knd: comkind): bool =
  case+ knd of COMKINDoutput _ => true | _ => false
// end of [comkind_is_output]

(* ****** ****** *)

viewtypedef arglst (n:int) = list_vt (comarg, n)

(* ****** ****** *)
//
#define POSMARK_NONE 0
#define POSMARK_SOME 1
//
#define POSMARKND_NONE 0
//
#define POSMARKND_HTML_BODY 01
#define POSMARKND_HTML_FILE 02
#define POSMARKND_HTML_XREF 03
//
(* ****** ****** *)

fn is_htmlbodyfile (x: int): bool =
  (x = POSMARKND_HTML_BODY orelse x = POSMARKND_HTML_FILE)
// end of [is_htmlbodyfile]

fn is_htmlxref (x: int): bool = (x = POSMARKND_HTML_XREF)

(* ****** ****** *)

fn posmarknd_isall
  (x: int): bool = case+ x of
  | POSMARKND_HTML_FILE => true // header + body
  | POSMARKND_HTML_XREF => true // header + body
  | _ => false  // body only
// end of [val]

(* ****** ****** *)

typedef
param_t = @{
  comkind= comkind
, wait= int
, prelude= int
//
, outmode= file_mode (w)
//
, depgen= int
, depgenout= Stropt
//
, taggen= int
, taggenout= Stropt
//
, posmark= int
, posmarknd= int
//
, typecheck_only= int
} // end of [param_t]

(* ****** ****** *)

(*
local

val the_ntaggen = ref_make_elt<int> (0)

in (* in of [local] *)

fn ntaggen_getinc (): int =
(
let val n = !the_ntaggen in !the_ntaggen := n+1; n end
) // end of [ntaggen_getinc]

end // end of [local]
*)

(* ****** ****** *)

local

typedef fil_t = $Fil.filename_t
val the_input_filename = ref_make_elt<fil_t> ($Fil.filename_stdin)

in (* in of [local] *)

fn input_filename_get
  (): fil_t = let
  val inp = !the_input_filename in
  !the_input_filename := $Fil.filename_dummy; inp
end // end of [input_filename_get]

fn input_filename_set (fil: fil_t) = (!the_input_filename := fil)

end // end of [local]

(* ****** ****** *)

local

val the_output_filename = ref_make_elt<Stropt> (stropt_none)

in (* in of [local] *)

fn output_filename_get
  (): Stropt = let
  val out = !the_output_filename in
  !the_output_filename := stropt_none; out
end // end of [output_filename_get]

fn output_filename_set (name: Stropt) = (!the_output_filename := name)

end // end of [local]

(* ****** ****** *)

fn do_parse_filename
(
  flag: int
, param: param_t
, basename: string
) : $Syn.d0eclst = let
  val debflag =
    $Deb.debug_flag_get ()
  val () = if
    debflag > 0 then let
    val cwd = getcwd0 () where {
      extern fun getcwd0 (): String = "atslib_getcwd0" // libc/SATS/unistd.sats
    } // end of [val]
  in
    print "cwd = "; print cwd; print_newline ()
  end // end of [if]
  val filename = (case+
    $Fil.filenameopt_make_relative basename of
    | ~Some_vt filename => filename | ~None_vt () => begin
        prerr "error(ATS)";
        prerr ": the filename ["; prerr basename; prerr "] is not available.";
        prerr_newline ();
        exit {$Fil.filename_t} (1)
      end // end of [None_vt]
  ) : $Fil.filename_t
  val () = input_filename_set (filename)
//
  val () = if param.posmark > POSMARK_NONE then $PM.posmark_enable ()
//
  var d0cs: $Syn.d0eclst = list_nil ()
  val () = $Fil.the_filenamelst_push (filename)
  val () = d0cs := $Par.parse_from_filename_d0eclst (flag, filename)
(*
  val () = $Fil.the_filenamelst_pop () // HX-2012-08: no pop for a permanent push
*)
//
  val () = if debflag > 0 then begin
    printf ("The file [%s] is successfully parsed!\n", @(basename))
  end // end of [if]
//
  val () = if param.posmark > POSMARK_NONE then let
    val () = $Syn.d0eclst_posmark d0cs in $PM.posmark_disable ()
  end // end of [val]
//
  val fullname = $Fil.filename_full (filename)
  val pmstropt = $PM.posmark_xref_testnot_if (fullname)
  val isposmark = stropt_is_some pmstropt
  val () = if isposmark then let
    val isall = true // header + body
    val () = $PM.posmark_push_dup ()
    val () = $PM.posmark_file_make_htm (isall, fullname, pmstropt)
    val () = $PM.posmark_pop ()
  in
    // empty
  end // end of [val]
//
in
  d0cs // the return value
end // end of [do_parse_filename]

(* ****** ****** *)

fn do_parse_stdin
  (flag: int): $Syn.d0eclst = let
//
// no support for position marking
//
val () = $Fil.the_filenamelst_push ($Fil.filename_stdin)
val d0cs = $Par.parse_from_stdin_d0eclst (flag)
(*
val () = $Fil.the_filenamelst_pop () // HX-2012-08: no pop for a permanent push
*)
in
  d0cs
end // end of [do_parse_stdin]

(* ****** ****** *)

fn do_trans12 (
    param: param_t
  , basename: string
  , d0cs: $Syn.d0eclst
  ) : $DEXP2.d2eclst = let
  val debug_flag = $Deb.debug_flag_get ()
//
  val () = $Trans1.initize ()
  val d1cs = $Trans1.d0eclst_tr (d0cs)
  val () = $Trans1.finalize ()
  val () = if debug_flag > 0 then begin
    print "The 1st translation (fixity) of [";
    print basename;
    print "] is successfully completed!";
    print_newline ()
  end // end of [if]
//
  val () = if param.posmarknd = POSMARKND_HTML_XREF then $PM.posmark_enable ()
  val d2cs = $Trans2.d1eclst_tr d1cs
  val () = if param.posmarknd = POSMARKND_HTML_XREF then $PM.posmark_disable ()
//
  val () = if debug_flag > 0 then begin
    print "The 2nd translation (binding) of [";
    print basename;
    print "] is successfully completed!";
    print_newline ()
  end // end of [if]
in
  d2cs
end // end of [do_trans12]

fn do_trans123 (
    param: param_t
  , basename: string
  , d0cs: $Syn.d0eclst
  ) : $DEXP3.d3eclst = let
  val d2cs = do_trans12 (param, basename, d0cs)
  val d3cs = $Trans3.d2eclst_tr d2cs
//
  val () =
    $CSTR.c3str_solve (c3t) where {
    val c3t = $Trans3.c3str_get_final ()
  } // end of [val]
//
(*
  val () = print_the_s3itemlst () where {
    extern fun print_the_s3itemlst (): void = "atsopt_print_the_s3itemlst"
  } // end of [val]
*)
  // HX: is this some sort of bug???
  val () = free_the_s3itemlst () where {
    extern fun free_the_s3itemlst (): void = "atsopt_free_the_s3itemlst"
  } // end of [val]
//
  val debug_flag = $Deb.debug_flag_get ()
//
  val () = if debug_flag > 0 then begin
    print "The 3rd translation (typechecking) of [";
    print basename;
    print "] is successfully completed!";
    print_newline ()
  end // end of [if]
in
  d3cs
end // end of [do_trans123]

fn do_trans1234 (
    param: param_t
  , flag: int
  , basename: string
  , d0cs: $Syn.d0eclst
  ) : void = let
  val d3cs = do_trans123 (param, basename, d0cs)
  val hids = $Trans4.d3eclst_tr (d3cs)
  val debug_flag = $Deb.debug_flag_get ()
  val () = if debug_flag > 0 then begin
    print "The 4th translation (proof erasure) of [";
    print basename;
    print "] is successfully completed!";
    print_newline ()
  end // end of [if]
  val infil = input_filename_get ()
  val outname = output_filename_get ()
in
  case+ outname of
  | _ when
      stropt_is_some (outname) => let
      val outname = stropt_unsome (outname)
      prval pf_mod = file_mode_lte_w_w
      val (pf_out | p_out) = fopen_exn (outname, param.outmode)
      val () = $CC.ccomp_main (pf_mod | flag, !p_out, infil, hids)
      val () = fprintf1_exn (
        pf_mod
      | !p_out
      , "\n/* ****** ****** */\n\n/* end of [%s] */\n"
      , @(outname)
      ) // end of [fprintf]
      val () = if debug_flag > 0 then begin
        print "The 5th translation (code emission) of [";
        print basename;
        print "] is successfully completed!";
        print_newline ()
      end // end of [if]
    in
      fclose_exn (pf_out | p_out)
    end // end of [_ when ...]
  | _ => let
    prval pf_mod = file_mode_lte_w_w
    val (pf_stdout | p_stdout) = stdout_get ()
    val () = $CC.ccomp_main
      (pf_mod | flag, !p_stdout, infil, hids)
    val () = fprint1_string
      (pf_mod | !p_stdout, "\n/* ****** ****** */\n")
  in
    stdout_view_set (pf_stdout | (*none*))
  end // end of [_]
end // end of [do_trans1234]

(* ****** ****** *)

extern fun is_posmark_html (str: string): bool

implement
is_posmark_html
  (str) = case+ str of
  | "--posmark_html" => true
(*
  | "--posmark_html_file" => true
*)
  | _ => false
// end of [is_posmark_html]

extern fun is_posmark_xref_prefix
  (str: string): bool = "atsopt_is_posmark_xref_prefix"
// end of [is_posmark_xref_prefix]

(* ****** ****** *)
//
extern fun DATS_wait_set (): void = "atsopt_DATS_wait_set"
extern fun DATS_wait_is_set (): bool = "atsopt_DATS_wait_is_set"
extern fun DATS_wait_clear (): void = "atsopt_DATS_wait_clear"
extern fun is_DATS_flag (s: string): bool = "atsopt_is_DATS_flag"
extern fun DATS_extract (s: string): Stropt = "atsopt_DATS_extract"
//
extern fun IATS_wait_set (): void = "atsopt_IATS_wait_set"
extern fun IATS_wait_is_set (): bool = "atsopt_IATS_wait_is_set"
extern fun IATS_wait_clear (): void = "atsopt_IATS_wait_clear"
extern fun is_IATS_flag (s: string): bool = "atsopt_is_IATS_flag"
extern fun IATS_extract (s: string): Stropt = "atsopt_IATS_extract"
//
(* ****** ****** *)
//
// HX: for processing command-line flag: -DATSXYZ=def or -DATS XYZ=def
//
fun process_DATS_def
  (def: string): void = let
  val def = string1_of_string (def)
  #define EQ '='
//
// HX: this is for ATS/Geizella
//
extern
fun string_index_of_char_from_left
  {n:nat} (str: string n, c: char):<> ssizeBtw (~1, n)
  = "atspre_string_index_of_char_from_left"
// end of [string_index_of_char_from_left]
//
  val i = string_index_of_char_from_left (def, EQ)
in
  if i >= 0 then let
    val i = size1_of_ssize1 (i)
    val part1 = string_make_substring (def, 0, i)
    val part1 = string1_of_strbuf (part1)
    val n = string1_length (def)
    val ni = n - (i + 1)
    val part2 = string_make_substring (def, i+1, ni)
    val part2 = string1_of_strbuf (part2)
    val sym = $Sym.symbol_make_string (part1)
    val e1xp = $SEXP1.e1xp_string
      ($Loc.location_dummy, part2, (int_of_size)ni)
  in
    $TransEnv1.the_e1xpenv_add (sym, e1xp)
  end else let // EQ is not in [def]
    val sym = $Sym.symbol_make_string (def)
    val e1xp = $SEXP1.e1xp_none ($Loc.location_dummy)
  in
    $TransEnv1.the_e1xpenv_add (sym, e1xp)
  end // end of [if]
end // end of [process_DATS_def]

(* ****** ****** *)

fun process_IATS_dir
  (dir: string): void = let
  val () = $Fil.the_pathlst_push (dir)
  val () = $Glo.the_IATSdirlst_push (dir)
in
  // nothing
end // end of [process_IATS_dir]

(* ****** ****** *)

implement
main {n} (argc, argv) = let
//
(*
val () = gc_chunk_count_limit_max_set (0) // for testing GC heavily
*)
val () = gc_chunk_count_limit_max_set (~1) // [~1] stands for infinity
//
val () = set () where {
  extern fun set (): void = "atsopt_ATSHOMERELOC_set"
} // end of [val]
//
val ATSHOME = getenv () where {
  extern fun getenv (): string = "atsopt_ATSHOME_getenv_exn"
} // end of [val]
//
// HX: for runtime and atslib
val () = $Fil.the_prepathlst_push (ATSHOME)
//
val () = $TransEnv2.trans2_env_initize ()
//
fn warning (str: string) = begin
  prerr "waring(ATS)";
  prerr ": unrecognized command line argument [";
  prerr str; prerr "] is ignored."; prerr_newline ()
end // end of [warning]

fun loop
  {i:nat | i <= n} .<i+1>.
(
  ATSHOME: string
, argv: &(@[string][n]), param: &param_t
, arglst: arglst i
) :<fun1> void = begin case+ arglst of
  | ~list_vt_cons (arg, arglst) => begin
    case+ arg of
    | _ when DATS_wait_is_set () => let
        val () = DATS_wait_clear ()
        val COMARGkey (_(*n*), def) = arg
        val () = process_DATS_def (def)
      in
        loop (ATSHOME, argv, param, arglst)
      end // end of [_ when ...]
    | _ when IATS_wait_is_set () => let
        val () = IATS_wait_clear ()
        val COMARGkey (_(*n*), dir) = arg
        val () = process_IATS_dir (dir)
      in
        loop (ATSHOME, argv, param, arglst)
      end // end of [_ when ...]
(*
    | _ when ATSHOMERELOC_wait_is_set () => let
        val COMARGkey (_(*n*), dir) = arg
        val () = ATSHOMERELOC_wait_clear ()
        val () = atshomereloc_dir_set (dir) in loop (ATSHOME, argv, param, arglst)
      end // end of [_ when ...]
*)
    | COMARGkey (1, str) => let
        val () = param.comkind := COMKINDnone (); val () =
          case+ str of
          | "-s" => begin
              param.comkind := COMKINDinput 0; param.wait := 1
            end // end of ["-s"]
          | "-d" => begin
              param.comkind := COMKINDinput 1; param.wait := 1
            end // end of ["-d"]
          | "-o" => begin
              param.comkind := COMKINDoutput ()
            end // end of ["-o"]
          | "-tc" => (param.typecheck_only := 1)
          | "-h" => begin
              param.comkind := COMKINDnone (); atsopt_usage (argv.[0])
            end // end of ["-h"]
          | "-v" => atsopt_version ()
//
          | "-dep" => (
               param.depgen := 1; param.depgenout := output_filename_get ()
             ) // end of ["-dep"]
          | "-dep2" => (
               param.depgen := 2; param.depgenout := output_filename_get ()
             ) // end of ["-dep2"]
//
          | "-tag" => (
               param.taggen := 1; param.taggenout := output_filename_get ()
             ) // end of ["-tag"]
//
          | _ when is_DATS_flag str => let
              val def = DATS_extract (str) in
              if stropt_is_some def then begin
                process_DATS_def (stropt_unsome def)
              end else begin
                DATS_wait_set ()
              end // end of [if]
            end (* end of [_ when ...] *)
          | _ when is_IATS_flag str => let
              val dir = IATS_extract (str) in
              if stropt_is_some dir then begin
                process_IATS_dir (stropt_unsome dir)
              end else begin
                IATS_wait_set ()
              end // end of [if]
            end (* end of [_ when ...] *)
          | _ => warning (str)
        // end of [val]
      in
        loop (ATSHOME, argv, param, arglst)
      end (* end of [COMARGkey (1, _)] *)
    | COMARGkey (2, str) => let
        val () =
          param.comkind := COMKINDnone ()
        val () = (
          case+ str of
          | "--static" =>
            (
              param.wait := 1 ;
              param.comkind := COMKINDinput (0)
            ) // end of ["--static"]
          | "--dynamic" =>
            (
              param.wait := 1 ;
              param.comkind := COMKINDinput (1)
            ) // end of ["--dynamic"]
          | "--pervasive" => begin
              param.comkind := COMKINDpervasive () // no wait
            end // end of ["--pervasive"]
//
          | "--output" => begin
              param.comkind := COMKINDoutput ()
            end // end of ["--output"]
          | "--output-w" =>
            (
              param.outmode := file_mode_w ;
              param.comkind := COMKINDoutput ()
            ) // end of ["--output-w"]
          | "--output-a" =>
            (
              param.outmode := file_mode_a ;
              param.comkind := COMKINDoutput ()
            ) // end of ["--output-a"]
//
          | "--depgen" => (
              param.depgen := 1; param.depgenout := output_filename_get ()
            ) // end of ["--depgen"]
          | "--depgen2" => (
              param.depgen := 2; param.depgenout := output_filename_get ()
            ) // end of ["--depgen2"]
//
          | "--taggen" => (
              param.taggen := 1; param.taggenout := output_filename_get ()
            ) // end of ["==taggen"]
//
          | "--typecheck" => (param.typecheck_only := 1)
//
          | "--xrefprelude" => (param.prelude := ~1)
//
          | _ when is_posmark_html (str) => let
              val () = param.posmark := POSMARK_SOME
              val () = param.posmarknd := POSMARKND_HTML_FILE
            in
             // nothing
            end // end of ["--posmark_html"]
//
          | "--posmark_html_body" => let
              val () = param.posmark := POSMARK_SOME
              val () = param.posmarknd := POSMARKND_HTML_BODY
            in
             // nothing
            end // end of ["--posmark_html_body"]
//
          | _ when is_posmark_xref_prefix (str) => let
              val () = param.posmark := POSMARK_SOME
              val () = param.posmarknd := POSMARKND_HTML_XREF
            in
              // nothing
            end // end of ["--posmark_xref"]
//
          | "--gline" => $Deb.gline_flag_set (1)
//
          | "--debug=0" => $Deb.debug_flag_set (0)
          | "--debug=1" => $Deb.debug_flag_set (1)
//
          | "--help" => begin
              param.comkind := COMKINDnone (); atsopt_usage (argv.[0])
            end // end of ["--help"]
          | "--version" => atsopt_version ()
          | _ => warning (str)
        ) (* end of [val] *)
      in
        loop (ATSHOME, argv, param, arglst)
      end // end of [COMARG (2, _)]
    | _ when comkind_is_input (param.comkind) => let
        var flag: int = 0
        val () = case+ param.comkind of
          | COMKINDinput i => flag := i | _ => ()
        // end of [val]
        val () = param.wait := 0
        val pv = param.prelude
        val () = if pv <= 0 then let
          val () = param.prelude := 1 in prelude_load (pv, ATSHOME)
        end // end of [val]
        val COMARGkey (_(*n*), basename) = arg
        val d0cs = do_parse_filename (flag, param, basename)
        val () = begin case+ 0 of
          | _ when param.depgen >= 1 => let
              val outname = param.depgenout // name for output file
              val () = (
                case+ 0 of
                | _ when stropt_is_some (outname) => let
                    val outname = stropt_unsome (outname)
                    prval pf_mod = file_mode_lte_w_w
                    val (pf_out | p_out) = fopen_exn (outname, param.outmode)
                    val () = $Syn.fprint_depgen (pf_mod | !p_out, basename, d0cs)
                    val ((*closed*)) = fclose_exn (pf_out | p_out)
                  in
                    // nothing
                  end // end of [stropt_is_some]
                | _ => () where {
                    prval pf_mod = file_mode_lte_w_w
                    val (pf_out | p_out) = stdout_get ()
                    val () = $Syn.fprint_depgen (pf_mod | !p_out, basename, d0cs)
                    val () = stdout_view_set (pf_out | (*none*))
                  } // end of [_]
              ) : void // end of [val]
            in
              if (param.depgen >= 2) then do_trans1234 (param, flag, basename, d0cs)
            end // end of [_ when ...]
//
          | _ when param.taggen >= 1 => let
              val outname =
                param.taggenout // name for output file
              val () = (
                case+ 0 of
                | _ when
                    stropt_is_some (outname) => let
                    val outname = stropt_unsome (outname)
                    val fmode = param.outmode
                    prval pf_mod = file_mode_lte_w_w
                    val (pf_out | p_out) = fopen_exn (outname, fmode)
                    val () = $Syn.fprint_taggen (pf_mod | !p_out, basename, d0cs)
                    val () = fprint_newline (pf_mod | !p_out)
                    val ((*closed*)) = fclose_exn (pf_out | p_out)
                  in
                    // nothing
                  end // end of [stropt_is_some]
                | _ => () where {
                    prval pf_mod = file_mode_lte_w_w
                    val (pf_out | p_out) = stdout_get ()
                    val () = $Syn.fprint_taggen (pf_mod | !p_out, basename, d0cs)
                    val () = fprint_newline (pf_mod | !p_out)
                    val () = stdout_view_set (pf_out | (*none*))
                  } // end of [_]
              ) (* end of [val] *)
            in
              // nothing
            end // end of [_ when ...]
//
          | _ when
              is_htmlbodyfile (param.posmarknd) => let
              val isall = posmarknd_isall (param.posmarknd)
              val outname = output_filename_get ()
              val () = $PM.posmark_file_make_htm (isall, basename, outname)
              val () = $PM.posmark_disable ()
            in
(*
              print "The syntax marking of [";
              print basename; print "] is successfully completed!";
              print_newline ()
*)
            end // end of [_ when ...]
//
          | _ when
              is_htmlxref (param.posmarknd) => let
              val isall = true // header + body
              val _(*d2cs*) = do_trans12 (param, basename, d0cs)
              val outname = output_filename_get ()
              val () = $PM.posmark_file_make_htm (isall, basename, outname)
              val () = $PM.posmark_disable ()
            in
(*
              print "The syntax cross referencing for [";
              print basename; print "] is successfully completed!";
              print_newline ()              
*)
            end // end of [_ when ...]
//
          | _ when param.typecheck_only > 0 => let
              val _(*d3cs*) = do_trans123 (param, basename, d0cs)
            in
              printf ("The file [%s] is successfully typechecked!", @(basename));
              print_newline ()
            end // end of [_ when ...]
          | _ => do_trans1234 (param, flag, basename, d0cs)
        end // end of [val]
      in
        loop (ATSHOME, argv, param, arglst)
      end // end of [_ when ...]
    | _ when
        comkind_is_pervasive (param.comkind) => let
        val pv = param.prelude
        val () = if pv <= 0 then let
          val () = param.prelude := 1 in prelude_load (pv, ATSHOME)
        end // end of [val]
        val COMARGkey (_(*n*), basename) = arg
        val d0cs = do_parse_filename (0(*static*), param, basename)
        val d1cs = $Trans1.d0eclst_tr d0cs
        val d2cs = $Trans2.d1eclst_tr d1cs
      in
        loop (ATSHOME, argv, param, arglst)
      end // end of [_ when ...]
    | _ when comkind_is_output (param.comkind) => let
        val () = param.comkind := COMKINDnone ()
        val COMARGkey (_(*n*), basename) = arg
        val basename = string1_of_string basename
        val () = output_filename_set (stropt_some basename)
      in
        loop (ATSHOME, argv, param, arglst)
      end // end of [_ when ...]
    | COMARGkey (_, str) => let
        val () = param.comkind := COMKINDnone ()
      in
        warning (str); loop (ATSHOME, argv, param, arglst)
      end // end of [_]
    end (* end of [list_vt_cons] *)
  | ~list_vt_nil () when param.wait > 0 => begin
    case+ param.comkind of
    | COMKINDinput flag => () where {
        val pv = param.prelude
        val () = if pv <= 0 then let
          val () = param.prelude := 1 in prelude_load (pv, ATSHOME)
        end // end of [val]
        val d0cs = do_parse_stdin (flag)
        val () = begin case+ 0 of
          | _ when param.depgen > 0 => ()
          | _ when param.taggen > 0 => ()
          | _ when param.posmark > POSMARK_NONE => ()
          | _ when param.typecheck_only > 0 => let
              val _(*d3cs*) = do_trans123 (param, "stdin", d0cs)
            in
              print ("The typechecking is successfully completed!");
              print_newline ()
            end // end of [_ when ...]
          | _ => do_trans1234 (param, flag, "stdin", d0cs)
        end // end of [val]
      } // end of [COMKINDinput]
    | _ => ()
    end // end of [list_vt_nil when param.wait > 0]
  | ~list_vt_nil () => loop_final (ATSHOME, param)
end // end of [loop]

and
loop_final .<0>.
(
  ATSHOME: string, param: &param_t
) : void =
(
  // it is yet empty
) // end of [loop_final]

val+~list_vt_cons
  (_, arglst) = comarglst_parse (argc, argv)
var param
  : param_t = @{
  comkind= COMKINDnone ()
, wait= 0
, prelude= 0
//
, outmode= file_mode_w
//
, depgen= 0
, depgenout= stropt_none // output filename for depgen
//
, taggen= 0
, taggenout= stropt_none // output filename for taggen
//
, posmark= POSMARK_NONE
, posmarknd= POSMARKND_NONE
, typecheck_only= 0
} (* end of [var] *)
//
val () = loop (ATSHOME, argv, param, arglst)
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [ats_main.dats] *)
