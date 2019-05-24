(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* some coommonly used macro definitions *)

(* ****** ****** *)

#include "prelude/params.hats"

#if VERBOSE_PRELUDE #then

#print "Loading [macdef.ats] starts!\n"

#endif

(* ****** ****** *)

macrodef min_mac x y = if ,(x) <= ,(y) then ,(x) else ,(y)
macrodef max_mac x y = if ,(x) <= ,(y) then ,(y) else ,(x)

(* ****** ****** *)

// [orelse] and [andalso] are not defined in the curried form
// as they are infix operators
macdef orelse (x, y) = if ,(x) then true else ,(y)
macdef andalso (x, y) = if ,(x) then ,(y) else false

(* macros in short form *)

macdef print_mac (fprint, x) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  ,(fprint) (file_mode_lte_w_w | !ptr_stdout, ,(x));
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_mac]

macdef prerr_mac (fprint, x) = let
  val (pf_stderr | ptr_stderr) = stderr_get ()
in
  ,(fprint) (file_mode_lte_w_w | !ptr_stderr, ,(x));
  stderr_view_set (pf_stderr | (*none*))
end // end of [prerr_mac]

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [macdef.ats] finishes!\n"

#endif

(* ****** ****** *)

(* end of [macdef.ats] *)
