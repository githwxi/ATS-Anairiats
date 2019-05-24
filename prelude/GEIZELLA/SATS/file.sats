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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

// some basic IO operations

#if VERBOSE_PRELUDE #then

#print "Loading [file.sats] starts!\n"

#endif

(* ****** ****** *)

%{#

#include <sys/stat.h>
#include "libc/CATS/stdio.cats"

%}

(* ****** ****** *)

typedef file_mode = [m:file_mode] file_mode (m)

(* ****** ****** *)

macdef file_mode_r = $extval (file_mode r, "\"r\"")
macdef file_mode_rr = $extval (file_mode rw, "\"rr\"")
macdef file_mode_w = $extval (file_mode w, "\"w\"")
macdef file_mode_ww = $extval (file_mode rw, "\"ww\"")
macdef file_mode_a = $extval (file_mode w, "\"a\"")
macdef file_mode_aa = $extval (file_mode rw, "\"aa\"")

(* ****** ****** *)

macdef EOF = $extval (int, "EOF")
macdef stdin_ref = $extval (FILEref, "stdin")
macdef stdout_ref = $extval (FILEref, "stdout")
macdef stderr_ref = $extval (FILEref, "stderr")

(* ****** ****** *)

symintr open_file

fun open_file
  (path: string, mode: file_mode): FILEref
  = "atslib_fopen_exn"

fun close_file (fil: FILEref): void = "atslib_fclose_exn"

fun reopen_file
  (path: string, mode: file_mode, fil: FILEref): void
  = "atslib_freopen_exn"

(* ****** ****** *)

fun fflush (fil: FILEref): void = "atslib_fflush_exn"

(* ****** ****** *)

fun test_file_eof (fil: FILEref): bool = "atslib_feof"
fun test_file_exists (path: string): bool = "atspre_test_file_exists"

fun test_file_isblk (path: string): bool = "atspre_test_file_isblk"
fun test_file_ischr (path: string): bool = "atspre_test_file_ischr"
fun test_file_isdir (path: string): bool = "atspre_test_file_isdir"
fun test_file_isfifo (path: string): bool = "atspre_test_file_isfifo"
fun test_file_isreg (path: string): bool = "atspre_test_file_isreg"
fun test_file_islnk (path: string): bool = "atspre_test_file_islnk"
fun test_file_issock (path: string): bool = "atspre_test_file_issock"

(* ****** ****** *)

fun input_line (fil: FILEref): string
fun output_line (fil: FILEref, line: string): void

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [file.sats] finishes!\n"

#endif

(* end of [file.sats] *)
