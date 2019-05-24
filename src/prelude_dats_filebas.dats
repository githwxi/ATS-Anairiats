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

%{^
#include <sys/stat.h>
#include "libc/CATS/stdio.cats"
%}

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

%{^

ats_bool_type
atspre_test_file_exists (ats_ptr_type path) {
  int ret ;
  struct stat buf ;

  ret = stat ((char*)path, &buf) ;

  if (!ret) {
    return ats_true_bool ; // ret == 0
  } else {
    return ats_false_bool ; // ret == -1
  }
} /* test_file_exists */

ats_bool_type
atspre_test_file_isdir (ats_ptr_type path) {
  int ret ;
  struct stat buf ; mode_t mode ;

  ret = stat ((char*)path, &buf) ;

  if (!ret) { // ret == 0
    mode = buf.st_mode ;
    return S_ISDIR(mode) ? ats_true_bool : ats_false_bool ;
  } else { // ret == -1
    return ats_false_bool ;
  }
} /* atspre_test_file_dir */

%} // end of [%{^]

(* ****** ****** *)

(* end of [prelude_dats_file.dats] *)

