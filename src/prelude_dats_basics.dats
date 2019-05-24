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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

// file_mode_lte_r_r : declared in basic_dyn.ats
implement file_mode_lte_r_r = file_mode_lte_refl {r} ()

// file_mode_lte_w_w : declared in basic_dyn.ats
implement file_mode_lte_w_w = file_mode_lte_refl {w} ()

(* ****** ****** *)

%{^

/* functions for exits */

ats_void_type // external
ats_exit(const ats_int_type n) { exit(n) ; return ; }

ats_void_type // external
ats_exit_errmsg
  (const ats_int_type n, const ats_ptr_type errmsg)
{
  fprintf(stderr, "%s", (char *)errmsg) ; exit(n) ; return ;
}

%} // end of [%{^]

(* ****** ****** *)

%{^

/* functions for asserts */

ats_void_type
atspre_assert (
  const ats_bool_type assertion
) {
  if (!assertion) {
    ats_exit_errmsg (1, "[Exit: atspre_assert] failed\n") ;
  }
  return ;
} // end of [atspre_assert]

ats_void_type
atspre_assert_errmsg (
  const ats_bool_type assertion, const ats_ptr_type errmsg
) {
  if (!assertion) {
    fprintf (stderr, "%s", (char *)errmsg) ;
    ats_exit_errmsg (1, "[Exit: atspre_assert_errmsg] failed\n") ;
  }
  return ;
} // end of [atspre_assert_errmsg]

%} // end of [%{^]

(* ****** ****** *)

(* end of [prelude_dats_basics.dats] *)
