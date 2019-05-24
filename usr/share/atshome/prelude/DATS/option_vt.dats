(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

staload "prelude/SATS/option_vt.sats"

(* ****** ****** *)

implement{a} option_vt_some (x) = Some_vt (x)
implement{a} option_vt_none ( ) = None_vt ( )

(* ****** ****** *)

implement{a}
option_vt_make_opt
  (b, x) = (
  if b then let
    prval () = opt_unsome {a} (x) in Some_vt (x)
  end else let
    prval () = opt_unnone {a} (x) in None_vt ( )
  end // end of [if]
) (* end of [option_vt_make_opt] *)

(* ****** ****** *)

implement
option_vt_is_none (x) = case+ x of
  | Some_vt _ => (fold@ (x); false) | None_vt _ => (fold@ (x); true)
// end of [option_vt_is_none]

implement
option_vt_is_some (x) = case+ x of
  | Some_vt _ => (fold@ (x); true) | None_vt _ => (fold@ (x); false)
// end of [option_vt_is_some]

(* ****** ****** *)

implement{a}
option_vt_unsome
  (opt) = x where { val+ ~Some_vt (x) = opt }
// end of [option_unsome]

implement{a}
option_vt_unnone
  (opt) = () where { val+ ~None_vt () = opt }
// end of [option_unnone]

(* ****** ****** *)

implement{a}
option_vt_free (x) = 
  case+ x of ~Some_vt _ => () | ~None_vt _ => ()
// end of [option_vt_free]

(* ****** ****** *)

(* end of [option_vt.dats] *)
