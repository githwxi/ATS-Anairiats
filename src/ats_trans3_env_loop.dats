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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December 2007

(* ****** ****** *)

staload Err = "ats_error.sats"

(* ****** ****** *)

staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

assume lamloop_env_token = unit_v

typedef lamlooplst = List lamloop

val the_lamloop = ref_make_elt<lamloop> (LMLPnone ())
val the_lamloops = ref_make_elt<lamlooplst> (list_nil)

(* ****** ****** *)

implement the_lamloop_env_top () = !the_lamloop

(* ****** ****** *)

implement the_lamloop_env_pop (pf | (*none*)) = let
  prval unit_v () = pf in case+ !the_lamloops of
  | list_cons (lmlp, lmlps) => begin
      !the_lamloop := lmlp; !the_lamloops := lmlps
    end // end of [list_cons]
  | list_nil () => begin
      prerr "INTERNAL ERROR (ats_trans3_env_loop)";
      prerr ": the_lamloop_env_pop"; prerr_newline ();
      $Err.abort {void} ()
    end // end of [list_nil]
end // end of [the_lamloop_env_pop]

(* ****** ****** *)

fn the_lamloop_env_push (lmlp: lamloop)
  : (lamloop_env_token | void) = begin
  !the_lamloops := list_cons (!the_lamloop, !the_lamloops);
  !the_lamloop := lmlp;
  (unit_v () | ())
end // end of [the_lamloop_env_push]

implement the_lamloop_env_push_lam (p3ts) = begin
  the_lamloop_env_push (LMLPlam p3ts)
end // end of [the_lamloop_env_push_lam]

implement the_lamloop_env_push_loop0 () = begin
  the_lamloop_env_push (LMLPloop0 ())
end // end of [the_lamloop_env_push_loop0]

implement the_lamloop_env_push_loop1
  (sbis, sac_init, sac_exit, post) = begin
  the_lamloop_env_push (LMLPloop1 (sbis, sac_init, sac_exit, post))
end // end of [the_lamloop_env_push_loop1]

(* ****** ****** *)

implement
the_lamloop_env_arg_get () = let
//
fun aux (
  lmlps: lamlooplst
) : Option_vt p3atlst = (
  case+ lmlps of
  | list_cons (lmlp, lmlps) => (
    case+ lmlp of
    | LMLPlam p3ts => Some_vt (p3ts) | _ => aux lmlps
    )
  | list_nil () => None_vt ()
) // end of [aux]
//
in
  case+ !the_lamloop of
  | LMLPlam p3ts => Some_vt (p3ts) | _ => aux !the_lamloops
end // end of [the_lamloop_env_arg_get]

(* ****** ******* *)

(* end of [ats_trans3_env_loop.dats] *)
