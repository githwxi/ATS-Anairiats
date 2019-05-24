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
// Time: January 2008
//
(* ****** ****** *)

(* Mainly for handling dynamic dereferences during type-checking *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

macdef prerr_location = $Loc.prerr_location

(* ****** ****** *)

implement
s2exp_addr_deref_slablst
  (loc0, s2e0, s2ls) = let
  val @(s2r0, s2ls0_ft) = s2exp_addr_normalize s2e0
  val s2ls = $Lst.list_append (s2ls0_ft, s2ls)
in
  case+ the_d2varset_env_find_viewat (s2r0, s2ls) of
  | ~Some_vt ans => let
      val @(d2v_view, s2e_vt, s2e_addr, s2ls_ft, s2ls_bk) = ans
(*
      val () = begin
        print "s2exp_add_deref_slablst: s2e_addr = "; print_s2exp s2e_addr; print_newline ();
        print "s2exp_add_deref_slablst: s2ls_ft = "; print_s2lablst s2ls_ft; print_newline ();
        print "s2exp_add_deref_slablst: s2ls_bk = "; print_s2lablst s2ls_bk; print_newline ();
      end // end of [val]
*)
      val _ (* is_local_llam *) =
        the_d2varset_env_d2var_is_llam_local d2v_view
      var cstr: s2explst = list_nil ()
      val (s2e_elt, s2e_vt, s2ls_bk) = begin
        s2exp_linget_slablst_cstr (loc0, s2e_vt, s2ls_bk, cstr)
      end // end of [val]
      val () = trans3_env_add_proplst (loc0, cstr)
(*
      val () = begin
        print "s2exp_addr_deref_slablst: d2v_view = "; print d2v_view; print_newline ();
        print "s2exp_addr_deref_slablst: s2e_vt = "; print s2e_vt; print_newline ();
        print "s2exp_addr_deref_slablst: s2e_elt = "; print s2e_elt; print_newline ();
        print "s2exp_addr_deref_slablst: s2e_addr = "; print s2e_addr; print_newline ();
      end // end of [val]
*)
      val s2ls0_bk = s2lablst_trim_s2lablst_s2lablst (s2ls0_ft, s2ls_ft, s2ls_bk)
(*
      val () = begin
        print "s2exp_add_deref_slablst; s2ls0_bk = "; print_s2lablst s2ls0_bk; print_newline ();
      end // end of [val]
*)
      val () = d2var_reset_typ_at (d2v_view, s2e_vt, s2e_addr)
    in
      (s2e_elt, s2ls0_bk)
    end // end of [Some_vt]
  | ~None_vt () => let
      fun aux (
        s2ls: s2lablst
      ) : void = begin
        case+ s2ls of
        | list_cons (s2l, s2ls) =>
            (prerr "."; prerr_s2lab s2l; aux s2ls)
        | list_nil () => ()
      end // end of [aux]
    in
      prerr_location loc0; prerr ": error(3)";
      prerr ": there is no view at ["; prerr s2r0; aux s2ls; prerr "]";
      prerr_newline ();
      $Err.abort ()
    end // end of [None_vt]
end // end of [s2exp_addr_deref_slablst]

(* ****** ****** *)

(* end of [ats_trans3_deref.dats] *)
