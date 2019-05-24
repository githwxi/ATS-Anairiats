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
// Time: December 2007
//
(* ****** ****** *)

(* Mainly for handling metric environment during the third translation *)

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Err = "ats_error.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

overload = with $Stamp.eq_stamp_stamp

(* ****** ****** *)

implement
metric_nat_check
  (loc0, s2es_met) = let
  fun aux (
    loc0: loc_t, s2es: s2explst
  ) : void = case+ s2es of
    | list_cons (s2e, s2es) => let
        val () =
          if s2e.s2exp_srt <= s2rt_int then begin
            trans3_env_add_cstr (c3str_metric_nat (loc0, s2e))
          end
      in
        aux (loc0, s2es)
      end // end of [list_cons]
    | list_nil () => () // end of [list_nil]
  // end of [aux]
in
  aux (loc0, s2es_met)
end // end of [metric_nat_check]

(* ****** ****** *)

local

assume metric_env_token = unit_v

viewtypedef metbindlst_vt = List_vt @(d2varlst, s2explst)
val the_metbindlst: ref (metbindlst_vt) = ref_make_elt (list_vt_nil ())

in // in of [local]

(* ****** ****** *)

implement
metric_env_get (d2v_stamp) = let
//
  fun aux1 (
    d2vs: d2varlst, d2v_stamp: stamp_t
  ) : bool = case+ d2vs of
    | list_cons (d2v, d2vs) => begin
        if d2var_get_stamp d2v = d2v_stamp then true else aux1 (d2vs, d2v_stamp)
      end // end of [list_cons]
    | list_nil () => false
  // end of [aux1]
//
  fun aux2 {n:nat} .<n>. (
    xs: !list_vt (@(d2varlst, s2explst), n), d2v_stamp: stamp_t
  ) : s2explstopt = case+ xs of
    | list_vt_cons (x, !xs1) => let
        val ans = (
          if aux1 (x.0, d2v_stamp) then Some (x.1) else aux2 (!xs1, d2v_stamp)
        ) : s2explstopt
      in
        fold@ xs; ans
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs; None ())
  // end of [aux2]
//
  val (vbox pf | p) = ref_get_view_ptr (the_metbindlst)
//
in
  $effmask_all (aux2 (!p, d2v_stamp))
end // end of [metric_env_get]

(* ****** ****** *)

implement
metric_env_pop (pf | (*none*)) = let
  prval unit_v () = pf; var err: int = 0
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_metbindlst)
  in
    case+ !p of
    | ~list_vt_cons (_, metbindlst) => (!p := (metbindlst: metbindlst_vt))
    | list_vt_nil () => (fold@ (!p); err := 1)
  end // end of [val]
in
  if err > 0 then begin
    prerr "INTERNAL ERROR (ats_trans3_env_met)";
    prerr ": metric_env_pop: the_metbindlst is empty."; prerr_newline ();
    $Err.abort {void} ()
  end (* end of [if] *)
end // end of [metric_env_pop]

implement
metric_env_push (d2vs, s2es_met) =
  let val (vbox pf | p) = ref_get_view_ptr (the_metbindlst) in
    !p := list_vt_cons (@(d2vs, s2es_met), !p); (unit_v () | ())
  end // end of [let]
// end of [metric_env_push]

end // end of [local]

(* ****** ****** *)

implement
s2exp_metfn_load
  (s2e0, d2v0) = let
//
  fun aux (
    s2e0: s2exp, s2ts: &s2rtlst
  ) :<cloptr1> Option_vt s2exp = begin
    case+ s2e0.s2exp_node of
    | S2Efun (fc, lin, s2fe, npf, s2es, s2e) => begin
        case+ aux (s2e, s2ts) of
        | ~Some_vt s2e => Some_vt (
            s2exp_fun_srt (s2e0.s2exp_srt, fc, lin, s2fe, npf, s2es, s2e)
          )
        | ~None_vt () => None_vt ()
      end // end of [S2Efun]
    | S2Emetfn (_(*stampopt*), s2es, s2e) => let
        val () = s2ts := aux s2es where {
          fun aux (s2es: s2explst): s2rtlst = case+ s2es of
            | list_cons (s2e, s2es) => list_cons (s2e.s2exp_srt, aux s2es)
            | list_nil () => list_nil ()
        } // end of [where]
      in
        Some_vt (s2exp_metfn (Some (d2var_get_stamp d2v0), s2es, s2e))
      end // end of [S2Emetfn]
    | S2Euni (s2vs, s2ps, s2e) => begin case+ aux (s2e, s2ts) of
      | ~Some_vt s2e => Some_vt (s2exp_uni (s2vs, s2ps, s2e))
      | ~None_vt () => None_vt ()
      end // end of [S2Euni]
    | _ => None_vt ()
  end // end of [aux]
//
  var s2ts: s2rtlst = list_nil ()
//
in
  case+ aux (s2e0, s2ts) of
  | ~Some_vt s2e => Some_vt @(s2e, s2ts) | ~None_vt () => None_vt ()
end // end of [s2exp_metfn_load]

(* ****** ****** *)

(* end of [ats_trans3_env_met.sats] *)
