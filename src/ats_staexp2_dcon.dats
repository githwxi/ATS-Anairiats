(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
// Start Time: October 2007
//
(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

typedef
d2con_struct = @{
  d2con_loc= loc_t // location
, d2con_fil= fil_t // filename
, d2con_sym= sym_t // the name
, d2con_scst= s2cst_t // datatype
, d2con_vwtp= int //
, d2con_qua= List @(s2varlst, s2explst) // quantifiers
, d2con_npf= int // pfarity
, d2con_arg= s2explst // views or viewtypes
, d2con_arity_full= int // full arity
, d2con_arity_real= int // real arity after erasure
, d2con_ind= Option s2explst // indexes
, d2con_typ= s2exp // type for dynamic constructor
, d2con_tag= int // tag for dynamic constructor
, d2con_stamp= stamp_t // uniqueness
} // end of [d2con_struct]

(* ****** ****** *)

local

assume d2con_t = [l:addr] (vbox (d2con_struct @ l) | ptr l)

in // in of [local]

implement d2con_make (
  loc, fil, id, s2c, vwtp, qua, npf, arg, ind
) = let
//
val stamp = $Stamp.d2con_stamp_make ()
val arity_full = $Lst.list_length (arg)
val arity_real = let
  fun aux1 (i: int, s2es: s2explst): s2explst = case+ s2es of
    | list_cons (_, s2es1) => if i > 0 then aux1 (i-1, s2es1) else s2es
    | list_nil () => list_nil ()
  // end of [aux1]
  fun aux2 (i: int, s2es: s2explst): int = case+ s2es of
    | list_cons (s2e, s2es1) => begin
        if s2exp_is_proof s2e then aux2 (i, s2es1) else aux2 (i+1, s2es1)
      end // end of [list_cons]
    | list_nil () => i // end of [list_nil]
  // end of [aux2]
in
  aux2 (0, aux1 (npf, arg))
end // end of [val]
//
val s2e_d2c = let
  fun aux (s2e: s2exp, s2vpss: List @(s2varlst, s2explst)): s2exp =
    case+ s2vpss of
    | list_cons (s2vps, s2vpss) => begin
        s2exp_uni (s2vps.0, s2vps.1, aux (s2e, s2vpss))
      end // end of [list_cons]
    | list_nil () => s2e
  // end of [aux]
  val s2e_res = case+ ind of
    | Some s2es => s2exp_cstapp (s2c, s2es) | None () => s2exp_cst (s2c)
  // end of [val]
in
  aux (s2exp_confun (npf, arg, s2e_res), qua)
end // end of [val]
//
val (pfgc, pfat | p) = ptr_alloc_tsz {d2con_struct} (sizeof<d2con_struct>)
prval () = free_gc_elim {d2con_struct?} (pfgc)
//
val () = begin
p->d2con_loc := loc;
p->d2con_fil := fil;
p->d2con_sym := id;
p->d2con_scst := s2c;
p->d2con_vwtp := vwtp;
p->d2con_qua := qua;
p->d2con_npf := npf;
p->d2con_arg := arg;
p->d2con_arity_full := arity_full;
p->d2con_arity_real := arity_real;
p->d2con_ind := ind;
p->d2con_typ := s2e_d2c;
p->d2con_tag := ~1;
p->d2con_stamp := stamp
end // end of [val]
//
val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
//
in
//
(pfbox | p)
//
end // end of [d2con_make]

(* ****** ****** *)

implement d2con_get_fil (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_fil end

implement d2con_get_sym (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_sym end

implement d2con_get_scst (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_scst end

implement d2con_get_vwtp (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_vwtp end

implement d2con_get_qua (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_qua end

implement d2con_get_npf (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_npf end

implement d2con_get_arg (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_arg end

implement d2con_get_arity_full (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_arity_full end

implement d2con_get_arity_real (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_arity_real end

implement d2con_get_typ (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_typ end

implement d2con_get_ind (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_ind end

implement d2con_get_tag (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_tag end

implement d2con_set_tag (d2c, tag) =
  let val (vbox pf | p) = d2c in p->d2con_tag := tag end

implement d2con_get_stamp (d2c) =
  let val (vbox pf | p) = d2c in p->d2con_stamp end

(* ****** ****** *)

implement lt_d2con_d2con
  (d2c1, d2c2) = compare_d2con_d2con (d2c1, d2c2) < 0
implement lte_d2con_d2con
  (d2c1, d2c2) = compare_d2con_d2con (d2c1, d2c2) <= 0

implement eq_d2con_d2con
  (d2c1, d2c2) = compare_d2con_d2con (d2c1, d2c2) = 0
implement neq_d2con_d2con
  (d2c1, d2c2) = compare_d2con_d2con (d2c1, d2c2) <> 0

fn _compare_d2con_d2con
  (d2c1: d2con_t, d2c2: d2con_t) = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2con_stamp end
  // end of [val]
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2con_stamp end
  // end of [val]
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end // end of [compare_d2con_d2con]

implement
compare_d2con_d2con (d2c1, d2c2) =
  $effmask_all ( _compare_d2con_d2con (d2c1, d2c2) )
// end of [compare_d2con_d2con]

(* ****** ****** *)

#define D2CON_TAG_EXN ~1

implement
d2con_is_exn (d2c) = let
  val (vbox pf | p) = d2c in p->d2con_tag = D2CON_TAG_EXN
end // end of [d2con_is_exn]

#define D2CON_TAG_MSG ~2
implement d2con_is_msg (d2c) = let
  val (vbox pf | p) = d2c in p->d2con_tag = D2CON_TAG_MSG
end // end of [d2con_is_msg]

implement
d2con_is_proof (d2c) = let
  val s2c = let val (vbox pf | p) = d2c in p->d2con_scst end
in
  s2rt_is_proof_fun (s2cst_get_srt s2c)
end // end of [d2con_is_proof]

end // end of [local] (for assuming d2con_t)

(* ****** ****** *)

implement
fprint_d2con (pf_out | out, d2c) =
  $Sym.fprint_symbol (pf_out | out, d2con_get_sym d2c)
// end of [fprint_d2con]

implement print_d2con (d2c) = print_mac (fprint_d2con, d2c)
implement prerr_d2con (d2c) = prerr_mac (fprint_d2con, d2c)

(* ****** ****** *)

implement
fprint_d2conlst
  {m} (pf | out, d2cs) = let
  fun aux (
    out: &FILE m, d2cs: d2conlst, i:int
  ) : void = begin case+ d2cs of
    | D2CONLSTcons (d2c, d2cs) => let
        val () = if i > 0 then
          fprint1_string (pf | out, ", ")
        val () = fprint_d2con (pf | out, d2c)
      in
        aux (out, d2cs, i+1)
      end // end of [D2CONLSTcons]
    | D2CONLSTnil () => () // end of [nil]
  end // end of [aux]
in
  aux (out, d2cs, 0)
end // end of [fprint_d2conlst]

implement print_d2conlst (d2cs) = print_mac (fprint_d2conlst, d2cs)
implement prerr_d2conlst (d2cs) = prerr_mac (fprint_d2conlst, d2cs)

(* ****** ****** *)

(* end of [ats_staexp2_dcon.dats] *)
