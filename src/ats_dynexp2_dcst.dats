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
// Time: November 2007
//
(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef
d2cst_struct = @{
  d2cst_loc= loc_t
, d2cst_fil= fil_t
, d2cst_sym= sym_t
, d2cst_kind= $Syn.dcstkind
, d2cst_decarg= s2qualst // template arg
, d2cst_arilst= List int // arity
, d2cst_typ= s2exp // assigned type
, d2cst_extdef= dcstextdef // external dcst definition
, d2cst_def= d2expopt // definition
, d2cst_stamp= stamp_t // unique stamp
, d2cst_hityp= Option (hityp_t) // type erasure
} // end of [d2cst_struct]

local

assume d2cst_t = [l:addr] (vbox (d2cst_struct @ l) | ptr l)

in // in of [local]

implement d2cst_make
  (id, fil, loc, dck, decarg, arilst, typ, extdef) = let

val stamp = $Stamp.d2cst_stamp_make ()
val (pfgc, pfat | p) = ptr_alloc_tsz {d2cst_struct?} (sizeof<d2cst_struct>)
prval () = free_gc_elim {d2cst_struct?} (pfgc)
//
val () = begin
p->d2cst_loc := loc;
p->d2cst_fil := fil;
p->d2cst_sym := id;
p->d2cst_kind := dck;
p->d2cst_decarg := decarg;
p->d2cst_arilst := arilst;
p->d2cst_typ := typ;
p->d2cst_extdef := extdef;
p->d2cst_def := None ();
p->d2cst_stamp := stamp;
p->d2cst_hityp := None ();
end // end of [val]
//
val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
//
in
//
(pfbox | p)
//
end // end of [d2cst_make]

implement d2cst_get_loc (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_loc end

implement d2cst_get_fil (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_fil end

implement d2cst_get_sym (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_sym end

implement d2cst_get_kind (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_kind end

implement d2cst_get_arilst (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_arilst end

implement d2cst_get_decarg (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_decarg end

implement d2cst_set_decarg (d2c, decarg) =
  let val (vbox pf | p) = d2c in p->d2cst_decarg := decarg end

implement d2cst_get_typ (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_typ end

implement d2cst_get_extdef (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_extdef end

implement d2cst_get_def (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_def end

implement d2cst_set_def (d2c, def) =
  let val (vbox pf | p) = d2c in p->d2cst_def := def end

implement d2cst_get_stamp (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_stamp end

// [d2cst_get_hityp] is declared in [ats_hiexp.sats]
implement d2cst_get_hityp (d2c) =
  let val (vbox pf | p) = d2c in p->d2cst_hityp end

(* ****** ****** *)

implement lt_d2cst_d2cst
  (d2c1, d2c2) = compare_d2cst_d2cst (d2c1, d2c2) < 0
implement lte_d2cst_d2cst
  (d2c1, d2c2) = compare_d2cst_d2cst (d2c1, d2c2) <= 0

implement eq_d2cst_d2cst
  (d2c1, d2c2) = compare_d2cst_d2cst (d2c1, d2c2) = 0
implement neq_d2cst_d2cst
  (d2c1, d2c2) = compare_d2cst_d2cst (d2c1, d2c2) <> 0

fn _compare_d2cst_d2cst
  (d2c1: d2cst_t, d2c2: d2cst_t): Sgn = let
  val stamp1 =
    let val (vbox pf1 | p1) = d2c1 in p1->d2cst_stamp end
  // end of [val]
  val stamp2 =
    let val (vbox pf2 | p2) = d2c2 in p2->d2cst_stamp end
  // end of [val]
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end // end of [_compare_d2cst_d2cst]

implement
compare_d2cst_d2cst (d2c1, d2c2) =
  $effmask_all ( _compare_d2cst_d2cst (d2c1, d2c2) )
// end of [compare_d2cst_d2cst]

(* ****** ****** *)

implement d2cst_is_fun (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_fun (knd)
end // end of [d2cst_is_fun]

(* ****** ****** *)

implement d2cst_is_extmac (d2c) = let
  val extdef = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_extdef end
  ) // end of [val]
in
  $Syn.dcstextdef_is_mac (extdef)
end // end of [d2cst_is_callfn]


implement d2cst_is_extsta (d2c) = let
  val extdef = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_extdef end
  ) // end of [val]
in
  $Syn.dcstextdef_is_sta (extdef)
end // end of [d2cst_is_callfn]

(* ****** ****** *)

implement d2cst_is_castfn (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_castfn (knd)
end // end of [d2cst_is_castfn]

//

implement d2cst_is_praxi (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_praxi (knd)
end // end of [d2cst_is_praxi]

implement d2cst_is_prfun (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_prfun (knd)
end // end of [d2cst_is_prfun]

implement d2cst_is_prval (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_prval (knd)
end // end of [d2cst_is_prval]

implement d2cst_is_proof (d2c) = let
  val knd = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_kind end
  ) // end of [val]
in
  $Syn.dcstkind_is_proof (knd)
end // end of [d2cst_is_proof]

//

implement d2cst_is_temp (d2c) = let
  val decarg = $effmask_ref (
    let val (vbox pf | p) = d2c in p->d2cst_decarg end
  ) // end of [val]
in
  case+ decarg of list_cons _ => true | list_nil _ => false
end // end of [d2cst_is_temp]

end // end of [local] (for assuming d2cst_t)

(* ****** ****** *)

implement
d2cst_get_name (d2c) =
  $Sym.symbol_name (d2cst_get_sym (d2c))
// end of [d2cst_get_name]

(* ****** ****** *)

implement
fprint_d2cst (pf_out | out, d2c) = begin
  $Sym.fprint_symbol (pf_out | out, d2cst_get_sym d2c)
end // end of [fprint_d2cst]

implement print_d2cst (d2c) = print_mac (fprint_d2cst, d2c)
implement prerr_d2cst (d2c) = prerr_mac (fprint_d2cst, d2c)

(* ****** ****** *)

implement
fprint_d2cstlst (pf | out, cs) =
  $Lst.fprintlst (pf | out, cs, ", ", fprint_d2cst)
// end of [fprint_d2cstlst]

implement print_d2cstlst (d2cs) = print_mac (fprint_d2cstlst, d2cs)
implement prerr_d2cstlst (d2cs) = prerr_mac (fprint_d2cstlst, d2cs)

(* ****** ****** *)

//
// HX: [d2cst_hityp_set] is declared in [ats_hiexp.sats]
//

extern typedef "d2cst_struct" = d2cst_struct

%{$

ats_void_type
atsopt_d2cst_set_hityp (
  ats_ptr_type d2c, ats_ptr_type ohit
) {
  ((d2cst_struct*)d2c)->atslab_d2cst_hityp = ohit ; return ;
} /* end of [atsopt_d2cst_set_hityp] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_dynexp2_dcst.dats] *)
