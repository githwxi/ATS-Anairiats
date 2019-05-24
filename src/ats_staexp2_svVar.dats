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
// Time: October 2007
//
(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Cnt = "ats_counter.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

// implementing [s2var_t]

typedef s2var_struct = @{
  s2var_sym= sym_t // the name
, s2var_srt= s2rt  // the sort
, s2var_tmplev= int // the template level
, s2var_sVarset= s2Varset_t // existential variable occurrences
, s2var_stamp= stamp_t // uniqueness
} // end of [s2var_struct]

local

assume s2var_t =
  [l:addr] (vbox (s2var_struct @ l) | ptr l)
// end of [s2var_t]

val s2var_name_counter = $Cnt.counter_make ()

fn s2var_name_make (): sym_t = let
  val n = $Cnt.counter_getinc s2var_name_counter
in
  $Sym.symbol_make_string ($Cnt.tostring_prefix_count ("$", n))
end // end of [s2var_name_make]

fn s2var_name_make_prefix (pre: string): sym_t = let
  val n = $Cnt.counter_getinc s2var_name_counter
in
  $Sym.symbol_make_string (pre + $Cnt.tostring_prefix_count ("$", n))
end // end of [s2var_name_make_prefix]

in // in of [local]

implement s2var_make_id_srt (id, s2t) = let

val stamp = $Stamp.s2var_stamp_make ()
val (pfgc, pfat | p) = ptr_alloc_tsz {s2var_struct?} (sizeof<s2var_struct>)
prval () = free_gc_elim {s2var_struct?} (pfgc)

val () = begin
p->s2var_sym := id;
p->s2var_srt := s2t;
p->s2var_tmplev := 0;
p->s2var_sVarset := s2Varset_nil;
p->s2var_stamp := stamp
end // end of [val]

val (pfbox | ()) = vbox_make_view_ptr (pfat | p)

in

(pfbox | p)

end // end of [s2var_make_id_srt]

implement
s2var_make_srt (s2t) = let
  val id = s2var_name_make ()
in
  s2var_make_id_srt (id, s2t)
end // end of [s2var_make_srt]

implement
s2var_copy (s2v0) = let
  val id0 = s2var_get_sym s2v0
  val s2t0 = s2var_get_srt s2v0
  val id_new = s2var_name_make_prefix ($Sym.symbol_name id0)
in
  s2var_make_id_srt (id_new, s2t0)
end // end of [s2var_copy]

(* ****** ****** *)

implement s2var_get_sym (s2v) =
  let val (vbox pf | p) = s2v in p->s2var_sym end
// end of [s2var_get_sym]

implement s2var_get_srt (s2v) =
  let val (vbox pf | p) = s2v in p->s2var_srt end
// end of [s2var_get_srt]

implement s2var_get_tmplev (s2v) =
  let val (vbox pf | p) = s2v in p->s2var_tmplev end
// end of [s2var_get_tmplev]

implement s2var_set_tmplev (s2v, lev) =
  let val (vbox pf | p) = s2v in p->s2var_tmplev := lev end
// end of [s2var_set_tmplev]

implement s2var_get_sVarset (s2v) =
  let val (vbox pf | p) = s2v in p->s2var_sVarset end
// end of [s2var_get_sVarset]

implement s2var_set_sVarset (s2v, sVs) =
  let val (vbox pf | p) = s2v in p->s2var_sVarset := sVs end
// end of [s2var_set_sVarset]

implement
s2varlst_set_sVarset (s2vs, sVs) = let
  fun loop (s2vs: s2varlst, sVs: s2Varset_t): void =
    case+ s2vs of
    | list_cons (s2v, s2vs) => (
        s2var_set_sVarset (s2v, sVs); loop (s2vs, sVs)
      ) // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (s2vs, sVs)
end // end of [s2varlst_set_sVarset]

implement s2var_get_stamp (s2v) =
  let val (vbox pf | p) = s2v in p->s2var_stamp end
// end of [s2var_get_stamp]

(* ****** ****** *)

implement lt_s2var_s2var
  (s2v1, s2v2) = compare_s2var_s2var (s2v1, s2v2) < 0
implement lte_s2var_s2var
  (s2v1, s2v2) = compare_s2var_s2var (s2v1, s2v2) <= 0

implement eq_s2var_s2var
  (s2v1, s2v2) = compare_s2var_s2var (s2v1, s2v2) = 0
implement neq_s2var_s2var
  (s2v1, s2v2) = compare_s2var_s2var (s2v1, s2v2) <> 0

fn _compare_s2var_s2var
  (s2v1: s2var_t, s2v2: s2var_t): Sgn = let
  val stamp1 =
    let val (vbox pf1 | p1) = s2v1 in p1->s2var_stamp end
  // end of [val]
  val stamp2 =
    let val (vbox pf2 | p2) = s2v2 in p2->s2var_stamp end
  // end of [val]
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end // end of [_compare_s2var_s2var]

implement
compare_s2var_s2var (s2v1, s2v2) =
  $effmask_all ( _compare_s2var_s2var (s2v1, s2v2) )
// end of [compare_s2var_s2var]

end // end of [local] // for assuming [s2var_t]

(* ****** ****** *)

implement s2var_is_boxed (s2v) =
  s2rt_is_boxed (s2var_get_srt s2v)
// end of [s2var_is_boxed]

implement s2var_is_unboxed (s2v) = ~(s2var_is_boxed s2v)

(* ****** ****** *)

implement
fprint_s2var (pf | out, s2v) = let
  val () = $Sym.fprint_symbol (pf | out, s2var_get_sym s2v)
// (*
  val () = fprint_string (pf | out, "(")
  val () = $Stamp.fprint_stamp (pf | out, s2var_get_stamp s2v)
  val () = fprint_string (pf | out, ")")
// *)
in
  // empty
end // end of [fprint_s2var]

implement print_s2var (s2v) = print_mac (fprint_s2var, s2v)
implement prerr_s2var (s2v) = prerr_mac (fprint_s2var, s2v)

(* ****** ****** *)

implement
fprint_s2varlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2var)
// end of [fprint_s2varlst]

implement
print_s2varlst (s2vs) = print_mac (fprint_s2varlst, s2vs)
implement
prerr_s2varlst (s2vs) = prerr_mac (fprint_s2varlst, s2vs)

(* ****** ****** *)
//
// HX: implementing [s2varset_t]
//

local

staload Set = "ats_set_fun.sats"
staload _(*anonymous*) = "ats_set_fun.dats"

assume s2varset_t = $Set.set_t (s2var_t)

fn cmp (
  s2v1: s2var_t, s2v2: s2var_t
) :<> Sgn =
  $effmask_all (compare_s2var_s2var (s2v1, s2v2))

fn fprint_s2varset_ptr
  {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w)
  , pf_out: !FILE m @ l
  | p: ptr l, svs: s2varset_t
  ) : void = let
//
typedef ptrint = (ptr l, int)
var pi: ptrint; val () = pi.0 := p; val () = pi.1 := 0
viewdef V = @(FILE m @ l, ptrint @ pi)
//
fn pr
  (pf: !V | s2v: s2var_t, pi: !ptr pi): void = let
  prval pf_out = pf.0
  prval pf_at = pf.1; val p = pi->0; val i = pi->1
in
  if i > 0 then fprint1_string (pf_mod | !p, ", ");
  pi->1 := i + 1;
  fprint_s2var (pf_mod | !p, s2v);
  pf.0 := pf_out;
  pf.1 := pf_at;
end // end of [pr]
//
prval pf = @(pf_out, view@ pi)
val () = $Set.set_foreach_main {V} {ptr pi} (pf | svs, pr, &pi)
//
in // in of [let]
//
pf_out := pf.0; view@ pi := pf.1
//
end // end of [fprint_s2varset_ptr]

in // in of [local]

implement fprint_s2varset (pf | out, svs) = 
  fprint_s2varset_ptr (pf, view@ out | &out, svs)

implement s2varset_nil = $Set.set_nil

implement s2varset_add (svs, s2v) = $Set.set_insert (svs, s2v, cmp)
implement s2varset_adds (svs, s2vs) = case+ s2vs of
  | list_cons (s2v, s2vs) => s2varset_adds (s2varset_add (svs, s2v), s2vs)
  | list_nil () => svs
// end of [s2varset_adds]

implement s2varset_del (svs, s2v) = $Set.set_remove (svs, s2v, cmp)
implement s2varset_dels (svs, s2vs) = case+ s2vs of
  | list_cons (s2v, s2vs) => s2varset_dels (s2varset_del (svs, s2v), s2vs)
  | list_nil () => svs
// end of [s2varset_dels]

implement s2varset_union (svs1, svs2) = $Set.set_union (svs1, svs2, cmp)

implement s2varset_ismem (svs, s2v) = $Set.set_member (svs, s2v, cmp)

end // end of [local] // for assuming [s2varset]

(* ****** ****** *)

// implementing [s2Var_t]

local

typedef s2Varbound_struct = @{
  s2Varbound_loc= loc_t, s2Varbound_val= s2exp
}

assume s2Varbound_t =
  [l:addr] (vbox (s2Varbound_struct @ l) | ptr l)

in // in of [local]

implement
s2Varbound_make
  (loc, s2e) = let
  val (pfgc, pfat | p) = begin
    ptr_alloc_tsz {s2Varbound_struct} (sizeof<s2Varbound_struct>)
  end // end of [val]
  prval () = free_gc_elim {s2Varbound_struct?} (pfgc)
  val () = (p->s2Varbound_loc := loc; p->s2Varbound_val := s2e)
  val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
in
  (pfbox | p)
end // end of [s2Varbound_make]

implement s2Varbound_get_loc (s2Vb) =
  let val (vbox pf | p) = s2Vb in p->s2Varbound_loc end
// end of [s2Varbound_get_loc]

implement s2Varbound_get_val (s2Vb) =
  let val (vbox pf | p) = s2Vb in p->s2Varbound_val end
// end of [s2Varbound_get_val]

end // end of [local] // for assuming [s2Varbound_t]

(* ****** ****** *)

typedef
s2Var_struct = @{
  s2Var_loc= loc_t // location
, s2Var_cnt= count_t // name count
, s2Var_srt= s2rt // sort may be lowered
, s2Var_svar= Option s2var_t // instantiated variable
, s2Var_equal= bool // equality status
, s2Var_link= s2expopt // solution
, s2Var_lbs= s2Varboundlst // lower bounds
, s2Var_ubs= s2Varboundlst // upper bounds
, s2Var_sVarset = s2Varset_t // avoided variable set
, s2Var_stamp= stamp_t // uniqueness
} // end of [s2Var_struct]

(* ****** ****** *)

local

assume s2Var_t =
  [l:addr] (vbox (s2Var_struct @ l) | ptr l)
// end of [s2Var_t]

val s2Var_name_counter = $Cnt.counter_make ()

in // in of [local]

implement
s2Var_make_srt (loc, s2t) = let
//
val cnt = $Cnt.counter_getinc (s2Var_name_counter)
val stamp = $Stamp.s2Var_stamp_make ()
val (pfgc, pfat | p) = ptr_alloc_tsz {s2Var_struct?} (sizeof<s2Var_struct>)
prval () = free_gc_elim {s2Var_struct?} (pfgc)
//
val () = begin
p->s2Var_loc := loc;
p->s2Var_cnt := cnt;
p->s2Var_svar := None ();
p->s2Var_srt := s2t;
p->s2Var_equal := false;
p->s2Var_link := None ();
p->s2Var_lbs := list_nil ();
p->s2Var_ubs := list_nil ();
p->s2Var_sVarset := s2Varset_nil;
p->s2Var_stamp := stamp
end // end of [val]
//
val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
//
in
//
(pfbox | p)
//
end // end of [s2Var_make_srt]

implement s2Var_make_var (loc, s2v) = let
//
val cnt = $Cnt.counter_getinc (s2Var_name_counter)
val stamp = $Stamp.s2Var_stamp_make ()
val s2t = s2var_get_srt s2v
val (pfgc, pfat | p) = ptr_alloc_tsz {s2Var_struct} (sizeof<s2Var_struct>)
prval () = free_gc_elim {s2Var_struct?} (pfgc)
//
val () = begin
p->s2Var_loc := loc;
p->s2Var_cnt := cnt;
p->s2Var_svar := Some s2v;
p->s2Var_srt := s2t;
p->s2Var_equal := false;
p->s2Var_link := None ();
p->s2Var_lbs := list_nil ();
p->s2Var_ubs := list_nil ();
p->s2Var_sVarset := s2Varset_nil;
p->s2Var_stamp := stamp
end // end of [val]
//
val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
//
in
//
(pfbox | p)
//
end // end of [s2Var_make_var]

(* ****** ****** *)

implement s2Var_get_loc (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_loc end
// end of [s2Var_get_loc]

implement s2Var_get_cnt (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_cnt end
// end of [s2Var_get_cnt]

implement s2Var_get_srt (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_srt end
// end of [s2Var_get_srt]

implement s2Var_set_srt (s2V, s2t) =
  let val (vbox pf | p) = s2V in p->s2Var_srt := s2t end
// end of [s2Var_set_srt]

implement s2Var_get_svar (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_svar end
// end of [s2Var_get_svar]

implement s2Var_get_link (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_link end
// end of [s2Var_get_link]

implement s2Var_set_link (s2V, os2e) =
  let val (vbox pf | p) = s2V in p->s2Var_link := os2e end
// end of [s2Var_set_link]

implement s2Var_get_lbs (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_lbs end
// end of [s2Var_get_lbs]

implement s2Var_set_lbs (s2V, lbs) =
  let val (vbox pf | p) = s2V in p->s2Var_lbs := lbs end
// end of [s2Var_set_lbs]

implement s2Var_get_ubs (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_ubs end
// end of [s2Var_get_ubs]

implement s2Var_set_ubs (s2V, ubs) =
  let val (vbox pf | p) = s2V in p->s2Var_ubs := ubs end
// end of [s2Var_set_ubs]

implement s2Var_get_sVarset (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_sVarset end
// end of [s2Var_get_sVarset]

implement s2Var_set_sVarset (s2V, sVs) =
  let val (vbox pf | p) = s2V in p->s2Var_sVarset := sVs end
// end of [s2Var_set_sVarset]

implement s2Var_get_stamp (s2V) =
  let val (vbox pf | p) = s2V in p->s2Var_stamp end
// end of [s2Var_get_stamp]

(* ****** ****** *)

implement lt_s2Var_s2Var
  (s2V1, s2V2) = compare_s2Var_s2Var (s2V1, s2V2) < 0
implement lte_s2Var_s2Var
  (s2V1, s2V2) = compare_s2Var_s2Var (s2V1, s2V2) <= 0

implement eq_s2Var_s2Var
  (s2V1, s2V2) = compare_s2Var_s2Var (s2V1, s2V2) = 0
implement neq_s2Var_s2Var
  (s2V1, s2V2) = compare_s2Var_s2Var (s2V1, s2V2) <> 0

implement
compare_s2Var_s2Var (s2V1, s2V2) = let
  val stamp1 =
    let val (vbox pf1 | p1) = s2V1 in p1->s2Var_stamp end
  // end of [val]
  val stamp2 =
    let val (vbox pf2 | p2) = s2V2 in p2->s2Var_stamp end
  // end of [val]
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end // end of [compare_s2Var_s2Var]

(* ****** ****** *)

end // end of [local] // for assuming [s2Var_t]

(* ****** ****** *)

implement
fprint_s2Var (pf | out, s2V) =
  $Cnt.fprint_count (pf | out, s2Var_get_cnt s2V)
// end of [fprint_s2Var]

implement print_s2Var (s2V) = print_mac (fprint_s2Var, s2V)
implement prerr_s2Var (s2V) = prerr_mac (fprint_s2Var, s2V)

(* ****** ****** *)

implement
fprint_s2Varlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s2Var)
// end of [fprint_s2Varlst]

implement print_s2Varlst (s2Vs) = print_mac (fprint_s2Varlst, s2Vs)
implement prerr_s2Varlst (s2Vs) = prerr_mac (fprint_s2Varlst, s2Vs)

(* ****** ****** *)
//
// HX: implementing [s2Varset_t]
//
local

staload Set = "ats_set_fun.sats"
staload _(*anonymous*) = "ats_set_fun.dats"

assume s2Varset_t = $Set.set_t (s2Var_t)

fn cmp (s2V1: s2Var_t, s2V2: s2Var_t):<> Sgn =
  $effmask_all (compare_s2Var_s2Var (s2V1, s2V2))
// end of [cmp]

in // in of [local]

fn fprint_s2Varset_ptr
  {m:file_mode} {l:addr} (
    pf_mod: file_mode_lte (m, w)
  , pf_out: !FILE m @ l
  | p: ptr l
  , sVs: s2Varset_t
  ) : void = let
//
  typedef ptrint = (ptr l, int)
  var pi: ptrint; val () = pi.0 := p; val () = pi.1 := 0
  viewdef V = @(FILE m @ l, ptrint @ pi)
//
  fn pr
    (pf: !V | s2V: s2Var_t, pi: !ptr pi): void = let
    prval pf_out = pf.0
    prval pf_at = pf.1; val p = pi->0; val i = pi->1
  in
    if i > 0 then fprint1_string (pf_mod | !p, ", ");
    pi->1 := i + 1;
    fprint_s2Var (pf_mod | !p, s2V);
    pf.0 := pf_out;
    pf.1 := pf_at;
  end // end of [pr]
//
  prval pf = @(pf_out, view@ pi)
  val () = $Set.set_foreach_main {V} {ptr pi} (pf | sVs, pr, &pi)
//
in // in of [let]
//
pf_out := pf.0; view@ pi := pf.1
//
end // end of [fprint_s2Varset_ptr]

implement
fprint_s2Varset (pf | out, sVs) = 
  fprint_s2Varset_ptr (pf, view@ out | &out, sVs)
// end of [fprint_s2Varset]

implement s2Varset_nil = $Set.set_nil

implement
s2Varset_add (sVs, s2V) = $Set.set_insert (sVs, s2V, cmp)
implement s2Varset_adds (sVs, s2Vs) = case+ s2Vs of
  | list_cons (s2V, s2Vs) => s2Varset_adds (s2Varset_add (sVs, s2V), s2Vs)
  | list_nil () => sVs
// end of [s2Varset_adds]

implement
s2Varset_del (sVs, s2V) = $Set.set_remove (sVs, s2V, cmp)
implement s2Varset_dels (sVs, s2Vs) = case+ s2Vs of
  | list_cons (s2V, s2Vs) => s2Varset_dels (s2Varset_del (sVs, s2V), s2Vs)
  | list_nil () => sVs
// end of [s2Varset_dels]

implement s2Varset_union (sVs1, sVs2) = $Set.set_union (sVs1, sVs2, cmp)

implement s2Varset_ismem (sVs, s2V) = $Set.set_member (sVs, s2V, cmp)

end // end of [local] // for assuming [s2Varset_t]

(* ****** ****** *)

(* end of [ats_staexp2_svVar.dats] *)
