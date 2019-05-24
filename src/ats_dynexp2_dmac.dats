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

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef d2mac_struct (narg:int) = @{
  d2mac_loc= loc_t
, d2mac_sym= sym_t
, d2mac_kind= int // short/long: 0/1
, d2mac_narg= int narg // argument
, d2mac_arglst= list (macarg, narg) // argument
, d2mac_def= d2exp // definition
, d2mac_stamp= stamp_t // uniqueness stamp
} // end of [d2mac_struct]

(* ****** ****** *)

local

assume d2mac_abs_t (narg:int) =
  [l:addr] (vbox (d2mac_struct narg @ l) | ptr l)
// end of [assume]

in // in of [local]

implement
d2mac_make {narg}
  (loc, name, knd, args, def) = let
//
val narg = aux args where {
  fun aux {narg:nat}
    (args: macarglst narg): int narg = case+ args of
    | list_cons (_, args) => 1 + aux (args) | list_nil () => 0
} // end of [where]
//
val stamp = $Stamp.d2mac_stamp_make ()
val (pfgc, pfat | p) =
  ptr_alloc_tsz {d2mac_struct narg} (sizeof<d2mac_struct narg>)
// end of [val]
prval () = free_gc_elim {d2mac_struct(narg)?} (pfgc)
//
val () = begin
p->d2mac_loc := loc;
p->d2mac_sym := name;
p->d2mac_kind := knd;
p->d2mac_narg := narg;
p->d2mac_arglst := args;
p->d2mac_def := def;
p->d2mac_stamp := stamp
end // end of [val]
//
val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
//
in // in of [let]
//
(pfbox | p)
//
end // end of [d2mac_make]

implement d2mac_get_loc (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_loc end

implement d2mac_get_sym (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_sym end

implement d2mac_get_kind (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_kind end

implement d2mac_get_narg (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_narg end

implement d2mac_get_arglst (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_arglst end

implement d2mac_get_def (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_def end

implement d2mac_set_def (d2m, def) =
  let val (vbox pf | p) = d2m in p->d2mac_def := def end

implement d2mac_get_stamp (d2m) =
  let val (vbox pf | p) = d2m in p->d2mac_stamp end

end // end of [d2mac_t] (for assuming d2mac_t)

(* ****** ****** *)

implement
fprint_d2mac (pf_out | out, d2m) =
  $Sym.fprint_symbol (pf_out | out, d2mac_get_sym d2m)
// end of [fprint_d2mac]

implement print_d2mac (d2m) = print_mac (fprint_d2mac, d2m)
implement prerr_d2mac (d2m) = prerr_mac (fprint_d2mac, d2m)

(* ****** ****** *)

(* end of [ats_dynexp2_dmac.dats] *)
