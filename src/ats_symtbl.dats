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
// Time: July 2007
//
(* ****** ****** *)

staload "ats_array.sats"
staload _(*anonymous*) = "ats_array.dats"

(* ****** ****** *)

staload "ats_counter.sats"

(* ****** ****** *)

staload "ats_symbol.sats"
staload "ats_symtbl.sats"

(* ****** ****** *)

viewtypedef
tblent = Option symbol_t

viewtypedef
symtbl (sz:int, n:int, l:addr) = @{
  ptr= ptr l
, view= @(free_gc_v (tblent?, sz, l), @[tblent][sz] @ l)
, size= int sz
, nitm= int n
} // end of [symtbl]

viewtypedef symtbl0 = symtbl (0, 0, null)

viewtypedef symtbl =
  [sz,n:nat | sz > 0] [l:addr] symtbl (sz, n, l)

assume symtbl_t =
  [l_tbl: addr] (vbox (symtbl @ l_tbl) | ptr l_tbl)

(* ****** ****** *)

implement
symtbl_make (sz) = let
  val (pf_tbl_gc, pf_tbl | p_tbl) =
    ptr_alloc_tsz {symtbl0} (sizeof<symtbl>)
  prval () = free_gc_elim {symtbl0?} (pf_tbl_gc)
(*
  val () = (
    print "symtbl_make: p_tbl = "; print p_tbl; print_newline ()
  ) // end of [val]
*)
  val asz = max (sz, 1)
  val tsz = sizeof<tblent>
  val (pf_arr_gc, pf_arr | p_arr) =
    array_ptr_alloc_tsz {tblent} (asz, tsz)
  val () = begin
    array_ptr_initialize_elt<tblent> (!p_arr, asz, ini)
  end where {
    var ini: tblent = None ()
  } // end of [val]
(*
  val () = (
    print "symtbl_make: p_arr = "; print p_arr; print_newline ()
  ) // end of [val]
*)
  val () = begin
    p_tbl->ptr := p_arr;
    p_tbl->view := @(pf_arr_gc, pf_arr);
    p_tbl->size := asz; p_tbl->nitm := 0
  end // end of [val]
  val (pfbox | ()) = vbox_make_view_ptr (pf_tbl | p_tbl)
in
  (pfbox | p_tbl)
end // end of [symtbl_make]

// linear probing
fun symtbl_search_probe
  {sz,i:nat | i < sz} {l:addr} (
    pf: !array_v(tblent, sz, l)
  | p: ptr l, sz: int sz, i: int i, name: string
  ) :<!ntm> tblent = let
(*
  val () = $effmask_all begin
    print "symtbl_search_probe: p = "; print p; print_newline ()
  end // end of [val]
*)
  val ent = p[i] in case+ ent of
  | Some (sym) => begin
      if symbol_name sym = name then ent else let
        val i = i + 1; val i = (if i < sz then i else 0): natLt sz
      in
        symtbl_search_probe (pf | p, sz, i, name)
      end // end of [if]
    end // end of [Some]
  | None () => None ()     
end // end of [symtbl_search_probe]

implement symtbl_search (tbl, name) = let
  val hash_val = string_hash_33 name
  val hash_val = uint_of_ulint (hash_val)
  val hash_val = uint1_of_uint (hash_val)
(*
  val () = printf ("symtbl_search: name = %s\n", @(name))
  val () = printf ("symtbl_search: hash_val = %u\n", @(hash_val))
*)
  val (vbox pf_tbl | p_tbl) = tbl
  val i = hash_val uimod p_tbl->size
in
  symtbl_search_probe (p_tbl->view.1 | p_tbl->ptr, p_tbl->size, i, name)
end // end of [symtbl_search]

(* ****** ****** *)

fun symtbl_insert_probe
  {sz,i:nat | i < sz} {l:addr} (
    pf: !array_v(tblent, sz, l)
  | p: ptr l, sz: int sz, i: int i, sym: symbol_t
  ) :<!ntm> void = let
  val ent = p[i] in case+ ent of
    | Some _ => let
        val i = i + 1; val i = (if i < sz then i else 0): natLt sz
      in
        symtbl_insert_probe (pf | p, sz, i, sym)
      end // end of [Some]
    | None () => begin
        p[i] := Some sym
      end // end of [None]
end // end of [symtbl_insert_probe]

(* ****** ****** *)

fun symtbl_resize_move
  {sz,i:nat | i <= sz} {l,l_new:addr} (
    pf: !array_v(tblent, sz, l),
    pf_new: !array_v(tblent, sz+sz, l_new)
  | p: ptr l, p_new: ptr l_new, sz: int sz, i: int i
  ) :<!ntm> void = begin
  if i < sz then let
    val () = (case+ p[i] of
      | Some sym => let
          val sz2 = sz + sz
          val hash_val = string_hash_33 (symbol_name sym)
          val hash_val = uint_of_ulint (hash_val)
          val hash_val = uint1_of_uint (hash_val)
          val i = hash_val uimod sz2
        in
          symtbl_insert_probe (pf_new | p_new, sz2, i, sym);
        end // end of [Some]
     | None () => ()
   ) : void // end of [val]
  in
     symtbl_resize_move (pf, pf_new | p, p_new, sz, i+1)
  end // end of [if]
end (* end of [symtbl_resize_move] *)

fun symtbl_resize
  (tbl: symtbl_t):<!ntm,!ref> void = let
  val (vbox pf_tbl | p_tbl) = tbl
  val p_arr = p_tbl->ptr
  prval (pf_arr_gc, pf_arr) = p_tbl->view
  val sz = p_tbl->size
  val sz2 = sz + sz; val tsz = sizeof<tblent>
  val (pf1_arr_gc, pf1_arr | p1_arr) =
    array_ptr_alloc_tsz {tblent} (sz2, tsz)
  val () = begin
    array_ptr_initialize_elt<tblent> (!p1_arr, sz2, ini)
  end where {
    var ini: tblent = None ()
  } // end of [val]
  val () = symtbl_resize_move (pf_arr, pf1_arr | p_arr, p1_arr, sz, 0)
  val () = array_ptr_free {tblent} (pf_arr_gc, pf_arr | p_arr)
in
  p_tbl->ptr := p1_arr;
  p_tbl->view := @(pf1_arr_gc, pf1_arr);
  p_tbl->size := sz + sz;
end // end of [symtbl_resize]

fun symtbl_resize_if
  (tbl: symtbl_t):<!ntm,!ref> void = let
  val nitm =
    let val (vbox pf_tbl | p_tbl) = tbl in p_tbl->nitm end
  val size = 
    let val (vbox pf_tbl | p_tbl) = tbl in p_tbl->size end
in
  if (2 * nitm > size) then symtbl_resize (tbl)
end // end of [symtbl_resize_if]

(* ****** ****** *)

implement
symtbl_insert (tbl, name, sym) = let

val () = symtbl_resize_if (tbl)
val hash_val = string_hash_33 name
val hash_val = uint_of_ulint (hash_val)
val hash_val = uint1_of_uint (hash_val)
(*
val () = printf ("symtbl_insert: name = %s\n", @(name))
val () = printf ("symtbl_insert: hash_val = %u\n", @(hash_val))
*)
val (vbox pf_tbl | p_tbl) = tbl
val i = hash_val uimod p_tbl->size

in

symtbl_insert_probe (p_tbl->view.1 | p_tbl->ptr, p_tbl->size, i, sym);
p_tbl->nitm := 1 + p_tbl->nitm

end // end of [symtbl_insert]

(* ****** ****** *)

(* end of [ats_symtbl.dats] *)
