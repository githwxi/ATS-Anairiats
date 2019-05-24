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
// Time: October 2008

(* ****** ****** *)

staload Sym = "ats_symbol.sats"
staload Map = "ats_map_lin.sats"

(* ****** ****** *)

staload "ats_symenv.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

#define THIS_FILE "ats_symenv.dats"

(* ****** ****** *)

typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

viewtypedef
symmap (itm:t@ype) = $Map.map_vt (sym_t, itm)
viewtypedef
symmaplst (itm:t@ype) = [n:nat] list_vt (symmap itm, n)

typedef
symenv (itm:t@ype) = '{
  map= ref (symmap itm)
, maplst= ref (symmaplst itm)
, savedlst= ref (List_vt @(symmap itm, symmaplst itm))
, pervasive= ref (symmaplst itm)
} // end of [symenv]

(* ****** ****** *)

assume symmap_t = symmap
assume symenv_t = symenv

(* ****** ****** *)
//
// HX: this one is used in other templates
//
fn{} prerr_interror () = prerr "INTERNAL ERROR (ats_symenv)"

(* ****** ****** *)

implement{itm}
symmap_search (m, k) =
  $Map.map_search<sym_t,itm> (m, k)
// end of [symmap_search]

implement{itm}
symmap_ref_search (r_m, k) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr r_m
in
  $Map.map_search<sym_t,itm> (!p_m, k)
end // end of [symmap_ref_search]

implement{itm}
symmap_list_get (m) = $Map.map_list_inf m

implement{itm}
symmap_reflist_get (r_m) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr r_m
in
  $Map.map_list_inf (!p_m)
end // end of [symmap_ref_list]

(* ****** ****** *)

implement{itm}
symmap_insert (m, k, i) = $Map.map_insert (m, k, i) 
// end of [symmap_insert]

implement{itm}
symmap_remove (m, k) = $Map.map_remove (m, k)

(* ****** ****** *)

implement{itm}
symmap_list_inf (m) = $Map.map_list_inf<sym_t,itm> (m)

(* ****** ****** *)

implement symmap_make {itm} () =
  $Map.map_make {sym_t,itm} ($Sym.compare_symbol_symbol)
// end of [symmap_make]

implement{itm} symmap_free (map) = $Map.map_free (map)

(* ****** ****** *)

fun{itm:t@ype}
symmaplst_free {n:nat} .<n>.
  (ms: list_vt (symmap itm, n)):<> void =
  case+ ms of
  | ~list_vt_cons (m, ms) => (
      symmap_free<itm> m; symmaplst_free<itm> ms
    ) // end of [list_vt_cons]
  | ~list_vt_nil () => ()
// end of [symmaplst_free]

(* ****** ****** *)

fun{itm:t@ype}
symmaplst_search {n:nat} .<n>. (
    ms0: !list_vt (symmap itm, n), k: sym_t
  ) :<> Option_vt itm = begin case+ ms0 of
  | list_vt_cons (!p_m, !p_ms) => let
      val ans = $Map.map_search (!p_m, k) in case+ ans of
      | Some_vt _ => ans where {
          val () = fold@ ms0; val () = fold@ ans
        } // end of [Some_vt]
      | ~None_vt () => ans where {
          val ans = symmaplst_search<itm> (!p_ms, k)
          val () = fold@ ms0
        } // end of [None_vt]
    end (* end of [list_vt_cons] *)
  | list_vt_nil () => (fold@ ms0; None_vt ())
end // end of [symmaplst_search]

(* ****** ****** *)

implement
symenv_make {itm} () = '{
  map= ref_make_elt (symmap_make {itm} ())
, maplst= ref_make_elt (list_vt_nil ())
, savedlst= ref_make_elt (list_vt_nil ())
, pervasive= ref_make_elt (list_vt_nil ())
} // end of [symenv_make]

(* ****** ****** *)

implement{itm}
symenv_insert_fst (env, k, i) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr env.map in
  $Map.map_insert (!p_m, k, i)
end // end of [symenv_insert_fst]

implement{itm}
symenv_remove_fst (env, k) = let
  val (vbox pf_m | p_m) = ref_get_view_ptr env.map in
  $Map.map_remove (!p_m, k)
end // end of [symenv_remove_fst]

(* ****** ****** *)

implement{itm}
symenv_search_all (env, k) = let
  val ans = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map in
    $Map.map_search (!p_m, k)
  end // end of [val]
in
  case+ ans of
  | Some_vt _ => begin
      let val () = fold@ ans in ans end
    end // end of [Some_vt]
  | ~None_vt () => let
      val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    in
      symmaplst_search<itm> (!p_ms, k)
    end // end of [None_vt]
end (* end of [symenv_search] *)

implement{itm}
symenv_pervasive_search (env, k) = let
  val (vbox pf_ms | p_ms) = ref_get_view_ptr env.pervasive
in
  symmaplst_search<itm> (!p_ms, k)
end // end of [symenv_pervasive_search]

(* ****** ****** *)

fun{itm:t@ype}
symmaplst_replace {n:nat} .<n>. (
    ms0: !list_vt (symmap itm, n), k: sym_t, i: itm
  ) :<> Option_vt itm = begin case+ ms0 of
  | list_vt_cons (!p_m, !p_ms) => let
      val ans = $Map.map_remove (!p_m, k) in case+ ans of
      | ~Some_vt _ => None_vt () where {
          val () = $Map.map_insert (!p_m, k, i)
          val () = fold@ ms0
        } // end of [Some_vt]
      | ~None_vt () => ans where {
          val ans = symmaplst_replace<itm> (!p_ms, k, i)
          val () = fold@ ms0
        } // end of [None_vt]
    end (* end of [list_vt_cons] *)
  | list_vt_nil () => (fold@ ms0; Some_vt i)
end // end of [symmaplst_replace]

implement{itm}
symenv_pervasive_replace (env, k, i) = let
  val (vbox pf_ms | p_ms) = ref_get_view_ptr env.pervasive
in
  symmaplst_replace<itm> (!p_ms, k, i)
end // end of [symenv_pervasive_search]

(* ****** ****** *)

implement{itm}
symenv_pop (env) = let
//
  fn abort (): symmap itm = begin
    prerr_interror ();
    prerr ": symenv_pop: env.maplst is empty"; prerr_newline ();
    exit {symmap itm} (1)
  end // [abort]
//
  val m = let
    val (pfbox | p_ms) = ref_get_view_ptr env.maplst
    prval vbox pf_ms = pfbox
  in
    case+ !p_ms of
    | ~list_vt_cons (m, ms) => begin
        !p_ms := (ms: symmaplst itm); m
      end // end of [list_vt_cons]
    | list_vt_nil () => begin
        fold@ (!p_ms); $effmask_ref (abort ())
      end // end of [list_vt_nil]
  end : symmap itm
  val (vbox pf_m | p_m) = ref_get_view_ptr env.map
in
  symmap_free<itm> (!p_m); !p_m := m
end // end of [symenv_pop]

//

implement
symenv_push {itm} (env) = let
  val m = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map
    val m = !p_m
  in
    !p_m := symmap_make (); m
  end : symmap itm
  val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
in
  !p_ms := list_vt_cons (m, !p_ms)
end // end of [symenv_push]

//

implement
symenv_swap
  {itm} (env, r_m) = () where {
  val (vbox pf1_m | p1_m) = ref_get_view_ptr env.map
  viewtypedef elt = symmap_t itm
  val () = $effmask_ref (ref_swap<elt> (r_m, !p1_m))
} // end of [symenv_swap]

(* ****** ****** *)

implement
symenv_save {itm} (env) = let
  val m = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map
    val m = !p_m
  in
    !p_m := symmap_make (); m
  end : symmap itm
//
  val ms = let
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    val ms = !p_ms
  in
    !p_ms := list_vt_nil (); ms
  end : symmaplst itm
//
  val (vbox pf_saved | p_saved) = ref_get_view_ptr env.savedlst
in
  !p_saved := list_vt_cons ( @(m, ms), !p_saved )
end // end of [symenv_save]

(* ****** ****** *)

implement{itm}
symenv_restore (env) = let
  viewtypedef mms = @(symmap itm, symmaplst itm)
//
  fn abort (): mms = begin
    prerr_interror ();
    prerr ": symenv_restore: env.savedlst is empty"; prerr_newline ();
    exit {mms} (1)
  end // end of [abort]
//
  val (m, ms) = let
    val (vbox pf_saved | p_saved) = ref_get_view_ptr env.savedlst
  in
    case+ !p_saved of
    | ~list_vt_cons (mms, rest) => begin
        !p_saved := (rest: List_vt mms); mms
      end // end of [list_vt_cons]
    | list_vt_nil () => begin
        fold@ (!p_saved); $effmask_ref (abort ())
      end // end of [list_vt_nil]
  end : mms // end of [val]
//
  val () = let
    val (vbox pf_m | p_m) = ref_get_view_ptr env.map
  in
    symmap_free<itm> (!p_m); !p_m := m
  end // end of [val]
//
  val () = let
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
  in
    symmaplst_free<itm> (!p_ms); !p_ms := ms
  end // end of [val]
in
  // no return value
end // end of [symenv_restore]

(* ****** ****** *)

implement
symenv_top_get (env) = let
  val r_m = env.map
  val (vbox pf_m | p_m) = ref_get_view_ptr r_m
  val m = !p_m
in
  !p_m := symmap_make (); m
end // end of [symenv_top]

implement symenv_reftop_get (env) = env.map

(* ****** ****** *)

implement{itm}
symenv_localjoin (env) = let
//
  fn abort (): symmap itm = begin
    prerr_interror ();
    prerr ": symenv_localjoin: env.maplst is empty"; prerr_newline ();
    exit {symmap itm} (1)
  end // end of [symenv_localjoint]
//
  val m1 = m where {
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    val m = (case+ !p_ms of
      | ~list_vt_cons (m, ms) => begin
          !p_ms := (ms: symmaplst itm); m
        end // list of [list_vt_cons]
      | list_vt_nil () => begin
          fold@ (!p_ms); $effmask_ref (abort ())
        end // end of [list_vt_nil]
    ) : symmap itm
  } // end of [where]
//
  val () = symmap_free<itm> m1
//
  val m2 = m where {
    val (vbox pf_ms | p_ms) = ref_get_view_ptr env.maplst
    val m = (case+ !p_ms of
      | ~list_vt_cons (m, ms) => m where {
          val () = !p_ms := (ms: symmaplst itm)
        } // end of [list_vt_cons]
      | list_vt_nil () => begin
          fold@ (!p_ms); $effmask_ref (abort ())
        end // end of [list_vt_nil]
    ) : symmap itm 
  } // end of [where]
//
  val (vbox pf_m | p_m) = ref_get_view_ptr env.map
in
  !p_m := $Map.map_join (m2, !p_m)
end // end of [symenv_localjoin]

(* ****** ****** *)

implement
symenv_pervasive_add (env, m) = let
  val (pfbox | p_ms) = ref_get_view_ptr env.pervasive
  prval vbox pf_ms = pfbox
in
  !p_ms := list_vt_cons (m, !p_ms)
end // end of [symenv_pervasive_add]

(* ****** ****** *)

(* end of [ats_symenv.dats] *)
