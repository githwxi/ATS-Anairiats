(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2009 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "symbol.sats"
staload "token.sats"
staload "grammar.sats"

(* ****** ****** *)

staload "atsyacc_top.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/lazy_vt.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"
staload _(*anonymous*) = "prelude/DATS/pointer.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"
// staload _(*anonymous*) = "prelude/DATS/slseg.dats"

(* ****** ****** *)

typedef lritem (n:int, i:int) = @{
  lritem_lhs= symbol_t
, lritem_rhs= rulerhs_t n
, lritem_ind= int i
}

typedef lritem = [n,i:nat | i <= n] lritem (n, i)

//

extern fun lritem_make {n,i:nat | i <= n}
  (lhs: symbol_t, rhs: rulerhs_t n, ind: int i): lritem (n, i)

implement lritem_make (lhs, rhs, ind) = @{
  lritem_lhs= lhs, lritem_rhs= rhs, lritem_ind= ind
}

//

extern fun lritem_nrhs_get (itm: lritem):<> int

implement lritem_nrhs_get (itm) = let
  val rhs = itm.lritem_rhs in rulerhs_num_get (rhs)
end // end of [lritem_nrhs_get]

//

extern fun lritem_is_beg (itm: lritem):<> bool
extern fun lritem_isnot_beg (itm: lritem):<> bool

implement lritem_is_beg (itm) = itm.lritem_ind = 0
implement lritem_isnot_beg (itm) = itm.lritem_ind > 0

//

extern fun lritem_is_end (itm: lritem):<> bool
extern fun lritem_isnot_end (itm: lritem):<> bool

implement lritem_is_end (itm) = let
  val rhs = itm.lritem_rhs
  val nsym = rulerhs_nsym_get (rhs)
  val ind = itm.lritem_ind
in
  if ind < nsym then false else true
end // end of [lritem_is_end]

implement lritem_isnot_end (itm) = let
  val rhs = itm.lritem_rhs
  val nsym = rulerhs_nsym_get (rhs)
  val ind = itm.lritem_ind
in
  if ind < nsym then true else false
end // end of [lritem_isnot_end]


//

extern
fun compare_lritem_lritem (itm1: lritem, itm2: lritem):<> Sgn
overload compare with compare_lritem_lritem

implement compare_lritem_lritem (itm1, itm2) = let
  val nrhs1 = lritem_nrhs_get itm1
  and nrhs2 = lritem_nrhs_get itm2
  val sgn1 = compare_int_int (nrhs1, nrhs2)
in
  if sgn1 <> 0 then sgn1 else
    compare_int_int (itm1.lritem_ind, itm2.lritem_ind)
  // end of [if]
end // end of [compare_lritem_lritem]

(* ****** ****** *)

fun fprint_lritem_rhs
  {m:file_mode} {n,i:nat | i <= n} (
    pf_mod: file_mode_lte (m, w)
  | out: &FILE m, rhs: rulerhs_t n, ind: int i
  ) : void = let
  val nsym = rulerhs_nsym_get (rhs)
  val alpha = rulerhs_symarr_get (rhs)
  fun loop {i:nat | i <= n}
    (out: &FILE m, i: int i, j: &int)
    :<cloref1> void = let
    val () = if (i = ind) then let
      val () = if (j > 0) then fprint_char (pf_mod | out, ' ')
      val () = j := j + 1
    in
      fprint_char (pf_mod | out, '.')
    end // end of [val]
  in
    if i < nsym then let
      val X = alpha[i]
      val () = if j > 0 then fprint_char (pf_mod | out, ' ')
      val () = j := j + 1
      val () = fprint_symbol (pf_mod | out, X)
    in
      loop (out, i + 1, j)
    end // end of [if]
  end (* end of [loop] *)
in
  loop (out, 0, j) where { var j: int = 0 }
end // end of [fprint_lritem_rhs]

extern fun fprint_lritem {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, itm: lritem): void

implement fprint_lritem (pf_mod | out, itm) = let
  val lhs = itm.lritem_lhs
  val () = fprint_symbol (pf_mod | out, lhs)
  val () = fprint_string (pf_mod | out, " : ")
  val () = fprint_lritem_rhs (
    pf_mod | out, itm.lritem_rhs, itm.lritem_ind
  ) // end of [val]
in
  // empty
end // end of [fprint_lritem]

extern fun print_lritem (itm: lritem): void
extern fun prerr_lritem (itm: lritem): void

implement print_lritem (itm) = print_mac (fprint_lritem, itm)
implement prerr_lritem (itm) = prerr_mac (fprint_lritem, itm)

(* ****** ****** *)

typedef lrlst = List @(lritem, symbolsetref)
viewtypedef lrlst_vt = List_vt @(lritem, symbolsetref)

typedef lrstaref = ref (lrstate_t)
typedef lrgotolst = List @(symbol_t, lrstaref)

(* ****** ****** *)

extern
fun lrstate_num_get (st: lrstate_t): int

extern
fun lrstate_num_set (st: lrstate_t, num: int): void
  = "atsyacc_lrstate_num_set"

extern
fun lrstate_lst_get (st: lrstate_t): lrlst

extern
fun lrstate_gotolst_get (st: lrstate_t): lrgotolst

extern
fun lrstate_gotolst_set (st: lrstate_t, gts: lrgotolst): void

extern fun the_lrstate_num_get (): int
extern fun the_lrstate_num_getinc (): int

extern val lrstate_none : lrstate_t
extern fun lrstate_make
  (num: int, lst: lrlst, gts: lrgotolst): lrstate_t

extern fun lrstaref_make_none (): lrstaref

(* ****** ****** *)

extern fun fprint_lrlst {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, lst: lrlst): void

implement fprint_lrlst {m}
  (pf_mod | out, lst) = loop (out, lst) where {
  fun loop (out: &FILE m, xs: lrlst): void = case+ xs of
    | list_cons (x, xs) => let
        val () = fprint_lritem (pf_mod | out, x.0)
        val () = fprint_newline (pf_mod | out) in loop (out, xs)
      end // end of [fprint_lrlst]
    | list_nil () => ()
} // end of [fprint_lrlst]

(* ****** ****** *)

staload S = "LIB/funset_avltree.dats"
typedef lrset = $S.set_t (lritem)

staload M = "LIB/funmap_avltree.dats"
typedef lrmap = $M.map_t (lritem, symbolsetref)

(* ****** ****** *)

extern fun fprint_lrmap {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, map: lrmap): void

implement fprint_lrmap {m}
  (pf_mod | out, map) = loop (out, xs) where {
  typedef keyitm = @(lritem, symbolsetref)
  fun loop (out: &FILE m, xs: stream_vt keyitm): void = case+ !xs of
    | ~stream_vt_cons (x, xs) => let
        val () = fprint_lritem (pf_mod | out, x.0)
        val () = fprint_newline (pf_mod | out) in loop (out, xs)
      end // end of [fprint_lrmap]
    | ~stream_vt_nil () => ()
  val xs = $M.funmap_make_stream_key_itm (map)
} // end of [fprint_lrmap]

extern fun print_lrmap (map: lrmap): void
extern fun prerr_lrmap (map: lrmap): void

implement print_lrmap (map) = print_mac (fprint_lrmap, map)
implement prerr_lrmap (map) = prerr_mac (fprint_lrmap, map)

(* ****** ****** *)

extern fun fprint0_lrstate {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, st: lrstate_t): void

implement fprint0_lrstate (pf_mod | out, st) = let
  val num = lrstate_num_get (st)
  val () = fprintf (pf_mod | out, "state(%i): begin\n", @(num))
  val lst = lrstate_lst_get (st)
  val () = fprint_lrlst (pf_mod | out, lst)
  val () = fprint_string (pf_mod | out, "end")
in
  fprint_newline (pf_mod | out)
end // end of [fprint0_lrstate]

extern fun print0_lrstate (st: lrstate_t): void
extern fun prerr0_lrstate (st: lrstate_t): void

implement print0_lrstate (st) = print_mac (fprint0_lrstate, st)
implement prerr0_lrstate (st) = prerr_mac (fprint0_lrstate, st)

(* ****** ****** *)

implement fprint_lrstate {m} (pf_mod | out, st) = let
  val num = lrstate_num_get (st)
  val () = fprintf (pf_mod | out, "state(%i):\n", @(num))
  val () = loop (out, lst) where {
    val lst = lrstate_lst_get (st)
    fun loop (out: &FILE m, xs: lrlst): void =
      case+ xs of
      | list_cons (x, xs) => let
          val itm = x.0; val isprint = begin
            if lritem_is_beg (itm) then lritem_is_end itm else true
          end : bool
          val () = if isprint then begin
            fprint_lritem (pf_mod | out, itm); fprint_newline (pf_mod | out)
          end // end of [val]
        in
          loop (out, xs)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop]
  } // end of [val]

  val () = () where {
    val gts = lrstate_gotolst_get (st)
    val () = fprint_newline (pf_mod | out)

    // handling terminals
    val () = loop (out, gts) where {
      fun loop (out: &FILE m, xs: lrgotolst): void =
        case+ xs of
        | list_cons (x, xs) => let
            val X = x.0 and r = x.1
          in
            case+ 0 of
            | _ when symbol_is_end X => () where {
                val () = fprint_symbol (pf_mod | out, X)
                val () = fprint_string (pf_mod | out, " : accept")
                val () = fprint_newline (pf_mod | out)
                val () = loop (out, xs)
              } // end of [_ when ...]
            | _ when symbol_is_term X => () where {
                val () = fprint_symbol (pf_mod | out, X)
                val () = fprint_string (pf_mod | out, " : shft ")
                val num1 = lrstate_num_get (!r)
                val () = fprint_int (pf_mod | out, num1)
                val () = fprint_newline (pf_mod | out)
                val () = loop (out, xs)
              } // end of [_ when ...]
            | _ => loop (out, xs)
          end // end of [list_cons]
        | list_nil () => ()
    } // end of [loop]

    // handling nonterminals
    val () = loop (out, gts) where {
      fun loop (out: &FILE m, xs: lrgotolst): void =
        case+ xs of
        | list_cons (x, xs) => let
            val X = x.0 and r = x.1
          in
            case+ 0 of
            | _ when symbol_is_nonterm X => () where {
                val () = fprint_symbol (pf_mod | out, X)
                val () = fprint_string (pf_mod | out, " : goto ")
                val num1 = lrstate_num_get (!r)
                val () = fprint_int (pf_mod | out, num1)
                val () = fprint_newline (pf_mod | out)
                val () = loop (out, xs)
              } // end of [_ when ...]
            | _ => loop (out, xs)
          end // end of [list_cons]
        | list_nil () => ()
    } // end of [loop]
  } // end of [val]

  val () = loop (out, lst) where {
    val lst = lrstate_lst_get (st)
    fun loop (out: &FILE m, xs: lrlst): void =
      case+ xs of
      | list_cons (x, xs) => let
          val itm = x.0
          val () = if lritem_is_end (itm) then let
            val () = fprint_string (pf_mod | out, "{")
            val () = fprint_symbolset (pf_mod | out, x.1)
            val () = fprint_string (pf_mod | out, "} reduce by ")
            val nrhs = lritem_nrhs_get (itm)
            val () = fprint_int (pf_mod | out, nrhs)
            val () =  fprint_newline (pf_mod | out)
          in
            // empty
          end // end of [val]
        in
          loop (out, xs)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop]
  } // end of [val]
in
  fprint_newline (pf_mod | out)
end // end of [fprint0_lrstate]

implement print_lrstate (st) = print_mac (fprint_lrstate, st)
implement prerr_lrstate (st) = prerr_mac (fprint_lrstate, st)


(* ****** ****** *)

extern
fun lrmap_nil (): lrmap

extern
fun lrmap_search (map: lrmap, k: lritem): Option_vt (symbolsetref)

extern
fun lrmap_insert (map: &lrmap, k: lritem, xs: symbolsetref): void

extern
fun lrmap_remove (map: &lrmap, k: lritem): void

//

extern fun lrset_insert (xs: &lrset, x: lritem): void

extern fun lrset_remove (xs: &lrset, x: lritem): void

extern fun lrset_choose (xs: &lrset): Option_vt (lritem)

//

local

val _cmp = lam
  (k1: lritem, k2: lritem): Sgn =<cloref> compare (k1, k2)

in

implement lrmap_nil () = $M.funmap_empty<> ()

implement lrmap_search (map, k) = $M.funmap_search (map, k, _cmp)

implement lrmap_insert (map, k, xs) =
  map := $M.funmap_insert (map, k, xs, _cmp)

implement lrmap_remove (map, k) =
  map := $M.funmap_remove (map, k, _cmp)

//

implement lrset_choose (xs) = ans where {
  val ans = $S.funset_choose<lritem> (xs)
  val () = case+ ans of
    | Some_vt x => (lrset_remove (xs, x); fold@ ans)
    | None_vt _ => (fold@ ans)
  // end of [val]
} // end of [lrset_choose]

implement lrset_insert (xs, x) = (xs := $S.funset_insert (xs, x, _cmp))
implement lrset_remove (xs, x) = (xs := $S.funset_remove (xs, x, _cmp))

end // end of [local]

(* ****** ****** *)

extern
fun eqkey_lrlst_lrlst (lst1: lrlst, lst2: lrlst):<> bool

implement eqkey_lrlst_lrlst (lst1, lst2) = let
  fun _eqkey (kis1: !lrlst, kis2: !lrlst): bool =
    case+ (kis1, kis2) of
    | (list_cons (ki1, kis1),
       list_cons (ki2, kis2)) => begin
        if compare (ki1.0, ki2.0) <> 0 then false else _eqkey (kis1, kis2)
      end (* end of [list_cons, list_cons] *)
    | (list_nil (), list_nil ()) => true
    | (_, _) => false
  // end of [_eqkey]
in
  $effmask_all (_eqkey (lst1, lst2))
end // end of [eqkey_lrlst_lrlst]

//

extern fun lrlst_hash (kis: lrlst):<> uint

implement lrlst_hash (kis) = let
  fun loop (kis: lrlst, h: uint): uint =
    case+ kis of
    | list_cons (ki, kis) => let
        val key = ki.0
        val nhrs = lritem_nrhs_get (key)
        val h = (h << 5) + h + (uint_of_int nhrs)
        val h = (h << 5) + h + (uint_of_int key.lritem_ind)
      in
        loop (kis, h)
      end // end of [list_vt_cons]
    | list_nil () => h
  // end of [loop]
in
  $effmask_all (loop (kis, 31415926U))
end // end of [lrlst_hash]

(* ****** ****** *)

local

typedef lrstate = '{
  lrstate_num= int
, lrstate_lst= lrlst
, lrstate_gotolst = lrgotolst
} // end of [lrstate]

extern castfn lrstate_intr (x: lrstate): lrstate_t
extern castfn lrstate_elim (x: lrstate_t): lrstate

val the_lrstate_num = ref_make_elt<int> (0)

in // in of [local]

extern typedef "lrstate_t" = lrstate

implement lrstate_num_get (st) = let
  val st = lrstate_elim (st) in st.lrstate_num
end // end of [lrstate_num_get]

implement lrstate_lst_get (st) = let
  val st = lrstate_elim (st) in st.lrstate_lst
end // end of [lrstate_lst_get]

implement lrstate_gotolst_get (st) = let
  val st = lrstate_elim (st) in st.lrstate_gotolst
end // end of [lrstate_gotolst_get]

//

implement the_lrstate_num_get () = !the_lrstate_num

implement the_lrstate_num_getinc () = let
  val n = !the_lrstate_num; val () = !the_lrstate_num := n+1 in n
end // end of [the_lrstate_num_getinc]

//

implement lrstate_make (num, lst, gts) = lrstate_intr '{
  lrstate_num= num
, lrstate_lst= lst // [lst] is required to be a closure
, lrstate_gotolst= gts
} // end of [lrstate_make]

implement lrstate_none =
  lrstate_make (~1, list_nil(*lrlst*), list_nil(*gts*))

implement lrstaref_make_none () =
  ref_make_elt<lrstate_t> (lrstate_none)

end // end of [local]

(* ****** ****** *)

staload H = "LIB/hashtable.dats"

extern fun the_lrlst_merge (lst: lrlst): void
extern fun the_lrlst_insert (lst: lrlst, st: lrstate_t): void
extern fun the_lrlst_search (lst: lrlst): Option_vt (lrstate_t)

local

typedef key = lrlst; typedef itm = lrstate_t

val the_lrlst_table = let
  val hfn = lam (x: lrlst): uint =<cloref> lrlst_hash (x)
  val efn = lam
    (x1: lrlst, x2: lrlst): bool =<cloref> eqkey_lrlst_lrlst (x1, x2)
in
  $H.hashtbl_make<key,itm> (hfn, efn)
end // end of [the_lrlst_table]

in

implement the_lrlst_merge (lst) = let
  val ost1 = $H.hashtbl_search (the_lrlst_table, lst)
  val () = case+ ost1 of
    | ~Some_vt st1 => let
        // this is a bit risky and innovative :)
        extern castfn lstcast_to (lst: lrlst): lrlst_vt
        extern castfn lstcast_of (lst: lrlst_vt): lrlst
        val lst0 = lstcast_to (lst)
        val lst1 = lrstate_lst_get (st1)
        val () = loop (lst0, lst1) where {
          fun loop (kis0: !lrlst_vt, kis1: lrlst): void =
            case+ kis0 of
            | list_vt_cons (!p_ki0, !p_kis0) => begin case+ kis1 of
              | list_cons (ki1, kis1) => let
                  val () = symbolset_union (p_ki0->1, ki1.1)
                in
                  fold@ kis0
                end // end of [let]
              | list_nil () => (fold@ kis0)
              end // end of [list_vt_cons]
            | list_vt_nil () => (fold@ kis0)
        } // end of [val]
        val lst = lstcast_of (lst0)
      in
        // empty
      end // end of [Some_vt]
    | ~None_vt () => ()
  // end of [val]
in
  // empty
end // end of [lrlst_insert]

implement the_lrlst_insert (lst, st) = () where {
  val ans = $H.hashtbl_insert_err<key,itm> (the_lrlst_table, lst, st)
  val () = case+ ans of ~Some_vt _ => () | ~None_vt () => ()
} // end of [the_lrlst_insert]

implement the_lrlst_search (lst) =
  $H.hashtbl_search<key,itm> (the_lrlst_table, lst)

end // end of [local]

(* ****** ****** *)

fun symarr_frstset_gen
  {n:nat} {lb,ub:nat | lb <= ub; ub <= n}
  (alpha: symarr n, lb: int lb, ub: int ub, nullable: &bool)
  : symbolsetref = let
  fun loop {lb,ub:nat | lb <= ub; ub <= n} .<ub-lb>.
    (lb: int lb, ub: int ub, res: symbolsetref, nullable: &bool)
    :<cloref1> symbolsetref =
    if lb < ub then let
      val X = alpha[lb]
      val X_fstset = symbol_frstset_get X
      val () = symbolset_union (res, X_fstset)
    in
      if symbol_nullable_get X then loop (lb+1, ub, res, nullable) else res
    end else begin
      nullable := true; res
    end // end of [if]
  // end of [loop]  
in
  loop (lb, ub, res, nullable) where { val res = symbolset_nil () }
end // end of [symarr_frstset_gen]

(* ****** ****** *)

fun lrmap_closurize (map0: lrmap): lrmap = let
  typedef key = lritem and itm = symbolsetref
  typedef keyset = $S.set_t (key)
  var set_r: keyset = $S.funset_empty<> ()
  viewdef V = keyset @ set_r
  val () = $M.funmap_foreach_clo {V}
    (view@ set_r | map0, !p_clo) where { var !p_clo = @lam
    (pf: !V | k: key, _: itm): void => lrset_insert (set_r, k)
  } // end of [val]
  var map_r: lrmap = map0
  val () = while (true) let
    val okey = lrset_choose (set_r)
    val key = (case+ okey of
      | ~Some_vt key => key | ~None_vt () => (break; exit {key} (1))
    ) : key // end of [val]
(*
    val () = begin
      print "lrmap_closurize: while: key = "; print_lritem key;
      print_newline ()
    end // end of [val]
*)
    val ind = key.lritem_ind
    val rhs = key.lritem_rhs; val nsym = rulerhs_nsym_get rhs
(*
    val () = begin
      print "lrmap_closurize: while: ind = "; print ind; print_newline ();
      print "lrmap_closurize: while: nsym = "; print nsym; print_newline ();
    end // end of [val]
*)
  in
    if ind < nsym then let
      val symarr = rulerhs_symarr_get rhs // itm = alpha . X beta
      val X = symarr[ind]; val X_rhss = symbol_rulerhslst_get (X)
(*
      val () = begin
        print "lrmap_closurize: while: X = "; print_symbol X;
        print_newline ();
      end // end of [val]
*)
    in
      case+ X_rhss of
      | list_cons _ => loop (set_r, map_r, X, X_rhss, xs) where {
          // if [xs] is empty, then the rule is not useful!!!
          val xs = xs where {
            var nullable: bool = false
            val xs = symarr_frstset_gen (symarr, ind + 1, nsym, nullable)
            val () = if nullable then let
              val oxs1 = lrmap_search (map_r, key) in case+ oxs1 of
                | ~Some_vt xs1 => symbolset_union (xs, xs1) | ~None_vt () => ()
            end : void
          } // end of [val]
(*
          val () = begin
            print "lrmap_closurize: while: xs = "; print_symbolset xs;
            print_newline ();
          end // end of [val]
*)
          fun loop (
              set_r: &keyset, map_r: &lrmap
            , lhs: symbol_t, rhss: rulerhslst, xs: symbolsetref
            ) : void = case+ rhss of
            | list_cons (rhs, rhss) => let
(*
                val () = begin
                  print "lrmap_closurize: loop: map_r = begin\n";
                  print_lrmap map_r;
                  print "end\n";
                end // end of [val]
*)
                val key0 = lritem_make (lhs, rhs, 0)
                val oxs0 = lrmap_search (map_r, key0)
                var flag: int = 0
                val () = case+ oxs0 of
                  | ~Some_vt xs0 =>
                      symbolset_union_flag (xs0, xs, flag)
                  | ~None_vt () => () where {
                      val xs0 = symbolset_nil ()
                      val () = symbolset_union (xs0, xs)
                      val () = flag := 1
                      val () = lrmap_insert (map_r, key0, xs0)
                    } // end of [None_vt]
                 // end of [val]
                 val () = if flag > 0 then lrset_insert (set_r, key0)
              in
                loop (set_r, map_r, lhs, rhss, xs)
              end // end of [list_cons]
            | list_nil () => ()
          // end of [loop]
        } // end of [list_cons]
      | list_nil () => ()
    end // end of [if ind < nsym ...]
  end (* end of [while] *)
in
  map_r // the computed closure of [map] *)
end (* end of [lrmap_closurize] *)

(* ****** ****** *)

extern
fun the_first_lritem_gen (): lritem 

implement the_first_lritem_gen () = let
  val lhs = the_accept_symbol
  val rhss = symbol_rulerhslst_get (lhs)
  val rhs = (case+ rhss of
    | list_cons (rhs, _) => rhs | list_nil () => begin
        prerr "error(INTERNAL): the_first_lritem"; prerr_newline ();
        exit {rulerhs_t} (1)
      end // end of [list_nil]
  ) : rulerhs_t
in
  lritem_make (lhs, rhs, 0)
end // end of [the_first_lritem_gen]

(* ****** ****** *)

staload Q = "LIB/linqueuelst.dats"

typedef mapstr = @(lrmap, lrstaref)

viewtypedef mapstrque =
  [n:nat] $Q.linqueuelst_vt (mapstr, n)

extern fun lrgotolst_make
  (que_r: &mapstrque, lst: lrlst): lrgotolst

typedef itmset = @(lritem, symbolsetref)

implement lrgotolst_make (que_r, lst) = let
  extern castfn lstcast_to (lst: lrlst): lrlst_vt
  extern castfn lstcast_of (lst: lrlst_vt): lrlst
  val lst = lstcast_to (lst)
  val lst1 = list_vt_copy (lst)
  val lst = lstcast_of (lst)
  fun _make_one
    (X: symbol_t, map_r: &lrmap, lst_r: &lrlst_vt): void =
    case+ lst_r of
    | list_vt_cons (itmxs, !p_lst) => let
        val itm = itmxs.0
        val rhs = itm.lritem_rhs
        val nsym = rulerhs_nsym_get (rhs)
        val ind = itm.lritem_ind
      in
        if ind < nsym then let
          val symarr = rulerhs_symarr_get (rhs)
          val X1 = symarr[ind]
        in
          if eq_symbol_symbol (X, X1) then let
            val itm_new =
              lritem_make (itm.lritem_lhs, rhs, ind+1)
            val () = lrmap_insert (map_r, itm_new, itmxs.1)
            val lst_nxt = !p_lst
            val () = (free@ {itmset} {0} (lst_r); lst_r := lst_nxt)
          in
            _make_one (X, map_r, lst_r)
          end else let
            val () = _make_one (X, map_r, !p_lst) in fold@ (lst_r)
          end // end of [if]
        end else let
          val lst_nxt = !p_lst
          val () = (free@ {itmset} {0} (lst_r); lst_r := lst_nxt)
        in
          _make_one (X, map_r, lst_r)
        end // end of [if]
      end (* end of [list_vt_cons] *)
    | list_vt_nil () => (fold@ lst_r)
  // end of [_make_one]
  fun _make_all (
      que_r: &mapstrque
    , map_r: &lrmap, lst: lrlst_vt
    , res: &lrgotolst? >> lrgotolst
    ): void = case+ lst of
    | ~list_vt_cons (itmxs, lst) => let
        val itm = itmxs.0
        val rhs = itm.lritem_rhs
        val nsym = rulerhs_nsym_get (rhs)
        val ind = itm.lritem_ind
      in
        if ind < nsym then let
          val symarr = rulerhs_symarr_get (rhs)
          val X = symarr[ind]
        in
          case+ 0 of
          | _ when symbol_is_end X =>
              _make_all (que_r, map_r, lst, res)
          | _ => let
              val itm_new =
                lritem_make (itm.lritem_lhs, rhs, ind+1)
              val () = lrmap_insert (map_r, itm_new, itmxs.1)
              var lst_r = lst
              val () = _make_one (X, map_r, lst_r)
              val map = map_r; val () = map_r := lrmap_nil ()
              val r = lrstaref_make_none ()
              val mapr = @(map, r)
              val () = $Q.linqueuelst_enqueue (que_r, mapr)
              typedef T = @(symbol_t, lrstaref)
              val Xr = @(X, r)
              val () = res := list_cons {T} {0} (Xr, ?)
              val+ list_cons (_, !p_res) = res
              val () = _make_all (que_r, map_r, lst_r, !p_res)
            in
              fold@ res
            end // end of [_]
          // end of [case]
        end else begin
          _make_all (que_r, map_r, lst, res)
        end // end of [if]
      end (* end of [list_vt_cons] *)
    | ~list_vt_nil () => (res := list_nil ())
  // end of [_make_all]
  var map_r: lrmap = lrmap_nil ()
  var res: lrgotolst // uninitialized
  val () = _make_all (que_r, map_r, lst1, res) 
in
  res 
end // end of [lrgotolst_make]

(* ****** ****** *)

viewtypedef lrstatelst_vt = List_vt (lrstate_t)

local

val the_lrstatelst_vt = ref_make_elt<lrstatelst_vt> (list_vt_nil)

in // in of [local]

fn the_lrstatelst_vt_add (st: lrstate_t): void = let
  val (vbox pf | p) = ref_get_view_ptr (the_lrstatelst_vt)
in
  !p := list_vt_cons (st, !p)
end // end of [the_lrstatelst_vt_add]

fn the_lrstatelst_vt_takeout (): lrstatelst_vt = let
  val (vbox pf | p) = ref_get_view_ptr (the_lrstatelst_vt)
  val sts = !p; val () = !p := list_vt_nil ()
in
  sts
end // end of [the_lrstatelst_vt_takeout]

end // end of [local]

(* ****** ****** *)

local

val the_lrstatelst = ref_make_elt<lrstatelst> (list_nil)

in // in of [local]

implement the_lrstatelst_get () = !the_lrstatelst
// end of [the_lrstatelst_get]

implement the_lrstatelst_initialize () = () where {
  val sts = the_lrstatelst_vt_takeout ()
  val sts = list_vt_reverse (sts)
  val () = !the_lrstatelst := list_of_list_vt (sts)
} // end of [the_lrstatelst_initialize]

end // end of [local]

(* ****** ****** *)

fn lrlst_make_lrmap (map: lrmap): lrlst = kis where {
  typedef keyitm = @(lritem, symbolsetref)
  val kis = $M.funmap_make_stream_key_itm (map)
  val (_(*n*), kis) = list_vt_of_stream_vt<keyitm> (kis)
  val kis = list_of_list_vt (kis)
} // end of [lrlst_make_lrmap]

implement the_lrtable_gen () = let
  var que_r: mapstrque = $Q.linqueuelst_nil<> ()
  val () = () where {
    var map_r: lrmap = lrmap_nil ()
    val itm = the_first_lritem_gen ()
    val () = lrmap_insert (map_r, itm, symbolset_nil ())
    val str = lrstaref_make_none ()
    val mapstr = @(map_r, str)
    val () = $Q.linqueuelst_enqueue (que_r, mapstr)
  } // end of [val]
  val () = while
    ($Q.linqueuelst_is_cons que_r) let
    val mapstr = $Q.linqueuelst_dequeue (que_r)
    val map = mapstr.0 and str = mapstr.1
    val map = lrmap_closurize map
    val lst = lrlst_make_lrmap map
    val ans = the_lrlst_search (lst)
    val () = case+ ans of
      | ~Some_vt st => let
(*
          val () = begin
            print "the_lrtable_gen: st = "; print0_lrstate (st);
            print_newline ()
          end // end of [val]
*)
          val () = !str := st in the_lrlst_merge (lst)
        end // end of [Some_vt]
      | ~None_vt () => let
          val gts = lrgotolst_make (que_r, lst)
          val num = the_lrstate_num_getinc ()
          val st_new = lrstate_make (num, lst, gts); val () = !str := st_new
          val () = the_lrstatelst_vt_add (st_new)
(*
          val () = begin
            print "the_lrtable_gen: st_new = "; print_lrstate (st_new);
            print_newline ()
          end // end of [val]
*)
        in
          the_lrlst_insert (lst, st_new)
        end // end of [None_vt]
    // end of [val]
  in
    // empty
  end // end of [while]
  val () = $Q.linqueuelst_free (que_r)
  val ntotal = the_lrstate_num_get ()
  val () = begin
    print "the total number of states = "; print (ntotal); print_newline ()
  end // end of [val]
in
  // empty
end // end of [the_lrtable_gen]

(* ****** ****** *)

%{$

ats_void_type
atsyacc_lrstate_num_set
  (ats_ptr_type st, ats_int_type num) {
  ((lrstate_t)st)->atslab_lrstate_num = num ; return ;
}

ats_void_type
atsyacc_lrstate_gotolst_set
  (ats_ptr_type st, ats_ptr_type gts) {
  ((lrstate_t)st)->atslab_lrstate_gotolst = gts ; return ;
}

%}

(* ****** ****** *)

(* end of [atsyacc_lrtable.dats] *)
