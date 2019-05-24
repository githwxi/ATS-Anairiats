(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2010
**
*)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t
overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_dynexp1_syndef.sats"
overload fprint with fprint_intlst
macdef matii = match_intlst_intlst

(* ****** ****** *)

staload "atsyndef_util.sats"
staload "atsyndef_main.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

macdef list_sing (x) = cons (,(x), nil)

(* ****** ****** *)

val _n1_p1 = (~1 :: 1 :: nil ()): intlst

(* ****** ****** *)

(*
array0! {T} ($exp_1, ..., $exp_n) =
  array0_make_arrsz {T} ($arrsz ($exp_1, ..., $exp_n))
*)

(* ****** ****** *)

fun d1exp_ofarrsz_n1_p1 (
  loc0: loc_t, fid: sym_t, d1es: d1explst
) : d1exp = let
//
  val- cons (d1e2, d1es) = d1es
  val d1es_elt = (case+ d1e2.d1exp_node of
    | D1Elist (_(*npf*), d1es) => d1es | _ => list_sing (d1e2)
  ) : d1explst // end of [val]
//
  val- cons (d1e1, d1es) = d1es
  val s1a = un_d1exp_sexparg (d1e1)
  val s1as = list_sing (s1a)
//
  val q = $Syn.d0ynq_none ()
  val qfid = d1exp_qid (loc0, q, fid)
//
  val d1e_fun = d1exp_app_sta (loc0, qfid, s1as)
  val d1e_arg = d1exp_arrpsz (loc0, None (), d1es_elt)
//
in
  d1exp_app_dyn (loc0, d1e_fun, loc0, 0(*npf*), list_sing (d1e_arg))
end // end of [d1exp_ofarrsz_n1_p1]

(* ****** ****** *)

extern
fun d1exp_array_n1_p1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_array0_n1_p1]

implement
d1exp_array_n1_p1
  (loc0, d1es) = let
  val fid = $Sym.symbol_make_string "array_make_arrsz"
in
  d1exp_ofarrsz_n1_p1 (loc0, fid, d1es)
end // end of [d1exp_array_n1_p1]

implement
search_ARRAY (ns) = let
(*
  val () = fprintln! (stdout_ref, "search_ARRAY: ns = ", ns)
*)
in
  case+ 0 of
  | _ when ns \matii _n1_p1 => Some_vt (d1exp_array_n1_p1)
  | _ => None_vt ()
end // end of [search_ARRAY]

(* ****** ****** *)

extern
fun d1exp_array0_n1_p1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_array0_n1_p1]

implement
d1exp_array0_n1_p1
  (loc0, d1es) = let
  val fid = $Sym.symbol_make_string "array0_make_arrsz"
in
  d1exp_ofarrsz_n1_p1 (loc0, fid, d1es)
end // end of [d1exp_array0_n1_p1]

implement
search_ARRAY0 (ns) = let
(*
  val () = fprintln! (stdout_ref, "search_ARRAY0: ns = ", ns)
*)
in
  case+ 0 of
  | _ when ns \matii _n1_p1 => Some_vt (d1exp_array0_n1_p1)
  | _ => None_vt ()
end // end of [search_ARRAY0]

(* ****** ****** *)

(* end of [atsyndef_ARRAY.dats] *)
