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
//
val symbol_DO = $Sym.symbol_DO
val symbol_FOR = $Sym.symbol_FOR
//
val symbol_IN_LIST = $Sym.symbol_make_string "in_list"
val symbol_IN_RANGE = $Sym.symbol_make_string "in_range"
//
(* ****** ****** *)

val _p1_p1_n1_p1_p1 = (1 :: 1 :: ~1 :: 1 :: 1 :: nil ()): intlst

(* ****** ****** *)

(*
for! ($x:$T) in_list $exp1 do $exp2 =>
  let
    var xs: List(T) = $exp1
  in
    while (list_is_cons (xs)) (xs := atsyndef__list_uncons<T> (xs, x); $exp2)
  end
*)

extern
fun for_list (
  loc0: loc_t
, x_qid: d1exp, T: s1exp, exp1: d1exp, exp2: d1exp
) : d1exp // end of [for_list]

(* ****** ****** *)

(*
for! (x:T) in_range $exp1 do $exp2 =>
  let
    var #x: T
    val (#init, #fini, #stride) = $exp1
  in
    for (x := #init; x < #fini; x := x + #stride) $exp2
  end
*)

extern
fun for_range (
  loc0: loc_t
, x_qid: d1exp, T: s1exp, exp1: d1exp, exp2: d1exp
) : d1exp // end of [for_list]

(* ****** ****** *)

extern
fun d1exp_for_p1_p1_n1_p1_p1
  (loc: loc_t, d1es: d1explst): d1exp
// end of [d1exp_for_p1_p1_n1_p1_p1]

implement
search_FOR (ns) = let
(*
  val () = fprintln! (stdout_ref, "search_FOR: ns = ", ns)
*)
in
  case+ 0 of
  | _ when ns \matii _p1_p1_n1_p1_p1 => Some_vt (d1exp_for_p1_p1_n1_p1_p1)
  | _ => None_vt ()
end // end of [search_FOR]


implement
d1exp_for_p1_p1_n1_p1_p1
  (loc0, d1es) = let
  val- cons (d1e5, d1es) = d1es
  val exp2 = d1e5
//
  val- cons (d1e4, d1es) = d1es
  val () = un_d1exp_idext_sym (d1e4, symbol_DO)
//
  val- cons (d1e3, d1es) = d1es
  val exp1 = d1e3
//
  val- cons (d1e2, d1es) = d1es
  val (in_q, in_id) = un_d1exp_qid (d1e2)
//
  val- cons (d1e1, d1es) = d1es
  val (x_qid, T) = un_d1exp_ann_type (d1e1)
//
in
  case+ 0 of
  | _ when in_id = symbol_IN_LIST => for_list (loc0, x_qid, T, exp1, exp2)
  | _ when in_id = symbol_IN_RANGE => for_range (loc0, x_qid, T, exp1, exp2)
  | _ => let
      val () = prerr_loc_syndef (loc0)
      val () = prerr ": this form of for-loop is not supported."
      val () = prerr_newline ()
    in
      $Err.abort ()
    end // end of [_]
end // end of [d1exp_for_p1_p1_n1_p1_p1]

(* ****** ****** *)

implement
for_list
  (loc0, x_qid, T, exp1, exp2) = let
//
  val is_cons_id =
    $Sym.symbol_make_string ("atsyndef__list_is_cons")
  val uncons_id = $Sym.symbol_make_string ("atsyndef__list_uncons")
//
  val (x_q, x_id) = un_d1exp_qid (x_qid)
//
  val s0taq0 = $Syn.s0taq_none ()
  val d0ynq0 = $Syn.d0ynq_none ()
//
  val x_typ = s1exp_top (T.s1exp_loc, 0(*knd*), T)
  val x_vardec = v1ardec_make 
    (loc0, 0(*non*), x_id, loc0, Some(x_typ), None(*wth*), None(*def*))
  // end of [x_v1ardec]
//
  val xs_id = $Sym.symbol_make_string ("#xs")
  val xs_qid = d1exp_qid (loc0, d0ynq0, xs_id)
//
  val List_id = $Sym.symbol_make_string ("atsyndef__List")
  val List_qid = s1exp_qid (loc0, s0taq0, List_id)
  val xs_typ = s1exp_app (loc0, List_qid, loc0, T :: nil)
  val xs_vardec = v1ardec_make
    (loc0, 0(*non*), xs_id, loc0, Some(xs_typ), None(*wth*), Some(exp1)(*def*))
  // end of [xs_v1ardec]
  val _let_dec = d1ec_vardecs (loc0, x_vardec :: xs_vardec :: nil)
//
  val _while_inv = loopi1nv_nil (loc0)
//
  val is_cons_qid = d1exp_qid (loc0, d0ynq0, is_cons_id)
  val _arglst = xs_qid :: nil
  val _while_test = d1exp_app_dyn (loc0, is_cons_qid, loc0, 0(*npf*), _arglst)
//
  val _t0id = tmpqi0de_make_qid (loc0, d0ynq0, uncons_id)
  val _decarg = TMPS1EXPLSTLSTcons (T.s1exp_loc, T :: nil, TMPS1EXPLSTLSTnil)
  val uncons_tid = d1exp_tmpid (loc0, _t0id, _decarg)
  val _arglst = xs_qid :: x_qid :: nil
  val uncons_exp = d1exp_app_dyn (loc0, uncons_tid, loc0, 0(*npf*), _arglst)
  val update_exp = d1exp_binop (loc0, $Sym.symbol_COLONEQ, xs_qid, uncons_exp)
//
  val _while_body = d1exp_seq (loc0, update_exp :: exp2 :: list_nil ())
//
  val _while_loop = d1exp_while (loc0, _while_inv, _while_test, _while_body)
//
in
  d1exp_let (loc0, _let_dec :: nil, _while_loop)
end // end of [for_list]

(* ****** ****** *)

fun d1exp_of_int (
  T: s1exp, int: d1exp
) : d1exp = let
  val loc0 = int.d1exp_loc
  val d0ynq0 = $Syn.d0ynq_none ()
  val of_int_id = $Sym.symbol_make_string ("atsyndef__of_int")
  val _t0id = tmpqi0de_make_qid (loc0, d0ynq0, of_int_id)
  val _decarg = TMPS1EXPLSTLSTcons (T.s1exp_loc, T :: nil, TMPS1EXPLSTLSTnil)
  val of_int_tid = d1exp_tmpid (loc0, _t0id, _decarg)
  val _arglst = int :: nil
in
  d1exp_app_dyn (loc0, of_int_tid, loc0, 0(*npf*), _arglst)
end // end of [d1exp_of_int]

(* ****** ****** *)

implement
for_range
  (loc0, ind_qid, T, exp1, exp2) = let
//
//  | WITHT1YPEnone
// fun p1at_ide (_: loc_t, id: sym_t): p1at
// fun v1aldec_make
//   (_: loc_t, pat: p1at, def: d1exp, typ: witht1ype): v1aldec
// end of [v1aldec_make]
//
  val (ind_q, ind_id) = un_d1exp_qid (ind_qid)
//
  val (
    init_exp
  , fini_exp
  , incr_exp
  ) = (case+ exp1.d1exp_node of
    | D1Elist (_npf, d1es1) => (
      case+ d1es1 of
      | d1e11 :: d1e12 :: nil () => let
          val d1e13 = d1exp_int (loc0, "1")
        in
          (d1e11, d1e12, d1e13)
        end // end of [D1Elist]
      | d1e11 :: d1e12 :: d1e13 :: nil () => (d1e11, d1e12, d1e13)
      | _ => let
          val () = prerr_loc_syndef (loc0)
          val () = prerr (
            ": the list expression should be of the form (init, fini) or (init, fini, incr)."
          ) // end of [val]
          val () = prerr_newline ()
        in
          $Err.abort ()
        end // end of [_]
      ) // end of [D1Elist]
    | _ => let
        val d1e11 = d1exp_int (loc0, "0")
        val d1e11 = d1exp_of_int (T, d1e11)
        val d1e12 = exp1
        val d1e13 = d1exp_int (loc0, "1")
      in
        (d1e11, d1e12, d1e13)
      end // end of [_]
  ) : @(d1exp, d1exp, d1exp)
//
  val s0taq0 = $Syn.s0taq_none ()
  val d0ynq0 = $Syn.d0ynq_none ()
//
  val ind_typ = T
  val ind_vardec = v1ardec_make
    (loc0, 0(*non*), ind_id, loc0, Some(ind_typ), None(*wth*), None(*def*))
  // end of [x_v1ardec]
  val ind_dec = d1ec_vardecs (loc0, ind_vardec :: nil)
//
  val VALKINDval = $Syn.VALKINDval
//
  val init_id = $Sym.symbol_make_string ("#init")
  val init_qid = d1exp_qid (loc0, $Syn.d0ynq_none (), init_id)
  val init_dec = d1ec_sym_exp (loc0, init_id, init_exp)
//
  val fini_id = $Sym.symbol_make_string ("#fini")
  val fini_qid = d1exp_qid (loc0, $Syn.d0ynq_none (), fini_id)
  val fini_dec = d1ec_sym_exp (loc0, fini_id, fini_exp)
//
  val incr_id = $Sym.symbol_make_string ("#incr")
  val incr_qid = d1exp_qid (loc0, $Syn.d0ynq_none (), incr_id)
  val incr_dec = d1ec_sym_exp (loc0, incr_id, incr_exp)
//
  val _for_inv = loopi1nv_nil (loc0)
  val _for_init = d1exp_binop
    (loc0, $Sym.symbol_COLONEQ, ind_qid, init_qid)
  val _for_test = d1exp_binop (loc0, $Sym.symbol_LT, ind_qid, fini_qid)
  val _for_incr = d1exp_binop (loc0, $Sym.symbol_ADD, ind_qid, incr_qid)
  val _for_post = d1exp_binop
    (loc0, $Sym.symbol_COLONEQ, ind_qid, _for_incr)
  val _for_body = d1exp_seq (loc0, exp2 :: list_nil ())
//
  val _for_loop = d1exp_for
    (loc0, _for_inv, _for_init, _for_test, _for_post, _for_body)
  // end of [val]
in
  d1exp_let (loc0, ind_dec :: init_dec :: fini_dec :: incr_dec :: nil, _for_loop)
end // end of [for_range]

(* ****** ****** *)

(* end of [atsyndef_FOR.dats] *)
