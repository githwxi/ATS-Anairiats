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
// Start Time: December 2007
//
(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

staload Lst = "ats_list.sats"

staload Syn = "ats_syntax.sats"
typedef funclo = $Syn.funclo

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_staexp2_pprint.sats"
staload "ats_stadyncst2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_staexp2_solve.sats"

(* ****** ****** *)

#define THISFILENAME "ats_staexp2_solve.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

overload = with $Lab.eq_label_label
overload = with $Stamp.eq_stamp_stamp
overload = with $Syn.eq_funclo_funclo

overload prerr with $Loc.prerr_location

(* ****** ****** *)

fn prerr_loc_error3 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(3)")
// end of [prerr_loc_error3]

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_staexp2_solve)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

datatype staerr =
  | STAERR_s2exp_tyleq of (loc_t, s2exp, s2exp)
  | STAERR_s2exp_equal of (loc_t, s2exp, s2exp)
  | STAERR_funclo_equal of (loc_t, funclo, funclo)
  | STAERR_s2eff_leq of (loc_t, s2eff, s2eff)
  | STAERR_s2exp_linearity of (loc_t, s2exp)
// end of [datatype]

viewtypedef staerrlst_vt = List_vt (staerr)

(* ****** ****** *)

local

var the_staerrlst: staerrlst_vt = list_vt_nil ()

val p_the_staerrlst =
  &the_staerrlst // end of [val]
val (pfbox_the_staerrlst | ()) =
  vbox_make_view_ptr {staerrlst_vt} (view@ (the_staerrlst) | p_the_staerrlst)
// end of [val]

in // in of [local]

fn the_staerrlst_add
  (x: staerr): void = let
  prval vbox pf = pfbox_the_staerrlst
in
  !p_the_staerrlst := list_vt_cons (x, !p_the_staerrlst)
end // end of [the_staerrlst_add]

fn the_staerrlst_get
  (): staerrlst_vt = let
  prval vbox pf = pfbox_the_staerrlst
  val xs = !p_the_staerrlst
  val () = !p_the_staerrlst := list_vt_nil ()
in
  xs
end // end of [the_staerrlst_get]

end // end of [local]

fn prerr_staerr_funclo_equal
  (loc: loc_t, fc1: funclo, fc2: funclo): void = begin
  prerr_loc_error3 (loc);
  prerr ": function/closure mismatch:\n";
  prerr "The needed funclo kind is: "; $Syn.prerr_funclo fc2; prerr_newline ();
  prerr "The actual funclo kind is: "; $Syn.prerr_funclo fc1; prerr_newline ();
end // end of [prerr_staerr_funclo_equal]

fn prerr_staerr_s2exp_tyleq
  (loc: loc_t, s2e1: s2exp, s2e2: s2exp): void = begin
  prerr_loc_error3 (loc);
  prerr ": mismatch of static terms (tyleq):\n";
  prerr "The needed term is: "; pprerr_s2exp s2e2; prerr_newline ();
  prerr "The actual term is: "; pprerr_s2exp s2e1; prerr_newline ();
end // end of [prerr_staerr_s2exp_tyleq]

fn prerr_staerr_s2exp_equal
  (loc: loc_t, s2e1: s2exp, s2e2: s2exp): void = begin
  prerr_loc_error3 (loc);
  prerr ": mismatch of static terms (equal):\n";
  prerr "The needed term is: "; pprerr_s2exp s2e2; prerr_newline ();
  prerr "The actual term is: "; pprerr_s2exp s2e1; prerr_newline ();
end // end of [prerr_staerr_s2exp_equal]

fn prerr_staerr_s2eff_leq
  (loc: loc_t, s2fe1: s2eff, s2fe2: s2eff): void = begin
  prerr_loc_error3 (loc);
  prerr ": mismatch of effects:\n";
  prerr "The needed term is: "; prerr_s2eff s2fe2; prerr_newline ();
  prerr "The actual term is: "; prerr_s2eff s2fe1; prerr_newline ();  
end // end of [prerr_staerr_s2eff_leq]

fn prerr_staerr_s2exp_linearity
  (loc: loc_t, s2e: s2exp): void = begin
  prerr_loc_error3 (loc);
  prerr ": mismatch of linearity:\n";
  prerr "A nonlinear term is needed: "; pprerr_s2exp s2e; prerr_newline ();
end // end of [prerr_staerr_s2exp_linearity]

fn prerr_the_staerrlst () = let
//
fun loop (
  xs: staerrlst_vt
) : void = case+ xs of
  | ~list_vt_cons (x, xs) => let
      val () = (case+ x of
      | STAERR_funclo_equal (loc, fc1, fc2) => prerr_staerr_funclo_equal (loc, fc1, fc2)
      | STAERR_s2exp_equal (loc, s2e1, s2e2) => prerr_staerr_s2exp_equal (loc, s2e1, s2e2)
      | STAERR_s2exp_tyleq (loc, s2e1, s2e2) => prerr_staerr_s2exp_tyleq (loc, s2e1, s2e2)
      | STAERR_s2eff_leq (loc, s2fe1, s2fe2) => prerr_staerr_s2eff_leq (loc, s2fe1, s2fe2)
      | STAERR_s2exp_linearity (loc, s2e) => prerr_staerr_s2exp_linearity (loc, s2e)
      ) : void // end of [case] // end of [val]
    in
      loop (xs)
    end // end of [list_vt_cons]
  | ~list_vt_nil () => ()
// end of [loop]
in
//
loop (the_staerrlst_get ())
//
end // end of [prerr_the_staerrlst]

(* ****** ****** *)

implement
label_equal_solve_err
  (loc, l1, l2, err) =
  if l1 = l2 then () else (err := err + 1)
// end of [label_equal_solve_err]

implement
stamp_equal_solve_err
  (loc, s1, s2, err) =
  if s1 = s2 then () else (err := err + 1)
// end of [stamp_equal_solve_err]

(* ****** ****** *)

implement
funclo_equal_solve
  (loc0, fc1, fc2) =
  if fc1 = fc2 then () else let
    val () = prerr_staerr_funclo_equal (loc0, fc1, fc2)
  in
    $Err.abort {void} ()
  end // end of [if]
// end of [funclo_equal_solve]

implement
funclo_equal_solve_err
  (loc0, fc1, fc2, err) =
  if fc1 = fc2 then () else let
    val () = err := err + 1
    val () = the_staerrlst_add (STAERR_funclo_equal (loc0, fc1, fc2))
  in
    // nothing
  end // end of [if]
// end of [funclo_equal_solve_err]

(* ****** ****** *)

implement
clokind_equal_solve_err
  (loc, knd1, knd2, err) =
  if knd1 = knd2 then () else (err := err + 1)
// end of [clokind_equal_solve_err]

implement
linearity_equal_solve_err
  (loc, lin1, lin2, err) =
  if lin1 = lin2 then () else (err := err + 1)
// end of [linearity_equal_solve_err]

implement
pfarity_equal_solve_err
  (loc, npf1, npf2, err) =
  if npf1 = npf2 then () else (err := err + 1)
// end of [pfarity_equal_solve_err]

(* ****** ****** *)

implement
tyreckind_equal_solve_err
  (loc, knd1, knd2, err) =
  if knd1 = knd2 then () else (err := err + 1)
// end of [tyreckind_equal_solve_err]

implement
refval_equal_solve_err
  (loc0, refval1, refval2, err) =
  if refval1 = refval2 then () else (err := err + 1)
// end of [refval_equal_solve_err]

(* ****** ****** *)

implement
s2exp_out_void_solve (loc0, s2e) = let
  var err: int = 0
  val s2e = s2exp_whnf s2e
  val () = case+ s2e.s2exp_node of
    | S2Ecst s2c =>
        if s2cstref_equ_cst (Void_t0ype, s2c) then () else err := err + 1
      // end of [S2Ecst]
    | S2Eout _ => ()
    | S2Etyrec (_knd, _npf, ls2es) => loop (loc0, ls2es) where {
        fun loop
          (loc0: loc_t, ls2es: labs2explst): void = case+ ls2es of
          | LABS2EXPLSTcons (_, s2e, ls2es) => let
              val () = s2exp_out_void_solve (loc0, s2e) in loop (loc0, ls2es)
            end // end of [LABS2EXPLSTcons]
          | LABS2EXPLSTnil () => ()
      } // end of [where] // end of [S2Etyrec]
    | _ => (err := err + 1)
  // end of [val]
in
  if err > 0 then begin
    prerr_loc_error3 (loc0);
    prerr ": the type ["; prerr s2e; prerr "] is expected to be empty.";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [s2exp_out_or_void_solve]

implement
s2exp_out_void_solve_at (loc0, s2e_at) = begin
  case+ un_s2exp_at_viewt0ype_addr_view s2e_at of
  | ~Some_vt s2ts2a => s2exp_out_void_solve (loc0, s2ts2a.0)
  | ~None_vt () => begin
      prerr_loc_error3 (loc0);
      prerr ": the type ["; prerr s2e_at; prerr "] is expected to be an @-view.";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [None_vt]
end // end of [s2exp_out_void_solve_at]

(* ****** ****** *)

fn s2exp_nonlin_test_err (
  loc: loc_t, s2e: s2exp, err: &int
) : void =
  if s2exp_is_linear s2e then let
    val () = err := err + 1
    val () = the_staerrlst_add (STAERR_s2exp_linearity (loc, s2e))
  in
    // nothing
  end // end of [if]
// end of [s2exp_nonlin_test_err]

fn s2exp_equal_solve_abscon_err (
  loc0: loc_t, s2e1: s2exp, s2e2: s2exp, err: &int
) : void = let
//
  fun aux_solve ( // nontailrec
    loc0: loc_t
  , s2e1: s2exp, s2e2: s2exp, err: &int
  ) : void = begin
    case+ (s2e1.s2exp_node, s2e2.s2exp_node) of
    | (S2Eapp (s2e11, s2es12), S2Eapp (s2e21, s2es22)) => let
        val () = aux_solve (loc0, s2e11, s2e21, err)
        val () = s2explst_equal_solve_err (loc0, s2es12, s2es22, err)
      in
        // nothing
      end // end of [S2Eapp, S2Eapp]
    | (_, _) => ()
  end // end of [aux_solve]
//
  fun aux_check ( // tailrec
    s2e1: s2exp, s2e2: s2exp
  ) : bool = begin
    case+ (s2e1.s2exp_node, s2e2.s2exp_node) of
    | (S2Ecst s2c1, S2Ecst s2c2) => eq_s2cst_s2cst (s2c1, s2c2)
    | (S2Eapp (s2e1, _), S2Eapp (s2e2, _)) => aux_check (s2e1, s2e2)
    | (_, _ ) => false
  end // end of [aux_check]
//
  val coneq = aux_check (s2e1, s2e2)
//
in
  if coneq then aux_solve (loc0, s2e1, s2e2, err) else (err := err + 1)
end // end of [s2exp_equal_solve_abscon_err]

fn s2exp_equal_solve_appvar_err (
  loc0: loc_t
, s2e1: s2exp, s2e2: s2exp, err: &int
) : void = let
  fun aux
    (loc0: loc_t, s2e1: s2exp, s2e2: s2exp, err: &int)
    : void = begin
    case+ (s2e1.s2exp_node, s2e2.s2exp_node) of
    | (S2Eapp (s2e11, s2es12), S2Eapp (s2e21, s2es22)) => begin
        aux (loc0, s2e11, s2e21, err);
        s2explst_equal_solve_err (loc0, s2es12, s2es22, err)
      end // end of [S2Eapp, S2Eapp]
    | (_, _) => ()
  end // end of [aux]
in
  aux (loc0, s2e1, s2e2, err)
end // end of [s2exp_equal_solve_appvar_err]

(* ****** ****** *)

implement
s2exp_equal_solve (loc0, s2e10, s2e20) = let
  var err: int = 0
  val () = s2exp_equal_solve_err (loc0, s2e10, s2e20, err)
in
  if err > 0 then let
    val () = prerr_the_staerrlst () in $Err.abort {void} ()
  end // end of [if]
end (* end of [s2exp_equal_solve] *)

implement
s2exp_equal_solve_err (loc0, s2e10, s2e20, err) = let
  val err0 = err
  val s2e10 = s2exp_whnf s2e10 and s2e20 = s2exp_whnf s2e20
(*
  val () = begin
    print "s2exp_equal_solve_err: s2e10 = "; print s2e10; print_newline ();
    print "s2exp_equal_solve_err: s2e20 = "; print s2e20; print_newline ();
    print "s2exp_equal_solve_err: err = "; print err; print_newline ();
  end // end of [val]
*)
//
  val () = case+ (s2e10.s2exp_node, s2e20.s2exp_node) of
  | (S2EVar s2V1, _) => begin
      s2exp_equal_solve_Var_err (loc0, s2V1, s2e10, s2e20, err)
    end // end of [S2EVar, _]
  | (_, S2EVar s2V2) => begin
      s2exp_equal_solve_Var_err (loc0, s2V2, s2e20, s2e10, err)
    end // end of [_, S2EVar]
(*
// HX-2010-12-04: inadequate design
  | (S2Enamed (_(*name*), s2e1), _) =>
      s2exp_equal_solve_err (loc0, s2e1, s2e20, err)
    // end of [S2Enamed, _]  
  | (_, S2Enamed (_(*name*), s2e2)) =>
      s2exp_equal_solve_err (loc0, s2e10, s2e2, err)
    // end of [_, S2Enamed]  
*)
  | (S2Ecrypt s2e1, s2en20) => begin case+ s2en20 of
    | S2Ecrypt s2e2 => s2exp_equal_solve_err (loc0, s2e1, s2e2, err)
    | _ => (err := err + 1)
    end // end of [S2Ecrypt, _]
  | (S2Ecst s2c1, s2en20) => begin case+ s2en20 of
    | S2Ecst s2c2 => begin
        if eq_s2cst_s2cst (s2c1, s2c2) then () else (err := err + 1)
      end // end of [S2Ecst]
    | _ => begin
        trans3_env_add_eqeq (loc0, s2e10, s2e20)
      end // end of [_]
    end // end of [S2Ecst, _]
  (* S2Eread is contravariant at its first argument *)
  | (S2Eread (_v1, s2e1), s2en20) => begin
    case+ s2en20 of
    | S2Eread (_v2, s2e2) => begin
        s2exp_equal_solve_err (loc0, _v2, _v1, err);
        s2exp_equal_solve_err (loc0, s2e1, s2e2, err)
      end // end of [S2Eread]
    | _ => (err := err + 1)
    end // end of [S2Eread, _]
  | (S2Esizeof s2e1, s2en20) => begin
    case+ s2en20 of
    | S2Esizeof s2e2 => begin
        s2exp_size_equal_solve_err (loc0, s2e1, s2e2, err)
      end // end of [S2Esizeof]
    | _ => (err := err + 1)
    end // end of [S2Esizeof, _]
  | (S2Etyarr (s2e1_elt, s2ess1_dim), s2en20) => begin
    case+ s2en20 of
    | S2Etyarr (s2e2_elt, s2ess2_dim) => begin
        s2exp_equal_solve_err (loc0, s2e1_elt, s2e2_elt, err);
        s2explstlst_equal_solve_err (loc0, s2ess1_dim, s2ess2_dim, err)
      end // end of [S2Etyarr]
    | _ => (err := err + 1)
    end // end of [S2Etyarr, _]
  | (S2Etyrec (knd1, npf1, ls2es1), s2en20) => begin
    case+ s2en20 of
    | S2Etyrec (knd2, npf2, ls2es2) => begin
        tyreckind_equal_solve_err (loc0, knd1, knd2, err);
        pfarity_equal_solve_err (loc0, npf1, npf2, err);
        labs2explst_equal_solve_err (loc0, ls2es1, ls2es2, err)
      end // end of [S2Etyrec]
    | _ => (err := err + 1)
    end // end of [S2Etyrec, _]
  | (S2Ewth (s2e1, wths2es1), s2en20) => begin
    case+ s2en20 of
    | S2Ewth (s2e2, wths2es2) => begin
        s2exp_equal_solve_err (loc0, s2e1, s2e2, err);
        wths2explst_equal_solve_err (loc0, wths2es1, wths2es2, err)
      end // end of [S2Ewth]
    | _ => (err := err + 1)
    end // end of [S2Ewth, _]
  | (_, _) when
      s2exp_is_abscon s2e10 andalso s2exp_is_abscon s2e20 => begin
      s2exp_equal_solve_abscon_err (loc0, s2e10, s2e20, err)
    end // end of [_, _ when ...]
  | (_, _) when s2exp_is_impredicative s2e10 => begin
      s2exp_tyleq_solve_err (loc0, s2e10, s2e20, err);
      s2exp_tyleq_solve_err (loc0, s2e20, s2e10, err)
    end // end of [_, _ when ...]
  | (_, _) when s2exp_syneq (s2e10, s2e20) => ()
  | (_, _) => trans3_env_add_eqeq (loc0, s2e10, s2e20)
// end of [case]  // end of [val]
  val () = if err > err0 then
    the_staerrlst_add (STAERR_s2exp_equal (loc0, s2e10, s2e20))
  // end of [val]
in
  // nothing
end // end of [s2exp_equal_solve_err]

implement
s2explst_equal_solve_err
  (loc0, s2es10, s2es20, err) = let
  fun aux ( // tail-recursive
      s2es1: s2explst, s2es2: s2explst, err: &int
    ) :<cloref1> void =
    case+ (s2es1, s2es2) of
    | (s2e1 :: s2es1, s2e2 :: s2es2) => begin
        s2exp_equal_solve_err (loc0, s2e1, s2e2, err);
        aux (s2es1, s2es2, err)
      end // end of [::, ::]
    | (nil _, nil _) => ()
    | (cons _, nil _) => (err := err + 1)
    | (nil _, cons _) => (err := err + 1)
  // end of [aux]
in
  aux (s2es10, s2es20, err)
end // end of [s2explst_equal_solve_err]

implement
labs2explst_equal_solve_err
  (loc0, ls2es10, ls2es20, err) = let
  fun aux (
      ls2es1: labs2explst
    , ls2es2: labs2explst
    , err: &int
    ) :<cloref1> void = begin
    case+ (ls2es1, ls2es2) of
    | (LABS2EXPLSTcons (l1, s2e1, ls2es1),
       LABS2EXPLSTcons (l2, s2e2, ls2es2)) => begin
        label_equal_solve_err (loc0, l1, l2, err);
        s2exp_equal_solve_err (loc0, s2e1, s2e2, err);
        aux (ls2es1, ls2es2, err)
      end // end of [LABS2EXPLSTcons, LABS2EXPLSTcons]
    | (LABS2EXPLSTnil _, LABS2EXPLSTnil _) => ()
    | (LABS2EXPLSTcons _, LABS2EXPLSTnil _) => (err := err + 1)
    | (LABS2EXPLSTnil _, LABS2EXPLSTcons _) => (err := err + 1)
  end // end of [aux]
in
  aux (ls2es10, ls2es20, err)
end // end of [labs2explst_equal_solve_err]

implement
wths2explst_equal_solve_err
  (loc0, wths2es10, wths2es20, err) = let
  fun aux (
      wths2es1: wths2explst
    , wths2es2: wths2explst
    , err: &int
    ) :<cloref1> void = begin
    case+ (wths2es1, wths2es2) of
    | (WTHS2EXPLSTcons_some (refval1, s2e1, wths2es1),
       WTHS2EXPLSTcons_some (refval2, s2e2, wths2es2)) => begin
(*
        refval_equal_solve_err (loc0, refval1, refval2, err); // no need
*)
        s2exp_equal_solve_err (loc0, s2e1, s2e2, err);
        aux (wths2es1, wths2es2, err)
      end // end of [WTHS2EXPLSTcons_some, WTHS2EXPLSTcons_some]
    | (WTHS2EXPLSTcons_none wths2es1,
       WTHS2EXPLSTcons_none wths2es2) => begin
        aux (wths2es1, wths2es2, err)
      end // end of [WTHS2EXPLSTcons_none, WTHS2EXPLSTcons_none]
    | (WTHS2EXPLSTnil _, WTHS2EXPLSTnil _) => ()
    | (_, _) => (err := err + 1)
  end // end of [aux]
in
  aux (wths2es10, wths2es20, err)
end // end of [wths2explst_equal_solve_err]

implement
s2explstlst_equal_solve_err
  (loc0, s2ess10, s2ess20, err) = let
  fun aux (
      s2ess1: s2explstlst, s2ess2: s2explstlst, err: &int
    ) :<cloref1> void = begin case+ (s2ess1, s2ess2) of
    | (cons (s2es1, s2ess1), cons (s2es2, s2ess2)) => let
        val () = s2explst_equal_solve_err (loc0, s2es1, s2es2, err)
      in
        aux (s2ess1, s2ess2, err)
      end // end of [cons, cons]
    | (nil (), nil ()) => ()
    | (_, _) => (err := err + 1)
  end // end of [aux]
in
  aux (s2ess10, s2ess20, err)
end // end of [s2explstlst_equal_solve_err]

(* ****** ****** *)

implement
s2exp_size_equal_solve_err
  (loc0, s2e10, s2e20, err) = let
(*
  val () = begin
    print "s2exp_size_equal_solve_err: s2e10 = "; print s2e10; print_newline ();
    print "s2exp_size_equal_solve_err: s2e20 = "; print s2e20; print_newline ();
    print "s2exp_size_equal_err: err = "; print err; print_newline ();
  end // end of [val]
*)
  val s2ze10 = s2zexp_make_s2exp s2e10
  and s2ze20 = s2zexp_make_s2exp s2e20
  val test = s2zexp_syneq (s2ze10, s2ze20)
in
  if test then ((*nothing*)) else (err := err + 1)
end (* end of [s2exp_size_equal_solve_err] *)

(* ****** ****** *)

implement
s2exp_tyleq_solve_err (loc0, s2e10, s2e20, err) = let
  val err0 = err
  val s2e10 = s2exp_whnf s2e10 and s2e20 = s2exp_whnf s2e20
//
(*
  val () = begin
    print "s2exp_tyleq_solve_err: s2e10 = "; print s2e10; print_newline ();
    print "s2exp_tyleq_solve_err: s2e20 = "; print s2e20; print_newline ();
    print "s2exp_tyleq_solve_err: err = "; print err; print_newline ();
  end // end of [val]
*)
//
  val () = case+ (s2e10.s2exp_node, s2e20.s2exp_node) of
  | (S2EVar s2V1, S2EVar s2V2) when eq_s2Var_s2Var (s2V1, s2V2) => ()
  | (S2EVar s2V1, _) => begin
      s2exp_tyleq_solve_Var_l_err (loc0, s2V1, s2e10, s2e20, err)
    end // end of [S2EVar, _]
  | (_, S2EVar s2V2) => begin
      s2exp_tyleq_solve_Var_r_err (loc0, s2e10, s2V2, s2e20, err)
    end // end of [_, S2EVar]
(*
// HX-2010-12-04: inadequate design
  | (S2Enamed (_(*name*), s2e1), _) =>
      s2exp_tyleq_solve_err (loc0, s2e1, s2e20, err)
  | (_, S2Enamed (_(*name*), s2e2)) =>
      s2exp_tyleq_solve_err (loc0, s2e10, s2e2, err)
*)
  | (s2en10, S2Etop (knd2, s2e2)) => begin case+ knd2 of
    | 0 (* topization *) => begin
        if s2exp_is_nonlin s2e10 then begin
          s2exp_size_equal_solve_err (loc0, s2e10, s2e20, err)
        end else (err := err + 1) // end of [if]
      end // end of [knd2 = 0]
    | _ (* typization *) => begin case+ s2en10 of
      | S2Etop (knd1, s2e1) =>
          if knd1 = 1 then begin
            s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
          end else (err := err + 1) // end of [if]
      | _ => (err := err + 1)
      end (* end of [knd2 = 1] *)
    end // end of [_, S2Etop]
(* ****** ******
//
// HX-2010-02-04: this is not common; should it be supported?
//
  | (S2Euni (nil (), _, _), _) => let
      val s2e1 = s2exp_uni_instantiate_all (loc0, s2e10)
      val () = s2exp_tyleq_solve_err (loc0, s2e1, s2e20, err)
    in
      // nothing
    end // end of [S2Euni (nil, _, _), _]
  | (_, S2Eexi (nil (), _, _)) => let
      val s2e2 = s2exp_exi_instantiate_all (loc0, s2e20)
      val () = s2exp_tyleq_solve_err (loc0, s2e10, s2e2, err)
    in
      // nothing
    end // end of [_, S2Eexi (nil, _, _)]
****** ****** *)
  | (S2Euni _, _) => let
      val () = trans3_env_push_sta ()
      // this order is mandatary!
      val s2e2 = s2exp_absuni_and_add (loc0, s2e20)
      val s2e1 = s2exp_uni_instantiate_all (loc0, s2e10)
      val () = s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
    in
      trans3_env_pop_sta_and_add_none (loc0)
    end // end of [S2Euni, _]
  | (_, S2Eexi _) => let
      val () = trans3_env_push_sta ()
      // this order is mandatary!
      val s2e1 = s2exp_opnexi_and_add (loc0, s2e10)
      val s2e2 = s2exp_exi_instantiate_all (loc0, s2e20)
      val () = s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
    in
      trans3_env_pop_sta_and_add_none (loc0)
    end // end of [_, S2Eexi]
  | (_, S2Euni _) => let
      val () = trans3_env_push_sta ()
      val s2e2 = s2exp_absuni_and_add (loc0, s2e20)
      val () = s2exp_tyleq_solve_err (loc0, s2e10, s2e2, err)
    in
      trans3_env_pop_sta_and_add_none (loc0)
    end // end of [_, S2Euni]
  | (S2Eexi _, _) => let
      val () = trans3_env_push_sta ()
      val s2e1 = s2exp_opnexi_and_add (loc0, s2e10)
      val () = s2exp_tyleq_solve_err (loc0, s2e1, s2e20, err)
    in
      trans3_env_pop_sta_and_add_none (loc0)
    end // end of [S2Eexi, _]
  | (S2Eapp (s2e1_fun, s2es1_arg), s2en20) => begin
    case+ s2en20 of
    | S2Eapp (s2e2_fun, s2es2_arg) => begin
      case+ (
        s2e1_fun.s2exp_node, s2e2_fun.s2exp_node
      ) of
      | (S2Ecst s2c1_fun, S2Ecst s2c2_fun) => begin
          if s2cst_is_eqsup (s2c1_fun, s2c2_fun) then begin
            case+ s2cst_get_argvar s2c1_fun of
            | Some argvarlst => begin
                s2explst_tyleq_solve_argvarlst_err
                  (loc0, s2es1_arg, s2es2_arg, argvarlst, err)
              end // end of [Some]
            | None () => begin
                s2explst_equal_solve_err (loc0, s2es1_arg, s2es2_arg, err)
              end // end of [None]
          end else begin
            err := err + 1
          end // end of [if]
        end (* [(S2Ecst, S2Ecst)] *)
      | (_, _) => begin (* sound but incomplete! *)
          s2exp_equal_solve_err (loc0, s2e1_fun, s2e2_fun, err);
          s2explst_equal_solve_err (loc0, s2es1_arg, s2es2_arg, err)
        end (* end of [_, _] *)
      end // end of [S2Eapp]
    | S2Ecst s2c2 => begin case+ s2e1_fun.s2exp_node of
      | S2Ecst s2c1_fun => begin
          if s2cst_is_eqsup (s2c1_fun, s2c2) then () else (err := err + 1)
        end // end of [S2Ecst]
      | _ => (err := err + 1)
      end // end of S2Ecst]
    | _ => (err := err + 1)
    end // end of [S2Eapp, _]
  | (S2Eclo (knd1, s2e1), s2en20) => begin case+ s2en20 of
    | S2Eclo (knd2, s2e2) => let
        val () = clokind_equal_solve_err (loc0, knd1, knd2, err)
      in
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
      end // end of [S2Eclo]
    | _ => (err := err + 1)
    end // end of [S2Eclo, _]
  | (S2Ecrypt s2e1, s2en20) => begin case+ s2en20 of
    | S2Ecrypt s2e2 => s2exp_equal_solve_err (loc0, s2e1, s2e2, err)
    | _ => (err := err + 1)
    end // end of [S2Ecrypt, _]
  | (S2Ecst s2c1, s2en20) => begin case+ s2en20 of
    | S2Ecst s2c2 => begin
        if s2cst_is_eqsup (s2c1, s2c2) then () else (err := err + 1)
      end
    | _ => (err := err + 1)
    end // end of [S2Ecst, _]
  | (S2Edatconptr (d2c1, s2es1), s2en20) => begin case+ s2en20 of
    | S2Edatconptr (d2c2, s2es2) => begin
        if d2c1 = d2c2 then begin
          s2explst_equal_solve_err (loc0, s2es1, s2es2, err)
        end else begin
          err := err + 1
        end
      end // end of [S2Edatconptr]
    | _ => (err := err + 1)
    end // end of [S2Edatconptr, _]
  | (S2Efun (fc1, lin1, s2fe1, npf1, s2es1_arg, s2e1_res), s2en20) => begin
    case+ s2en20 of
    | S2Efun (
        fc2, lin2, s2fe2, npf2, s2es2_arg, s2e2_res
      ) => () where {
        val () = funclo_equal_solve_err (loc0, fc1, fc2, err)
        val () = linearity_equal_solve_err (loc0, lin1, lin2, err)
        val () = pfarity_equal_solve_err (loc0, npf1, npf2, err)
        val () = s2eff_leq_solve_err (loc0, s2fe1, s2fe2, err)
        val () = s2explst_tyleq_solve_err (loc0, s2es2_arg, s2es1_arg, err)
        val () = s2exp_tyleq_solve_err (loc0, s2e1_res, s2e2_res, err)
      } // end of [S2Efun]
    | S2Eclo (knd2, s2e2_fun) => let
        val () = case+ fc1 of
          | $Syn.FUNCLOclo knd1 => begin
              clokind_equal_solve_err (loc0, knd1, knd2, err)
            end // end of [FUNCLOclo]
          | _ => (err := err + 1)
        val s2t1: s2rt = if lin1 > 0 then s2rt_viewtype else s2rt_type
        val s2e1_fun = s2exp_fun_srt
          (s2t1, $Syn.FUNCLOfun (), lin1, s2fe1, npf1, s2es1_arg, s2e1_res)
        // end of [val]
      in
        s2exp_tyleq_solve_err (loc0, s2e1_fun, s2e2_fun, err)
      end // end of [S2Eclo]
    | _ => (err := err + 1)
    end // end of [S2Efun, _]
  (* S2Eread is contravariant at its first argument *)
  | (S2Eread (_v1, s2e1), s2en20) => begin case+ s2en20 of
    | S2Eread (_v2, s2e2) => begin
        s2exp_tyleq_solve_err (loc0, _v2, _v1, err);
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
      end // end of [S2Eread]
    | _ => (err := err + 1)
    end // end of [S2Eread, _]
  | (S2Erefarg (refval1, s2e1), s2en20) => begin case+ s2en20 of
    | S2Erefarg (refval2, s2e2) => begin
        refval_equal_solve_err (loc0, refval1, refval2, err);
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
      end // end of [S2Erefarg]
    | _ => (err := err + 1)
    end // end of [S2Erefarg, _]
  | (S2Etyarr (s2e1_elt, s2ess1_dim), s2en20) => begin case+ s2en20 of
    | S2Etyarr (s2e2_elt, s2ess2_dim) => () where {
        val () = s2exp_tyleq_solve_err (loc0, s2e1_elt, s2e2_elt, err)
        val () = s2explstlst_equal_solve_err (loc0, s2ess1_dim, s2ess2_dim, err)
      } // end of [S2Etyarr]
    | _ => (err := err + 1)
    end // end of [S2Etyarr, _]
  | (S2Etylst s2es1, s2en20) => begin case+ s2en20 of
    | S2Etylst s2es2 => begin
        s2explst_tyleq_solve_err (loc0, s2es1, s2es2, err)
      end // end of [S2Etylst]
    | _ => (err := err + 1)
    end // end of [S2Etylst, _]
  | (S2Etyrec (knd1, npf1, ls2es1), s2en20) => begin
    case+ s2en20 of
    | S2Etyrec (knd2, npf2, ls2es2) => () where {
(*
        val () = begin
          print "ls2es1 = "; print ls2es1; print_newline ();
          print "ls2es2 = "; print ls2es2; print_newline ();
        end // end of [val]
*)
        val () = tyreckind_equal_solve_err (loc0, knd1, knd2, err)
        val () = pfarity_equal_solve_err (loc0, npf1, npf2, err)
        val () = labs2explst_tyleq_solve_err (loc0, ls2es1, ls2es2, err)
      } // end of [S2Etyrec]
    | S2Evararg s2e2 => let
        val s2e1 = s2exp_tylst (s2es) where {
          fun aux (
              loc0: loc_t, ls2es: labs2explst, err: &int
            ) : s2explst = case+ ls2es of
            | LABS2EXPLSTcons (_, s2e, ls2es) => let
                val () = s2exp_nonlin_test_err (loc0, s2e, err)
                val s2es = aux (loc0, ls2es, err)
              in
                list_cons (s2e, s2es)
              end // end of [LABS2EXPLSTcons]
            | LABS2EXPLSTnil () => list_nil ()
          // end of [aux]
          val s2es = aux (loc0, ls2es1, err)
        } // end of [where]
        val () = tyreckind_equal_solve_err (loc0, knd1, TYRECKINDflt0, err)
        val () = pfarity_equal_solve_err (loc0, npf1, 0, err)
      in
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
      end // end of [S2Evararg]
    | _ => (err := err + 1)
    end // end of [S2Etyrec, _]
  | (S2Eunion (s1, s2i1, ls2es1), s2en20) => begin case+ s2en20 of
    | S2Eunion (s2, s2i2, ls2es2) => let
        val () = stamp_equal_solve_err (loc0, s1, s2, err)
        val () = s2exp_equal_solve_err (loc0, s2i1, s2i2, err) // indexes must equal
      in
        labs2explst_tyleq_solve_err (loc0, ls2es1, ls2es2, err)
      end // end of [S2Eunion]
    | _ => (err := err + 1)
    end // end of [S2Eunion, _]
  | (S2Evar s2v1, s2en20) => begin case+ s2en20 of
    | S2Evar s2v2 =>
        if s2v1 = s2v2 then () else (err := err + 1)
      // end of [S2Evar]
    | _ => (err := err + 1)
    end // end of [S2Evar, _]
  | (S2Evararg s2e1, s2en20) => begin
    case+ s2en20 of
    | S2Evararg s2e2 => s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
    | _ => (err := err + 1)
    end // end of [S2Evararg, _]
  | (S2Ewth (s2e1, wths2es1), s2en20) => begin
    case+ s2en20 of
    | S2Ewth (s2e2, wths2es2) => () where {
        val () = s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
        val () = wths2explst_tyleq_solve_err (loc0, wths2es1, wths2es2, err)
      } // end of [S2Ewth]
    | _ => (err := err + 1)
    end // end of [S2Ewth, _]
  | (_, _) when s2exp_syneq (s2e10, s2e20) => ()
  | (_, _) => begin
      err := err + 1
    end // end of [_, _]
// end of [case]  // end of [val]
  val () = if err > err0 then
    the_staerrlst_add (STAERR_s2exp_tyleq (loc0, s2e10, s2e20))
  // end of [val]
in
  // nothing
end // end of [s2exp_tyleq_solve_err]

implement
s2explst_tyleq_solve_err
  (loc0, s2es10, s2es20, err) = let
  fun aux (s2es1: s2explst, s2es2: s2explst, err: &int)
    :<cloptr1> void = begin case+ (s2es1, s2es2) of
    | (s2e1 :: s2es1, s2e2 :: s2es2) => begin
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err);
        aux (s2es1, s2es2, err)
      end // end of [::, ::]
    | (nil _, nil _) => ()
    | (cons _, nil _) => (err := err + 1)
    | (nil _, cons _) => (err := err + 1)
  end // end of [aux]
in
  aux (s2es10, s2es20, err)
end // end of [s2explst_tyleq_solve_err]

implement
s2explst_tyleq_solve_argvarlst_err
  (loc0, s2es1, s2es2, argvarlst, err) = begin
  case+ argvarlst of
  | cons (argvar, argvarlst) => begin case+ (s2es1, s2es2) of
    | (s2e1 :: s2es1, s2e2 :: s2es2) => let
        val pol = argvar.2
        val () = begin
          if pol > 0 then begin
            s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err)
          end else if pol < 0 then begin
            s2exp_tyleq_solve_err (loc0, s2e2, s2e1, err)
          end else begin
            s2exp_equal_solve_err (loc0, s2e1, s2e2, err)
          end // end of [if]
        end // end of [val]
      in
        s2explst_tyleq_solve_argvarlst_err (loc0, s2es1, s2es2, argvarlst, err)
      end // end of [::, ::]
    | (_, _) => begin
        prerr_loc_interror loc0;
        prerr ": s2explst_tyleq_solve_argvarlst_err"; prerr_newline ();
        $Err.abort {void} ()        
      end // end of [_, _]
    end // end of [case]
  | nil () => ()
end // end of [s2explst_tyleq_solve_argvarlst_err]

implement
labs2explst_tyleq_solve_err
  (loc0, ls2es10, ls2es20, err) = let
  fun aux (ls2es1: labs2explst, ls2es2: labs2explst, err: &int)
    :<cloptr1> void = begin case+ (ls2es1, ls2es2) of
    | (LABS2EXPLSTcons (l1, s2e1, ls2es1),
       LABS2EXPLSTcons (l2, s2e2, ls2es2)) => begin
        label_equal_solve_err (loc0, l1, l2, err);
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err);
        aux (ls2es1, ls2es2, err)
      end
    | (LABS2EXPLSTnil _, LABS2EXPLSTnil _) => ()
    | (LABS2EXPLSTcons _, LABS2EXPLSTnil _) => (err := err + 1)
    | (LABS2EXPLSTnil _, LABS2EXPLSTcons _) => (err := err + 1)
  end // end of [aux]
in
  aux (ls2es10, ls2es20, err)
end // end of [labs2explst_tyleq_solve_err]

implement
wths2explst_tyleq_solve_err
  (loc0, wths2es10, wths2es20, err) = let
  fun aux (wths2es1: wths2explst, wths2es2: wths2explst, err: &int)
    :<cloptr1> void = begin case+ (wths2es1, wths2es2) of
    | (WTHS2EXPLSTcons_some (refval1, s2e1, wths2es1),
       WTHS2EXPLSTcons_some (refval2, s2e2, wths2es2)) => begin
(*
        refval_equal_solve_err (loc0, refval1, refval2, err); // no need
*)
        s2exp_tyleq_solve_err (loc0, s2e1, s2e2, err);
        aux (wths2es1, wths2es2, err)
      end // end of [WTHS2EXPLSTcons_some, WTHS2EXPLSTcons_some]
    | (WTHS2EXPLSTcons_none wths2es1,
       WTHS2EXPLSTcons_none wths2es2) => begin
        aux (wths2es1, wths2es2, err)
      end // end of [WTHS2EXPLSTcons_none, WTHS2EXPLSTcons_none]
    | (WTHS2EXPLSTnil _, WTHS2EXPLSTnil _) => ()
    | (_, _) => (err := err + 1)
  end // end of [aux]
in
  aux (wths2es10, wths2es20, err)
end // end of [wths2explst_tyleq_solve_err]

//

implement
s2eff_leq_solve (loc0, s2fe1, s2fe2) = let
  var err: int = 0
  val () = s2eff_leq_solve_err (loc0, s2fe1, s2fe2, err)
in
  if err > 0 then begin
    prerr_loc_error3 (loc0);
    prerr ": the computed effects [";
    prerr s2fe1;
    prerr "] does not match the expected effects [";
    prerr s2fe2;
    prerr "].";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [s2eff_leq_solve]

implement
s2eff_leq_solve_err (loc0, s2fe1, s2fe2, err) = let
(*
  val () = begin
    print "s2eff_leq_solve_err: s2fe1 = "; print s2fe1; print_newline ();
    print "s2eff_leq_solve_err: s2fe2 = "; print s2fe2; print_newline ();
  end // end of [val]
*)
  val ans = (case+ s2fe2 of
    | S2EFFset (effs, s2es2) => begin case+ s2es2 of
      | cons (s2e2, nil ()) => let
          val s2e2_whnf = s2exp_whnf s2e2
        in
          case+ s2e2_whnf.s2exp_node of
          | S2EVar s2V2 => let
              val s2e1 = s2exp_eff s2fe1
            in
              s2exp_equal_solve_Var_err (loc0, s2V2, s2e2, s2e1, err); 0
            end // end of [S2EVar]
          | _ => 1
        end
      | _ => 1
      end // end of [S2EFFset]
    | _ => 1
  ) : int // end of [val]
in
  if ans > 0 then
    if s2eff_contain_s2eff (s2fe2, s2fe1) then () else let
      val () = the_staerrlst_add (STAERR_s2eff_leq (loc0, s2fe1, s2fe2))
    in
      err := err + 1
    end // end of [if]
  // end of [if]
end // end of [s2eff_leq_solve_err]

(* ****** ****** *)

fun s2exp_tyleq_solve_lbs_err (
  loc0: loc_t, lbs: s2Varboundlst, s2e: s2exp, err: &int
) : void =
  case+ lbs of
  | cons (lb, lbs) => let
      val lb_s2e = s2Varbound_get_val (lb)
      val () = s2exp_tyleq_solve_err (loc0, lb_s2e, s2e, err)
    in
      s2exp_tyleq_solve_lbs_err (loc0, lbs, s2e, err)
    end // end of [cons]
  | nil () => ()
// end of [s2exp_tyleq_solve_lbs_err]

fun s2exp_tyleq_solve_ubs_err (
  loc0: loc_t, s2e: s2exp, ubs: s2Varboundlst, err: &int
) : void =
  case+ ubs of
  | cons (ub, ubs) => let
      val ub_s2e = s2Varbound_get_val (ub)
      val () = s2exp_tyleq_solve_err (loc0, s2e, ub_s2e, err)
    in
      s2exp_tyleq_solve_ubs_err (loc0, s2e, ubs, err)
    end // end of [cons]
  | nil () => ()
// end of [s2exp_tyleq_solve_ubs_err]

(* ****** ****** *)

implement
s2exp_equal_solve_Var_err
  (loc0, s2V1, s2e1, s2e2, err) = let
(*
  val () = begin
    print "s2exp_equal_solve_Var_err: s2V1 = "; print s2V1; print_newline ();
    print "s2exp_equal_solve_Var_err: s2e2 = "; print s2e2; print_newline ();
    print "s2exp_equal_solve_Var_err: err = "; print err; print_newline ();
  end // end of [val]
*)
  var s2cs: s2cstlst = S2CSTLSTnil () and s2vs: s2varlst = list_nil ()
  val ans = s2Var_s2exp_occurs (s2V1, s2e2, s2cs, s2vs)
(*
  val () = begin
    print "s2exp_equal_solve_Var_err: ans = "; print ans; print_newline ();
    print "s2exp_equal_solve_Var_err: s2cs = "; print s2cs; print_newline ();
    print "s2exp_equal_solve_Var_err: s2vs = "; print s2vs; print_newline ();
  end // end of [val]
*)
in
  case+ (ans, s2cs, s2vs) of
  | (0, S2CSTLSTnil (), list_nil ()) => let
      val s2t1 = s2Var_get_srt s2V1 and s2t2 = s2e2.s2exp_srt
(*
      val () = begin
        print "s2exp_equal_solve_Var_err: s2t1 = "; print s2t1; print_newline ();
        print "s2exp_equal_solve_Var_err: s2t2 = "; print s2t2; print_newline ();
      end // end of [val]
*)
    in
      if (s2t2 <= s2t1) then let
        val () = s2Var_set_srt (s2V1, s2t2)
        val () = s2exp_set_srt (s2e1, s2t2)
(*
        val () = begin
          print "s2exp_equal_solve_Var_err: "; print s2V1; print " <- "; print s2e2;
          print_newline ()
        end // end of [val]
*)
        val () = s2Var_set_link (s2V1, Some s2e2)
      in
        s2exp_tyleq_solve_lbs_err (loc0, s2Var_get_lbs s2V1, s2e2, err);
        s2exp_tyleq_solve_ubs_err (loc0, s2e2, s2Var_get_ubs s2V1, err);
      end else begin
        prerr_loc_error3 (loc0);
        $Deb.debug_prerrf (": %s: s2exp_equal_solve_Var_err", @(THISFILENAME));
        prerr ": sort mismatch: the sort of [";
        prerr s2V1;
        prerr "] is [";
        prerr s2t1;
        prerr "], but the sort of its solution is [";
        prerr s2t2;
        prerr "].";
        prerr_newline ();
        err := err + 1
      end // end of [if]
    end // end of [0, S2CSTLSTnil, list_nil]
  | (_, _, _) => let
(*
      val () = begin
        print "s2exp_equal_solve_Var_err: s2e1 = "; print s2e1; print_newline ();
        print "s2exp_equal_solve_Var_err: s2e2 = "; print s2e2; print_newline ();
      end // end of [val]
*)
    in
      trans3_env_add_eqeq (loc0, s2e1, s2e2)
    end // end of (_, _, _)
end // end of [s2exp_equal_solve_Var_err]

implement
s2exp_tyleq_solve_Var_l_err
  (loc0, s2V1, s2e1, s2e2, err) = let
  val lbs = s2Var_get_lbs s2V1 and ubs = s2Var_get_ubs s2V1
  var s2cs: s2cstlst = S2CSTLSTnil () and s2vs: s2varlst = list_nil ()
  val ans = s2Var_s2exp_occurs (s2V1, s2e2, s2cs, s2vs)
in
  case+ (ans, s2cs, s2vs) of
  | (0, S2CSTLSTnil (), list_nil ()) => let
      val () = s2exp_tyleq_solve_lbs_err (loc0, lbs, s2e2, err)
(*
      val s2t1 = s2Var_get_srt (s2V1)
      val s2t2 = s2e2.s2exp_srt
      val () = if s2t2 <= s2t1 then () else begin
        prerr_loc_error3 (loc0);
        $Deb.debug_prerrf (": %s: s2exp_equal_solve_Var_err", @(THISFILENAME));
        prerr ": sort mismatch: the sort of [s2V(";
        prerr s2V1;
        prerr ")] is [";
        prerr s2t1;
        prerr "], but the sort of its upper bound is [";
        prerr s2t2;
        prerr "].";
        prerr_newline ();
        err := err + 1
      end // end of [val]
*)
      val ub = s2Varbound_make (loc0, s2e2)
    in
      s2Var_set_ubs (s2V1, list_cons (ub, ubs))
    end // end of [0, S2CSTLSTnil, list_nil]
  | (_, _, _) => let
(*
      val () = begin
        print "s2exp_tyleq_solve_Var_l_err: s2e1 = "; print s2e1; print_newline ();
        print "s2exp_tyleq_solve_Var_l_err: s2e2 = "; print s2e2; print_newline ();
      end // end of [val]
*)
    in
      trans3_env_add_tyleq (loc0, s2e1, s2e2)
    end // end of [_, _, _]
end // end of [s2exp_tyleq_solve_Var_l_err]

implement
s2exp_tyleq_solve_Var_r_err
  (loc0, s2e1, s2V2, s2e2, err) = let
  val lbs = s2Var_get_lbs s2V2 and ubs = s2Var_get_ubs s2V2
  var s2cs: s2cstlst = S2CSTLSTnil () and s2vs: s2varlst = list_nil ()
  val ans = s2Var_s2exp_occurs (s2V2, s2e1, s2cs, s2vs)
in
  case+ (ans, s2cs, s2vs) of
  | (0, S2CSTLSTnil (), list_nil ()) => let
      val () = s2exp_tyleq_solve_ubs_err (loc0, s2e1, ubs, err)
      val s2t1 = s2e1.s2exp_srt
      val s2t2 = s2Var_get_srt (s2V2)
      val () = if s2t1 <= s2t2 then () else begin
        prerr_loc_error3 (loc0);
        $Deb.debug_prerrf (": %s: s2exp_equal_solve_Var_err", @(THISFILENAME));
        prerr ": sort mismatch: the sort of [s2V(";
        prerr s2V2;
        prerr ")] is [";
        prerr s2t2;
        prerr "], but the sort of its lower bound is [";
        prerr s2t1;
        prerr "].";
        prerr_newline ();
        err := err + 1
      end // end of [val]
    val lb = s2Varbound_make (loc0, s2e1)
    in
      s2Var_set_lbs (s2V2, list_cons (lb, lbs))
    end // end of [...]
  | (_, _, _) => let
(*
      val () = begin
        print "s2exp_tyleq_solve_Var_r_err: s2e1 = "; print s2e1; print_newline ();
        print "s2exp_tyleq_solve_Var_r_err: s2e2 = "; print s2e2; print_newline ();
      end // end of [val]
*)
    in
      trans3_env_add_tyleq (loc0, s2e1, s2e2)
    end // end of [_,_,_]
end // end of [s2exp_tyleq_solve_Var_r_err]

(* ****** ****** *)

implement
s2exp_tyleq_solve
  (loc0, s2e10, s2e20) = let
  var err: int = 0
  val () = s2exp_tyleq_solve_err (loc0, s2e10, s2e20, err)
in
  if err > 0 then let
    val () = prerr_the_staerrlst () in $Err.abort {void} ()
  end // end of [if]
end (* end of [s2exp_tyleq_solve] *)

implement
s2explst_arg_tyleq_solve (loc0, s2es10, s2es20) = let
  fun aux {n:nat}
    (loc0: loc_t, s2es1: list (s2exp, n), s2es2: list (s2exp, n))
    : void = case+ s2es1 of
    | (cons (s2e1, s2es1)) => let
        val+ cons (s2e2, s2es2) = s2es2
        val s2e2 = un_s2exp_refarg_arg s2e2
      in
        s2exp_tyleq_solve (loc0, s2e1, s2e2); aux (loc0, s2es1, s2es2)
      end
    | nil () => ()
  val [sgn:int] sgn = $Lst.list_length_compare (s2es10, s2es20)
  val () = (
    if (sgn <> 0) then begin
      prerr_loc_error3 (loc0);
      $Deb.debug_prerrf (": %s: s2exp_arg_tyleq_solve", @(THISFILENAME));
      if sgn > 0 then prerr ": this function call needs more arguments.";
      if sgn < 0 then prerr ": this function call needs fewer arguments.";
      prerr_newline ();
      $Err.abort {void} ();
      assert (sgn = 0)
    end else begin
      () // [sgn = 0] holds!
    end (* end of [if] *)
  ) : [sgn==0] void
in
  aux (loc0, s2es10, s2es20)
end // end of [s2explst_arg_tyleq_solve]

(* ****** ****** *)

fn s2exp_hypo_equal_solve_con (
  loc0: loc_t, s2e1: s2exp, s2e2: s2exp
) : void = let
(*
  val () = begin
    print "s2exp_hypo_equal_solve_con: s2e1 = "; print s2e1; print_newline ();
    print "s2exp_hypo_equal_solve_con: s2e2 = "; print s2e2; print_newline ();
  end // end of [val]
*)
  fun aux_solve (loc0: loc_t, s2e1: s2exp, s2e2: s2exp): void =
    case+ (s2e1.s2exp_node, s2e2.s2exp_node) of
    | (S2Eapp (s2e1_fun, s2es1_arg), S2Eapp (s2e2_fun, s2es2_arg)) => begin
        aux_solve (loc0, s2e1_fun, s2e2_fun);
        s2explst_hypo_equal_solve (loc0, s2es1_arg, s2es2_arg)
      end
    | (_, _) => ()
  fun aux_check (s2e1: s2exp, s2e2: s2exp): bool =
    case+ (s2e1.s2exp_node, s2e2.s2exp_node) of
    | (S2Ecst s2c1, S2Ecst s2c2) => eq_s2cst_s2cst (s2c1, s2c2)
    | (S2Eapp (s2e1, _), S2Eapp (s2e2, _)) => aux_check (s2e1, s2e2)
    | (_, _) => false
in
  if aux_check (s2e1, s2e2) then begin
    aux_solve (loc0, s2e1, s2e2) // c1 arg1_1 ... arg1_n = c2 arg2_1 ... arg2_n
  end else begin
    trans3_env_hypo_add_prop (loc0, s2exp_bool false)
  end
end // end of [s2exp_hypo_equal_solve_con]

implement
s2exp_hypo_equal_solve
  (loc0, s2e1, s2e2) = let
  val s2e1 = s2exp_whnf s2e1 and s2e2 = s2exp_whnf s2e2
(*
  val () = begin
    print "s2exp_hypo_equal_solve: s2e1 = "; print s2e1; print_newline ();
    print "s2exp_hypo_equal_solve: s2e2 = "; print s2e2; print_newline ();
  end // end of [val]
*)
in
  case+ (s2e1.s2exp_node, s2e2.s2exp_node) of
  | (_, _) when (s2exp_is_abscon s2e1 andalso s2exp_is_abscon s2e2) =>
      s2exp_hypo_equal_solve_con (loc0, s2e1, s2e2)
  | (S2Ecst s2c1, S2Ecst s2c2) when s2c1 = s2c2 => ()
(*
// HX-2010-12-04: inadequate design
  | (S2Enamed (_(*name*), s2e1), _) =>
      s2exp_hypo_equal_solve (loc0, s2e1, s2e2)
    // end of [S2Enamed, _]  
  | (_, S2Enamed (_(*name*), s2e2)) =>
      s2exp_hypo_equal_solve (loc0, s2e1, s2e2)
    // end of [_, S2Enamed]  
*)
(*
  | (S2Evar s2v1, S2Evar s2v2) when s2v1 = s2v2 => ()
*)
  | (S2Evar s2v1, S2Evar s2v2) => let
      val sgn = compare_s2var_s2var (s2v1, s2v2)
    in
      case+ sgn of 
      | _ when sgn > 0 => begin
          trans3_env_hypo_add_bind (loc0, s2v1, s2e2)
        end
      | _ when sgn < 0 => begin
          trans3_env_hypo_add_bind (loc0, s2v2, s2e1)
        end
      | _ (*sgn = 0*) => ()
    end // end of [S2Evar _, S2Evar _]
  | (S2Evar s2v1, _) => let
(*
      val s2t_var = s2var_get_srt s2v1
      val s2t_exp = s2e2.s2exp_srt
      val () = begin
        if not (s2t_var <= s2t_exp) then s2var_set_srt (s2v1, s2t_exp)
      end // end of [val]
*)
    in
      trans3_env_hypo_add_bind (loc0, s2v1, s2e2)
    end // end of [S2Evar _, _]
  | (_, S2Evar s2v2) => let
(*
      val s2t_var = s2var_get_srt s2v2
      val s2t_exp = s2e1.s2exp_srt
      val () = begin
        if not (s2t_var <= s2t_exp) then s2var_set_srt (s2v2, s2t_exp)
      end // end of [val]
*)
    in
      trans3_env_hypo_add_bind (loc0, s2v2, s2e1)
    end // end of [_, S2Evar _]
  | (S2Efun (_(*fc*), _(*lin*), _(*sf2e*), _(*npf*), s2es11, s2e12),
     S2Efun (_(*fc*), _(*lin*), _(*sf2e*), _(*npf*), s2es21, s2e22)) => begin
       s2explst_hypo_equal_solve (loc0, s2es21, s2es11);
       s2exp_hypo_equal_solve (loc0, s2e12, s2e22)
     end // end of [S2Efun _, S2Efun _]
  | (_, _) => trans3_env_hypo_add_eqeq (loc0, s2e1, s2e2)
end // end of [s2exp_hypo_equal_solve]

implement
s2explst_hypo_equal_solve
  (loc0, s2es1, s2es2) = begin
  case+ (s2es1, s2es2) of
  | (cons (s2e1, s2es1), cons (s2e2, s2es2)) => begin
      s2exp_hypo_equal_solve (loc0, s2e1, s2e2);
      s2explst_hypo_equal_solve (loc0, s2es1, s2es2)
    end // end of [cons, cons]
  | (nil (), nil ()) => ()
  | (_, _) => begin
      trans3_env_hypo_add_prop (loc0, s2exp_bool false)
    end // end of [_, _]
end // end of [s2explst_hypo_equal_solve]

(* ****** ****** *)

(* end of [ats_staexp2_solve.dats] *)
