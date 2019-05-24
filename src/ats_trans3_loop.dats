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
// March 2008
//
(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_dynexp3.sats"

(* ****** ****** *)

staload "ats_trans3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

fn i2nvarg_subst
  (sub: stasub_t, arg: i2nvarg): i2nvarg = let
  val d2v = arg.i2nvarg_var
  val os2e = (
    case+ arg.i2nvarg_typ of
    | Some s2e => Some (s2exp_subst (sub, s2e)) | None () => None ()
  ) : s2expopt
in
  i2nvarg_make (d2v, os2e)
end // end of [i2nvarg_subst]

fn i2nvarglst_subst
  (sub: stasub_t, args: i2nvarglst): i2nvarglst = begin
  $Lst.list_map_cloptr (
    args, lam arg =<cloptr1> i2nvarg_subst (sub, arg)
  )
end // end of [i2nvarglst_subst]

fn d2exp_loopinv_tr
  (i2nv: loopi2nv): @(s2explstopt, i2nvresstate) = let
  val loc0 = i2nv.loopi2nv_loc
  val i2nv_arg = i2nv.loopi2nv_arg
  val i2nv_res = i2nv.loopi2nv_res
  val i2nv_res_svs = i2nv_res.i2nvresstate_svs
  val i2nv_res_gua = i2nv_res.i2nvresstate_gua
(*
  // this is already done by [staftscstr_stbefitemlst_update]
  val () = trans3_env_add_svarlst i2nv_res_svs
  val () = trans3_env_hypo_add_proplst (loc0, i2nv_res_gua)
*)
  val i2nv_met = os2es where {
    val os2es = i2nv.loopi2nv_met
    val () = case+ os2es of
      | Some s2es => metric_nat_check (loc0, s2es) | None _ => ()
    // end of [val]
  } // end of [val]
  val res_exit = let
    val i2nv_res_arg = i2nv_res.i2nvresstate_arg
    // [i2nv_res_arg] must be ahead of [i2nv_arg]
    val i2nv_res_arg_new = $Lst.list_append (i2nv_res_arg, i2nv_arg)
  in
    i2nvresstate_make (i2nv_res_svs, i2nv_res_gua, i2nv_res_arg_new)
  end // end of [val]
  val () = let
    fn aux (arg: i2nvarg)
      :<cloptr1> void = let
      val d2v = arg.i2nvarg_var
    in
      case+ arg.i2nvarg_typ of
      | Some s2e => let
          val s2e = s2exp_opnexi_and_add (loc0, s2e)
        in
          d2var_set_typ (d2v, Some s2e)
        end // end of [Some]
      | None () => d2var_set_typ (d2v, None ())
     end // end of [aux]
  in
    $Lst.list_foreach_cloptr (i2nv_arg, aux)
  end // end of [val]
in
  @(i2nv_met, res_exit)
end // end of [d2exp_loopinv_tr]

(* ****** ****** *)

implement d2exp_loop_tr_up
  (loc0, i2nv, od2e_init, d2e_test, od2e_post, d2e_body) = let
  val s2e_void = s2exp_void_t0ype ()
//
  val od3e_init = (case+ od2e_init of
    | Some d2e => begin
        let val d3e = d2exp_tr_dn (d2e, s2e_void) in Some d3e end
      end // end of [Some]
    | None () => None ()
  ) : d3expopt
//  
  val i2nv = loopi2nv_update (i2nv)
  val i2nv_met = i2nv.loopi2nv_met
  val () = begin case+ i2nv_met of // ntm effect or not
    | None _ => the_effect_env_check_ntm (loc0) | Some _ => ()
  end // end of [val]
  val res_init = i2nvresstate_make_met
    (i2nv.loopi2nv_svs, i2nv.loopi2nv_gua, i2nv.loopi2nv_arg, i2nv_met)
  val sbis = the_d2varset_env_stbefitemlst_save ()
//
  val () = trans3_env_push_sta ()
  val d3e_test = d2exp_tr_up d2e_test
  val () = d3exp_open_and_add d3e_test
  val s2e_test = d3e_test.d3exp_typ
  val () = assert_bool_tr_dn (loc0, true, s2e_test)
  val (pf_lamloop | ()) = the_lamloop_env_push_loop0 ()
  val d3e_body = d2exp_tr_dn (d2e_body, s2e_void)
  val od3e_post = (case+ od2e_post of
    | Some d2e => begin
        let val d3e = d2exp_tr_dn (d2e, s2e_void) in Some d3e end
      end // end of [Some]
    | None () => None ()
  ) : d3expopt
  val () = the_lamloop_env_pop (pf_lamloop | (*none*))
  val () = trans3_env_pop_sta_and_free ()
//
  val () = stbefitemlst_restore_typ (sbis) // keep [lin]
  val sac0_init = staftscstr_initize (res_init, sbis)
  val () = trans3_env_push_sta ()
  val () = staftscstr_stbefitemlst_merge (loc0, sac0_init, sbis)
  val knd = C3STRKINDloop 0(*enter*)
  val () = trans3_env_pop_sta_and_add (loc0, knd)
  val () = // checking that the loop invariant holds
  // when the loop is entered for the first time
    staftscstr_stbefitemlst_check (loc0, sac0_init, sbis)
//
  val () = trans3_env_push_sta () // loop checking begs
  val () =
    // updating the types of the modified variables
    // according to the types given in the invariant
    staftscstr_stbefitemlst_update (loc0, sac0_init, sbis)
  (* end of [val] *)
//
  val sac_init = staftscstr_initize (res_init, sbis)
  val () = staftscstr_stbefitemlst_merge_skipmetck (loc0, sac_init, sbis)
  val (i2nv_met, res_exit) = d2exp_loopinv_tr (i2nv)
  val () = staftscstr_met_set (sac_init, i2nv_met)
  val sac_exit = staftscstr_initize (res_exit, sbis)
//
  val d3e_test = d2exp_tr_up d2e_test
  val () = d3exp_open_and_add d3e_test
  val s2e_test = d3e_test.d3exp_typ
  val () = let (* loop exit *)
    val () = trans3_env_push_sta ()
    val () = assert_bool_tr_dn (loc0, false, s2e_test)
    val () = staftscstr_stbefitemlst_merge (loc0, sac_exit, sbis)
    val knd = C3STRKINDloop 1(*exit*)
    val () = trans3_env_pop_sta_and_add (loc0, knd)
  in
    // empty
  end // end of [val]
//
  val d3e_body = let (* loop body *)
    val () = trans3_env_push_sta ()
    val () = assert_bool_tr_dn (loc0, true, s2e_test)
    val (pf_lamloop | ()) = begin
      the_lamloop_env_push_loop1 (sbis, sac_init, sac_exit, od2e_post)
    end // end of [val]
    val d3e_body = d2exp_tr_dn (d2e_body, s2e_void)
    val () = begin case+ od2e_post of
      | Some d2e => begin
          let val _(*d3e*) = d2exp_tr_dn (d2e, s2e_void) in () end
        end // end of [Some]
      | None () => ()
    end // end of [val]
    val () = the_lamloop_env_pop (pf_lamloop | (*none*))
    val () = if not (d2exp_is_raised d2e_body) then
      staftscstr_stbefitemlst_merge (loc0, sac_init, sbis)
    // end of [val]
    val knd = C3STRKINDloop 2(*repeat*)
    val () = trans3_env_pop_sta_and_add (loc0, knd)
  in
    d3e_body
  end // end of [val]
//
  val () = staftscstr_stbefitemlst_check (loc0, sac_init, sbis)
  val () = staftscstr_stbefitemlst_check (loc0, sac_exit, sbis)
  val () = trans3_env_pop_sta_and_add_none (loc0) // loop checking ends
//
  val () = staftscstr_stbefitemlst_update (loc0, sac_exit, sbis)
in
  d3exp_loop (loc0, od3e_init, d3e_test, od3e_post, d3e_body)
end // end of [d2exp_loop_tr_up]

(* ****** ****** *)

// 0/1: break/continue
implement
d2exp_loopexn_tr_up
  (loc0, i) = let
//
val lmlp =
  the_lamloop_env_top ()
val () = (case+ lmlp of
  | LMLPloop0 () => () // skip it
  | LMLPloop1 (
      sbis, sac_init, sac_exit, od2e_post
    ) => let
      val () =
        if i > 0 then (
        case+ od2e_post of
        | Some d2e => begin
            let val _ = d2exp_tr_dn (d2e, s2exp_void_t0ype ()) in () end
          end // end of [Some]
        | None () => ()
      ) // end of [if] // end of [val]
    in
      if i > 0 then begin // continue
        staftscstr_stbefitemlst_merge (loc0, sac_init, sbis)
      end else begin // break
        staftscstr_stbefitemlst_merge (loc0, sac_exit, sbis)
      end // end of [if]
    end // end of [LMLPloop1]
  | _ => begin
      $Loc.prerr_location loc0;
      prerr ": INTERNAL ERROR (ats_trans3_loop)";
      prerr ": d2exp_loopexn_tr_up"; prerr_newline ();
      $Err.abort {void} ()
    end // end of [_]
) : void // end of [val]
//
in
  d3exp_loopexn (loc0, i)
end // end of [d2exp_loopexn_tr_up]

(* ****** ****** *)

(* end of [ats_trans3_loop.dats] *)
