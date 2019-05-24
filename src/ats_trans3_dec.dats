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
// Time: December 2007

(* ****** ****** *)

(* Mainly for handling dynamic declarations during type-checking *)

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_stadyncst2.sats"
staload "ats_patcst2.sats"
staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

#define THISFILENAME "ats_trans3_dec.dats"

(* ****** ****** *)

fn prerr_loc_error3 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(3)")
// end of [prerr_loc_error3]

fn prerr_interror
 () = prerr "INTERNAL ERROR (ats_trans3_dec)"
// end of [prerr_interror]

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_trans3_dec)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

fn caskind_of_valkind
  (valknd: $Syn.valkind): int = begin case+ valknd of
  | $Syn.VALKINDval () => 0
  | $Syn.VALKINDvalminus () => ~1
  | $Syn.VALKINDvalplus () => 1
  | $Syn.VALKINDprval () => 1
end // end of [caskind_of_valkind]

(* ****** ****** *)

fn v2aldec_tr
  (valknd: $Syn.valkind, d2c: v2aldec): v3aldec = let
  val loc0 = d2c.v2aldec_loc
  val p2t = d2c.v2aldec_pat
(*
  val () = begin
    print "v2aldec_tr: p2t = "; print p2t; print_newline ()
  end
*)
  val [b:bool] isprf = (
    case+ valknd of $Syn.VALKINDprval () => true | _ => false
  ) : Bool
  val (pfopt | ()) = (
    if isprf then let
      val (pf | ()) = the_effect_env_push_eff ($Eff.effectlst_all)
    in
      (Some_v pf | ())
    end else begin
      (None_v () | ())
    end // end of [if]
  ) : (option_v (effect_env_token, b) | void)
  val d2e_def = d2c.v2aldec_def
  val d3e_def = (case+ d2c.v2aldec_ann of
    | Some s2e_ann => d2exp_tr_dn (d2e_def, s2e_ann)
    | None () => d2exp_tr_up d2e_def
  ) : d3exp
  val () =
    if isprf then let
      prval Some_v pf = pfopt
    in
      the_effect_env_pop (pf | (*none*))
    end else let
      prval None_v () = pfopt in ()
    end // end of [if]
  val s2e_def = d3e_def.d3exp_typ

  // checking for pattern match exhaustiveness
  val p2ts = '[p2t]
  val p2tcss = p2atcstlst_complement (p2atcstlst_of_p2atlst p2ts)
  val cmplt = (
    case+ p2tcss of cons _ => 0(*incomplete*) | nil _ => 1
  ) : int
  val () = if cmplt = 0 then let
    val casknd = caskind_of_valkind valknd
  in
    trans3_env_add_p2atcstlstlst_false (loc0, casknd, p2tcss, '[s2e_def])
  end // end of [val]

  val p3t = p2at_tr_dn (p2t, s2e_def)
(*
  val () = begin
    print "v2aldec_tr: s2e_def = "; print s2e_def; print_newline ();
    print "v2aldec_tr: p3t = "; print p3t; print_newline ();
  end

  val () = let
    val () = print "v2aldec_tr: typ_lft = ";
  in
    case+ p3t.p3at_typ_lft of
    | Some s2e => begin
        print "Some ("; print s2e; print ")"; print_newline ()
      end
    | None () => begin
        print "None ()"; print_newline ()
      end
  end // end of [val]
*)
  val () = d3exp_lval_set_typ_pat (d3e_def, p3t)
  val () = the_d2varset_env_add_p2at (p2t)
(*
  val () = let
    val s3is = trans3_env_s3itemlst_copy ()
    val () = begin
      print "v2aldec_tr: s3is = "; print_s3itemlst_vt s3is; print_newline ()
    end
  in
    $Lst.list_vt_free (s3is)
  end // end of [val]
*)
in
  v3aldec_make (loc0, p3t, d3e_def)
end // end of [v2aldec_tr]

(* ****** ****** *)

fun v2aldeclst_tr
  (valknd: $Syn.valkind, d2cs: v2aldeclst): v3aldeclst = let
  fun aux (d2cs: v2aldeclst):<cloptr1> v3aldeclst = case+ d2cs of
    | cons (d2c, d2cs) => cons (v2aldec_tr (valknd, d2c), aux d2cs)
    | nil () => nil ()
  // end of [aux]
in
  aux (d2cs)
end // end of [v2aldeclst_tr]

fun v2aldeclst_rec_tr
  (d2cs: v2aldeclst): v3aldeclst = d3cs where {
  val p3ts = aux1 (d2cs) where {
    fun aux1 {n:nat} .<n>.
      (d2cs: list (v2aldec, n))
      : list (p3at, n) = case+ d2cs of
      | list_cons (d2c, d2cs) => let
          val p2t = d2c.v2aldec_pat
          val s2e_pat = case+ d2c.v2aldec_ann of
            | Some s2e => s2e | None () => p2at_typ_syn (p2t)
          val () = // checking for nonlinearity
            if s2exp_is_linear s2e_pat then begin
              prerr_loc_error3 (p2t.p2at_loc);
              prerr ": this pattern can only be assigned a nonlinear type.";
              prerr_newline ();
              $Err.abort {void} () 
            end // end of [if]
          val p3t = p2at_tr_dn (p2t, s2e_pat)
        in
          list_cons (p3t, aux1 d2cs)
        end // end of [list_cons]
      | list_nil () => list_nil ()
    // end of [aux1]
  } // end of [val]
  val d3cs = aux2 (d2cs, p3ts) where {
    fun aux2 {n:nat} .<n>. (
        d2cs: list (v2aldec, n)
      , p3ts: list (p3at, n)
      ) : list (v3aldec, n) = case+ d2cs of
      | list_cons (d2c, d2cs) => let
          val+ list_cons (p3t, p3ts) = p3ts
          val d2e_def = d2c.v2aldec_def
          val s2e_pat = p3t.p3at_typ
          val d3e_def = d2exp_tr_dn (d2e_def, s2e_pat)
(*
          // this is not needed as [s2e_pat] cannot be linear!
          val () = d3exp_lval_set_typ_pat (d3e_def, p3t)
          val () = the_d2varset_env_add_p2at (d2c.v2aldec_pat)
*)

          val d3c = v3aldec_make (d2c.v2aldec_loc, p3t, d3e_def)
        in
          list_cons (d3c, aux2 (d2cs, p3ts))
        end // end of [list_cons]
      | list_nil () => list_nil ()
    // end of [aux2]
  } // end of [val]
} // end of [v2aldeclst_rec_tr]

(* ****** ****** *)

fn f2undec_tr (d2c: f2undec): d3exp = let
  val d2v_fun = d2c.f2undec_var
  val d2v_loc = d2var_get_loc d2v_fun
  val d2v_decarg = d2var_get_decarg d2v_fun
  val d2e_def = d2c.f2undec_def
(*
  val () = begin
    print "f2undec_tr: var = "; print d2v_fun; print_newline ();
  end
  val () = begin
    print "f2undec_tr: def = "; print d2e_def; print_newline ();
  end
*)
  val () = trans3_env_push_sta ()
  val () = trans3_env_hypo_add_s2qualst (d2v_loc, d2v_decarg)

  val d3e_def = (case+ d2c.f2undec_ann of
    | Some s2e_ann => let
(*
        val () = begin
          print "f2undec_tr: s2e_ann = "; print s2e_ann; print_newline ();
          print "f2undec_tr: d2e_def = "; print d2e_def; print_newline ();
        end // end of [val]
*)
      in
        d2exp_tr_dn (d2e_def, s2e_ann)
      end // end of [Some]
    | None () => d2exp_tr_up d2e_def
  ) : d3exp

  val () = trans3_env_pop_sta_and_add_none (d2c.f2undec_loc)
  val s2e_fun = d3e_def.d3exp_typ
(*
  val () = begin
    print "f2undec_tr: s2e_fun = "; print s2e_fun; print_newline ()
  end // end of [val]
*)
(*
  val s2e_fun_gen = s2exp_generalize s2e_fun
  val () = d3exp_set_typ (d2e_def, s2e_fun_gen)
  val () = begin
    print "f2undec_tr: s2e_fun_gen = ";
    print d3e_def.d3exp_typ; print_newline ()
  end // end of [val]
  val () = let
    val s3is = trans3_env_s3itemlst_copy ()
    val () = begin
      print "f2undec_tr: s3is = "; print_s3itemlst_vt s3is; print_newline ()
    end // end of [val]
  in
    $Lst.list_vt_free (s3is)
  end // end of [val]
*)
in
  d3e_def
end // end of [f2undec_tr]

(* ****** ****** *)

fn d2exp_metfn_load
  (d2e0: d2exp, d2vs_fun: d2varlst): void = let
  fun aux (d2e0: d2exp, d2vs_fun: d2varlst): void =
    case+ d2e0.d2exp_node of
    | D2Elam_dyn (_, _, _, d2e) => aux (d2e, d2vs_fun)
    | D2Elam_met (r, _, _) => !r := d2vs_fun
    | D2Elam_sta (_, _, d2e) => aux (d2e, d2vs_fun)
    | _ => ()
  // end of [aux]
in
  aux (d2e0, d2vs_fun)
end // end of [d2exp_metfn_load]

fn f2undeclst_tr
  (fk: $Syn.funkind, d2cs: f2undeclst): f3undeclst = let
  val isrec = $Syn.funkind_is_recursive fk
  fun aux_ini
    (i: int, os2ts0: &s2rtlstopt, d2cs: f2undeclst, d2vs_fun: d2varlst)
    : void = begin case+ d2cs of
    | cons (d2c, d2cs) => let
        val d2v_fun = d2c.f2undec_var
        val d2e_def = d2c.f2undec_def
        val () = d2exp_metfn_load (d2e_def, d2vs_fun)
        var os2ts: s2rtlstopt = None ()
        val s2e_fun = let
          val s2e = (
            case+ d2c.f2undec_ann of
            | Some s2e_ann => s2e_ann | None () => d2exp_typ_syn d2e_def
          ) : s2exp // end of [val]
          val os2tss2e = s2exp_metfn_load (s2e, d2v_fun)
        in
          case+ os2tss2e of
          | ~Some_vt (s2tss2e) => (os2ts := Some s2tss2e.1; s2tss2e.0)
          | ~None_vt () => s2e
        end // end of [val]
        val () = // checking metric sorts
          if i > 0 then let
            val compatible: bool =
              case+ (os2ts0, os2ts) of
              | (Some s2ts0, Some s2ts) => s2ts0 <= s2ts
              | (None (), None ()) => true
              | (_, _) => false
          in
            if not (compatible) then begin
              prerr_loc_error3 (d2c.f2undec_loc);
              prerr ": incompatible termination metric for this function.";
              prerr_newline ();
              $Err.abort {void} ()
            end
          end else begin
            os2ts0 := os2ts
          end
        val os2e_fun = Some s2e_fun
        val () = d2var_set_typ (d2v_fun, os2e_fun)
        val () = d2var_set_mastyp (d2v_fun, os2e_fun)
      in
        aux_ini (i+1, os2ts0, d2cs, d2vs_fun)
      end // end of [cons]
    | nil () => ()
    end // end of [aux_ini]
  val () = // initialization for recursive functions
    if isrec then let
      var os2ts0: s2rtlstopt = None ()
      val d2vs_fun = aux d2cs where {
        fun aux (d2cs: f2undeclst): d2varlst = case+ d2cs of
          | cons (d2c, d2cs) => cons (d2c.f2undec_var, aux d2cs)
          | nil () => nil ()
      } // end of [where]
    in
      aux_ini (0, os2ts0, d2cs, d2vs_fun)
    end
  fun aux_fin {n:nat}
    (d2cs: list (f2undec, n), d3es_def: list_vt (d3exp, n))
    :<cloptr1> f3undeclst = case+ d2cs of
    | cons (d2c, d2cs) => let
        val+ ~list_vt_cons (d3e_def, d3es_def) = d3es_def
        val d2v_fun = d2c.f2undec_var
        val s2e_fun = d3e_def.d3exp_typ
        val () = let
          val os2e_fun = Some s2e_fun
        in
          d2var_set_typ (d2v_fun, os2e_fun);
          d2var_set_mastyp (d2v_fun, os2e_fun);
        end
        val d3c = f3undec_make (d2c.f2undec_loc, d2v_fun, d3e_def)
        val d3cs = aux_fin (d2cs, d3es_def)
      in
        cons (d3c, d3cs)
      end // end of [cons]
    | nil () => let
        val+ ~list_vt_nil () = d3es_def in nil ()
      end // end of [nil]
  val d3es_def = aux d2cs where {
    fun aux {n:nat} (d2cs: list (f2undec, n)): list_vt (d3exp, n) =
      case+ d2cs of
      | cons (d2c, d3cs) => list_vt_cons (f2undec_tr d2c, aux d3cs)
      | nil () => list_vt_nil ()
    // end of [aux]
  } // end of [where]
in
  aux_fin (d2cs, d3es_def)
end // end of [f2undeclst_tr]

(* ****** ****** *)
//
// HX: [sta] means allocation at compile-time
//
fn v2ardec_tr_sta
  (d2c: v2ardec): v3ardec = let
  val loc0 = d2c.v2ardec_loc
  val d2v_ptr = d2c.v2ardec_dvar
(*
  val () = the_d2varset_env_add d2v_ptr // no need as [d2v_ptr] is not linear
*)
  val s2v_addr = d2c.v2ardec_svar
  val s2e_addr = s2exp_var (s2v_addr)
  val () = let // assuming the address being positive
    val s2p = s2exp_gt_addr_addr_bool (s2e_addr, s2exp_null_addr ())
  in
    trans3_env_hypo_add_prop (loc0, s2p)
  end // end of [val]
  val s2e_ptr = s2exp_ptr_addr_type (s2e_addr)
  val os2e_ptr = Some s2e_ptr
  val () = d2var_set_addr (d2v_ptr, Some s2e_addr)
  val () = d2var_set_mastyp (d2v_ptr, os2e_ptr)
  val () = d2var_set_typ (d2v_ptr, os2e_ptr)
  val od2v_view = d2c.v2ardec_wth
  val d2v_view = d2var_ptr_viewat_make (d2v_ptr, od2v_view)
  // make [d2v_ptr] a mutable variable
  val () = d2var_set_view (d2v_ptr, D2VAROPTsome d2v_view)
  val () = the_d2varset_env_add (d2v_view)
  var s2e_elt: s2exp // uninitialized
  val od3e_ini = (
    case+ :(s2e_elt: s2exp) => (d2c.v2ardec_typ, d2c.v2ardec_ini) of
    | (None (), Some d2e_ini) => let
        val d3e_ini = d2exp_tr_up d2e_ini
        val () = d3exp_open_and_add d3e_ini
        val s2e_ini = d3e_ini.d3exp_typ
        val s2e_ini_top = s2exp_topize_0 s2e_ini
        val s2e_view = s2exp_at_viewt0ype_addr_view (s2e_ini, s2e_addr)
        val () = d2var_set_typ (d2v_view, Some s2e_view)
        val s2e_view_fin = begin
          s2exp_at_viewt0ype_addr_view (s2e_ini_top, s2e_addr)
        end
        val () = d2var_set_mastyp (d2v_view, Some s2e_view_fin)
        val () = d2var_set_fin (d2v_view, D2VARFINsome (s2e_view_fin))
       in
         s2e_elt := s2e_ini_top; Some d3e_ini
       end // end of [None, Some]
    | (Some s2e_ann, None ()) => let
        val () = let
          val s2e = s2exp_at_viewt0ype_addr_view (s2e_ann, s2e_addr)
        in
          d2var_set_mastyp (d2v_view, Some s2e)
        end // end of [val]
        val s2e_view = begin
          s2exp_at_viewt0ype_addr_view (s2exp_topize_0 s2e_ann, s2e_addr)
        end // end of [val]
        val () = d2var_set_typ (d2v_view, Some s2e_view)
        val () = d2var_set_fin (d2v_view, D2VARFINsome s2e_view)
      in
        s2e_elt := s2e_ann; None ()
      end // end of [Some, None]
    | (Some s2e_ann, Some d2e_ini) => let
        val d3e_ini = d2exp_tr_up d2e_ini
        val () = d3exp_open_and_add d3e_ini
        val s2e_ini = d3e_ini.d3exp_typ
        val () = $SOL.s2exp_tyleq_solve (loc0, s2e_ini, s2e_ann)
        val s2e_ann_view = s2exp_at_viewt0ype_addr_view (s2e_ann, s2e_addr)
        val () = d2var_set_mastyp (d2v_view, Some s2e_ann_view)
        val s2e_ini_view = s2exp_at_viewt0ype_addr_view (s2e_ini, s2e_addr)
        val () = d2var_set_typ (d2v_view, Some s2e_ini_view)
        val () = let
          val s2e_ann_top = s2exp_topize_0 s2e_ann
          val s2e_view_fin = s2exp_at_viewt0ype_addr_view (s2e_ann_top, s2e_addr)
        in
          d2var_set_fin (d2v_view, D2VARFINsome s2e_view_fin)
        end // end of [val]
      in
        s2e_elt := s2e_ann; Some d3e_ini
      end // end of [Some, Some]
    | (None (), None ()) => let
        val () = prerr_loc_error3 (loc0)
        val () = prerr ": the uninitialized dynamic variable ["
        val () = prerr d2v_ptr
        val () = prerr "] needs to be ascribed a type."
        val () = prerr_newline ()
        val () = s2e_elt := $Err.abort {s2exp} ()
      in
        None ()
      end // end of [None, None]
    ) : d3expopt // end of [case]
in
  v3ardec_make (loc0, 0(*knd*), d2v_ptr, d2v_view, s2e_elt, od3e_ini)
end // end of [v2ardec_tr_sta]

(* ****** ****** *)

fun d2exp_is_laminit
  (d2e: d2exp): bool =
  case+ d2e.d2exp_node of
  | D2Elaminit_dyn _ => true
  | D2Elam_sta (_(*s2vs*), _(*s2ps*), d2e) => d2exp_is_laminit (d2e)
  | D2Elam_met (_(*d2vs*), _(*s2es*), d2e) => d2exp_is_laminit (d2e)
  | D2Efix (_(*knd*), _(*d2v*), d2e_def) => d2exp_is_laminit (d2e_def)
  | _ => false
// end of [d2exp_is_laminit]

//
// HX: [dyn] means allocation at run-time
//
fn v2ardec_tr_dyn
  (d2c: v2ardec): v3ardec = let
  val loc0 = d2c.v2ardec_loc
  val d2v_ptr = d2c.v2ardec_dvar
(*
  val () = the_d2varset_env_add d2v_ptr // no need as [d2v_ptr] is not linear
*)
  val s2v_addr = d2c.v2ardec_svar
  val s2e_addr = s2exp_var (s2v_addr)
  val () = let // assuming the address being positive
    val s2p = s2exp_gt_addr_addr_bool (s2e_addr, s2exp_null_addr ())
  in
    trans3_env_hypo_add_prop (loc0, s2p)
  end // end of [val]
  val s2e_ptr = s2exp_ptr_addr_type (s2e_addr)
  val os2e_ptr = Some s2e_ptr
  val () = d2var_set_addr (d2v_ptr, Some s2e_addr)
  val () = d2var_set_mastyp (d2v_ptr, os2e_ptr)
  val () = d2var_set_typ (d2v_ptr, os2e_ptr)
  val od2v_view = d2c.v2ardec_wth
  val d2v_view = d2var_ptr_viewat_make (d2v_ptr, od2v_view)
(*
  // d2v_ptr is not mutable!!!
  // val () = d2var_set_view (d2v_ptr, D2VAROPTsome d2v_view)
*)
  val () = the_d2varset_env_add (d2v_view)

  val d2e_ini = (case+ d2c.v2ardec_ini of
    | Some d2e => d2e | None () => begin
        prerr_loc_error3 (loc0);
        prerr ": the syntax for allocating memory on stack (alloca) is incorrect.";
        prerr_newline (); $Err.abort {d2exp} ()
      end // end of [None]
  ) : d2exp // end of [val]
  val loc_ini = d2e_ini.d2exp_loc
in
  case+ d2e_ini.d2exp_node of
  | D2Earrinit (s2e_elt, od2e_asz, d2es_elt) => let
      var od3e_asz: d3expopt = None ()
      val s2e_dim = (case+ od2e_asz of
        | Some d2e_asz => let
            val loc_asz = d2e_asz.d2exp_loc
            val d3e_asz = d2exp_tr_up d2e_asz
            val s2e_asz = s2exp_whnf (d3e_asz.d3exp_typ)
            val os2e_dim = un_s2exp_int_int_t0ype (s2e_asz)
            val os2e_dim = (case+ os2e_dim of
              | Some_vt _ => (fold@ os2e_dim; os2e_dim)
              | ~None_vt () => un_s2exp_size_int_t0ype (s2e_asz)
            ) : s2expopt_vt
            val s2e_dim = case+ os2e_dim of
              | ~Some_vt s2e_dim => s2e_dim
              | ~None_vt () => let
                  val () = prerr_loc_error3 (loc_asz)
                  val () = $Deb.debug_prerrf (": %s: v2ardec_tr_dyn", @(THISFILENAME))
                  val () = prerr ": the dynamic expression is assgined the type ["
                  val () = prerr_s2exp s2e_asz
                  val () = prerr "], but it is expected to be a nonnegative integer."
                  val () = prerr_newline ()
                in
                  $Err.abort {s2exp} ()
                end // end of [None]
            // end of [val]
            val () = trans3_env_add_prop (loc_asz, s2p) where {
              val s2p = s2exp_gte_int_int_bool (s2e_dim, s2exp_int_0)
            } // end of [val]
          in
            od3e_asz := Some d3e_asz; s2e_dim
          end // end of [Some]
        | None () => let
            val n = $Lst.list_length (d2es_elt) in s2exp_int (n)
          end // end of [None]
      ) : s2exp // end of [val]
      val d3es_elt = aux (d2es_elt, s2e_elt) where {
        fun aux (d2es: d2explst, s2e: s2exp): d3explst = case+ d2es of
          | list_cons (d2e, d2es) => let
              val d3e = d2exp_tr_dn (d2e, s2e) in list_cons (d3e, aux (d2es, s2e))
            end // end of [list_cons]
          | list_nil () => list_nil ()
        // end of [aux]
      } // end of [val]
      val s2es_dim: s2explst = list_cons (s2e_dim, list_nil ())
      val s2ess_dim: s2explstlst = list_cons (s2es_dim, list_nil ())
      val s2e_ann = s2exp_tyarr (s2e_elt, s2ess_dim)
      val s2e_ann_top = let
        val s2e_elt = s2exp_topize_0 s2e_elt in s2exp_tyarr (s2e_elt, s2ess_dim)
      end  // end of [val]
      val s2e_ann_view = s2exp_at_viewt0ype_addr_view (s2e_ann, s2e_addr)
      val () = d2var_set_mastyp (d2v_view, Some s2e_ann_view)
      val s2e_ini = (case+ d3es_elt of list_cons _ => s2e_ann | _ => s2e_ann_top): s2exp
      val d3e_ini = d3exp_arrinit (loc_ini, s2e_ini, s2e_elt, od3e_asz, d3es_elt)
      val s2e_ini_view = s2exp_at_viewt0ype_addr_view (s2e_ini, s2e_addr)
      val () = d2var_set_typ (d2v_view, Some s2e_ini_view)
      val () = d2var_set_fin (d2v_view, D2VARFINsome s2e_fin_view) where {
        val s2e_fin_view = s2exp_at_viewt0ype_addr_view (s2e_ann_top, s2e_addr)
      }  // end of [val]
    in
      v3ardec_make (loc0, 1(*knd*), d2v_ptr, d2v_view, s2e_ann, Some d3e_ini)
    end // end of [D2Earrinit]
  | _ when d2exp_is_laminit (d2e_ini) => let
      val d3e_ini = d2exp_tr_up (d2e_ini)
      val s2e_ini = d3e_ini.d3exp_typ
      val s2e_ini_view = s2exp_at_viewt0ype_addr_view (s2e_ini, s2e_addr)
      val () = d2var_set_mastyp (d2v_view, Some s2e_ini_view)
      val s2e_fin = s2exp_topize_0 (s2e_ini)
      val s2e_fin_view = s2exp_at_viewt0ype_addr_view (s2e_fin, s2e_addr)
      val () = d2var_set_typ (d2v_view, Some s2e_ini_view)
      val () = d2var_set_fin (d2v_view, D2VARFINsome s2e_fin_view)
    in
      v3ardec_make (loc0, 1(*knd*), d2v_ptr, d2v_view, s2e_ini, Some d3e_ini)
    end // end of [D2Elam when ...]
  | _ => begin
      prerr_loc_error3 (loc0);
      $Deb.debug_prerrf (": %s: v2ardec_tr_dyn", @(THISFILENAME));
      prerr ": the syntax for allocating memory on stack (alloca) is incorrect.";
      prerr_newline ();
      prerr "d2e_ini = "; prerr_d2exp d2e_ini; prerr_newline ();
      $Err.abort {v3ardec} ()
    end // end of [_]
end // end of [v2ardec_tr_dyn]

(* ****** ****** *)

fn v2ardec_tr (
  d2c: v2ardec
) : v3ardec = let
  val knd = d2c.v2ardec_knd
in
  if knd = 0 then begin
    v2ardec_tr_sta (d2c) // static allocation
  end else begin (* dynamic *)
    v2ardec_tr_dyn (d2c) // dynamic allocation
  end // end of [if]
end // end of [v2ardec_tr]

fn v2ardeclst_tr (
  d2cs: v2ardeclst
) : v3ardeclst = let
  val () = aux d2cs where {
    fun aux // add static address variables into the environment
      (d2cs: v2ardeclst): void = case+ d2cs of
      | cons (d2c, d2cs) => begin
          trans3_env_add_svar (d2c.v2ardec_svar); aux d2cs
        end // end of [cons]
      | nil () => () // end of [nil]
    // end of [aux]
  } // end of [where]
in
  $Lst.list_map_fun (d2cs, v2ardec_tr)
end // end of [v2ardeclst_tr]

(* ****** ****** *)

implement d2ec_tr (d2c0) = let
(*
  val () = begin
    print "d2ec_tr: d2c0 = ..."; print_newline ()
  end // end of [val]
*)
in
  case+ d2c0.d2ec_node of
  | D2Cnone () => d3ec_none (d2c0.d2ec_loc)
  | D2Clist d2cs => begin
      d3ec_list (d2c0.d2ec_loc, d2eclst_tr d2cs)
    end // end of [D2Clist]
  | D2Cinclude d2cs => begin
      d3ec_list (d2c0.d2ec_loc, d2eclst_tr d2cs)
    end // end of [D2Cinclude]
  | D2Csymintr _ => d3ec_none (d2c0.d2ec_loc)
  | D2Csymelim _ => d3ec_none (d2c0.d2ec_loc)
  | D2Cstavars (d2cs) => let
      fn f (d2c: s2tavar): void = let
        val loc = d2c.s2tavar_loc; val s2v = d2c.s2tavar_var
        val () = trans3_env_add_svar s2v
        val s2e = s2exp_Var_make_var (loc, s2v)
        val () = trans3_env_hypo_add_bind (loc, s2v, s2e)
      in
        // empty
      end
      val () = $Lst.list_foreach_fun (d2cs, f)
    in
      d3ec_none (d2c0.d2ec_loc)
    end // end of [D2Cstavars]
  | D2Csaspdec (d2c) => let
      val loc = d2c.s2aspdec_loc
      val s2c = d2c.s2aspdec_cst
      val s2e = d2c.s2aspdec_def
      val () = the_s2cstlst_env_bind_and_add (loc, s2c, s2e)
    in
      d3ec_saspdec (d2c0.d2ec_loc, d2c)
    end // end of [D2Csaspec]
  | D2Cdcstdec (dck, d2cs) => begin
      d3ec_dcstdec (d2c0.d2ec_loc, dck, d2cs)
    end // end of [D2Cdcstdec]
  | D2Cdatdec (knd, s2cs) => let
      fun aux
        (sVs: s2Varset_t, s2cs: s2cstlst): void =
        case+ s2cs of
        | S2CSTLSTcons (s2c, s2cs) => let
            val () = s2cst_set_sVarset (s2c, sVs) in aux (sVs, s2cs)
          end // end of [S2CSTLSTcons]
        | S2CSTLSTnil () => ()
      // end of [aux]
      val () = aux (the_s2Varset_env_get (), s2cs)
    in
      d3ec_datdec (d2c0.d2ec_loc, knd, s2cs)
    end // end of [D2Cdatdec]
  | D2Cexndec (d2cs) => begin
      d3ec_exndec (d2c0.d2ec_loc, d2cs)
    end // end of [D2Cexndec]
  | D2Coverload (id, d2i) => d3ec_none (d2c0.d2ec_loc)
  | D2Cextype (name, s2e_def) => let
(*
      val () = begin
        print ": d2ec_tr: D2Cextype: s2e_def = "; print s2e_def;
        print_newline ()
      end // end of [val]
*)
    in
      d3ec_extype (d2c0.d2ec_loc, name, s2e_def)
    end // end of [D2Cextype]
  | D2Cextval (name, d2e_def) => begin
      d3ec_extval (d2c0.d2ec_loc, name, d2exp_tr_up d2e_def)
    end // end of [D2Cextval]
  | D2Cextcode (position, code) => begin
      d3ec_extcode (d2c0.d2ec_loc, position, code)
    end // end of [D2Cextcode]
  | D2Cvaldecs (knd, d2cs) => let
      val d3cs = v2aldeclst_tr (knd, d2cs)
    in
      d3ec_valdecs (d2c0.d2ec_loc, knd, d3cs)
    end // end of [D2Cvaldecs]
  | D2Cvaldecs_par (d2cs) => let
      val d3cs = v2aldeclst_tr ($Syn.VALKINDval (), d2cs)
    in
      d3ec_valdecs_par (d2c0.d2ec_loc, d3cs)
    end // end of [D2Cvaldecs_par]
  | D2Cvaldecs_rec (d2cs) => let
      val d3cs = v2aldeclst_rec_tr (d2cs)
    in
      d3ec_valdecs_rec (d2c0.d2ec_loc, d3cs)
    end // end of [D2Cvaldecs_rec]
  | D2Cfundecs (decarg, knd, d2cs) => let
      val d3cs = f2undeclst_tr (knd, d2cs)
    in
      d3ec_fundecs (d2c0.d2ec_loc, decarg, knd, d3cs)
    end // end of [D2Cfundecs]
  | D2Cvardecs (d2cs) => let
      val d3cs = v2ardeclst_tr (d2cs)
    in
      d3ec_vardecs (d2c0.d2ec_loc, d3cs)
    end // end of [D2Cvardecs]
  | D2Cimpdec i2mpdec => let
      val loc = i2mpdec.i2mpdec_loc
      val loc_id = i2mpdec.i2mpdec_loc_id
      val d2c = i2mpdec.i2mpdec_cst
      val decarg = i2mpdec.i2mpdec_decarg
      val tmparg = i2mpdec.i2mpdec_tmparg
      val tmpgua = i2mpdec.i2mpdec_tmpgua
(*
      val () = begin
        print "d2ec_tr: D2Cimpdec: d2c = "; print d2c; print_newline ()
      end // end of [val]
*)
      val () = trans3_env_push_sta ()
      val () = trans3_env_add_proplstlst (loc_id, tmpgua)
      val () = trans3_env_hypo_add_s2qualst (loc, decarg)
      val d3e_def = d2exp_tr_up (i2mpdec.i2mpdec_def)
      val () = trans3_env_pop_sta_and_add_none (loc)
      val d3c = i3mpdec_make (loc, d2c, decarg, tmparg, d3e_def)
    in
      d3ec_impdec (d2c0.d2ec_loc, d3c)
    end // end of [D2Cimpdec]
  | D2Clocal (d2cs_head, d2cs_body) => let
      val (pf1 | ()) = the_s2cstlst_env_push ()
      val d3cs_head = d2eclst_tr d2cs_head
      val (pf2 | ()) = the_s2cstlst_env_push ()
      val d3cs_body = d2eclst_tr d2cs_body
      val s2cs_body = the_s2cstlst_env_pop (pf2 | (*none*))
      val () = the_s2cstlst_env_pop_and_unbind (pf1 | (*none*))
      val () = the_s2cstlst_env_addlst (s2cs_body)
    in
      d3ec_local (d2c0.d2ec_loc, d3cs_head, d3cs_body)
    end // end of [D2Clocal]
  | D2Cstaload (qua, fil, loaded, loadflag, d2cs) => let
      val od3cs = (
        if loaded > 0 then None () else let
          val (pf | ()) = the_s2cstlst_env_push ()
          val d3cs = d2eclst_tr d2cs
          val () = the_s2cstlst_env_pop_and_unbind (pf | (*none*))
        in
          Some d3cs
        end // end of [Some]
      ) : Option (d3eclst)
    in
      d3ec_staload (d2c0.d2ec_loc, fil, loadflag, od3cs)
    end // end of [D2Cstaload]
  | D2Cdynload fil => d3ec_dynload (d2c0.d2ec_loc, fil)
(*
  | _ => begin
      prerr_loc_interror d2c0.d2ec_loc;
      prerr ": d2ec_tr: not implemented yet."; prerr_newline ();
      $Err.abort {d3ec} ()
    end // end of [_]
*)
end (* end of [d2ec_tr] *)

(* ****** ****** *)

// [list_map_fun] is tail-recursive!
implement d2eclst_tr (d2cs) = $Lst.list_map_fun (d2cs, d2ec_tr)

(* ****** ****** *)

implement
c3str_get_final () = let
 val s3is = trans3_env_s3itemlst_get ()
 val s3is_rev = $Lst.list_vt_reverse_list s3is
(*
 val () = begin
   print "c3str_get_final: s3is_rev = "; print_s3itemlst s3is_rev;
   print_newline ()
 end // end of [val]
*)
in
 c3str_itmlst ($Loc.location_dummy, C3STRKINDmain, s3is_rev)
end // end of [c3str_get_final]

(* ****** ****** *)

(* end of [ats_trans3_dec.dats] *)
