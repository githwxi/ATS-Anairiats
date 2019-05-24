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
// Time: December 2007
//
(* ****** ****** *)
//
// History of bug fixes:
//
// HX-2010-05-27:
// The use of [s2Var_link_set] is now replaced with [s2exp_equal_solve];
// the former does not work correctly if either the lower or the upper
// bound of a [s2Var] is already set.
//
(* ****** ****** *)

(* Mainly for handling patterns during type-checking *)

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload Eff = "ats_effect.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

staload SOL = "ats_staexp2_solve.sats"

(* ****** ****** *)

staload "ats_dynexp3.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_trans3.sats"

(* ****** ****** *)

#define THISFILENAME "ats_trans3_pat.dats"

(* ****** ****** *)

overload = with $Lab.eq_label_label
overload prerr with $Loc.prerr_location

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans3_pat)"

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_trans3_pat)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

fun p3at_readize
  (s2e_v: s2exp, p3t: p3at): void = begin
  case+ p3t.p3at_node of
  | P3Tann (p3t, _) => p3at_readize (s2e_v, p3t)
  | P3Tany d2v => d2var_readize (s2e_v, d2v)
  | P3Tas (_, d2v, p3t) => begin
      d2var_readize (s2e_v, d2v); p3at_readize (s2e_v, p3t)
    end // end of [P3Tas]
  | P3Tcon (_, _, _, p3ts) => p3atlst_readize (s2e_v, p3ts)
  | P3Texist (_, p3t) => p3at_readize (s2e_v, p3t)
  | P3Tlst (_, p3ts) => p3atlst_readize (s2e_v, p3ts)
  | P3Trec (_, _, lp3ts) => labp3atlst_readize (s2e_v, lp3ts)
  | P3Tvar (_, d2v) => d2var_readize (s2e_v, d2v)
  | _ => ()
end // end of [p3at_readize]

and p3atlst_readize
 (s2e_v: s2exp, p3ts: p3atlst): void = begin case+ p3ts of
  | list_cons (p3t, p3ts) => begin
      p3at_readize (s2e_v, p3t); p3atlst_readize (s2e_v, p3ts)
    end (* end of [list_cons] *)
  | list_nil () => ()
end // end of [p3atlst_readize]

and labp3atlst_readize
  (s2e_v: s2exp, lp3ts: labp3atlst): void = begin
  case+ lp3ts of
  | LABP3ATLSTcons (_, p3t, lp3ts) => begin
      p3at_readize (s2e_v, p3t); labp3atlst_readize (s2e_v, lp3ts)
    end (* end of [LABP3ATLSTcons] *)
  | _ => ()
end // end of [labp3atlst_readize]

(* ****** ****** *)

fun labp2atlst_typ_syn
  (loc0: loc_t, lp2ts: labp2atlst): labs2explst =
  case+ lp2ts of
  | LABP2ATLSTcons (l, p2t, lp2ts) => begin
      LABS2EXPLSTcons (l, p2at_typ_syn p2t, labp2atlst_typ_syn (loc0, lp2ts))
    end // end of [LABS2EXPLSTcons]
  | LABP2ATLSTnil () => LABS2EXPLSTnil ()
  | LABP2ATLSTdot () => begin
      prerr loc0; prerr ": error(3)";
      prerr ": type synthesis cannot be done for a partial record pattern.";
      prerr_newline ();
      $Err.abort {labs2explst} ()
    end (* end of [LABP2ATLSTdot] *)
// end of [labp2atlst_typ_syn]

implement
p2at_typ_syn (p2t0) = let
  val s2e0 = (case+ p2t0.p2at_node of
    | P2Tann (_, s2e) => s2e
    | P2Tany () => begin
        s2exp_Var_make_srt (p2t0.p2at_loc, s2rt_t0ype)
      end // end of [P2Tany]
    | P2Tas (_, _, p2t) => p2at_typ_syn (p2t)
    | P2Tbool _ => s2exp_bool_t0ype ()
    | P2Tchar _ => s2exp_char_t0ype ()
    | P2Tcon _ => begin
        s2exp_Var_make_srt (p2t0.p2at_loc, s2rt_t0ype)
      end // end of [P2Tcon]
    | P2Tempty () => s2exp_void_t0ype ()
    | P2Texist _ => begin
        prerr p2t0.p2at_loc; prerr ": error(3)";
        prerr ": type synthesis is not supported for an existentially quantified pattern.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end // end of [P2Texist]
    | P2Tfloat _ => s2exp_double_t0ype ()
    | P2Tint _ => s2exp_int_t0ype ()
    | P2Tlist _ => begin
        prerr_loc_interror p2t0.p2at_loc;
        prerr ": p2at_typ_syn: P2Tlist"; prerr_newline ();
        $Err.abort {s2exp} ()
      end // end of [P2Tlist]
    | P2Tlst _ => begin
        s2exp_Var_make_srt (p2t0.p2at_loc, s2rt_t0ype)
      end // end of [P2Tlst]
    | P2Trec (recknd, npf, lp2ts) => let
        val ls2es = labp2atlst_typ_syn (p2t0.p2at_loc, lp2ts)
      in
        s2exp_tyrec (recknd, npf, ls2es)
      end // end of [P2Trec]
    | P2Tstring s => s2exp_string_type ()
    | P2Tvar (refknd, d2v) => begin
        s2exp_Var_make_srt (p2t0.p2at_loc, s2rt_t0ype)
      end // end of [P2Tvar]
    | P2Tvbox d2v => let
        val s2e = s2exp_Var_make_srt (p2t0.p2at_loc, s2rt_view)
      in
        s2exp_vbox_view_prop (s2e)
      end // end of [P2Tvbox]
  ) : s2exp // end of [val]
in
  p2at_set_typ (p2t0, Some s2e0); s2e0
end // end of [p2at_typ_syn]

implement
p2atlst_typ_syn (p2ts) = case+ p2ts of
  | list_cons (p2t, p2ts) => begin
      list_cons (p2at_typ_syn p2t, p2atlst_typ_syn p2ts)
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [p2atlst_typ_syn]

(* ****** ****** *)

fn pfarity_check
  (loc0: loc_t, npf1: int, npf2: int): void =
  if npf1 <> npf2 then begin
    prerr loc0; prerr ": error(3)";
    $Deb.debug_prerrf (": %s", @(THISFILENAME));
    prerr ": pfarity_check: pfarity mismatch";
    if npf1 < npf2 then prerr ": more proof components are needed.";
    if npf1 > npf2 then prerr ": fewer proof components are needed.";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
// end of [pfarity_check]

(* ****** ****** *)

fun labp3atlst_typ_get
  (lp3ts: labp3atlst): labs2explst = begin
  case+ lp3ts of
  | LABP3ATLSTcons (l, p3t, lp3ts) => begin
      LABS2EXPLSTcons (l, p3t.p3at_typ, labp3atlst_typ_get lp3ts)
    end
  | LABP3ATLSTnil () => LABS2EXPLSTnil ()
  | LABP3ATLSTdot () => begin
      prerr_interror ();
      prerr ": labp2atlst_typ_get: LABP3ATLSTdot"; prerr_newline ();
      $Err.abort {labs2explst} ()
    end // end of [LABP3ATLSTdot]
end // end of [labp3atlst_typ_get]

(* ****** ****** *)

fn p2at_any_tr_dn
  (loc0: loc_t, s2e0: s2exp): p3at = let
  val d2v = d2var_make_any loc0
  val () = the_d2varset_env_add d2v
  val p3t = p3at_any (loc0, s2e0, d2v)
  val s2e = s2exp_opnexi_and_add (loc0, s2e0)
(*
  // unnecessary as [None] is the default value
  val () = d2var_set_typ (d2v, None ())
*)
  val () = begin
    if s2exp_is_linear s2e then p3at_set_typ_lft (p3t, Some s2e)
  end // end of [val]
in
  p3t
end // end of [p2at_any_tr_dn]

(* ****** ****** *)

fn p2at_bool_tr_dn (
    loc0: loc_t, b: bool, s2e0: s2exp
  ) : p3at = let
  val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) when
      s2cstref_equ_exp (Bool_bool_t0ype, s2e_fun) => let
      val s2e_arg = case+ s2es_arg of
      | list_cons (s2e, _) => s2e | list_nil _ => begin
          prerr_loc_interror loc0;
          prerr ": p2at_bool_tr_dn"; prerr_newline ();
          $Err.abort {s2exp} ()
        end (* end of [list_nil] *)
      // end of [val]
      val () = trans3_env_hypo_add_eqeq (loc0, s2exp_bool b, s2e_arg)
    in
      p3at_bool (loc0, s2exp_bool_bool_t0ype b, b)
    end (* end of [S2Eapp] *)
  | _ => let
      val s2e_bool = s2exp_bool_t0ype ()
      val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2e_bool)
    in
      p3at_bool (loc0, s2e_bool, b)
    end (* end of [_] *)
end // end of [p2at_bool_tr_dn]

(* ****** ****** *)

fn p2at_char_tr_dn
  (loc0: loc_t, c: char, s2e0: s2exp): p3at = let
  val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) when
      s2cstref_equ_exp (Char_char_t0ype, s2e_fun) => let
      val s2e_arg = case+ s2es_arg of
      | list_cons (s2e, _) => s2e | list_nil _ => begin
          prerr_loc_interror loc0;
          prerr ": p2at_char_tr_dn"; prerr_newline ();
          $Err.abort {s2exp} ()
        end (* end of [list_nil] *)
      // end of [val]
      val () = trans3_env_hypo_add_eqeq (loc0, s2exp_char c, s2e_arg)
    in
      p3at_char (loc0, s2exp_char_char_t0ype c, c)
    end (* end of [S2Eapp] *)
  | _ => let
      val s2e_char = s2exp_char_t0ype ()
      val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2e_char)
    in
      p3at_char (loc0, s2e_char, c)
    end (* end of [_] *)
end // end of [p2at_char_tr_dn]

(* ****** ****** *)
//
// for instance: [list] translates into [[n:int] list (X, n)]
//
fn s2cst_closure_make_predicative
  (loc0: loc_t, s2c: s2cst_t): s2exp = let
  val s2t_s2c = s2cst_get_srt s2c in case+ un_s2rt_fun s2t_s2c of
  | ~Some_vt (argres) (* @(s2rtlst, s2rt) *) => let
      var s2vs: s2varlst = list_nil () and s2es: s2explst = list_nil ()
      val () = loop (loc0, argres.0, s2vs, s2es) where {
        fun loop (
          loc0: loc_t, s2ts: s2rtlst, s2vs: &s2varlst, s2es: &s2explst
          ) : void = begin case+ s2ts of
          | list_cons (s2t, s2ts) => let
              val () =
                if s2rt_is_impredicative_fun s2t then let
                  val s2e = s2exp_Var_make_srt (loc0, s2t)
                in
                  s2es := list_cons (s2e, s2es);
                end else let
                  val s2v = s2var_make_srt s2t; val s2e = s2exp_var s2v
                in
                  s2vs := list_cons (s2v, s2vs); s2es := list_cons (s2e, s2es)
                end (* end of [if] *)
            in
              loop (loc0, s2ts, s2vs, s2es)
            end (* end of [list_cons] *)
          | list_nil () => ()
          end // end of [loop]
        } // end of [where]
      val () = begin
        s2vs := $Lst.list_reverse s2vs; s2es := $Lst.list_reverse s2es
      end // end of [val]
    in
      s2exp_exi (s2vs, list_nil (), s2exp_cstapp (s2c, s2es))
    end (* end of [Some_vt] *)
  | ~None_vt () => s2exp_cst s2c
end // end of [s2cst_closure_make_predicative]

(* ****** ****** *)

// [freeknd]: 0: nonlinear; 1: preserve; ~1: free
fn p3at_con_free_update
  (p3t0: p3at, freeknd: int, d2c: d2con_t, p3ts: p3atlst): void = let
(*
  val () = begin
    print "p3at_con_free_update: p3t0 = "; print p3t0; print_newline ();
    print "p3at_con_free_update: freeknd = "; print freeknd; print_newline ();
    print "p3at_con_free_update: d2c = "; print d2c; print_newline ();
  end // end of [val]
*)
  fun aux_var (
    d2v_ptr: d2var_t, s2e: s2exp
  ) : @(d2var_t, s2exp) = let
    val sym = d2var_get_sym (d2v_ptr)
    val s2v_addr =
      s2var_make_id_srt (sym, s2rt_addr)
    val () = trans3_env_add_svar s2v_addr
    val s2e_addr = s2exp_var s2v_addr
    val s2e_ptr = s2exp_ptr_addr_type (s2e_addr)
    val os2e_ptr = Some s2e_ptr
    val () = d2var_set_lin (d2v_ptr, ~1)
    val () = d2var_set_addr (d2v_ptr, Some s2e_addr)
    val () = d2var_set_mastyp (d2v_ptr, os2e_ptr)
    val () = d2var_set_typ (d2v_ptr, os2e_ptr)
    val d2v_view = d2var_ptr_viewat_make_none (d2v_ptr)
    val () = the_d2varset_env_add (d2v_view)
    val s2e_at = s2exp_at_viewt0ype_addr_view (s2e, s2e_addr)
    val os2e_at = Some s2e_at
    val () = d2var_set_mastyp (d2v_view, os2e_at)
    val () = d2var_set_typ (d2v_view, os2e_at)
    val () = d2var_set_fin (d2v_view, D2VARFINnone ())
  in
    (d2v_view, s2e_addr)
  end // end of [aux_var]
  fn aux_pat (
    p3t: p3at
  ) :<cloref1> s2exp = let
    val d2v_ptr = (case+ p3t.p3at_node of
      | P3Tany (d2v) => let
          val os2e = (
            case+ p3t.p3at_typ_lft of
            | None () => Some (s2exp_topize_1 p3t.p3at_typ)
            | os2e => os2e
          ) : s2expopt // end of [val]
        in
          d2var_set_typ (d2v, os2e); d2v
        end (* end of [P3Tany] *)
      | P3Tvar (refknd, d2v) when refknd > 0 => d2v
      | P3Tas (refknd, d2v, p3t_as) when refknd > 0 => d2v
      | _ => let
          val d2v = d2var_make_any (p3t.p3at_loc)
          val os2e = (
            case+ p3t.p3at_typ_lft of
            | None () => Some (s2exp_topize_1 p3t.p3at_typ)
            | os2e => os2e
          ) : s2expopt // end of [val]
        in
          d2var_set_typ (d2v, os2e); d2v
        end (* end of [_] *)
    ) : d2var_t // end of [val]    
(*
    val () = begin
      print "p3at_con_free_update: aux_pat: d2v_ptr = "; print d2v_ptr; print_newline ()
    end // end of [val]
*)
    val s2e = d2var_get_typ_some (p3t.p3at_loc, d2v_ptr)
    val (d2v_view, s2e_addr) = aux_var (d2v_ptr, s2e)
    val () = // handling deconstruction
      if freeknd < 0  then let
        val () = // linearity checking
          if s2exp_is_linear s2e then begin
            prerr p3t0.p3at_loc; prerr ": error(3)";
            prerr ": a value matching this pattern may not be freed";
            prerr ", as it contains a linear component of the type [";
            prerr s2e; prerr "].";
            prerr_newline ();
            $Err.abort ()
          end // end of [if]
      in
        d2var_set_typ (d2v_view, None ())
      end // end of [if]
  in
    s2e_addr
  end // end of [aux_pat]
  val s2es_addr = aux_patlst (p3ts) where {
    fun aux_patlst (p3ts: p3atlst):<cloref1> s2explst =
      case+ p3ts of
      | list_cons (p3t, p3ts) => list_cons (aux_pat p3t, aux_patlst p3ts)
      | list_nil () => list_nil ()
  } // end of [aux_p3atlst]
in
  if freeknd > 0 then (
    p3at_set_typ_lft (p3t0, Some (s2exp_datconptr (d2c, s2es_addr)))
  ) // end of [if]
end // end of [p3at_con_free_update]

(* ****** ****** *)

datatype p2atcontrup =
  {n:nat} P2ATCONTRUPcon of (list (p2at, n), list (s2exp, n), s2exp)
// end of [p2atcontrup]

fn p2at_con_tr_up
  (loc0: loc_t, d2c: d2con_t,
   s2vpss: s2qualst, s2e_con: s2exp, npf: int, p2ts: p2atlst)
  : p2atcontrup = let
//
val () = aux s2vpss where {
  fun aux (s2vpss: s2qualst): void =
    case+ s2vpss of
    | list_cons (s2vps, s2vpss) => let
        val s2vs = s2vps.0
(*
        val () = begin
          print "p2at_con_tr_up: aux: s2vs = "; print_s2varlst s2vs; print_newline ()
        end // end of [val]
*)
        val () = trans3_env_add_svarlst s2vs
      in
        aux s2vpss
      end // end of [list_cons]
    | list_nil () => ()
  // end of [aux]
} // end [where]
//
val () = aux (loc0, s2vpss) where {
  fun aux (loc0: loc_t, s2vpss: s2qualst): void =
    case+ s2vpss of
    | list_cons (s2vps, s2vpss) => begin
        trans3_env_hypo_add_proplst (loc0, s2vps.1); aux (loc0, s2vpss)
      end (* end of [list_cons] *)
    | list_nil () => ()
  // end of [aux]
} // end [where]
//
in
  case+ s2e_con.s2exp_node of
  | S2Efun (
      _fc, _lin, _s2fe, npf_con, s2es_arg, s2e_res
    ) => let
      val () = pfarity_check (loc0, npf, npf_con)
      stavar np2ts: int and ns2es: int
      val np2ts: int np2ts = $Lst.list_length p2ts
      val ns2es_arg: int ns2es = $Lst.list_length s2es_arg
      val () = ( // arity checking
        if (np2ts <> ns2es_arg) then begin
          prerr loc0; prerr ": error(3)";
          prerr ": the constructor ["; prerr d2c; prerr "] needs";
          if np2ts < ns2es_arg then prerr " more arguments.";
          if np2ts > ns2es_arg then prerr " fewer arguments.";
          $Err.abort {void} ();
          assert (np2ts = ns2es_arg) // deadcode
        end else begin
          () // [np2ts = ns2es_arg] holds!
        end
      ) : [np2ts==ns2es] void
    in
      P2ATCONTRUPcon (p2ts, s2es_arg, s2e_res)
    end // end of [S2Efun]
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": p2at_con_tr_up"; prerr_newline ();
      $Err.abort {p2atcontrup} ()
    end // end of [_]
end // end of [p2at_con_tr_up]

fn p2at_con_tr_dn (
    loc0: loc_t
  , freeknd: int // [freeknd]: 0: nonlinear; 1: preserve; ~1: free
  , d2c: d2con_t
  , s2vpss: s2qualst
  , s2e_con: s2exp
  , npf: int
  , p2ts: p2atlst
  , s2e0: s2exp
  ) : p3at = let
  val s2e0 = s2exp_whnf (s2e0)
  val s2c = d2con_get_scst (d2c)
  val s2e0 = (case+ s2e0.s2exp_node of
    | S2EVar s2V => let
        val s2e_s2c = (
          s2cst_closure_make_predicative (loc0, s2c)
        ) : s2exp // end of [val]
        val () = $SOL.s2exp_equal_solve (loc0, s2e0, s2e_s2c)
      in
        s2e_s2c
      end (* end of [S2EVar] *)
    | _ => s2e0
  ) : s2exp // end of [val]
  var s2e0: s2exp = s2exp_opnexi_and_add (loc0, s2e0)
  val os2es2e = un_s2exp_read s2e0
  var isread: bool = false
  val os2e_v = (case+ os2es2e of
    | ~Some_vt s2es2e => begin
        isread := true; s2e0 := s2es2e.1; Some_vt s2es2e.0
      end (* end of [Some_vt] *)
    | ~None_vt () => None_vt ()
  ) : s2expopt_vt
  val err_os2e_v = (case+ os2e_v of
    | Some_vt s2e_v => let
        val ans = (
          case+ the_d2varset_env_find_view s2e_v of
          | ~Some_vt _ => None_vt () | ~None_vt _ => Some_vt s2e_v
        ) : s2expopt_vt
      in
        fold@ os2e_v; ans
      end (* end of [Some_vt] *)
    | None_vt () => (fold@ os2e_v; None_vt ())
  ) : s2expopt_vt
  val () = case+ err_os2e_v of
    | ~Some_vt s2e_v => begin
        prerr loc0; prerr ": error(3)";
        $Deb.debug_prerrf (": %s: p2at_con_tr_dn", @(THISFILENAME));
        prerr ": a proof of the view [";
        prerr s2e_v; prerr "] is not avaible for reading.";
        prerr_newline ();
        $Err.abort {void} ()
      end (* end of [Some_vt] *)
    | ~None_vt () => ()
  // end of [val]
  val s2e_head = s2exp_get_head (s2e0)
  var flag: int = ~1 and freeknd: int = freeknd
  var s2es_arg_var: s2explst = list_nil ()
  val () = case+ s2e_head.s2exp_node of
    | S2Ecst s2c1 => if s2c = s2c1 then flag := 0
    | S2Edatcontyp (d2c1, s2es) => begin
        if d2c = d2c1 then (flag := 1; s2es_arg_var := s2es)
      end // end of [S2Edatcontyp]
    | _ => ()
  // end of [val]
  val () = if flag < 0 then begin
    prerr loc0; prerr ": error(3)";
    $Deb.debug_prerrf (": %s: p2at_con_tr_dn", @(THISFILENAME));
    prerr ": the constructor pattern is assigned the type [";
    prerr s2e0;
    prerr "] but it should not be.";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
  val flag_vwtp = (
    if isread then 0 else begin
      if flag > 0 then 1 else d2con_get_vwtp (d2c)
    end // end of [if]
  ) : int // end of [val]
  val () = // checking for legality of destruction 
    if freeknd > 0 then begin
      (if flag_vwtp > 0 then () else freeknd := 0)
    end else begin // [freeknd < 0]
      if flag_vwtp > 0 then () else begin
        prerr loc0; prerr ": error(3)";
        $Deb.debug_prerrf (": %s: p2at_con_tr_dn", @(THISFILENAME));
        prerr ": the constructor [";
        prerr d2c;
        prerr "] is not allowed to be freed.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [if]
    end (* end of [if] *)
  // end of [val]
  val p3t0 = (case+ 0 of
  | _  when flag = 0 => let // s2e0 = S2Ecst (...)
      val+ P2ATCONTRUPcon (p2ts, s2es_arg, s2e_res) =
        p2at_con_tr_up (loc0, d2c, s2vpss, s2e_con, npf, p2ts)
      val () = $SOL.s2exp_hypo_equal_solve (loc0, s2e_res, s2e0)
      val s2es_arg = s2explst_nfapp s2es_arg // this is important for erasure!
      val p3ts = p2atlst_tr_dn (p2ts, s2es_arg)
      val p3t0 = p3at_con (loc0, s2e0, freeknd, d2c, npf, p3ts)
      val () = (case+ 0 of
        | _ when freeknd = 0 => () where {
            fun aux (p3ts: p3atlst, err: &int)
              :<cloref1> void = begin case+ p3ts of
              | list_cons (p3t, p3ts) => aux (p3ts, err) where {
                  val () = (case+ p3t.p3at_node of
                    | P3Tvar (refknd, _) => if refknd > 0 then err := err + 1
                    | P3Tas (refknd, _, _) => if refknd > 0 then err := err + 1
                    | _ => ()
                  ) : void // end of [val]
                } // end of [list_cons]
              | list_nil () => ()
            end // end of [aux]
            var err: int = 0; val () = aux (p3ts, err)
            val () = if err > 0 then begin
              prerr loc0; prerr ": error(3)";
              $Deb.debug_prerrf (": %s: p2at_con_tr_dn", @(THISFILENAME));
              prerr ": the constructor ["; prerr d2c;
              prerr "] is not allowed to have a reference argument.";
              prerr_newline ();
              $Err.abort {void} ()
            end // end of [val]
          } // end of [_ when freeknd = 0]
        | _ (*freeknd <> 0*) => p3at_con_free_update (p3t0, freeknd, d2c, p3ts)
      ) : void // end of [val]
    in
      p3t0 // the returned constructor pattern
    end (* end of [_ when flag = 0] *)
  | _ (*flag<>0*) => let // s2e0 = S2Edatuni (...)
      val s2es_arg = (s2es_arg_var: s2explst)
//
(*
      val () = (
        print "p2at_con_tr_dn: s2es_arg = "; print_s2explst s2es_arg; print_newline ()
      ) // end of [val]
*)
//
      val [sgn:int] sgn = $Lst.list_length_compare (p2ts, s2es_arg)
      val () = (if sgn <> 0 then begin
        prerr_loc_interror loc0;
        prerrf (": p2at_con_tr_dn: sgn = %i", @(sgn)); prerr_newline ();
        $Err.abort {void} ();
        assert (sgn = 0) // deadcode
      end else begin
        () // [sgn = 0] holds!
      end) : [sgn==0] void
      val p3ts = p2atlst_tr_dn (p2ts, s2es_arg)
      val p3t0 = p3at_con (loc0, s2e0, freeknd, d2c, npf, p3ts)
      val () = p3at_con_free_update (p3t0, freeknd, d2c, p3ts)
    in
      p3t0 // the returned constructor pattern
    end (* end of [_ when flag <> 0] *)
  ) : p3at // end of [val]
  val () = (case+ os2e_v of
    | ~Some_vt s2e_v => p3at_readize (s2e_v, p3t0) | ~None_vt () => ()
  ) : void // readizing all the dynamic variables in [p3t0]
in
  p3t0
end // end of [p2at_con_tr_dn]

(* ****** ****** *)

fn p2at_exist_tr_dn
  (p2t0: p2at, s2vs0: s2varlst, p2t: p2at, s2e0: s2exp): p3at = let
  val loc0 = p2t0.p2at_loc
  val s2e0 = s2exp_whnf s2e0
in
  case+ s2e0.s2exp_node of
  | S2Eexi (s2vs, s2ps, s2e) => let
      val sub = aux (s2vs, s2vs0) where {
        fun aux (s2vs: s2varlst, s2vs0: s2varlst):<cloref1> stasub_t =
          case+ (s2vs, s2vs0) of
          | (list_cons (s2v, s2vs), list_cons (s2v0, s2vs0)) => let
              val s2t = s2var_get_srt s2v and s2t0 = s2var_get_srt s2v0
            in
              if s2t0 <= s2t then
                stasub_add (aux (s2vs, s2vs0), s2v, s2exp_var s2v0)
              else begin
                prerr loc0; prerr "error(3)";
                prerr ": the bound variable [";
                prerr s2v;
                prerr "] is given the sort [";
                prerr s2t;
                prerr "] but it is expected to be of the sort [";
                prerr s2t0;
                prerr "].";
                prerr_newline ();
                $Err.abort {stasub_t} ()
              end // end of [if]
            end (* end of [list_cons, list_cons] *)
          | (list_nil (), list_nil ()) => stasub_nil
          | (list_cons _, list_nil _) => begin
              prerr loc0; prerr "error(3)";
              prerr ": the existentially quantified pattern needs fewer bound variables.";
              prerr_newline ();
              $Err.abort {stasub_t} ()
            end (* end of [list_cons, list_nil] *)
          | (list_nil _, list_cons _) => begin
              prerr loc0; prerr "error(3)";
              prerr ": the existentially quantified pattern needs more bound variables.";
              prerr_newline ();
              $Err.abort {stasub_t} ()
            end (* end of [list_nil, list_cons] *)
      } // end of [where]
      val () = trans3_env_add_svarlst s2vs0
      val () = trans3_env_hypo_add_proplst (loc0, s2explst_subst (sub, s2ps))
      val p3t = p2at_tr_dn (p2t, s2exp_subst (sub, s2e))
    in
      p3at_exist (loc0, s2e0, s2vs0, p3t)
    end (* end of [S2Eexist] *)
  | _ => begin
      prerr loc0; prerr ": error(3)";
      prerr ": the pattern is given the type ["; prerr s2e0;
      prerr "] but an existentially quantified type is expected.";
      prerr_newline ();
      $Err.abort {p3at} ()
    end (* end of [_] *)
end // end of [p2at_exist_tr_dn]

(* ****** ****** *)

fun p2atlst_elt_tr_dn
  (p2ts: p2atlst, s2e: s2exp): p3atlst =
  case+ p2ts of
  | list_cons (p2t, p2ts) => begin
      list_cons (p2at_tr_dn (p2t, s2e), p2atlst_elt_tr_dn (p2ts, s2e))
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [p2atlst_elt_tr_dn]

fn p2at_lst_tr_dn (
    loc0: loc_t, p2ts: p2atlst, s2e0: s2exp
  ) : p3at = let
  val s2e_lst = s2exp_opnexi_and_add (loc0, s2e0)
in
  case+ un_s2exp_list_t0ype_int_type s2e_lst of
  | ~Some_vt s2es2i => let
      val s2e_elt = s2es2i.0
      val np2ts = $Lst.list_length p2ts
      val () = trans3_env_hypo_add_eqeq (loc0, s2es2i.1, s2exp_int np2ts)
      val p3ts = p2atlst_elt_tr_dn (p2ts, s2e_elt)
    in
      p3at_lst (loc0, s2e_elt, s2e0, p3ts)
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr loc0; prerr ": error(3)";
      prerr ": the pattern is given the type ["; prerr s2e_lst;
      prerr "] but a type of the form [list (_, _)] is expected.";
      prerr_newline ();
      $Err.abort {p3at} ()
    end // end of [None_vt]
end // end of [p2at_lst_tr_dn]

(* ****** ****** *)

fun labs2explst_revapp
  (ls2es1: labs2explst, ls2es2: labs2explst): labs2explst = begin
  case+ ls2es1 of
  | LABS2EXPLSTcons (l1, s2e1, ls2es1) => begin
      labs2explst_revapp (ls2es1, LABS2EXPLSTcons (l1, s2e1, ls2es2))
    end
  | LABS2EXPLSTnil () => ls2es2
end // end of [labs2explst_revapp]

fn labp2atlst_tr_dn
  (loc0: loc_t, lp2ts0: labp2atlst, ls2es0: labs2explst): labp3atlst = let
  fun aux (
      loc0: loc_t
    , lp2ts0: labp2atlst
    , ls2es0: labs2explst
    , omits: labs2explst
    ) : labp3atlst = begin case+ lp2ts0 of
    | LABP2ATLSTcons (l1, p2t, lp2ts) => begin case+ ls2es0 of
      | LABS2EXPLSTcons (l2, s2e, ls2es) => begin
          if l1 = l2 then let
            val p3t = p2at_tr_dn (p2t, s2e)
          in
            LABP3ATLSTcons (l1, p3t, aux (loc0, lp2ts, ls2es, omits))
          end else begin
            aux (loc0, lp2ts0, ls2es, LABS2EXPLSTcons (l2, s2e, omits))
          end
        end // end of [LABS2EXPLSTcons]
      | LABS2EXPLSTnil () => begin
          prerr loc0; prerr ": error(3)";
          prerr ": the pattern contains a component with the label [";
          $Lab.prerr_label l1;
          prerr "] but it should not according to its assigned type.";
          prerr_newline ();
          $Err.abort {labp3atlst} ()
        end // end of [LABS2EXPLSTnil]
      end // end of [LABP2ATLSTcons]
    | LABP2ATLSTnil () => let
        val omits = labs2explst_revapp (omits, ls2es0)
        val () = case+ omits of
          | LABS2EXPLSTcons (l, _, _) => begin
              prerr loc0; prerr ": error(3)";
              prerr ": the pattern does not contain a component with the label [";
              $Lab.prerr_label l;
              prerr "] but it should according to its assigned type.";
              prerr_newline ();
              $Err.abort {void} ()
            end
          | _ => ()
      in
        LABP3ATLSTnil ()
      end // end of [LABP2ATLSTnil]
    | LABP2ATLSTdot () => let
        fun auxcheck
          (loc0: loc_t, omits: labs2explst): void = begin
          case+ omits of
          | LABS2EXPLSTcons (l, s2e, omits) => let
               val () = // linearity check
                 if s2exp_is_linear s2e then begin
                   prerr loc0; prerr ": error(3)";
                   prerr ": the component with the label [";
                   $Lab.prerr_label l;
                   prerr "] is omitted but it is linear";
                   prerr ": only a nonlinear component can be omitted.";
                   prerr_newline ();
                   $Err.abort {void} ()
                 end // end of [if]
            in
              auxcheck (loc0, omits)
            end // end of [LABS2EXPcons]
          | LABS2EXPLSTnil () => ()
        end // end of [auxcheck]
        val omits = labs2explst_revapp (omits, ls2es0)
        val () = auxcheck (loc0, omits)
      in
        LABP3ATLSTdot ()
      end // end of [LABP2ATLSTdot]
  end // end of [aux]
in
  aux (loc0, lp2ts0, ls2es0, LABS2EXPLSTnil ())
end // end of [labp2atlst_tr_dn]

fn p2at_rec_tr_dn
  (p2t0: p2at,
   recknd: int, npf1: int, lp2ts: labp2atlst, s2e0: s2exp): p3at = let
  val loc0 = p2t0.p2at_loc
  val s2e0 = s2exp_whnf s2e0
  val s2e0 = (case+ s2e0.s2exp_node of
    | S2EVar s2V => let
        val tyrecknd = (case+ recknd of
          | 0 => TYRECKINDflt0 () | _ => TYRECKINDbox ()
        ) : tyreckind
        val ls2es = aux (loc0, lp2ts) where {
          fun aux (loc0: loc_t, lp2ts: labp2atlst): labs2explst =
            case+ lp2ts of
            | LABP2ATLSTcons (l, p2t, lp2ts) => let
                val s2e = s2exp_Var_make_srt (p2t.p2at_loc, s2rt_t0ype)
              in
                LABS2EXPLSTcons (l, s2e, aux (loc0, lp2ts))
              end // end of [LABP2ATLSTcons]
            | LABP2ATLSTnil () => LABS2EXPLSTnil ()
            | LABP2ATLSTdot () => begin
                prerr loc0; prerr ": error(3)";
                prerr ": type synthesis for a partial record pattern is not supported.";
                prerr_newline ();
                $Err.abort {labs2explst} ()
              end // end of [LABP2ATLSTdot]
          // end of [aux]
        } // end of [where]
        val s2e_rec = s2exp_tyrec (recknd, npf1, ls2es)
        val s2t_s2V = s2Var_get_srt (s2V) and s2t_s2c_rec = s2e_rec.s2exp_srt
        val () = ( // sort checking
          if lte_s2rt_s2rt (s2t_s2c_rec, s2t_s2V) then () else begin
             prerr loc0; prerr ": error(3)";
             prerr ": the pattern cannot be assigned a type of the sort ["; prerr s2t_s2V; prerr "].";
             prerr_newline ();
             $Err.abort {void} ()
          end // end of [if]
        ) : void // end of [val]
        val () = $SOL.s2exp_equal_solve (loc0, s2e0, s2e_rec)
      in
        s2e_rec
      end // end of [S2EVar]
    | _ => s2e0
  ) : s2exp // end of [val]
  val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
in
  case+ s2e0.s2exp_node of
  | S2Etyrec (tyrecknd, npf2, ls2es) => let
      val () = case+ (recknd, tyrecknd) of
        | (0, TYRECKINDbox _) => begin
            prerr loc0; prerr ": error(3)";
            prerr ": the flat record pattern cannot be assigned a boxed type.";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [0, TYRECKINDbox]
        | (0, _) => ()
        | (_, TYRECKINDbox _) => () // recknd > 0
        | (_, _) => begin // recknd > 0 and tyrecknd is flat
            prerr loc0; prerr ": error(3)";
            prerr ": the boxed record pattern cannot be assigned a flat type.";
            prerr_newline ();
            $Err.abort {void} ()              
          end // end of [_, _]
      val () = pfarity_check (loc0, npf1, npf2)
      val lp3ts = labp2atlst_tr_dn (loc0, lp2ts, ls2es)
    in
      p3at_rec (loc0, s2e0, recknd, npf1, lp3ts)
    end // end of [S2Etyrec]
  | _ => begin
      prerr loc0; prerr ": error(3)";
      prerr ": the record pattern is given a type that is not for records.";
      prerr_newline ();
      $Err.abort {p3at} ()
    end // end of [_]
end // end of [p2at_rec_tr_dn]

(* ****** ****** *)

fn p2at_var_tr_dn (
    p2t0: p2at
  , refknd: int
  , d2v: d2var_t
  , s2e0: s2exp
  ) : p3at = let
  val loc0 = p2t0.p2at_loc
//
// HX-2011-02-22:
// this allows a val to be linear although its value is not
// for instance:
// val x = null : ptr : viewtype
//
  val islin = s2exp_is_linear (s2e0)
//
  val s2e0 = s2exp_whnf (s2e0) // sort of [s2e0] may change
  val () = d2var_set_mastyp (d2v, Some s2e0)
  val () = if islin then ( // linear var
    d2var_set_lin (d2v, 0); d2var_set_fin (d2v, D2VARFINnone ())
  ) // end of [val]
(*
  val () = begin
    print "p2at_var_tr_dn: d2v = "; print d2v; print_newline ();
    print "p2at_var_tr_dn: s2e0 = "; print s2e0; print_newline ();
    print "p2at_var_tr_dn: s2t0 = "; print s2e0.s2exp_srt; print_newline ();
  end // end of [val]
*)
  val s2e = s2exp_opnexi_and_add (loc0, s2e0)
  val () = d2var_set_typ (d2v, Some s2e)
  val p3t0 = p3at_var (loc0, s2e0, refknd, d2v)
(*
  val () = begin
    print "p2at_tr_var_dn: d2v = "; print d2v; print_newline ();
    print "p2at_tr_var_dn: s2e = "; print s2e; print_newline ();
  end // end of [val]
*)
in
  p3t0
end // end of [p2at_var_tr_dn]

(* ****** ****** *)

fn p2at_vbox_tr_dn
  (loc0: loc_t, d2v: d2var_t, s2e0: s2exp): p3at = let
  val s2e0 = s2exp_whnf s2e0
  val s2e0 = (case+ s2e0.s2exp_node of
    | S2EVar s2V => let
        val s2e = s2exp_Var_make_srt (loc0, s2rt_view)
        val s2e_vbox = s2exp_vbox_view_prop (s2e)
        val () = $SOL.s2exp_equal_solve (loc0, s2e0, s2e_vbox)
      in
        s2e_vbox
      end (* end of [S2EVar] *)
    | _ => s2e0
  ) : s2exp // end of [val]
in
  case+ un_s2exp_vbox_view_prop (s2e0) of
  | ~Some_vt s2e_v => let
      val () = d2var_set_mastyp (d2v, Some s2e_v)
      val () = // linearity status
        if s2exp_is_linear s2e_v then begin
          d2var_set_lin (d2v, 0); d2var_set_fin (d2v, D2VARFINvbox s2e_v)
        end // end of [if]
      val s2e_v = s2exp_opnexi_and_add (loc0, s2e_v)
      val () = d2var_set_typ (d2v, Some s2e_v)
      val p3t0 = p3at_vbox (loc0, s2e0, d2v)
    in
      p3t0
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr loc0; prerr ": error(3)";
      prerr ": a [vbox] pattern is assgined the type [";
      prerr s2e0; prerr "] that is not a [vbox] prop.";
      prerr_newline ();
      $Err.abort {p3at} ()
    end // end of [None_vt]
end // end of [p2at_vbox_tr_dn]

(* ****** ****** *)

implement
p2at_tr_dn
  (p2t0, s2e0) = let
  val loc0 = p2t0.p2at_loc
(*
  val () = begin
    print "p2at_tr_dn: p2t0 = "; print p2t0; print_newline ();
    print "p2at_tr_dn: s2e0 = "; print s2e0; print_newline ();
  end // end of [val]
*)
in
  case+ p2t0.p2at_node of
  | P2Tann (p2t, s2e_ann) => let
      val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2e_ann)
      val p3t = p2at_tr_dn (p2t, s2e0)
    in
      p3at_ann (loc0, s2e0, p3t, s2e_ann)
    end // end of [P2Tann]
  | P2Tany () => p2at_any_tr_dn (loc0, s2e0)
  | P2Tas (refknd, d2v, p2t) => let
      val s2e0 = s2exp_whnf s2e0
      val p3t = p2at_tr_dn (p2t, s2e0)
      val () = d2var_set_mastyp (d2v, Some s2e0)
      val s2e_d2v: s2exp = case+ p3t.p3at_typ_lft of
        | None () => s2exp_topize_1 p3t.p3at_typ (* problematic? *)
        | Some s2e => s2e 
      val () = if s2exp_is_linear s2e_d2v then ( // linear var
        d2var_set_lin (d2v, 0); d2var_set_fin (d2v, D2VARFINnone ())
      ) : void // end of [val]
      val () = d2var_set_typ (d2v, Some s2e_d2v)
    in
      p3at_as (loc0, s2e0, refknd, d2v, p3t)
    end // end of [P2Tas]
  | P2Tbool b => p2at_bool_tr_dn (loc0, b, s2e0)
  | P2Tchar c => p2at_char_tr_dn (loc0, c, s2e0)
  | P2Tcon (freeknd, d2c, s2vpss, s2e_con, npf, p2ts) => begin
      p2at_con_tr_dn (loc0, freeknd, d2c, s2vpss, s2e_con, npf, p2ts, s2e0)
    end // end of [P2Tcon]
  | P2Tempty () => let
      val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
      val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2exp_void_t0ype ())
    in
      p3at_empty (loc0, s2e0)
    end // end of [P2Tempty]
  | P2Texist (s2vs, p2t) => begin
      p2at_exist_tr_dn (p2t0, s2vs, p2t, s2e0)
    end // end of [P2Texist]
  | P2Tfloat f(*string*) => let
      val s2e_float = s2exp_double_t0ype ()
      val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2e_float)
    in
      p3at_float (loc0, s2e_float, f)
    end // end of [P2Tfloat]
  | P2Tint (s, i) => let
      val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
    in
      case+ s2e0.s2exp_node of
      | S2Eapp (s2e_fun, s2es_arg) when
          s2cstref_equ_exp (Int_int_t0ype, s2e_fun) => let
          val s2e_arg = case+ s2es_arg of
          | list_cons (s2e, _) => s2e | list_nil () => begin
              prerr_loc_interror loc0;
              prerr ": p2at_tr_dn: P2Tint"; prerr_newline ();
              $Err.abort {s2exp} ()
            end (* end of [list_nil] *)
          // end of [val]
          val () = trans3_env_hypo_add_eqeq (loc0, s2exp_intinf i, s2e_arg)
        in
          p3at_int (loc0, s2exp_int_intinf_t0ype i, s, i)
        end // end of [S2Eapp]
      | _ => let
          val s2e_int = s2exp_int_t0ype ()
          val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2e_int)
        in
          p3at_int (loc0, s2e_int, s, i)
        end // end of [_]
    end // end of [P2Tint]
  | P2Tlst (p2ts) =>
      p2at_lst_tr_dn (loc0, p2ts, s2e0)
    // end of [P2Tlst]
  | P2Trec (recknd, npf, lp2ts) =>
      p2at_rec_tr_dn (p2t0, recknd, npf, lp2ts, s2e0)
    // end of [P2Trec]
  | P2Tstring str => let
      val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
    in
      case+ s2e0.s2exp_node of
      | S2Eapp (s2e_fun, s2es_arg) when
          s2cstref_equ_exp (String_int_type, s2e_fun) => let
          val s2e_arg = case+ s2es_arg of
          | list_cons (s2e, _) => s2e | list_nil _ => begin
              prerr_loc_interror loc0;
              prerr ": p2at_tr_dn: P2Tstring"; prerr_newline ();
              $Err.abort {s2exp} ()
            end // end of [list_nil]
          // end of [val]
          val n = string0_length str
          val n = size1_of_size (n); val n = int1_of_size1 (n)
          val () = trans3_env_hypo_add_eqeq (loc0, s2e_arg, s2exp_int n)
        in
          p3at_string (loc0, s2exp_string_int_type n, str)
        end // end of [S2Eapp]
      | _ => let
          val s2e_string = s2exp_string_type ()
          val () = $SOL.s2exp_tyleq_solve (loc0, s2e0, s2e_string)
        in
          p3at_string (loc0, s2e_string, str)
        end // end of [_]
    end // end of [P2Tstring]
  | P2Tvar (refknd, d2v) => p2at_var_tr_dn (p2t0, refknd, d2v, s2e0)
  | P2Tvbox d2v => let
      val () = the_effect_env_check_ref (loc0)
      val () = the_effect_env_add_eff ($Eff.effect_ref)
    in
      p2at_vbox_tr_dn (loc0, d2v, s2e0)
    end // end of [P2Tvbox]
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": p2at_tr_dn: not implemented yet: p2t0 = "; prerr p2t0;
      prerr_newline ();
      $Err.abort {p3at} ()
    end // end of [_]
end // end of [p2at_tr_dn]

(* ****** ****** *)

implement p2atlst_tr_dn (p2ts, s2es) = case+ p2ts of
  | list_cons (p2t, p2ts) => let
      val+ list_cons (s2e, s2es) = s2es in
      list_cons (p2at_tr_dn (p2t, s2e), p2atlst_tr_dn (p2ts, s2es))
    end (* end of [list_cons] *)
  | list_nil () => list_nil ()
// end of [p2atlst_tr_dn]

(* ****** ****** *)

implement
p2at_arg_tr_up (p2t0) = let
(*
  val () = begin
    print "p2at_arg_tr_up: p2t0 = "; print p2t0; print_newline ();
  end // end of [val]
*)
in
  case+ p2t0.p2at_node of
  | P2Tann (p2t, s2e) => p2at_arg_tr_dn (p2t, s2e)
  | _ => begin case+ p2t0.p2at_typ of
    | Some s2e => p2at_tr_dn (p2t0, s2e)
    | None () => begin
        prerr_loc_interror p2t0.p2at_loc;
        prerr ": p2at_arg_tr_up: p2t0 = "; prerr p2t0; prerr_newline ();
        $Err.abort {p3at} ()
      end // end of [None] 
    end (* end of [_] *)
end (* end of [p2at_arg_tr_up] *)

implement
p2at_arg_tr_dn (p2t0, s2e0) = let
//
(*
  val () = begin
    print "p2at_arg_tr_dn: p2t0 = "; print p2t0; print_newline ();
    print "p2at_arg_tr_dn: s2e0 = "; print s2e0; print_newline ();
  end // end of [val]
*)
//
  val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
  | S2Erefarg (refval, s2e_arg) => let
(*
      val () = begin
        print "p2at_arg_tr_dn: p2t0 = "; print p2t0; print_newline ();
        print "p2at_arg_tr_dn: s2e_arg = "; print s2e_arg; print_newline ();
      end // end of [val]
*)
      fn refknd_check (p2t0: p2at, refknd: int): void =
        if refknd > 0 then begin
          prerr p2t0.p2at_loc; prerr ": error(3)";
          prerr ": misuse of refvar pattern."; prerr_newline ();
          $Err.abort {void} ()
        end // end of [if]
    in
      case+ p2t0.p2at_node of
      | P2Tvar (refknd(*=0*), d2v) => let
(*
          val () = refknd_check (p2t0, refknd) // is there a need?
*)
        in
          case+ refval of
          | _ when refval = 0 => let // call-by-value
              val p3t0 = p2at_var_tr_dn (p2t0, refknd, d2v, s2e_arg)
              val () = d2var_set_mastyp (d2v, Some s2e_arg)
            in
              p3at_set_typ (p3t0, s2e0); p3t0
            end // end of [refval = 0]
          | _ (*refval = 1*) => let // call-by-reference
              val loc0 = p2t0.p2at_loc
              val s2e_arg_opn = s2exp_opnexi_and_add (loc0, s2e_arg)
              val s2v_addr = s2var_make_id_srt (d2var_get_sym d2v, s2rt_addr)
              val s2e_addr = s2exp_var s2v_addr
              val () = trans3_env_add_svar s2v_addr
              val () = d2var_set_addr (d2v, Some s2e_addr)
              val () = trans3_env_hypo_add_prop (loc0, s2p) where {
                val s2p = s2exp_gt_addr_addr_bool (s2e_addr, s2exp_null_addr ())
              } // end of [val]
              val d2v_view = d2var_ptr_viewat_make_none (d2v)
              val () = d2var_set_view (d2v, D2VAROPTsome d2v_view) // [d2v] is mutable
              val () = the_d2varset_env_add (d2v_view)
              val s2e_arg_at = s2exp_at_viewt0ype_addr_view (s2e_arg, s2e_addr)
              val () = d2var_set_mastyp (d2v_view, Some s2e_arg_at)
              val () = d2var_set_typ (d2v_view, Some s2e_at) where {
                val s2e_at = s2exp_at_viewt0ype_addr_view (s2e_arg_opn, s2e_addr)
              } // end of [val]
            in
              p3at_var (loc0, s2e0, refknd, d2v)
            end // end of [refval = 1]
          end (* end of [P2Tvar] *)
      | P2Tas (refknd(*=0*), d2v, p2t) => let
(*
          val () = refknd_check (p2t0, refknd) // is there a need?
*)
        in
          case+ refval of
          | _ when refval = 0 => let // call-by-value
              val loc0 = p2t0.p2at_loc;
              val p3t = p2at_tr_dn (p2t, s2e_arg)
              val () = d2var_set_mastyp (d2v, Some s2e_arg)
              val () = d2var_set_typ (d2v, os2e) where { val os2e = (
                case+ p3t.p3at_typ_lft of
                | None () => Some (s2exp_topize_1 p3t.p3at_typ) | os2e (*Some*) => os2e
                ) : s2expopt
              } // end of [where]
            in
              p3at_as (loc0, s2e0, refknd, d2v, p3t)
            end // end of [_ when refvar = 0]
          | _ (*refval = 1*) => let // call-by-reference
              val loc0 = p2t0.p2at_loc;
              val p3t = p2at_tr_dn (p2t, s2e_arg)
              val s2v_addr = s2var_make_id_srt (d2var_get_sym d2v, s2rt_addr)
              val s2e_addr = s2exp_var s2v_addr
              val () = trans3_env_add_svar s2v_addr
              val () = d2var_set_addr (d2v, Some s2e_addr)
              val () = trans3_env_hypo_add_prop (loc0, s2p) where {
                val s2p = s2exp_gt_addr_addr_bool (s2e_addr, s2exp_null_addr ())
              } // end of [where]
              val d2v_view = d2var_ptr_viewat_make_none (d2v)
              val () = d2var_set_view (d2v, D2VAROPTsome d2v_view) // [d2v] is mutable
              val () = the_d2varset_env_add (d2v_view)
              val s2e_arg_at = s2exp_at_viewt0ype_addr_view (s2e_arg, s2e_addr)
              val () = d2var_set_mastyp (d2v_view, Some s2e_arg_at)
              val () = d2var_set_typ (d2v_view, Some s2e_at) where {
                val s2e = (case+ p3t.p3at_typ_lft of
                  | Some s2e => s2e | None () => s2exp_topize_1 p3t.p3at_typ
                ) : s2exp // end of [val]
                val s2e_at = s2exp_at_viewt0ype_addr_view (s2e, s2e_addr)
              } // end of [val]
            in
              p3at_as (loc0, s2e0, refknd, d2v, p3t)
            end // end of [_ when refval = 1]
          end (* end of [P2Tas] *)
      | _ => begin
          prerr p2t0.p2at_loc; prerr ": error(3)";
          prerr ": the pattern is expected to be a variable but it is not.";
          prerr_newline ();
          $Err.abort {p3at} ()
        end (* end of [_] *)
    end // end of [S2Erefarg]
  | S2Evararg s2e_arg => let // va_start ...
(*
** HX: this special argument is to be set as a pointer to a value of of the type
** [va_list] (declared in stdarg.h)
*)
    in
      case+ p2t0.p2at_node of
      | P2Tvar (refknd(*=0*), d2v) => let
          val loc0 = p2t0.p2at_loc
          val s2e_valst0 = s2exp_va_list_viewt0ype ()
          val s2e_valst1 = s2exp_va_list_types_viewt0ype (s2e_arg)
          val s2v_addr = s2var_make_id_srt (d2var_get_sym d2v, s2rt_addr)
          val s2e_addr = s2exp_var s2v_addr
          val () = trans3_env_add_svar s2v_addr
          val () = d2var_set_addr (d2v, Some s2e_addr)
          val d2v_view = d2var_ptr_viewat_make_none (d2v)
          val () = d2var_set_view (d2v, D2VAROPTsome d2v_view) // [d2v] is mutable
          val () = the_d2varset_env_add (d2v_view)
          val s2e_valst0_at = s2exp_at_viewt0ype_addr_view (s2e_valst0, s2e_addr)
          val () = d2var_set_mastyp (d2v_view, Some s2e_valst0_at)
          val s2e_valst1_at = s2exp_at_viewt0ype_addr_view (s2e_valst1, s2e_addr)
          val () = d2var_set_typ (d2v_view, Some s2e_valst1_at)
          // note that [va_end] is to be done explicitly!!!
          val () = d2var_set_fin (
            d2v_view, D2VARFINsome s2e_valst0_top_at
          ) where {
            val s2e_valst0_top = s2exp_topize_0 (s2e_valst0)
            val s2e_valst0_top_at = s2exp_at_viewt0ype_addr_view (s2e_valst0_top, s2e_addr)
          } // end of [val]
        in
          p3at_var (loc0, s2e0, refknd, d2v) // HX: this one translates to argtmpref
        end // end of [P2Tvar]
      | _ => begin
          prerr p2t0.p2at_loc; prerr ": error(3)";
          prerr ": the pattern is expected to be a variable but it is not.";
          prerr_newline ();
          $Err.abort {p3at} ()
        end (* end of [_] *)
    end // end of [S2Evararg]
  | _ => p2at_tr_dn (p2t0, s2e0)
end (* end of [p2at_arg_tr_dn] *)

fn p2at_proofize (p2t: p2at) = let
  fun loop (d2vs: d2varlst): void = case+ d2vs of
    | list_cons (d2v, d2vs) => (d2var_set_isprf (d2v, true); loop d2vs)
    | list_nil () => ()
  // end of [loop]  
in
  loop (d2varlst_of_d2varlstord p2t.p2at_dvs)
end (* end of [p2at_proofize] *)

implement
p2atlst_arg_tr_up (npf, p2ts) = let
  fun aux {n:nat} .<n>. // nontailrec
    (i: int, p2ts: p2atlst n): p3atlst n = case+ p2ts of
    | list_cons (p2t, p2ts) => let
        val () = (if i > 0 then p2at_proofize p2t) in
        list_cons (p2at_arg_tr_up p2t, aux (i - 1, p2ts))
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux]
in
  aux (npf, p2ts)
end (* end of [p2atlst_arg_tr_up] *)

implement
p2atlst_arg_tr_dn (npf, p2ts, s2es) = let
  fun aux {n:nat} .<n>.
    (i: int, p2ts: p2atlst n, s2es: s2explst n): p3atlst n =
    case+ p2ts of
    | list_cons (p2t, p2ts) => let
        val+ list_cons (s2e, s2es) = s2es
        val () = if i > 0 then p2at_proofize p2t 
        val p3t = p2at_arg_tr_dn (p2t, s2e)
      in
        list_cons (p3t, aux (i-1, p2ts, s2es))
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux]  
in
  aux (npf, p2ts, s2es)
end (* end of [p2atlst_arg_tr_dn] *)

(* ****** ****** *)

(* end of [ats_trans3_pat.dats] *)
