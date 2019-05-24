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
// Time: October 2007

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%}

(* ****** ****** *)

staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

overload = with $Stamp.eq_stamp_stamp

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_staexp2)"

(* ****** ****** *)

implement eq_tyreckind_tyreckind (k1, k2) = begin
  case+ (k1, k2) of
  | (TYRECKINDbox (), TYRECKINDbox ()) => true
  | (TYRECKINDflt0 (), TYRECKINDflt0 ()) => true
  | (TYRECKINDflt1 s1, TYRECKINDflt1 s2) => (s1 = s2)
  | (TYRECKINDflt_ext s1, TYRECKINDflt_ext s2) => (s1 = s2)
  | (_, _) => false
end // end of [eq_tyreckind_tyreckind]

(* ****** ****** *)

val s2tb_addr: s2rtbas = S2RTBASpre ($Sym.symbol_ADDR)
val s2tb_bool: s2rtbas = S2RTBASpre ($Sym.symbol_BOOL)
val s2tb_char: s2rtbas = S2RTBASpre ($Sym.symbol_CHAR)
val s2tb_cls: s2rtbas = S2RTBASpre ($Sym.symbol_CLS)
val s2tb_eff: s2rtbas = S2RTBASpre ($Sym.symbol_EFF)
val s2tb_int: s2rtbas = S2RTBASpre ($Sym.symbol_INT)

implement s2rt_addr = S2RTbas s2tb_addr
implement s2rt_bool = S2RTbas s2tb_bool
implement s2rt_char = S2RTbas s2tb_char
implement s2rt_cls = S2RTbas s2tb_cls
implement s2rt_eff = S2RTbas s2tb_eff
implement s2rt_int = S2RTbas s2tb_int

(* ****** ****** *)

#define PROOF_LEVEL 2

val s2tb_prop: s2rtbas =
  S2RTBASimp ($Sym.symbol_PROP, PROOF_LEVEL, 0)
val s2tb_type: s2rtbas =
  S2RTBASimp ($Sym.symbol_TYPE, 0, 0)
val s2tb_t0ype: s2rtbas =
  S2RTBASimp ($Sym.symbol_T0YPE, 1, 0)
val s2tb_view: s2rtbas =
  S2RTBASimp ($Sym.symbol_VIEW, PROOF_LEVEL, 1)
val s2tb_viewtype: s2rtbas =
  S2RTBASimp ($Sym.symbol_VIEWTYPE, 0, 1)
val s2tb_viewt0ype: s2rtbas =
  S2RTBASimp ($Sym.symbol_VIEWT0YPE, 1, 1)
val s2tb_types: s2rtbas = (* it is like [t@ype] *)
  S2RTBASimp ($Sym.symbol_TYPES, 1, 0)

implement s2rt_prop = S2RTbas s2tb_prop
implement s2rt_type = S2RTbas s2tb_type
implement s2rt_t0ype = S2RTbas s2tb_t0ype
implement s2rt_types = S2RTbas s2tb_types
implement s2rt_view = S2RTbas s2tb_view
implement s2rt_viewtype = S2RTbas s2tb_viewtype
implement s2rt_viewt0ype = S2RTbas s2tb_viewt0ype

(* ****** ****** *)

implement s2rt_linearize
  (s2t: s2rt): s2rt = let
  var s2t: s2rt = s2t; var err: int = 0
  val () = case+ s2t of
    | S2RTbas s2tb => begin case+ s2tb of
      | S2RTBASimp (name, prf, lin) => begin
          s2t := S2RTbas (S2RTBASimp (name, prf, 1))
        end // end of [S2RTBASimp]
      | _ => err := 1
      end // end of [S2RTbas]
    | _ => err := 1
  val () = if err > 0 then begin
    prerr_interror ();
    prerr ": s2rt_linearize: s2t = "; prerr s2t; prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
in
  s2t
end // end of [s2rt_linearize]

(* ****** ****** *)

typedef s2rtdat_struct = @{
  s2rtdat_sym= sym_t // name
, s2rtdat_conlst= s2cstlst
, s2rtdat_stamp= stamp_t // unique stamp
} // end of [s2rtdat_struct]

local

assume s2rtdat_t = [l:addr] (vbox (s2rtdat_struct @ l) | ptr l)

in // in of [local]

implement s2rtdat_make (id) = let
  val stamp = $Stamp.s2rtdat_stamp_make ()
  val (pf_gc, pf | p) =
    ptr_alloc_tsz {s2rtdat_struct} (sizeof<s2rtdat_struct>)
  // end of [val]
  prval () = free_gc_elim {s2rtdat_struct?} (pf_gc)
  val () = p->s2rtdat_sym := id
  val () = p->s2rtdat_conlst := S2CSTLSTnil ()
  val () = p->s2rtdat_stamp := stamp
  val (pfbox | ()) = vbox_make_view_ptr (pf | p)
in // in of [let]
  (pfbox | p)
end // end of [s2rtdat_make]

implement s2rtdat_get_sym (s2td) =
  let val (vbox pf | p) = s2td in p->s2rtdat_sym end
// end of [s2rtdat_get_sym]

implement s2rtdat_get_conlst (s2td) =
  let val (vbox pf | p) = s2td in p->s2rtdat_conlst end
// end of [s2rtdat_conlst]

implement s2rtdat_set_conlst (s2td, s2cs) =
  let val (vbox pf | p) = s2td in p->s2rtdat_conlst := s2cs end
// end of [s2rtdat_conlst]

implement s2rtdat_get_stamp (s2td) =
  let val (vbox pf | p) = s2td in p->s2rtdat_stamp end
// end of [s2rtdat_get_stamp]

implement eq_s2rtdat_s2rtdat (s2td1, s2td2) = let
  val stamp1 =
    let val (vbox pf1 | p1) = s2td1 in p1->s2rtdat_stamp end
  // end of [val]
  val stamp2 =
    let val (vbox pf2 | p2) = s2td2 in p2->s2rtdat_stamp end
  // end of [val]
in
  stamp1 = stamp2
end // end of [eq_s2rtdat_s2rtdat]

end // end of [local]

(* ****** ****** *)

implement s2rt_fun
  (s2ts_arg, s2t_res) =  S2RTfun (s2ts_arg, s2t_res)
// end of [s2rt_fun]

implement s2rt_tup (s2ts_elt) = S2RTtup s2ts_elt

implement un_s2rt_fun (s2t) = case+ s2t of
  | S2RTfun (s2ts, s2t) => Some_vt @(s2ts, s2t) | _ => None_vt ()
// end of [un_s2rt_fun]

implement un_s2rt_tup (s2t) = case+ s2t of
  | S2RTtup s2ts => Some_vt (s2ts) | _ => None_vt ()
// end of [un_s2rt_tup]

(* ****** ****** *)

implement s2arg_make (loc, id, os2t) = '{
  s2arg_loc= loc, s2arg_sym= id, s2arg_srt= os2t
} // end of [s2arg_make]

(* ****** ****** *)

implement sp2at_con (loc, s2c, s2vs_arg) = let
  val s2e_pat = s2exp_cstapp (s2c, s2es_arg) where {
    val s2es_arg = $Lst.list_map_fun (s2vs_arg, s2exp_var)
  } // end of [val]
  val sp2t = SP2Tcon (s2c, s2vs_arg)
in '{
  sp2at_loc= loc, sp2at_exp= s2e_pat, sp2at_node = sp2t
} end // end of [sp2at_con]

(* ****** ****** *)

implement s2exp_app_srt
  (s2t, s2e_fun, s2es_arg) = '{
  s2exp_srt= s2t, s2exp_node= S2Eapp (s2e_fun, s2es_arg)
} (* end of [s2exp_app_srt] *)

(* ****** ****** *)

implement s2exp_app_wind (s2e_fun, s2ess_arg) = let
fun loop (s2t: s2rt, s2e: s2exp, s2ess: s2explstlst): s2exp =
  case+ s2ess of
  | s2es :: s2ess => begin case+ un_s2rt_fun s2t of
    | ~Some_vt s2ts_s2t => let
        val s2t = s2ts_s2t.1
        val s2e = s2exp_app_srt (s2t, s2e, s2es)
      in
        loop (s2t, s2e, s2ess)
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr_interror (); prerr ": s2exp_app_wind"; prerr_newline ();
        $Err.abort ()
      end // end of [None_vt]
    end (* end of [::] *)
  | nil () => s2e
in
  loop (s2e_fun.s2exp_srt, s2e_fun, s2ess_arg)
end // end of [s2exp_app_wind]

(* ****** ****** *)

implement s2exp_char (chr) = '{
  s2exp_srt= s2rt_char, s2exp_node= S2Echar chr
} // end of [s2exp_char]

implement s2exp_clo_srt (s2t, knd, s2e) = '{
  s2exp_srt= s2t, s2exp_node= S2Eclo (knd, s2e)
} // end of [s2exp_clo_srt]

implement s2exp_confun (npf, s2es_arg, s2e_res) = '{
  s2exp_srt= s2rt_type
, s2exp_node= S2Efun (
    $Syn.FUNCLOfun (), 0(*lin*), S2EFFnil (), npf, s2es_arg, s2e_res
  ) // end of [S2Efun]
} (* end of [s2exp_confun] *)

implement s2exp_crypt (s2e) = '{
  s2exp_srt= s2e.s2exp_srt, s2exp_node= S2Ecrypt (s2e)
} // end of [s2exp_crypt]

implement s2exp_cst (s2c) = '{
  s2exp_srt= s2cst_get_srt s2c, s2exp_node= S2Ecst s2c
} // end of [s2exp_cst]

(* ****** ****** *)

implement
s2exp_cstapp
  (s2c_fun, s2es_arg) = let
  val s2t_fun = s2cst_get_srt s2c_fun
  and s2e_fun = s2exp_cst s2c_fun
in
  case+ un_s2rt_fun s2t_fun of
  | ~Some_vt s2ts_arg_s2t_res => begin
      s2exp_app_srt (s2ts_arg_s2t_res.1, s2e_fun, s2es_arg)
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr_interror ();
      prerr "s2exp_cstapp: the sort of the static constant [";
      prerr s2c_fun;
      prerr "] is not functional: ";
      prerr s2t_fun;
      prerr_newline ();
      $Err.abort ()
    end // end of [None_vt]
end // end of [s2exp_cstapp]

(* ****** ****** *)

implement
s2exp_datconptr (d2c, s2es_arg) = let
  val arity_real = d2con_get_arity_real d2c; val s2t =
    (if arity_real > 0 then s2rt_viewtype else s2rt_type): s2rt
in '{
  s2exp_srt= s2t, s2exp_node= S2Edatconptr (d2c, s2es_arg)
} end // end of [s2exp_datconptr]

//
// HX: [s2es_arg] cannot be empty!
//
implement
s2exp_datcontyp (d2c, s2es_arg) = '{
  s2exp_srt= s2rt_viewtype, s2exp_node= S2Edatcontyp (d2c, s2es_arg)
} // end of [s2exp_datcontyp]

(* ****** ****** *)

implement s2exp_eff (s2fe): s2exp = '{
  s2exp_srt= s2rt_eff, s2exp_node= S2Eeff s2fe
} // end of [s2exp_eff]

implement
s2exp_eqeq (s2e1, s2e2) = '{
  s2exp_srt= s2rt_bool, s2exp_node= S2Eeqeq (s2e1, s2e2)
} // end of [s2exp_eqeq]

implement
s2exp_exi
  (s2vs, s2ps, s2e_scope) = begin
  case+ (s2vs, s2ps) of
  | (nil (), nil ()) => s2e_scope
  | (_, _) => '{
      s2exp_srt= s2e_scope.s2exp_srt
    , s2exp_node= S2Eexi (s2vs, s2ps, s2e_scope)
    } // end of [s2exp_exi]
end // end of [s2exp_exi]

implement
s2exp_extype_srt (s2t, name, arglst) = '{
  s2exp_srt= s2t, s2exp_node= S2Eextype (name, arglst)
} // end of [s2exp_extype_srt]

implement s2exp_fun_srt
  (s2t, fc, lin, s2fe, npf, _arg, _res) = '{
  s2exp_srt= s2t, s2exp_node= S2Efun (fc, lin, s2fe, npf, _arg, _res)
} // end of [s2exp_fun_srt]

implement s2exp_int (i(*int*)) = '{
  s2exp_srt= s2rt_int, s2exp_node= S2Eint i
} // end of [s2exp_int]

implement s2exp_int_0 = s2exp_int 0
implement s2exp_int_1 = s2exp_int 1

implement s2exp_intinf (i(*intinf*)) = '{
  s2exp_srt= s2rt_int, s2exp_node= S2Eintinf i
} // end of [s2exp_intinf]

implement s2exp_lam_srt
  (s2t_fun, s2vs_arg, s2e_body) = '{
  s2exp_srt= s2t_fun, s2exp_node= S2Elam (s2vs_arg, s2e_body)
} // end of [s2exp_lam_srt]

implement s2exp_metfn
  (d2vopt(*stamp*), met, s2e_fun) = '{
  s2exp_srt= s2e_fun.s2exp_srt
, s2exp_node= S2Emetfn (d2vopt, met, s2e_fun)
} // end of [s2exp_metfn]

implement s2exp_metlt (s2es1, s2es2) = '{
  s2exp_srt= s2rt_bool, s2exp_node= S2Emetlt (s2es1, s2es2)
} // end of [s2exp_metlt]

(*
// HX-2010-12-04: inadequate design
implement s2exp_named (s2t, name, s2e) = '{
  s2exp_srt= s2t, s2exp_node= S2Enamed (name, s2e)
} // end of [s2exp_named]
*)

implement s2exp_out (s2e) = '{
  s2exp_srt= s2rt_t0ype, s2exp_node= S2Eout s2e
} // end of [s2exp_out]

implement s2exp_proj (s2e, s2l) = '{
  s2exp_srt= s2rt_addr, s2exp_node= S2Eproj (s2e, s2l)
} // end of [s2exp_proj]

implement s2exp_read (s2e_v, s2e) = let
  val s2t: s2rt = s2rt_readize (s2e.s2exp_srt)
in '{
  s2exp_srt= s2t, s2exp_node= S2Eread (s2e_v, s2e)
} end // end of [s2exp_read]

implement
s2exp_read_srt (s2t, s2e_v, s2e) = '{
  s2exp_srt= s2t, s2exp_node= S2Eread (s2e_v, s2e)
} // end of [s2exp_read_srt]

implement
un_s2exp_read (s2e) = begin
  case+ s2e.s2exp_node of
  | S2Eread (s2e_v, s2e_vt) => Some_vt @(s2e_v, s2e_vt)
  | _ => None_vt ()
end // end of [un_s2exp_read]

(* ****** ****** *)

implement
s2exp_refarg (refval, s2e) = '{
  s2exp_srt= s2e.s2exp_srt, s2exp_node= S2Erefarg (refval, s2e)
} // end of [s2exp_refarg]

implement
un_s2exp_refarg_arg (s2e) =
  case+ s2e.s2exp_node of S2Erefarg (_, s2e_arg) => s2e_arg | _ => s2e
// end of [un_s2exp_refarg_arg]

implement
s2exp_sel_srt (s2t, s2e, i) = '{
  s2exp_srt= s2t, s2exp_node= S2Esel (s2e, i)
} // end of [s2exp_sel_srt]

implement
s2exp_size (s2ze) = '{
  s2exp_srt= s2rt_int, s2exp_node= S2Esize s2ze
} // end of [s2exp_size]

implement
s2exp_sizeof (s2e) = '{
  s2exp_srt= s2rt_int, s2exp_node= S2Esizeof s2e
} // end of [s2exp_sizeof]

implement
s2exp_top_srt (s2t, knd, s2e) = '{
  s2exp_srt= s2t, s2exp_node= S2Etop (knd, s2e)
} // end of [s2exp_top_srt]

implement
s2exp_tup_srt (s2t, s2es) = '{
  s2exp_srt= s2t, s2exp_node= S2Etup s2es
} // end of [s2exp_tup_srt]

implement
s2exp_tyarr (s2e_elt, s2ess_dim) = let
  val s2t: s2rt =
    if s2exp_is_linear s2e_elt then s2rt_viewt0ype else s2rt_t0ype
in '{
  s2exp_srt= s2t, s2exp_node= S2Etyarr (s2e_elt, s2ess_dim)
} end // end of [s2exp_tyarr]

implement
s2exp_tyleq (knd, s2e1, s2e2) = '{
  s2exp_srt= s2rt_bool, s2exp_node= S2Etyleq (knd, s2e1, s2e2)
} // end of [s2exp_tyleq]

(* s2exp_list: [s2es] consists of types (not viewtypes) *)
implement
s2exp_tylst (s2es) = '{
  s2exp_srt= s2rt_types, s2exp_node= S2Etylst s2es
} // end of [s2exp_tylst]

implement
s2exp_tyrec_srt
  (s2t, k, npf, ls2es) = '{
  s2exp_srt= s2t, s2exp_node= S2Etyrec (k, npf, ls2es)
} // end of [s2exp_tyrec_srt]

implement
s2exp_uni
  (s2vs, s2ps, s2e_scope) = begin
  case+ (s2vs, s2ps) of
  | (nil (), nil ()) => s2e_scope
  | (_, _) => '{
      s2exp_srt= s2e_scope.s2exp_srt
    , s2exp_node= S2Euni (s2vs, s2ps, s2e_scope)
    } // end of [s2exp_uni]
end // end of [s2exp_uni]

implement
s2exp_union_srt (s2t, stamp, s2i, ls2es) = '{
  s2exp_srt= s2t, s2exp_node= S2Eunion (stamp, s2i, ls2es)
} // end of [s2exp_union_srt]

implement
s2exp_Var (s2V) = '{
  s2exp_srt= s2Var_get_srt s2V, s2exp_node= S2EVar s2V
} // end of [s2exp_Var]

implement
s2exp_var (s2v) = '{
  s2exp_srt= s2var_get_srt s2v, s2exp_node= S2Evar s2v
} // end of [s2exp_var]

implement
s2exp_vararg (s2e_arg) = '{
  s2exp_srt= s2rt_t0ype, s2exp_node= S2Evararg s2e_arg
} // end of [s2exp_vararg]

implement
s2exp_wth (s2e, wths2es) = '{
  s2exp_srt= s2e.s2exp_srt, s2exp_node= S2Ewth (s2e, wths2es)
} // end of [s2exp_wth]

(* ****** ****** *)

implement
s2exparg_one (loc) = '{
  s2exparg_loc= loc, s2exparg_node= S2EXPARGone ()
} // end of [s2exparg_one]

implement
s2exparg_all (loc) = '{
  s2exparg_loc= loc, s2exparg_node= S2EXPARGall ()
} // end of [s2exparg_all]

implement
s2exparg_seq (loc, s2es) = '{
  s2exparg_loc= loc, s2exparg_node= S2EXPARGseq (s2es)
} // end of [s2exparg_seq]

(* ****** ****** *)

extern typedef "s2exp_t" = s2exp

%{$
//
ats_void_type
atsopt_s2exp_set_srt
  (ats_ptr_type s2e, ats_ptr_type s2t) {
  ((s2exp_t)s2e)->atslab_s2exp_srt = s2t ; return ;
} /* end of [atsopt_s2exp_set_srt] */
//
ats_bool_type
atsopt_eqref_s2exp_s2exp
  (ats_ptr_type s2e1, ats_ptr_type s2e2) {
  return (s2e1 == s2e2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atsopt_eqref_s2exp_s2exp] */
//
%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_staexp2.dats] *)
