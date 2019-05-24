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
// Time: November 2007

(* ****** ****** *)

staload Err = "ats_error.sats"
staload TransEnv2 = "ats_trans2_env.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_stadyncst2.sats"

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol
overload prerr with $Sym.prerr_symbol

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_stadyncst2)"

(* ****** ****** *)

typedef s2cstref_struct = @{
  sym= sym_t, cst= Option s2cst_t
} // end of [s2cstref_struct]

typedef s2cstref =
  [l:addr] (vbox (s2cstref_struct @ l) | ptr l)
assume s2cstref_t = s2cstref

implement s2cstref_make (name) = let
  val id = $Sym.symbol_make_string name
  val (pfgc, pfat | p) = begin
    ptr_alloc_tsz {s2cstref_struct} (sizeof<s2cstref_struct>)
  end // end of [val]
  prval () = free_gc_elim {s2cstref_struct?} (pfgc)
  val () = (p->sym := id; p->cst := None ())
  val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
in
  (pfbox | p)
end  // end of [s2cstref_make]

(* ****** ****** *)

implement s2cstref_get_cst (r) = let
  val os2c = let val (vbox pf | p) = r in p->cst end
in
  case+ os2c of
  | Some s2c => s2c
  | None () => let
      val id = let val (vbox pf | p) = r in p->sym end
      val os2c = (
        case+ $TransEnv2.the_s2expenv_pervasive_find (id) of
        | ~Some_vt s2i => begin case+ s2i of
          | S2ITEMcst (S2CSTLSTcons (s2c, _)) => let
              val (vbox pf | p) = r; val os2c = Some s2c
            in
              p->cst := os2c; os2c
            end
          | _ => None ()
          end // end of [Some_vt]
        | ~None_vt () => None ()
      ) : Option s2cst_t
    in
      case+ os2c of
      | Some s2c => s2c | None () => begin
          prerr_interror ();
          prerr ": s2cstref_get_cst: ";
          prerr "the pervasive static constant [";
          prerr id; prerr "] is not available.";
          prerr_newline ();
          $Err.abort {s2cst_t} ()
        end // end of [None]
    end (* end of [None] *)
end // end of [s2cstref_get_cst]

(* ****** ****** *)

implement
s2cstref_get_exp
  (s2cref, os2es) = let
  val s2c =
    s2cstref_get_cst (s2cref)
  // end of [val]
  val s2e = s2exp_cst s2c
in
  case+ os2es of
  | ~Some_vt s2es => let
      val s2t_res = (
      case+ s2cst_get_srt s2c of
      | S2RTfun (_, s2t_res) => s2t_res
      | _ => begin
          prerr_interror ();
          prerr ": s2cstref_get_exp: s2c = "; prerr s2c; prerr_newline ();
          $Err.abort {s2rt} ()
        end // end of [_]
      ) : s2rt // end of [val]
    in
      s2exp_app_srt (s2t_res, s2e, s2es)
    end // end of [Some_vt]
  | ~None_vt () => s2e
end (* end of [s2cstref_get_exp] *)

implement s2cstref_unget_exp (s2cref, s2e) = begin
  case+ s2e.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin case+ s2e_fun.s2exp_node of
    | S2Ecst (s2c) => begin
        if s2cstref_get_cst (s2cref) = s2c then Some_vt (s2es_arg) else None_vt ()
      end
    | _ => None_vt ()
    end
  | S2Ecst (s2c) => begin
      if s2cstref_get_cst (s2cref) = s2c then Some_vt (list_nil ()) else None_vt ()
    end
  | _ => None_vt ()
end // end of [s2cstref_unget_exp]

(* ****** ****** *)

implement
s2cstref_equ_cst (s2cref, s2c) =
  eq_s2cst_s2cst (s2cstref_get_cst s2cref, s2c)
// end of [s2cstref_equ_cst]

implement
s2cstref_equ_exp
  (s2cref, s2e) = begin
  case+ s2e.s2exp_node of
  | S2Eapp (s2e, _) => s2cstref_equ_exp (s2cref, s2e)
  | S2Ecst s2c => s2cstref_equ_cst (s2cref, s2c)
  | _ => false
end // end of [s2cstref_equ_exp]

(* ****** ****** *)

implement True_bool = s2cstref_make "true_bool"
implement False_bool = s2cstref_make "false_bool"

(* ****** ****** *)

implement Bool_t0ype = s2cstref_make "bool_t0ype"
implement Bool_bool_t0ype = s2cstref_make "bool_bool_t0ype"
implement Byte_t0ype = s2cstref_make "byte_t0ype"
implement Char_t0ype = s2cstref_make "char_t0ype"
implement Char_char_t0ype = s2cstref_make "char_char_t0ype"
implement Double_t0ype = s2cstref_make "double_t0ype"
implement Double_long_t0ype = s2cstref_make "double_long_t0ype"
implement Float_t0ype = s2cstref_make "float_t0ype"
implement Int_t0ype = s2cstref_make "int_t0ype"
implement Int_int_t0ype = s2cstref_make "int_int_t0ype"
implement Lint_t0ype = s2cstref_make "int_long_t0ype"
implement Lint_int_t0ype = s2cstref_make "lint_int_t0ype"
implement Opt_viewt0ype_bool_viewt0ype = s2cstref_make "opt_viewt0ype_bool_viewt0ype"
implement Ptr_type = s2cstref_make "ptr_type"
implement Ptr_addr_type = s2cstref_make "ptr_addr_type"
implement Ref_viewt0ype_type = s2cstref_make "ref_viewt0ype_type"
implement Size_t0ype = s2cstref_make "size_t0ype"
implement Size_int_t0ype = s2cstref_make "size_int_t0ype"
implement Ssize_t0ype = s2cstref_make "ssize_t0ype"
implement Ssize_int_t0ype = s2cstref_make "ssize_int_t0ype"
implement Strbuf_t0ype = s2cstref_make "strbuf_t0ype"
implement Strbuf_int_int_t0ype = s2cstref_make "strbuf_int_int_t0ype"
implement String_type = s2cstref_make "string_type"
implement String_int_type = s2cstref_make "string_int_type"
implement Uint_t0ype = s2cstref_make "uint_t0ype"
implement Uint_int_t0ype = s2cstref_make "uint_int_t0ype"
implement Ulint_t0ype = s2cstref_make "uint_long_t0ype"
implement Ulint_int_t0ype = s2cstref_make "ulint_int_t0ype"
implement Void_t0ype = s2cstref_make "void_t0ype"

(* ****** ****** *)

implement Int_long_t0ype =
  s2cstref_make "int_long_t0ype"

implement Int_long_long_t0ype =
  s2cstref_make "int_long_long_t0ype"

implement Uint_long_t0ype =
  s2cstref_make "uint_long_t0ype"

implement Uint_long_long_t0ype =
  s2cstref_make "uint_long_long_t0ype"

implement Int_short_t0ype =
  s2cstref_make "int_short_t0ype"

implement Int_short_short_t0ype =
  s2cstref_make "int_short_short_t0ype"

implement Uint_short_t0ype =
  s2cstref_make "uint_short_t0ype"

implement Uint_short_short_t0ype =
  s2cstref_make "uint_short_short_t0ype"

(* ****** ****** *)

implement Bottom_t0ype_exi =
  s2cstref_make "bottom_t0ype_exi"

implement Bottom_t0ype_uni =
  s2cstref_make "bottom_t0ype_uni"

implement Bottom_viewt0ype_exi =
  s2cstref_make "bottom_viewt0ype_exi"

implement Bottom_viewt0ype_uni =
  s2cstref_make "bottom_viewt0ype_uni"

implement Exception_viewtype =
  s2cstref_make "exception_viewtype"

(* ****** ****** *)

implement Array_viewt0ype_int_type =
  s2cstref_make "array_viewt0ype_int_type"

implement Array_viewt0ype_int_viewtype = 
  s2cstref_make "array_viewt0ype_int_viewtype"

implement Arrayptrsize_viewt0ype_int_viewt0ype = 
  s2cstref_make "arrayptrsize_viewt0ype_int_viewt0ype"

(* ****** ****** *)

implement List_t0ype_int_type =
  s2cstref_make "list_t0ype_int_type"

implement List_viewt0ype_int_viewtype = 
  s2cstref_make "list_viewt0ype_int_viewtype"

(* ****** ****** *)

implement At_viewt0ype_addr_view =
  s2cstref_make "at_viewt0ype_addr_view"

(* ****** ****** *)

implement Crypt_viewt0ype_viewt0ype =
  s2cstref_make "crypt_viewt0ype_viewt0ype"

(* ****** ****** *)

implement Clo_viewt0ype_viewt0ype =
  s2cstref_make "clo_viewt0ype_viewt0ype"

implement Cloptr_viewt0ype_viewtype =
  s2cstref_make "cloptr_viewt0ype_viewtype"

implement Cloref_t0ype_type =
  s2cstref_make "cloref_t0ype_type"

(* ****** ****** *)

implement Lazy_t0ype_type =
  s2cstref_make "lazy_t0ype_type"

implement Lazy_viewt0ype_viewtype =
  s2cstref_make "lazy_viewt0ype_viewtype"

(* ****** ****** *)

implement Printf_c_types_type =
  s2cstref_make "printf_c_types_type"

(* ****** ****** *)

implement Va_list_viewt0ype =
  s2cstref_make "va_list_viewt0ype"

implement Va_list_types_viewt0ype =
  s2cstref_make "va_list_types_viewt0ype"

(* ****** ****** *)

implement Vbox_view_prop =
  s2cstref_make "vbox_view_prop"

(* ****** ****** *)

implement Neg_bool_bool = s2cstref_make "neg_bool_bool"
implement Add_bool_bool_bool = s2cstref_make "add_bool_bool_bool"
implement Mul_bool_bool_bool = s2cstref_make "mul_bool_bool_bool"

implement Eq_bool_bool_bool = s2cstref_make "eq_bool_bool_bool"
implement Neq_bool_bool_bool = s2cstref_make "neq_bool_bool_bool"

(* ****** ****** *)

implement Sub_char_char_int = s2cstref_make "sub_char_char_int"

implement Gt_char_char_bool = s2cstref_make "gt_char_char_bool"
implement Gte_char_char_bool = s2cstref_make "gte_char_char_bool"
implement Lt_char_char_bool = s2cstref_make "lt_char_char_bool"
implement Lte_char_char_bool = s2cstref_make "lte_char_char_bool"

implement Eq_char_char_bool = s2cstref_make "eq_char_char_bool"
implement Neq_char_char_bool = s2cstref_make "neq_char_char_bool"

(* ****** ****** *)

implement Neg_int_int = s2cstref_make "neg_int_int"
implement Add_int_int_int = s2cstref_make "add_int_int_int"
implement Sub_int_int_int = s2cstref_make "sub_int_int_int"
implement Mul_int_int_int = s2cstref_make "mul_int_int_int"

implement Gt_int_int_bool = s2cstref_make "gt_int_int_bool"
implement Gte_int_int_bool = s2cstref_make "gte_int_int_bool"
implement Lt_int_int_bool = s2cstref_make "lt_int_int_bool"
implement Lte_int_int_bool = s2cstref_make "lte_int_int_bool"

implement Eq_int_int_bool = s2cstref_make "eq_int_int_bool"
implement Neq_int_int_bool = s2cstref_make "neq_int_int_bool"

implement Div_int_int_int = s2cstref_make "div_int_int_int"
implement Div_int_int_int_bool = s2cstref_make "div_int_int_int_bool"

implement Max_int_int_int = s2cstref_make "max_int_int_int"
implement Max_int_int_int_bool = s2cstref_make "max_int_int_int_bool"

implement Min_int_int_int = s2cstref_make "min_int_int_int"
implement Min_int_int_int_bool = s2cstref_make "min_int_int_int_bool"

(* ****** ****** *)

implement Abs_int_int = s2cstref_make "abs_int_int"
implement Abs_int_int_bool = s2cstref_make "abs_int_int_bool"

implement Btw_int_int_int_bool = s2cstref_make "btw_int_int_int_bool"

implement IntOfBool_bool_int = s2cstref_make "int_of_bool"
implement IntOfBool_bool_int_bool = s2cstref_make "int_of_bool_bool"

implement Size_int_int_bool = s2cstref_make "size_int_int_bool"
implement Sizeof_viewt0ype_int = s2cstref_make "sizeof_viewt0ype_int"

(* ****** ****** *)

implement Null_addr = s2cstref_make "null_addr"

implement Add_addr_int_addr = s2cstref_make "add_addr_int_addr"
implement Sub_addr_int_addr = s2cstref_make "sub_addr_int_addr"
implement Sub_addr_addr_int = s2cstref_make "sub_addr_addr_int"

implement Gt_addr_addr_bool = s2cstref_make "gt_addr_addr_bool"
implement Gte_addr_addr_bool = s2cstref_make "gte_addr_addr_bool"
implement Lt_addr_addr_bool = s2cstref_make "lt_addr_addr_bool"
implement Lte_addr_addr_bool = s2cstref_make "lte_addr_addr_bool"

implement Eq_addr_addr_bool = s2cstref_make "eq_addr_addr_bool"
implement Neq_addr_addr_bool = s2cstref_make "neq_addr_addr_bool"

(* ****** ****** *)

implement Lte_cls_cls_bool = s2cstref_make "lte_cls_cls_bool"

(* ****** ****** *)

local

typedef d2conref_struct = @{
  sym= sym_t, con= Option d2con_t
} // end of [d2conref_struct]

typedef d2conref =
  [l:addr] (vbox (d2conref_struct @ l) | ptr l)
assume d2conref_t = d2conref

in // in of [local]

implement d2conref_make (name) = let
  val id = $Sym.symbol_make_string name
  val (pfgc, pfat | p) = begin
    ptr_alloc_tsz {d2conref_struct} (sizeof<d2conref_struct>)
  end // end of [val]
  prval () = free_gc_elim {d2conref_struct?} (pfgc)
  val () = (p->sym := id; p->con := None ())
  val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
in
  (pfbox | p)
end  // end of [d2conref_make]

implement d2conref_con_get (r) = let
  val od2c = let val (vbox pf | p) = r in p->con end
in
  case+ od2c of
  | None () => let
      val id = let val (vbox pf | p) = r in p->sym end
      val od2c = let
        val od2i = $TransEnv2.the_d2expenv_pervasive_find (id)
      in
        begin case+ od2i of
        | ~Some_vt d2i => begin case+ d2i of
          | D2ITEMcon d2cs => begin case+ d2cs of
            | D2CONLSTcons (d2c, _) => let
                val (vbox pf | p) = r; val od2c = Some d2c
              in
                p->con := od2c; od2c
              end
            | D2CONLSTnil () => None ()
            end
          | _ => None ()
          end // end of [Some_vt]
        | ~None_vt () => None ()
        end : Option d2con_t
      end
    in
      case+ od2c of
      | Some d2c => d2c | None () => begin
          prerr_interror ();
          prerr ": d2conref_con_get: ";
          prerr "the pervasive dynamic constructor [";
          prerr id; prerr "] is not available.";
          prerr_newline ();
          $Err.abort {d2con_t} ()
        end // end of [None]
    end // end of [None]
  | Some d2c => d2c
end // end of [d2conref_con_get]

end // end of [local]

implement List_nil = d2conref_make "list_nil"
implement List_cons = d2conref_make "list_cons"

implement List_vt_nil = d2conref_make "list_vt_nil"
implement List_vt_cons = d2conref_make "list_vt_cons"

(*

// it is now supported internally; see [prelude/CATS/lazy.cats]

implement ThunkValue_thunk = d2conref_make "thunkvalue_thunk"
implement ThunkValue_value = d2conref_make "thunkvalue_value"

implement ThunkValue_vt_thunk = d2conref_make "thunkvalue_vt_thunk"
implement ThunkValue_vt_value = d2conref_make "thunkvalue_vt_value"

*)

(* ****** ****** *)

local

typedef d2cstref_struct = @{
  sym= sym_t, cst= Option d2cst_t
} // end of [d2cstref_struct]

typedef d2cstref =
  [l:addr] (vbox (d2cstref_struct @ l) | ptr l)
assume d2cstref_t = d2cstref

in // in of [local]

implement d2cstref_make (name) = let
  val id = $Sym.symbol_make_string name
  val (pfgc, pfat | p) = begin
    ptr_alloc_tsz {d2cstref_struct} (sizeof<d2cstref_struct>)
  end // end of [val]
  prval () = free_gc_elim {d2cstref_struct?} (pfgc)
  val () = (p->sym := id; p->cst := None ())
  val (pfbox | ()) = vbox_make_view_ptr (pfat | p)
in
  (pfbox | p)
end  // end of [d2cstref_make]

implement
d2cstref_get_cst (r) = let
  val od2c = p->cst where { val (vbox pf | p) = r }
in
  case+ od2c of
  | None () => let
      val id = let val (vbox pf | p) = r in p->sym end
      val od2c = let
        val od2i = $TransEnv2.the_d2expenv_pervasive_find (id)
      in
        case+ od2i of
        | ~Some_vt d2i => begin case+ d2i of
          | D2ITEMcst d2c => let
              val (vbox pf | p) = r
              val od2c = Some d2c in p->cst := od2c; od2c
            end (* end of [D2ITEMcst] *)
          | _ => None ()
          end // end of [Some_vt]
        | ~None_vt () => None ()
      end : Option d2cst_t // end of [val]
    in
      case+ od2c of
      | Some d2c => d2c | None () => begin
          prerr_interror ();
          prerr ": d2cstref_get_cst: ";
          prerr "the pervasive dynamic constant [";
          prerr id; prerr "] is not available.";
          prerr_newline ();
          $Err.abort {d2cst_t} ()
        end // end of [None]
    end // end of [None]
  | Some d2c => d2c
end (* end of [d2cstref_get_cst] *)

end // end of [local]

implement Ats_main_void = d2cstref_make "main_void"
implement Ats_main_argc_argv = d2cstref_make "main_argc_argv"
implement Ats_main_dummy = d2cstref_make "main_dummy"

(* ****** ****** *)

implement s2exp_bool (b) = let
  val s2c = (if b
    then s2cstref_get_cst (True_bool)
    else s2cstref_get_cst (False_bool)
  ) : s2cst_t
in
  s2exp_cst (s2c)
end // end of [s2exp_bool]

implement s2exp_bool_t0ype () = let
  val s2c = s2cstref_get_cst (Bool_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_bool_t0ype]

implement s2exp_bool_bool_t0ype (b) = let
  val s2c = s2cstref_get_cst (Bool_bool_t0ype) in
  s2exp_cstapp (s2c, '[s2exp_bool b])
end // end of [s2exp_bool_bool_t0ype]

implement s2exp_char_t0ype () = let
  val s2c = s2cstref_get_cst (Char_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_char_t0ype]

implement s2exp_char_char_t0ype (c) = let
  val s2c = s2cstref_get_cst (Char_char_t0ype) in
  s2exp_cstapp (s2c, '[s2exp_char c])
end // end of [s2exp_char_char_t0ype]

implement s2exp_double_t0ype () = let
  val s2c = s2cstref_get_cst (Double_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_double_t0ype]

implement s2exp_double_long_t0ype () = let
  val s2c = s2cstref_get_cst (Double_long_t0ype) in
  s2exp_cst (s2c)
end // end of [s2exp_double_long_t0ype]

implement s2exp_float_t0ype () = let
  val s2c = s2cstref_get_cst (Float_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_float_t0ype]

implement s2exp_int_t0ype () = let
  val s2c = s2cstref_get_cst (Int_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_int_t0ype]

implement s2exp_int_int_t0ype (i) = let
  val s2c = s2cstref_get_cst (Int_int_t0ype) in
  s2exp_cstapp (s2c, '[s2exp_int i])
end // end of [s2exp_int_int_t0ype]

implement s2exp_int_intinf_t0ype (i) = let
  val s2c = s2cstref_get_cst (Int_int_t0ype) in
  s2exp_cstapp (s2c, '[s2exp_intinf i])
end // end of [s2exp_int_intinf_t0ype]

//

implement s2exp_ptr_type () = let
  val s2c = s2cstref_get_cst (Ptr_type) in s2exp_cst (s2c)
end // end of [s2exp_ptr_type]

implement s2exp_ptr_addr_type (s2e_addr) = let
  val s2c = s2cstref_get_cst (Ptr_addr_type)
in
  s2exp_app_srt (s2rt_type, s2exp_cst s2c, '[s2e_addr])
end // end of [s2exp_ptr_addr_type]

implement s2exp_string_type () = let
  val s2c = s2cstref_get_cst (String_type) in s2exp_cst (s2c)
end // end of [s2exp_string_type]

implement s2exp_string_int_type (n) = let
  val s2c = s2cstref_get_cst (String_int_type) in
  s2exp_cstapp (s2c, '[s2exp_int n])
end // end of [s2exp_string_int_type]

implement s2exp_void_t0ype () =
  s2exp_cst (s2cstref_get_cst (Void_t0ype))
// end of [s2exp_void_t0ype]

(* ****** ****** *)

fn s2exp_is_app_s2cstref
  (s2e: s2exp, s2cref: s2cstref): bool =
  case+ s2e.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
    case+ s2e_fun.s2exp_node of
    | S2Ecst (s2c) => begin
        if s2cstref_get_cst (s2cref) = s2c then true else false
      end // end of [S2Ecst]
    | _ => false
    end // end of [S2Eapp]
  | _ => false
// end of [s2exp_is_app_s2cstref]

(* ****** ****** *)

fn un_s2exp_s2cstref_1
  (s2e: s2exp, s2cref: s2cstref): Option_vt (s2exp) = begin
  case+ s2e.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin case+ s2e_fun.s2exp_node of
    | S2Ecst (s2c) => begin
        if s2cstref_get_cst (s2cref) = s2c then (
          case+ s2es_arg of
          | list_cons (s2e, list_nil ()) => Some_vt (s2e)
          | _ => begin
              prerr_interror ();
              prerr ": un_s2exp_s2cref: s2c = "; prerr s2c; prerr_newline ();
              $Err.abort {Option_vt s2exp} ()
            end // end of [_]
        ) else (
          None_vt ()
        ) // end of [if]
      end // end of [S2Ecst]
    | _ => None_vt ()
    end // end of [S2Eapp]
  | _ => None_vt ()
end // end of [un_s2exp_s2cstref_1]

fn un_s2exp_s2cstref_2
  (s2e: s2exp, s2cref: s2cstref): Option_vt @(s2exp, s2exp) = begin
  case+ s2e.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin case+ s2e_fun.s2exp_node of
    | S2Ecst (s2c) => begin
        if s2cstref_get_cst (s2cref) = s2c then
          case+ s2es_arg of
          | list_cons (s2e1, list_cons (s2e2, list_nil ())) =>
              Some_vt @(s2e1, s2e2)
            // end of [list_cons (list_cons (list_nil))]
          | _ => begin
              prerr_interror ();
              prerr ": un_s2exp_s2cref: s2c = "; prerr s2c; prerr_newline ();
              $Err.abort {Option_vt @(s2exp, s2exp)} ()
            end // end of [_]
        else None_vt ()
      end // end of [S2Ecst]
    | _ => None_vt ()
    end // end of [S2Eapp]
  | _ => None_vt ()
end // end of [un_s2exp_s2cstref_2]

(* ****** ****** *)

implement un_s2exp_bool_bool_t0ype (s2e) =
  un_s2exp_s2cstref_1 (s2e, Bool_bool_t0ype)

implement un_s2exp_char_char_t0ype (s2e) =
  un_s2exp_s2cstref_1 (s2e, Char_char_t0ype)

implement un_s2exp_int_int_t0ype (s2e) =
  un_s2exp_s2cstref_1 (s2e, Int_int_t0ype)

implement un_s2exp_ref_viewt0ype_type (s2e) =
  un_s2exp_s2cstref_1 (s2e, Ref_viewt0ype_type)

implement un_s2exp_size_int_t0ype (s2e) =
  un_s2exp_s2cstref_1 (s2e, Size_int_t0ype)

implement un_s2exp_string_int_type (s2e) =
  un_s2exp_s2cstref_1 (s2e, String_int_type)
  
(* ****** ****** *)

implement s2exp_uint_t0ype () = let
  val s2c = s2cstref_get_cst (Uint_t0ype)
in
  s2exp_cst (s2c)
end // end of [s2exp_uint_t0ype]

implement s2exp_uint_int_t0ype (i) = let
  val s2c = s2cstref_get_cst (Uint_int_t0ype)
in
  s2exp_cstapp (s2c, '[s2exp_int i])
end // end of [s2exp_uint_int_t0ype]

implement s2exp_uint_intinf_t0ype (i) = let
  val s2c = s2cstref_get_cst (Uint_int_t0ype)
in
  s2exp_cstapp (s2c, '[s2exp_intinf i])
end // end of [s2exp_uint_intinf_t0ype]

(* ****** ****** *)

implement s2exp_lint_t0ype () = let
  val s2c = s2cstref_get_cst (Int_long_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_lint_t0ype]

implement s2exp_lint_intinf_t0ype (i) = let
  val s2c = s2cstref_get_cst (Lint_int_t0ype)
in
  s2exp_cstapp (s2c, '[s2exp_intinf i])
end // end of [s2exp_lint_intinf_t0ype]

implement s2exp_ulint_t0ype () = let
  val s2c = s2cstref_get_cst (Uint_long_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_ulint_t0ype]

implement s2exp_ulint_intinf_t0ype (i) = let
  val s2c = s2cstref_get_cst (Ulint_int_t0ype)
in
  s2exp_cstapp (s2c, '[s2exp_intinf i])
end // end of [s2exp_ulint_intinf_t0ype]

(* ****** ****** *)

implement s2exp_llint_t0ype () = let
  val s2c = s2cstref_get_cst (Int_long_long_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_llint_t0ype]

implement s2exp_ullint_t0ype () = let
  val s2c = s2cstref_get_cst (Uint_long_long_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_ullint_t0ype]

(* ****** ****** *)

implement s2exp_sint_t0ype () = let
  val s2c = s2cstref_get_cst (Int_short_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_sint_t0ype]

implement s2exp_ussint_t0ype () = let
  val s2c = s2cstref_get_cst (Uint_short_short_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_ussint_t0ype]

(* ****** ****** *)

implement s2exp_ssint_t0ype () = let
  val s2c = s2cstref_get_cst (Int_short_short_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_ssint_t0ype]

implement s2exp_usint_t0ype () = let
  val s2c = s2cstref_get_cst (Uint_short_t0ype) in s2exp_cst (s2c)
end // end of [s2exp_usint_t0ype]

(* ****** ****** *)

implement un_s2exp_ptr_addr_type (s2e) =
  un_s2exp_s2cstref_1 (s2e, Ptr_addr_type)

(* ****** ****** *)

implement s2exp_bottom_t0ype_exi () =
  s2exp_cst (s2cstref_get_cst (Bottom_t0ype_exi))

implement s2exp_bottom_t0ype_uni () =
  s2exp_cst (s2cstref_get_cst (Bottom_t0ype_uni))

implement s2exp_bottom_viewt0ype_exi () =
  s2exp_cst (s2cstref_get_cst (Bottom_viewt0ype_exi))

implement s2exp_bottom_viewt0ype_uni () =
  s2exp_cst (s2cstref_get_cst (Bottom_viewt0ype_uni))

implement s2exp_exception_viewtype () =
  s2exp_cst (s2cstref_get_cst (Exception_viewtype))

(* ****** ****** *)

implement s2exp_at_viewt0ype_addr_view (s2e_elt, s2e_addr) = let
  val s2c = s2cstref_get_cst (At_viewt0ype_addr_view)
in
  s2exp_app_srt (s2rt_view, s2exp_cst s2c, '[s2e_elt, s2e_addr])
end // end of [s2exp_at_viewt0ype_addr_view]

implement un_s2exp_at_viewt0ype_addr_view (s2e) =
  un_s2exp_s2cstref_2 (s2e, At_viewt0ype_addr_view)

(* ****** ****** *)

// the length of an array is assumed to be less than [INTMAX]
implement s2exp_array_viewt0ype_int_type (s2e_elt, sz) = let
  val s2c = s2cstref_get_cst (Array_viewt0ype_int_type)
  val s2e_sz = s2exp_int sz
in
  s2exp_app_srt (s2rt_type, s2exp_cst s2c, '[s2e_elt, s2e_sz])
end // end of [s2exp_array_viewt0ype_int_type]

// the length of an array is assumed to be less than [INTMAX]
implement s2exp_array_viewt0ype_int_viewtype (s2e_elt, sz) = let
  val s2c = s2cstref_get_cst (Array_viewt0ype_int_viewtype)
  val s2e_sz = s2exp_int sz
in
  s2exp_app_srt (s2rt_viewtype, s2exp_cst s2c, '[s2e_elt, s2e_sz])
end // end of [s2exp_array_viewt0ype_int_viewtype]

// the length of an array is assumed to be less than [INTMAX]
implement
s2exp_arrayptrsize_viewt0ype_int_viewt0ype (s2e_elt, sz) = let
  val s2c = s2cstref_get_cst (Arrayptrsize_viewt0ype_int_viewt0ype)
  val s2e_sz = s2exp_int sz
in
  s2exp_app_srt (s2rt_viewt0ype, s2exp_cst s2c, '[s2e_elt, s2e_sz])
end // end of [s2exp_arrayptrsize_viewt0ype_int_viewt0ype]

(* ****** ****** *)

// the length of a list is assumed to be less than [INTMAX]
implement s2exp_list_t0ype_int_type (s2e_elt, ln) = let
  val s2c = s2cstref_get_cst (List_t0ype_int_type)
  val s2e_ln = s2exp_int ln
in
  s2exp_app_srt (s2rt_type, s2exp_cst s2c, '[s2e_elt, s2e_ln])
end // end of [s2exp_list_t0ype_int_type]

implement un_s2exp_list_t0ype_int_type (s2e) =
  un_s2exp_s2cstref_2 (s2e, List_t0ype_int_type)

// the length of a list is assumed to be less than [INTMAX]
implement s2exp_list_viewt0ype_int_viewtype (s2e_elt, ln) = let
  val s2c = s2cstref_get_cst (List_viewt0ype_int_viewtype)
  val s2e_ln = s2exp_int ln
in
  s2exp_app_srt (s2rt_viewtype, s2exp_cst s2c, '[s2e_elt, s2e_ln])
end // end of [s2exp_list_viewt0ype_int_viewtype]

(* ****** ****** *)

implement s2exp_lazy_t0ype_type (s2e) = let
  val s2c = s2cstref_get_cst (Lazy_t0ype_type)
in
  s2exp_app_srt (s2rt_type, s2exp_cst s2c, '[s2e])
end // end of [s2exp_lazy_t0ype_type]

implement s2exp_lazy_viewt0ype_viewtype (s2e) = let
  val s2c = s2cstref_get_cst (Lazy_viewt0ype_viewtype)
in
  s2exp_app_srt (s2rt_viewtype, s2exp_cst s2c, '[s2e])
end // end of [s2exp_lazy_viewt0ype_viewtype]

implement un_s2exp_lazy_t0ype_type (s2e) =
  un_s2exp_s2cstref_1 (s2e, Lazy_t0ype_type)

implement un_s2exp_lazy_viewt0ype_viewtype (s2e) =
  un_s2exp_s2cstref_1 (s2e, Lazy_viewt0ype_viewtype)

(* ****** ****** *)

implement s2exp_printf_c_types_type (s2e) = let
  val s2c = s2cstref_get_cst (Printf_c_types_type)
in
  s2exp_app_srt (s2rt_type, s2exp_cst s2c, '[s2e])
end // end of [s2exp_printf_c_types_type]

(* ****** ****** *)

implement s2exp_va_list_viewt0ype () = let
  val s2c = s2cstref_get_cst (Va_list_viewt0ype) in s2exp_cst s2c
end // end of [s2exp_va_list_viewt0ype]

implement s2exp_va_list_types_viewt0ype (s2e) = let
  val s2c = s2cstref_get_cst (Va_list_types_viewt0ype)
in
  s2exp_app_srt (s2rt_viewt0ype, s2exp_cst s2c, '[s2e])
end // end of [s2exp_va_list_types_viewt0ype]

(* ****** ****** *)

implement s2exp_vbox_view_prop (s2e) = let
  val s2c = s2cstref_get_cst (Vbox_view_prop)
in
  s2exp_app_srt (s2rt_prop, s2exp_cst s2c, '[s2e])
end // end of [s2exp_vbox_view_prop]

implement un_s2exp_vbox_view_prop (s2e) =
  un_s2exp_s2cstref_1 (s2e, Vbox_view_prop)
// end of ...

(* ****** ****** *)

implement s2exp_neg_bool_bool (s2p) = let
  val s2c = s2cstref_get_cst (Neg_bool_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2p])
end // end of [s2exp_neg_bool_bool]

implement s2exp_add_bool_bool_bool (s2p1, s2p2) = let
  val s2c = s2cstref_get_cst (Add_bool_bool_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2p1, s2p2])
end // end of [s2exp_add_bool_bool_bool]

implement s2exp_mul_bool_bool_bool (s2p1, s2p2) = let
  val s2c = s2cstref_get_cst (Mul_bool_bool_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2p1, s2p2])
end // end of [s2exp_mul_bool_bool_bool]

(* ****** ****** *)

implement s2exp_gt_int_int_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Gt_int_int_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_gt_int_int_bool]

implement s2exp_gte_int_int_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Gte_int_int_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_gte_int_int_bool]

//

implement s2exp_lt_int_int_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Lt_int_int_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_lt_int_int_bool]

implement s2exp_lte_int_int_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Lte_int_int_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_lte_int_int_bool]

//

implement s2exp_neq_int_int_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Neq_int_int_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_neq_int_int_bool]

implement s2exp_btw_int_int_int_bool (s2e_l, s2e_m, s2e_r) = let
  val s2c = s2cstref_get_cst (Btw_int_int_int_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e_l, s2e_m, s2e_r])
end // end of [s2exp_btw_int_int_int_bool]

(* ****** ****** *)

implement s2exp_null_addr () =
  s2exp_cst (s2cstref_get_cst (Null_addr))

//

implement s2exp_gt_addr_addr_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Gt_addr_addr_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_gt_addr_addr_bool]

implement s2exp_gte_addr_addr_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Gte_addr_addr_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_gte_addr_addr_bool]

//

implement s2exp_lt_addr_addr_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Lt_addr_addr_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_lt_addr_addr_bool]

implement s2exp_lte_addr_addr_bool (s2e1, s2e2) = let
  val s2c = s2cstref_get_cst (Lte_addr_addr_bool)
in
  s2exp_app_srt (s2rt_bool, s2exp_cst s2c, '[s2e1, s2e2])
end // end of [s2exp_lte_addr_addr_bool]

(* ****** ****** *)

implement
clo_viewt0ype_viewt0ype_assume () = let
  val s2c = s2cstref_get_cst (Clo_viewt0ype_viewt0ype)
  val s2t_def = s2cst_get_srt s2c
  val s2v_arg = s2var_make_srt s2rt_viewt0ype
  val knd = 0(*clo*)
  val s2e_body = s2exp_clo_srt (s2rt_viewt0ype, knd, s2exp_var s2v_arg)
  val s2e_def = s2exp_lam_srt (s2t_def, '[s2v_arg], s2e_body)
in
  s2cst_set_def (s2c, Some s2e_def)
end // end of [clo_viewt0ype_viewt0ype_assume]

implement
cloptr_viewt0ype_viewtype_assume () = let
  val s2c = s2cstref_get_cst (Cloptr_viewt0ype_viewtype)
  val s2t_def = s2cst_get_srt s2c
  val s2v_arg = s2var_make_srt s2rt_viewt0ype
  val knd = 1(*cloptr*)
  val s2e_body = s2exp_clo_srt (s2rt_viewtype, knd, s2exp_var s2v_arg)
  val s2e_def = s2exp_lam_srt (s2t_def, '[s2v_arg], s2e_body)
in
  s2cst_set_def (s2c, Some s2e_def)
end // end of [cloptr_viewt0ype_viewtype_assume]

implement
cloref_t0ype_type_assume () = let
  val s2c = s2cstref_get_cst (Cloref_t0ype_type)
  val s2t_def = s2cst_get_srt s2c
  val s2v_arg = s2var_make_srt s2rt_t0ype
  val knd = ~1(*cloref*)
  val s2e_body = s2exp_clo_srt (s2rt_type, knd, s2exp_var s2v_arg)
  val s2e_def = s2exp_lam_srt (s2t_def, '[s2v_arg], s2e_body)
in
  s2cst_set_def (s2c, Some s2e_def)
end // end of [cloptr_viewt0ype_viewtype_assume]

(* ****** ****** *)

implement
crypt_viewt0ype_viewt0ype_assume () = let
  val s2c = s2cstref_get_cst (Crypt_viewt0ype_viewt0ype)
  val s2t_def = s2cst_get_srt s2c
  val s2v_arg = s2var_make_srt s2rt_viewt0ype
  val s2e_body = s2exp_crypt (s2exp_var s2v_arg)
  val s2e_def = s2exp_lam_srt (s2t_def, '[s2v_arg], s2e_body)
in
  s2cst_set_def (s2c, Some s2e_def)
end // end of [crypt_viewt0ype_viewt0ype_assume]

(* ****** ****** *)

implement
sizeof_viewt0ype_int_assume () = let
  val s2c = s2cstref_get_cst (Sizeof_viewt0ype_int)
  val s2t_def = s2cst_get_srt s2c
  val s2v_arg = s2var_make_srt s2rt_t0ype
  val s2e_body = s2exp_sizeof (s2exp_var s2v_arg)
  val s2e_def = s2exp_lam_srt (s2t_def, '[s2v_arg], s2e_body)
in
  s2cst_set_def (s2c, Some s2e_def)
end // end of [sizeof_viewt0ype_int_assume]

(* ****** ****** *)

(* end of [ats_stadyncst2.dats] *)
