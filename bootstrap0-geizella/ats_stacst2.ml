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
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
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

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

open Ats_misc
open Ats_staexp2

module P = Printf

module Err = Ats_error
module Loc = Ats_location
module Sym = Ats_symbol

module Lab = Ats_label
module SEnv2 = Ats_staenv2


(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location
type symbol = Sym.symbol

type labsexp2 = lab * sexp2

(* a standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_stacst2: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

let sexp2_is_tyarr (s2e: sexp2): bool =
  match s2e.sexp2_node with SE2tyarr _ -> true | _ -> false

(* ****** ****** *)

let scst2_dummy = { 
  scst2_name= Syn.make_sid_with_string "";
  scst2_sort= SRT2tup [];
  scst2_isabs= None;
  scst2_iscon= false;
  scst2_isrec= false;
  scst2_arity= [];
  scst2_arg= None;
  scst2_cons= None;
  scst2_islst= None;
  scst2_env= [];
  scst2_def= None;
  scst2_isasp= false;
  scst2_stamp= Cnt.zero; 
  scst2_copy= None;
} (* end of [scst2_make] *)

(* ****** ****** *)

module type Scst2Type = sig
  val name : symbol
  val make_cst : unit -> scst2
  val make_cst_opt : unit -> scst2 option
  val eq_cst : scst2 -> bool
  val eq_cst_opt : scst2 -> bool
  val eq_exp : sexp2 -> bool
  val make_exp : (sexp2 list) option -> sexp2
  val un_make_exp : sexp2 -> (sexp2 list) option
end (* end of [Scst2Type] *)

module type Scst2NameType = sig
  val name : string
end

module Scst2Fun (N: Scst2NameType): Scst2Type = struct
  let cst_r = ref None
  let name = Sym.make_with_string N.name
  let make_cst () = match !cst_r with
    | None ->
	let s2c = match SEnv2.SEXP2env.find_in_pervasives name with
	  | Some (SI2cst [s2c]) -> s2c
	  | _ -> begin
	      P.fprintf stderr "Scst2Fun: make_cst: %s\n" N.name;
	      Err.abort ();
	    end in
	  (cst_r := Some s2c; s2c)
    | Some s2c -> s2c

  let make_cst_opt () = match !cst_r with
    | None -> begin
	let os2c =
	  match SEnv2.SEXP2env.find_in_pervasives name with
	    | Some (SI2cst [s2c]) -> Some s2c | _ -> None in
	  (cst_r := os2c; os2c)
      end (* end of [None] *)
    | os2c -> os2c

  let eq_cst (s2c) = scst2_eq s2c (make_cst ())

  let eq_cst_opt (s2c) = match make_cst_opt () with
    | Some s2c1 -> scst2_eq s2c s2c1 | None -> false

  let rec eq_exp (s2e: sexp2): bool =
    match s2e.sexp2_node with
      | SE2cst s2c -> eq_cst s2c
      | SE2app (s2e, _) -> eq_exp s2e
      | _ -> false

  let make_exp (os2es: (sexp2 list) option): sexp2 =
    let s2c = make_cst () in
    let s2e_cst = sexp2_cst s2c in match os2es with
      | None -> s2e_cst
      | Some s2es -> begin match un_srt2_fun s2c.scst2_sort with
	  | None -> error_of_deadcode "ats_stacst2: make_exp"
	  | Some (_, s2t_res) -> sexp2_app_with_sort s2t_res s2e_cst s2es
	end

  let un_make_exp (s2e: sexp2): (sexp2 list) option =
    match s2e.sexp2_node with
      | SE2app (s2e_fun, s2es_arg) -> begin
	  match s2e_fun.sexp2_node with
	    | SE2cst s2c -> if eq_cst s2c then Some (s2es_arg) else None
	    | _ -> None
	end (* end of [SE2app] *)
      | _ -> None
end (* end of [Scst2Fun] *)

(* ****** ****** *)

module True_bool: Scst2Type =
  Scst2Fun (struct let name = "true_bool" end)
module False_bool: Scst2Type =
  Scst2Fun (struct let name = "false_bool" end)

let sexp2_bool (b: bool): sexp2 = begin
  if b then True_bool.make_exp None else False_bool.make_exp None
end (* end of [sexp2_bool] *)

module Null_addr: Scst2Type =
  Scst2Fun (struct let name = "null_addr" end)

(* ****** ****** *)

module Btw_int_int_int_bool: Scst2Type =
  Scst2Fun (struct let name = "btw_int_int_int_bool" end)

(* ****** ****** *)

module At_viewt0ype_addr_view: Scst2Type =
  Scst2Fun (struct let name = "at_viewt0ype_addr_view" end)

let sexp2_at_viewt0ype_addr_view s2e1 s2e2: sexp2 =
  At_viewt0ype_addr_view.make_exp (Some [s2e1; s2e2])

let un_sexp2_at_viewt0ype_addr_view (s2e: sexp2): (sexp2 * sexp2) option =
  match At_viewt0ype_addr_view.un_make_exp s2e with
    | Some [s2e1; s2e2] -> Some (s2e1, s2e2) | None -> None
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_at_viewt0ype_addr_view"
(* end of [un_sexp2_at_viewt0ype_addr_view] *)

(* ****** ****** *)

module Bool_t0ype: Scst2Type = Scst2Fun (struct let name = "bool_t0ype" end)
module Bool_bool_t0ype: Scst2Type =
  Scst2Fun (struct let name = "bool_bool_t0ype" end)

let sexp2_bool_bool_t0ype (b: bool): sexp2 =
  Bool_bool_t0ype.make_exp (Some [sexp2_bool b])

let un_sexp2_bool_bool_t0ype (s2e: sexp2): sexp2 option =
  match Bool_bool_t0ype.un_make_exp s2e with
    | Some [s2b] -> Some (s2b) | None -> None
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_bool_bool_t0ype"
(* end of [un_sexp2_bool_bool_t0ype] *)

(* ****** ****** *)

module Byte_t0ype: Scst2Type = Scst2Fun (struct let name = "byte_t0ype" end)

(* ****** ****** *)

module Char_t0ype: Scst2Type = Scst2Fun (struct let name = "char_t0ype" end)
module Char_char_t0ype: Scst2Type =
  Scst2Fun (struct let name = "char_char_t0ype" end)

let sexp2_char_char_t0ype (c: char): sexp2 =
  Char_char_t0ype.make_exp (Some [sexp2_char c])

(* ****** ****** *)

module Double_t0ype: Scst2Type =
  Scst2Fun (struct let name = "double_t0ype" end)
module Double_long_t0ype: Scst2Type =
  Scst2Fun (struct let name = "double_long_t0ype" end)
module Float_t0ype: Scst2Type =
  Scst2Fun (struct let name = "float_t0ype" end)

(* ****** ****** *)

module Exception_viewtype: Scst2Type =
  Scst2Fun (struct let name = "exception_viewtype" end)

(* ****** ****** *)

module Int_t0ype: Scst2Type = Scst2Fun (struct let name = "int_t0ype" end)
module Int_int_t0ype: Scst2Type =
  Scst2Fun (struct let name = "int_int_t0ype" end)

let sexp2_int_int_t0ype (i: intinf): sexp2 =
  Int_int_t0ype.make_exp (Some [sexp2_intinf i])

let un_sexp2_int_int_t0ype (s2e: sexp2): sexp2 option =
  match Int_int_t0ype.un_make_exp s2e with
    | Some [s2i] -> Some (s2i) | None -> None
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_int_int_t0ype"
(* end of [un_sexp2_int_int_t0ype] *)

module Uint_t0ype: Scst2Type =
  Scst2Fun (struct let name = "uint_t0ype" end)
module Uint_int_t0ype: Scst2Type =
  Scst2Fun (struct let name = "uint_int_t0ype" end)

let sexp2_uint_int_t0ype (i: intinf): sexp2 =
  Uint_int_t0ype.make_exp (Some [sexp2_intinf i])

let un_sexp2_uint_int_t0ype (s2e: sexp2): sexp2 option =
  match Uint_int_t0ype.un_make_exp s2e with
    | Some [s2i] -> Some (s2i) | None -> None
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_uint_int_t0ype"
(* end of [un_sexp2_uint_int_t0ype] *)

(* ****** ****** *)

module Int_long_t0ype: Scst2Type =
  Scst2Fun (struct let name = "int_long_t0ype" end)
module Uint_long_t0ype: Scst2Type =
  Scst2Fun (struct let name = "uint_long_t0ype" end)

let sexp2_lint_t0ype () = Int_long_t0ype.make_exp None 
let sexp2_ulint_t0ype () = Uint_long_t0ype.make_exp None 

(* ****** ****** *)

module Lint_int_t0ype: Scst2Type =
  Scst2Fun (struct let name = "lint_int_t0ype" end)
module Ulint_int_t0ype: Scst2Type =
  Scst2Fun (struct let name = "ulint_int_t0ype" end)

(* ****** ****** *)

module Int_long_long_t0ype: Scst2Type =
  Scst2Fun (struct let name = "int_long_long_t0ype" end)
module Uint_long_long_t0ype: Scst2Type =
  Scst2Fun (struct let name = "uint_long_long_t0ype" end)

module Int_short_t0ype: Scst2Type =
  Scst2Fun (struct let name = "int_short_t0ype" end)
module Uint_short_t0ype: Scst2Type =
  Scst2Fun (struct let name = "uint_short_t0ype" end)

let sexp2_sint_t0ype () = Int_short_t0ype.make_exp None 
let sexp2_usint_t0ype () = Uint_short_t0ype.make_exp None 

module Int_short_short_t0ype: Scst2Type =
  Scst2Fun (struct let name = "int_short_short_t0ype" end)
module Uint_short_short_t0ype: Scst2Type =
  Scst2Fun (struct let name = "uint_short_short_t0ype" end)

(* ****** ****** *)

module Size_t0ype: Scst2Type =
  Scst2Fun (struct let name = "size_t0ype" end)
module Size_int_t0ype: Scst2Type =
  Scst2Fun (struct let name = "size_int_t0ype" end)

let sexp2_size_int_t0ype (i: intinf): sexp2 =
  Size_int_t0ype.make_exp (Some [sexp2_intinf i])

let un_sexp2_size_int_t0ype (s2e: sexp2): sexp2 option =
  match Size_int_t0ype.un_make_exp s2e with
    | Some [s2i] -> Some (s2i) | None -> None
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_size_int_t0ype"
(* end of [un_sexp2_size_int_t0ype] *)

(* ****** ****** *)

module Ssize_t0ype: Scst2Type =
  Scst2Fun (struct let name = "ssize_t0ype" end)
module Ssize_int_t0ype: Scst2Type =
  Scst2Fun (struct let name = "ssize_int_t0ype" end)

(* ****** ****** *)

let sexp2_int_t0ype_with_kind (ik: Syn.intkind) (i: intinf): sexp2 =
  match ik with
    | Syn.IKint -> sexp2_int_int_t0ype i
    | Syn.IKuint -> sexp2_uint_int_t0ype i
    | Syn.IKlint -> sexp2_lint_t0ype ()
    | Syn.IKulint -> sexp2_ulint_t0ype () 
    | Syn.IKsint -> sexp2_sint_t0ype ()
    | Syn.IKusint -> sexp2_usint_t0ype ()
    | _ -> error_of_unavailability "ats_stacst2: sexp2_int_t0ype_with_kind"
(* end of [sexp2_int_t0ype_with_kind] *)

(* ****** ****** *)

module Crypt_viewt0ype_viewt0ype: Scst2Type =
  Scst2Fun (struct let name = "crypt_viewt0ype_viewt0ype" end)

let sexp2_crypt_viewt0ype_viewt0ype (s2e: sexp2): sexp2 =
  Crypt_viewt0ype_viewt0ype.make_exp (Some [s2e])

let un_sexp2_crypt_viewt0ype_viewt0ype (s2e: sexp2): sexp2 option =
  match Crypt_viewt0ype_viewt0ype.un_make_exp s2e with
    | None -> None | Some [s2e] -> Some (s2e) | _ -> begin
	error_of_deadcode
	  "ats_stacst2: un_sexp2_crypt_viewt0ype_viewt0ype"
      end
(* end of [un_sexp2_crypt_viewt0ype_viewt0ype] *)

(* ****** ****** *)

module Lazy_t0ype_type: Scst2Type =
  Scst2Fun (struct let name = "lazy_t0ype_type" end)

let sexp2_lazy_t0ype_type (s2e: sexp2): sexp2 =
  Lazy_t0ype_type.make_exp (Some [s2e])

module Lazy_viewt0ype_viewtype: Scst2Type =
  Scst2Fun (struct let name = "lazy_viewt0ype_viewtype" end)

let sexp2_lazy_viewt0ype_viewtype (s2e: sexp2): sexp2 =
  Lazy_viewt0ype_viewtype.make_exp (Some [s2e])

(* ****** ****** *)

module Ptr_type: Scst2Type =
  Scst2Fun (struct let name = "ptr_type" end)

let sexp2_ptr_type (): sexp2 = Ptr_type.make_exp None

module Ptr_addr_type: Scst2Type =
  Scst2Fun (struct let name = "ptr_addr_type" end)

let sexp2_ptr_addr_type (s2l: sexp2): sexp2 =
  Ptr_addr_type.make_exp (Some [s2l])

let un_sexp2_ptr_addr_type (s2e: sexp2): sexp2 option =
  match Ptr_addr_type.un_make_exp s2e with
    | None -> None
    | Some [s2l] -> Some (s2l)
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_ptr_addr_type"
(* end of [un_sexp2_ptr_add_type] *)

(* ****** ****** *)

module Ref_viewt0ype_type: Scst2Type =
  Scst2Fun (struct let name = "ref_viewt0ype_type" end)

let un_sexp2_ref_viewt0ype_type (s2e: sexp2): sexp2 option =
  match Ref_viewt0ype_type.un_make_exp s2e with
    | None -> None
    | Some [s2e_elt] -> Some (s2e_elt)
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_ref_viewt0ype_type"
(* end of [un_sexp2_ref_viewt0ype_type] *)

module Refconst_t0ype_type: Scst2Type =
  Scst2Fun (struct let name = "refconst_t0ype_type" end)

let un_sexp2_refconst_t0ype_type (s2e: sexp2): sexp2 option =
  match Refconst_t0ype_type.un_make_exp s2e with
    | None -> None
    | Some [s2e_elt] -> Some (s2e_elt)
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_refconst_t0ype_type"
(* end of [un_sexp2_refconst_t0ype_type] *)

(* ****** ****** *)

module Arrayptrsize_viewt0ype_int_viewt0ype: Scst2Type =
  Scst2Fun (struct let name = "arrayptrsize_viewt0ype_int_viewt0ype" end)

let sexp2_arrayptrsize_viewt0ype_int_viewt0ype
  (s2e_elt: sexp2) (n: int) =
  Arrayptrsize_viewt0ype_int_viewt0ype.make_exp (Some [s2e_elt; sexp2_int n])

(* ****** ****** *)

module Clo_viewt0ype_viewt0ype: Scst2Type =
  Scst2Fun (struct let name = "clo_viewt0ype_viewt0ype" end)

let clo_viewt0ype_viewt0ype_assume () =
  let s2c = Clo_viewt0ype_viewt0ype.make_cst () in
  let s2e_def =
    let s2t = s2c.scst2_sort in
    let s2v = svar2_new srt2_viewt0ype in
    let knd = 0 in
    let s2e = sexp2_clo_with_sort srt2_viewt0ype knd (sexp2_var s2v) in
      sexp2_lam_with_sort s2t [s2v] s2e in
    (s2c.scst2_def <- Some s2e_def)
(* end of [clo_viewt0ype_viewt0ype_assume] *)

module Cloptr_viewt0ype_viewtype: Scst2Type =
  Scst2Fun (struct let name = "cloptr_viewt0ype_viewtype" end)

let cloptr_viewt0ype_viewtype_assume () =
  let s2c = Cloptr_viewt0ype_viewtype.make_cst () in
  let s2e_def =
    let s2t = s2c.scst2_sort in
    let s2v = svar2_new srt2_viewt0ype in
    let knd = 1 in
    let s2e = sexp2_clo_with_sort srt2_viewtype knd (sexp2_var s2v) in
      sexp2_lam_with_sort s2t [s2v] s2e in
    (s2c.scst2_def <- Some s2e_def)
(* end of [cloptr_viewt0ype_viewtype_assume] *)

module Cloref_t0ype_type: Scst2Type =
  Scst2Fun (struct let name = "cloref_t0ype_type" end)

let cloref_t0ype_type_assume () =
  let s2c = Cloref_t0ype_type.make_cst () in
  let s2e_def =
    let s2t = s2c.scst2_sort in
    let s2v = svar2_new srt2_t0ype in
    let knd = (-1) in
    let s2e = sexp2_clo_with_sort srt2_type knd (sexp2_var s2v) in
      sexp2_lam_with_sort s2t [s2v] s2e in
    (s2c.scst2_def <- Some s2e_def)

(* ****** ****** *)

module Printf_c_types_type: Scst2Type =
  Scst2Fun (struct let name = "printf_c_types_type" end)

let sexp2_printf_c_types_type (s2e: sexp2): sexp2 =
  Printf_c_types_type.make_exp (Some [s2e])

let un_sexp2_printf_c_types_type (s2e: sexp2): sexp2 option =
  match Printf_c_types_type.un_make_exp s2e with
    | None -> None
    | Some [s2e] -> Some (s2e)
    | _ -> begin
	error_of_deadcode "ats_stacst2: un_sexp2_printf_c_types_type"
      end
(* end of [un_sexp2_printf_c_types_type] *)

(* ****** ****** *)

module List_t0ype_int_type: Scst2Type =
  Scst2Fun (struct let name = "list_t0ype_int_type" end)

let sexp2_list_t0ype_int_type (s2e1: sexp2) (i2: int): sexp2 =
  List_t0ype_int_type.make_exp (Some [s2e1; sexp2_int i2])

let un_sexp2_list_t0ype_int_type (s2e: sexp2): (sexp2 * sexp2) option =
  match List_t0ype_int_type.un_make_exp s2e with
    | None -> None
    | Some [s2e; s2i] -> Some (s2e, s2i)
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_list_t0ype_int_type"
(* end of [un_sexp2_list_t0ype_int_type] *)

(* ****** ****** *)

module String_type: Scst2Type =
  Scst2Fun (struct let name = "string_type" end)
module String_int_type: Scst2Type =
  Scst2Fun (struct let name = "string_int_type" end)

let sexp2_string_int_type (s: string): sexp2 =
  let n = String.length s in
    String_int_type.make_exp (Some [sexp2_int n])
(* end of [sexp2_string_int_type] *)

(* ****** ****** *)

let scst2_sizeof_viewt0ype_int (): scst2 =
  match SEnv2.SEXP2env.find_in_pervasives Sym.symSIZEOF with
    | Some (SI2cst [s2c]) -> s2c
    | _ -> error_of_deadcode "ats_stacst2: scst2_sizeof_viewt0ype_int"
(* end of [scst2_sizeof_viewt0ype_int] *)

(* ****** ****** *)

module Vbox_view_prop: Scst2Type =
  Scst2Fun (struct let name = "vbox_view_prop" end)

let un_sexp2_vbox_view_prop (s2e: sexp2): sexp2 option =
  match Vbox_view_prop.un_make_exp s2e with
    | None -> None
    | Some [s2e] -> Some (s2e)
    | _ -> error_of_deadcode "ats_stacst2: un_sexp2_vbox_view_prop"
(* end of [un_sexp2_vbox_view_prop] *)

(* ****** ****** *)

module Void_t0ype: Scst2Type = Scst2Fun (struct let name = "void_t0ype" end)

let sexp2_void_t0ype (): sexp2 = Void_t0ype.make_exp None

module None_viewt0ype: Scst2Type = Scst2Fun (struct let name = "none_viewt0ype" end)

let sexp2_none_viewt0ype (): sexp2 = None_viewt0ype.make_exp None

(* ****** ****** *)

module Bneg: Scst2Type = Scst2Fun (struct let name = "neg_bool_bool" end)

module Badd: Scst2Type =
  Scst2Fun (struct let name = "add_bool_bool_bool" end)
module Bmul: Scst2Type =
  Scst2Fun (struct let name = "mul_bool_bool_bool" end)

module Beq: Scst2Type =
  Scst2Fun (struct let name = "eq_bool_bool_bool" end)
module Bneq: Scst2Type =
  Scst2Fun (struct let name = "neq_bool_bool_bool" end)


(* ****** ****** *)

module Ineg: Scst2Type = Scst2Fun (struct let name = "neg_int_int" end)
module Iadd: Scst2Type = Scst2Fun (struct let name = "add_int_int_int" end)
module Isub: Scst2Type = Scst2Fun (struct let name = "sub_int_int_int" end)
module Imul: Scst2Type = Scst2Fun (struct let name = "mul_int_int_int" end)
module Idiv: Scst2Type = Scst2Fun (struct let name = "div_int_int_int" end)

module Iabs: Scst2Type = Scst2Fun (struct let name = "abs_int_int" end)
module Nsub: Scst2Type = Scst2Fun (struct let name = "nsub_int_int_int" end)
module Imax: Scst2Type = Scst2Fun (struct let name = "max_int_int_int" end)
module Imin: Scst2Type = Scst2Fun (struct let name = "min_int_int_int" end)

(* ****** ****** *)

module Igt: Scst2Type =
  Scst2Fun (struct let name = "gt_int_int_bool" end)
module Igte: Scst2Type =
  Scst2Fun (struct let name = "gte_int_int_bool" end)

let sexp2_igte_zero (s2e: sexp2): sexp2 =
  Igte.make_exp (Some [s2e; sexp2_intinf_zero])

module Ilt: Scst2Type =
  Scst2Fun (struct let name = "lt_int_int_bool" end)
module Ilte: Scst2Type =
  Scst2Fun (struct let name = "lte_int_int_bool" end)

module Ieq: Scst2Type =
  Scst2Fun (struct let name = "eq_int_int_bool" end)
module Ineq: Scst2Type =
  Scst2Fun (struct let name = "neq_int_int_bool" end)
  

(* ****** ****** *)

module Padd: Scst2Type =
  Scst2Fun (struct let name = "add_addr_int_addr" end)
module Psub: Scst2Type =
  Scst2Fun (struct let name = "sub_addr_int_addr" end)
module Pdiff: Scst2Type =
  Scst2Fun (struct let name = "sub_addr_addr_int" end)

(* ****** ****** *)

module Pgt: Scst2Type =
  Scst2Fun (struct let name = "gt_addr_addr_bool" end)
module Pgte: Scst2Type =
  Scst2Fun (struct let name = "gte_addr_addr_bool" end)

let sexp2_pgt_null (s2e: sexp2): sexp2 =
  let s2e_pgt = Pgt.make_exp None in
  let s2e_null = Null_addr.make_exp None in
    sexp2_app_with_sort srt2_bool s2e_pgt [s2e; s2e_null]

module Plt: Scst2Type =
  Scst2Fun (struct let name = "lt_addr_addr_bool" end)
module Plte: Scst2Type =
  Scst2Fun (struct let name = "lte_addr_addr_bool" end)

module Peq: Scst2Type =
  Scst2Fun (struct let name = "eq_addr_addr_bool" end)
module Pneq: Scst2Type =
  Scst2Fun (struct let name = "neq_addr_addr_bool" end)

(* ****** ****** *)

(* defined relations *)

module Idiv_r: Scst2Type =
  Scst2Fun (struct let name = "div_int_int_int_bool" end)

module Iabs_r: Scst2Type =
  Scst2Fun (struct let name = "abs_int_int_bool" end)

module Nsub_r: Scst2Type =
  Scst2Fun (struct let name = "nsub_int_int_int_bool" end)

module Imax_r: Scst2Type =
  Scst2Fun (struct let name = "max_int_int_int_bool" end)

module Imin_r: Scst2Type =
  Scst2Fun (struct let name = "min_int_int_int_bool" end)

(* ****** ****** *)

module VTsizeof: Scst2Type =
  Scst2Fun (struct let name = "sizeof_viewt0ype_int" end)

module VTsizeof_r: Scst2Type =
  Scst2Fun (struct let name = "sizeof_viewt0ype_int_bool" end)

let sexp2_sizeof_viewt0ype_int (s2e: sexp2): sexp2 =
  let s2c = scst2_sizeof_viewt0ype_int () in
    sexp2_app_with_sort srt2_int (sexp2_cst s2c) [s2e]
(* end of [sexp2_sizeof_viewt0ype_int] *)

(* ****** ****** *)

let scst2_leq_table: (scst2, scst2 list) Hashtbl.t = Hashtbl.create 23

let scst2_leq_table_clear () = Hashtbl.clear scst2_leq_table

let scst2_leq_table_find (s2c: scst2): scst2 list =
  try Hashtbl.find scst2_leq_table s2c with Not_found -> []

let scst2_leq_table_add s2c1 s2c2 =
  Hashtbl.replace scst2_leq_table
    s2c1 (s2c2 :: scst2_leq_table_find s2c1)

let scst2_leq_table_initialize () = begin
  scst2_leq_table_clear ();
  scst2_leq_table_add (Bool_bool_t0ype.make_cst ()) (Bool_t0ype.make_cst ());

  scst2_leq_table_add (Char_char_t0ype.make_cst ()) (Char_t0ype.make_cst ());

  scst2_leq_table_add (Int_int_t0ype.make_cst ()) (Int_t0ype.make_cst ());
(*
  scst2_leq_table_add (Int_short_short_t0ype.make_cst ()) (Int_short_t0ype.make_cst ());
  scst2_leq_table_add (Int_short_t0ype.make_cst ()) (Int_t0ype.make_cst ());
  scst2_leq_table_add (Int_t0ype.make_cst ()) (Int_long_t0ype.make_cst ());
  scst2_leq_table_add (Int_long_t0ype.make_cst ()) (Int_long_long_t0ype.make_cst ());
*)
  scst2_leq_table_add (Uint_int_t0ype.make_cst ()) (Uint_t0ype.make_cst ());
(*
  scst2_leq_table_add (Uint_short_short_t0ype.make_cst ()) (Uint_short_t0ype.make_cst ());
  scst2_leq_table_add (Uint_short_t0ype.make_cst ()) (Uint_t0ype.make_cst ());
  scst2_leq_table_add (Uint_t0ype.make_cst ()) (Uint_long_t0ype.make_cst ());
  scst2_leq_table_add (Uint_long_t0ype.make_cst ()) (Uint_long_long_t0ype.make_cst ());
*)

  scst2_leq_table_add (Ptr_addr_type.make_cst ()) (Ptr_type.make_cst ());

  scst2_leq_table_add (Size_int_t0ype.make_cst ()) (Size_t0ype.make_cst ());
  scst2_leq_table_add (Ssize_int_t0ype.make_cst ()) (Ssize_t0ype.make_cst ());

  scst2_leq_table_add (String_int_type.make_cst ()) (String_type.make_cst ());

end (* end of [scst2_leq_table_initialize] *)

let rec scst2_leq (s2c1: scst2) (s2c2: scst2): bool =
  if scst2_eq s2c1 s2c2 then true
  else List.exists
    (function x -> scst2_leq x s2c2) (scst2_leq_table_find s2c1)
(* end of [scst2_leq] *)

let rec scst2_root (s2c: scst2): scst2 =
  let s2cs = scst2_leq_table_find s2c in
    match s2cs with s2c :: _ -> scst2_root s2c | [] -> s2c
(* end of [scst2_root] *)

(* ****** ****** *)

let stacst2_initialize () = begin
  scst2_leq_table_initialize ();
  clo_viewt0ype_viewt0ype_assume ();
  cloptr_viewt0ype_viewtype_assume ();
  cloref_t0ype_type_assume ();
end (* end of [stacst2_initialize] *)

(* ****** ****** *)

(* end of ats_stacst2.ml *)
