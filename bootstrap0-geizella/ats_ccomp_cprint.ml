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
 *)

(* ****** ****** *)

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

open Ats_misc
open Ats_staexp2
open Ats_staexp2_util
open Ats_dynexp2
open Ats_dynexp2_util

open Ats_hiexp
open Ats_hiexp_util
open Ats_trans4

open Ats_ccomp
open Ats_ccomp_util

(* ****** ****** *)

module PR = Printf

module Cnt = Ats_counter
module Eff = Ats_effect
module Fil = Ats_filename
module Lab = Ats_label
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_ccomp_print: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

let cprint_label (out: out_channel) (l: Lab.label): unit =
  Lab.fprint out l

let cprint_filename (out: out_channel) (f: Fil.filename): unit =
  PR.fprintf out "%s" (Fil.filename_fullname_id f)

let cprint_con (out: out_channel) (d2c: dcon2): unit =
  PR.fprintf out "%s" d2c.dcon2_fullname_id

let cprint_cst (out: out_channel) (d2c: dcst2): unit =
  PR.fprintf out "%s" d2c.dcst2_fullname_id

let cprint_funlab (out: out_channel) (fl: funlab): unit =
  PR.fprintf out "%s" fl.funlab_name

(* ****** ****** *)

let rec cprint_hityp (out: out_channel) (hit: hityp): unit =
  match hit.hityp_name with
    | HITNAM name -> PR.fprintf out "%s" name
    | HITNAM_ptr name -> PR.fprintf out "%s*" name
(* end of [cprint_hityp] *)

let rec cprint_hityp_0 (out: out_channel) (hit: hityp): unit =
  match hit.hityp_name with
    | HITNAM name -> PR.fprintf out "%s" name
    | HITNAM_ptr name -> PR.fprintf out "ats_ptr_type"
(* end of [cprint_hityp_0] *)

let rec cprint_hityp_ptr (out: out_channel) (hit: hityp): unit =
  match hit.hityp_name with
    | HITNAM_ptr name -> PR.fprintf out "%s" name
    | HITNAM name -> begin
	PR.eprintf "cprint_hityp_ptr: name = %s\n" name;
	Err.abort ();
      end
(* end of [cprint_hityp_ptr] *)

let cprint_hityp_list_with_comma (out: out_channel) (hits: hityp list): unit =
  List.iter (function hit -> PR.fprintf out ", %a" cprint_hityp hit) hits

let cprint_hityp_list (out: out_channel) (hits: hityp list): unit =
  match hits with
    | hit :: hits ->
	(cprint_hityp out hit; cprint_hityp_list_with_comma out hits)
    | [] -> ()
(* end of [cprint_hityp_list] *)

(* ****** ****** *)

let cprint_hityp_clo
  (out: out_channel) (hits_arg: hityp list) (hit_res: hityp): unit = begin
  PR.fprintf out "%a (*)(ats_clo_ptr_type%a)"
    cprint_hityp hit_res cprint_hityp_list_with_comma hits_arg
 end (* end of [cprint_hityp_clo] *)

let cprint_hityp_fun
  (out: out_channel) (hits_arg: hityp list) (hit_res: hityp): unit = begin
  PR.fprintf out "%a (*)(%a)" cprint_hityp hit_res cprint_hityp_list hits_arg
end (* end of [cprint_hityp_fun] *)

(* ****** ****** *)

let name_is_array0 (name: string): string option =
  let n = String.length name in
    if n >= 2 then
      if String.unsafe_get name 0 = '[' then
        Some (String.sub name 1 (n-2))
      else None
    else None

let cprint_hityp_rec (out: out_channel) (lnames: labstring list): unit =
  let aux (l, name) = match name_is_array0 name with
    | Some name_elt -> begin
        PR.fprintf out "%s atslab_%a[] ;\n" name_elt cprint_label l
      end
    | None -> PR.fprintf out "%s atslab_%a ;\n" name cprint_label l in
    begin
      PR.fprintf out "typedef struct {\n"; List.iter aux lnames; PR.fprintf out "}"
    end
(* end of [cprint_hityp_rec] *)

(* ****** ****** *)

let cprint_hityp_sum_con
  (tag: int) (out: out_channel) (names: string list): unit =
  let rec aux i = function
    | name :: names -> begin
	PR.fprintf out "%s atslab_%i ;\n" name i; aux (i+1) names
      end
    | [] -> () in begin match tag with
	| 0 -> begin
	    PR.fprintf out "typedef struct {\n";
	    aux 0 names;
	    PR.fprintf out "}"
	  end
	| 1 -> begin
	    PR.fprintf out "typedef struct {\nint tag ;\n";
	    aux 0 names;
	    PR.fprintf out "}"
	  end
	| _ (* -1 *) -> begin
	    PR.fprintf out "typedef struct {\nint tag ;\nchar *name ;\n";
	    aux 0 names;
	    PR.fprintf out "}"
	  end
    end
(* end of [cprint_hityp_sum_con] *)

(* ****** ****** *)

let cprint_hityp_uni (out: out_channel) (lnames: labstring list): unit =
  let aux (l, name) =
    PR.fprintf out "%s atslab_%a ;\n" name cprint_label l in begin
      PR.fprintf out "typedef union {\n"; List.iter aux lnames; PR.fprintf out "}"
    end
(* end of [cprint_hityp_uni] *)

(* ****** ****** *)

external is_printable: char -> bool = "caml_is_printable"

let cprint_bool (out: out_channel) (b: bool): unit =
  if b then PR.fprintf out "ats_true_bool" else PR.fprintf out "ats_false_bool"

let cprint_char (out: out_channel) (c: char): unit =
  match c with
    | '\'' -> PR.fprintf out "\\'"
    | '\\' -> PR.fprintf out "\\\\"
    | '\n' -> PR.fprintf out "\\n"
    | '\t' -> PR.fprintf out "\\t"
    | _ -> begin
	if is_printable c then PR.fprintf out "%c" c
	else begin
          let n = Char.code c in
	  let i3 = n mod 8 in
	  let n8 = n / 8 in
	  let i2 = n8 mod 8 in
	  let i1 = n8 / 8 in
	    PR.fprintf out "\\%i%i%i" i1 i2 i3
	end
      end
(* end of [cprint_char] *)

let cprint_char_in_string (out: out_channel) (c: char): unit =
  match c with
    | '"'  -> PR.fprintf out "\\\""
    | '\\' -> PR.fprintf out "\\\\"
    | '\n' -> PR.fprintf out "\\n"
    | '\t' -> PR.fprintf out "\\t"
    | _ -> begin
	if is_printable c then PR.fprintf out "%c" c
	else begin
          let n = Char.code c in
	  let i3 = n mod 8 in
	  let n8 = n / 8 in
	  let i2 = n8 mod 8 in
	  let i1 = n8 / 8 in
	    PR.fprintf out "\\%i%i%i" i1 i2 i3
	end
      end
(* end of [cprint_char_in_string] *)

external string_unsafe_get : string -> int -> char = "%string_unsafe_get"

let cprint_string (out: out_channel) (s: string): unit =
  for i = 0 to String.length s - 1 do
    cprint_char_in_string out (string_unsafe_get s i)
  done
(* end of [cprint_string] *)

let cprint_tmplab (out: out_channel) (tl: tmplab): unit =
  PR.fprintf out "__ats_lab_%a" Cnt.fprint tl.tmplab_stamp

let cprint_tmpvar (out: out_channel) (tmp: tmpvar): unit =
  let tmp = match tmp.tmpvar_root with None -> tmp | Some tmp -> tmp in
    PR.fprintf out "tmp%a" Cnt.fprint (tmp.tmpvar_stamp) 
(* end of [cprint_tmpvar] *)

let cprint_tmpvar_val (out: out_channel) (tmp: tmpvar): unit =
  let tmp =
    match tmp.tmpvar_root with
      | None -> tmp | Some tmp -> tmp in
    begin
      PR.fprintf out "tmp%a" Cnt.fprint (tmp.tmpvar_stamp) 
    end
(* end of [cprint_tmpvar_val] *)

(* ****** ****** *)

let the_funarg_list: (valprim list) ref = ref []
let funarg_list_set (vps: valprim list): unit = the_funarg_list := vps
let funarg_list_reset (): unit = the_funarg_list := []

let funarg_list_find (i: int): valprim option = begin
  let rec aux i = function
    | vp :: vps -> if i > 0 then aux (i-1) vps else Some vp | [] -> None in
    aux i !the_funarg_list
end (* end of [funarg_list_find] *)

(* ****** ****** *)

let rec cprint_valprim (out: out_channel) (vp: valprim): unit =
  match vp.valprim_node with
    | VParg i -> cprint_valprim_arg out i
    | VParg_ptr i -> cprint_valprim_arg_ptr out i vp.valprim_type
    | VPbool b -> cprint_bool out b
    | VPcastfn (d2c, vp_arg) -> begin
        PR.fprintf out "ats_castfn_mac(%a, %a)"
          cprint_hityp vp.valprim_type cprint_valprim vp_arg
      end (* end of [VPcastfn] *)
    | VPchar c -> PR.fprintf out "'%a'" cprint_char c
    | VPclo (_, fl, ctx) -> cprint_valprim_clo out fl ctx
    | VPcst d2c -> begin
	if dcst2_is_funcst d2c then
	  PR.fprintf out "(&%a)" cprint_cst d2c
	else cprint_cst out d2c
      end
    | VPenv vt -> begin
	let env_i = envmap_find vt in
	  if dvar2_is_mutable vt.vartyp_var then
	    PR.fprintf out "*((%a*)env%i)" cprint_hityp vp.valprim_type env_i
	  else PR.fprintf out "env%i" env_i
      end
    | VPext code -> PR.fprintf out "%s" code
    | VPfloat f -> begin
	if String.get f 0 == '~' then
	  (String.set f 0 '-'; PR.fprintf out "%s" f; String.set f 0 '~')
	else PR.fprintf out "%s" f
      end
    | VPfun fl -> PR.fprintf out "&%a" cprint_funlab fl
    | VPint (ik, i) -> PR.fprintf out "%s" (string_of_intinf i)
    | VPptrof vp -> cprint_valprim_ptrof out vp
    | VPptrof_ptr_offs (vp, offs) ->
	cprint_valprim_ptrof_ptr_offs vp out offs
    | VPptrof_var_offs (vp, offs) ->
	cprint_valprim_ptrof_var_offs vp out offs
    | VPsizeof hit -> PR.fprintf out "sizeof(%a)" cprint_hityp hit
    | VPstring s -> PR.fprintf out "\"%a\"" cprint_string s
    | VPtmp tmp -> cprint_tmpvar_val out tmp
    | VPtop -> PR.fprintf out "?top"
    | VPvoid -> PR.fprintf out "?void"
    | _ -> begin
	PR.fprintf stderr "cprint_valprim: %a\n" fprint_valprim vp;
	Err.abort ();
      end
(* end of [cprint_valprim] *)

and cprint_valprim_arg out (i: int): unit =
  match funarg_list_find i with
    | Some vp -> cprint_valprim out vp | None -> PR.fprintf out "arg%i" i

and cprint_valprim_arg_ptr out (i: int) (hit: hityp): unit =
  match funarg_list_find i with
    | Some vp ->
	PR.fprintf out "*((%a*)%a)" cprint_hityp hit cprint_valprim vp
    | None -> PR.fprintf out "*((%a*)arg%i)" cprint_hityp hit i

and cprint_valprim_clo
  (out: out_channel) (fl: funlab) (ctx: varctx): unit =
  let f = function_store_find fl in
    PR.fprintf out "(%a_clo_make (%a))"
      cprint_funlab fl (cprint_envmap ctx) f.function_envmap

and cprint_envmap (ctx: varctx)
  (out: out_channel) (envmap: envmap_t): unit =
  let aux vt i =
    let oind = envmap_find_opt vt in
    let () = if i > 0 then PR.fprintf out ", " in
      begin match oind with
	| Some ind -> PR.fprintf out "env%i" ind
	| None -> begin
	    let d2v = vt.vartyp_var in
	    let vp = varctx_find ctx d2v in
	    let () =
	      if dvar2_is_mutable d2v then PR.fprintf out "&" in
	      cprint_valprim out vp
	  end
      end in
    VarTypMap.iter aux envmap
(* end of [cprint_envmap] *)

(* ****** ****** *)

and cprint_valprim_ptrof (out: out_channel) (vp: valprim): unit =
  match vp.valprim_node with
    | VParg i -> PR.fprintf out "(&%a)" cprint_valprim_arg i
    | VParg_ptr i -> PR.fprintf out "%a" cprint_valprim_arg i
    | VPenv vt -> begin
	let env_i = envmap_find vt in PR.fprintf out "env%i" env_i
      end
    | VPtmp tmp -> PR.fprintf out "(&%a)" cprint_tmpvar tmp
    | _ -> begin
	PR.eprintf "cprint_valprim_ptrof: vp = %a\n" fprint_valprim vp;
	Err.abort ();
      end
(* end of [cprint_valprim_ptrof] *)

and cprint_valprim_ptrof_ptr_offs
  (vp: valprim) (out: out_channel) (offs: offset_t list): unit =
  PR.fprintf out "(&%a)" (cprint_valprim_select_ptr vp) offs

and cprint_valprim_ptrof_var_offs
  (vp: valprim) (out: out_channel) (offs: offset_t list): unit =
  PR.fprintf out "(&%a)" (cprint_valprim_select_var vp) offs

(* ****** ****** *)

and cprint_valprim_list
  (out: out_channel) (vps: valprim list): unit =
  let rec aux vp vps = match vps with
    | [] -> cprint_valprim out vp
    | vp1 :: vps1 -> begin
	cprint_valprim out vp; PR.fprintf out ", "; aux vp1 vps1
      end in
    match vps with vp :: vps -> aux vp vps | [] -> ()
(* end of [cprint_valprim_list] *)

and cprint_valprim_list_with_comma
  (out: out_channel) (vps: valprim list): unit =
  let aux vp = (PR.fprintf out ", "; cprint_valprim out vp) in
    List.iter aux vps
(* end of [cprint_valprim_list_with_comma] *)

(* ****** ****** *)

and cprint_select_lab
  (out: out_channel) (lab: Lab.label): unit =
  PR.fprintf out ".atslab_%a" cprint_label lab

and cprint_select_ptr_lab
  (out: out_channel) (lab: Lab.label): unit =
  PR.fprintf out "->atslab_%a" cprint_label lab

and cprint_array_ind
  (out: out_channel) (vpss: valprim list list): unit = 
  let aux vps = PR.fprintf out "[%a]" cprint_valprim_list vps in
    List.iter aux vpss

(* ****** ****** *)

and cprint_valprim_select_bef
  (out: out_channel) (offs: offset_t list): unit =
  let rec aux_list = function
    | OFFind (vpss, hit_elt) :: offs ->
	let name = name_of_hityp hit_elt in
	  (PR.fprintf out "((%s*)" name; aux_list offs)
    | OFFlab (l, hit_rec) :: offs -> begin
	let () = match hit_rec.hityp_name with
	  | HITNAM name ->
	      PR.fprintf out "("
	  | HITNAM_ptr name ->
	      PR.fprintf out "((%s*)" name in
	  aux_list offs
      end
    | [] -> () in
    aux_list offs
(* end of [cprint_valprim_select_bef] *)

and cprint_valprim_select_aft
  (out: out_channel) (offs: offset_t list): unit =
  let rec aux_list = function
    | OFFind (ind, hit_elt) :: offs ->
	(PR.fprintf out ")%a" cprint_array_ind ind; aux_list offs)
    | OFFlab (lab, hit_rec) :: offs ->
      let istyarr = label_is_tyarr (hit_rec) (lab) in
	if hityp_is_boxed hit_rec then
          let () = PR.fprintf out ")%a" cprint_select_ptr_lab lab in
          let () = if istyarr then PR.fprintf out "[0]" in (* erroneous case *)
       	  aux_list offs
	else if hityp_is_singular_rec hit_rec then
          let () = PR.fprintf out ")" in aux_list offs
	else
          let () =  PR.fprintf out ")%a" cprint_select_lab lab in
          let () = if istyarr then PR.fprintf out "[0]" in
	  aux_list offs
        (* end of [if] *)
      (* end of [let] *)
    | [] -> () in
    aux_list offs
(* end of [cprint_valprim_select_aft] *)

and cprint_valprim_select
  (vp_root: valprim)
  (out: out_channel)
  (offs: offset_t list): unit = begin
  cprint_valprim_select_bef out offs;
  cprint_valprim out vp_root;
  cprint_valprim_select_aft out offs
end (* end of [cprint_valprim_select] *)

and cprint_valprim_select_ptr
  (vp_ptr: valprim) (out: out_channel) (offs: offset_t list): unit =
  let aux_first = function
    | OFFind (ind, hit_elt) ->
      let () = PR.fprintf out "(((%a*)%a)%a)"
        cprint_hityp hit_elt cprint_valprim vp_ptr cprint_array_ind ind in ()
    | OFFlab (lab, hit_rec) ->
      let istyarr = label_is_tyarr (hit_rec) (lab) in
      let () = PR.fprintf out "(((%a*)%a)%a"
        cprint_hityp hit_rec cprint_valprim vp_ptr cprint_select_ptr_lab lab in
      let () = if istyarr then PR.fprintf out "[0]" in (* erroneous case *)
      let () = PR.fprintf out ")" in ()
  in (* in of [let] *)
  let (off, offs) = match offs with
    | off :: offs -> (off, offs)
    | [] -> error_of_deadcode
	"ats_ccomp_print: cprint_valprim_select_ptr" in
    begin
      cprint_valprim_select_bef out offs;
      aux_first off;
      cprint_valprim_select_aft out offs
    end
(* end of [cprint_valprim_select_ptr] *)

and cprint_valprim_select_var
  (vp_root: valprim) (out: out_channel) (offs: offset_t list): unit =
  let aux_first = function
    | OFFind (ind, hit_elt) ->
      let () = PR.fprintf out "(((%a*)%a)%a)"
        cprint_hityp hit_elt cprint_valprim_ptrof vp_root cprint_array_ind ind in ()
    | OFFlab (lab, hit_rec) ->
      let istyarr = label_is_tyarr (hit_rec) (lab) in        
	if hityp_is_boxed hit_rec then
          let () = PR.fprintf out "(((%a)%a)%a"
            cprint_hityp hit_rec cprint_valprim vp_root cprint_select_ptr_lab lab in
          let () = if istyarr then PR.fprintf out "[0]" in (* erroneous case *)
          let () = PR.fprintf out ")" in ()          
	else if hityp_is_singular_rec hit_rec then
          let () = PR.fprintf out "((%a)%a)"
            cprint_hityp hit_rec cprint_valprim vp_root in ()
	else
          let () = PR.fprintf out "((%a)%a"
            cprint_valprim vp_root cprint_select_lab lab in
          let () = if istyarr then PR.fprintf out "[0]" in
          let () = PR.fprintf out ")" in ()          
	(* end of [if] *)
  in (* end of [let] *)
  let (off, offs) = match offs with
    | off :: offs -> (off, offs)
    | [] -> begin
	error_of_deadcode
	  "ats_ccomp_print: cprint_valprim_select_var"
      end in
    begin
      cprint_valprim_select_bef out offs;
      aux_first off;
      cprint_valprim_select_aft out offs
    end
(* end of [cprint_valprim_select_var] *)

(* ****** ****** *)

let cprint_envarg (out: out_channel) (m: envmap_t): unit =
  let aux vt i =
    if i > 0 then PR.fprintf out ", env%i" i else PR.fprintf out "env0" in
    VarTypMap.iter aux m
(* end of [cprint_envarg] *)

let cprint_apply (out: out_channel) (tmp_res: tmpvar)
  (hit_fun: hityp) (vp_fun: valprim) (vps_arg: valprim list): unit =
  let (fcr, hits_arg, hit_res) = match hit_fun.hityp_node with
    | HITfun (fc, hits_arg, hit_res) -> (fc, hits_arg, hit_res)
    | _ -> error_of_deadcode "ats_ccomp_print: cprint_apply" in
  let () =
    if hityp_is_void hit_res then
      PR.fprintf out "/* %a = */ " cprint_tmpvar_val tmp_res
    else
      PR.fprintf out "%a = " cprint_tmpvar_val tmp_res in
    begin match fcr with
      | Syn.FUNCLOclo _ -> begin
	  PR.fprintf out "(("; cprint_hityp_clo out hits_arg hit_res;
          PR.fprintf out ")(ats_closure_fun(%a))) (%a%a) ;"
	    cprint_valprim vp_fun cprint_valprim vp_fun
	    cprint_valprim_list_with_comma vps_arg
	end
      | Syn.FUNCLOfun -> begin
	  PR.fprintf out "(("; cprint_hityp_fun out hits_arg hit_res;
          PR.fprintf out ")%a) (%a) ;"
	    cprint_valprim vp_fun cprint_valprim_list vps_arg
	end
    end
(* end of [cprint_apply] *)

(* ****** ****** *)

let cprint_cont
  (out: out_channel) (k: cont_t): unit = match k with
  | CONTtmplab tl ->
      PR.fprintf out "goto %a" cprint_tmplab tl
  | CONTfunarg_fail fl ->
      PR.fprintf out "ats_funarg_match_failure_handle(\"GEIZELLA\")"
  | CONTmatch_fail ->
      PR.fprintf out "ats_caseof_failure_handle(\"GEIZELLA\")"
  | CONTraise vp ->
      PR.fprintf out "ats_raise_exn(%a)" cprint_valprim vp
(* end of [cprint_cont] *)

(* ****** ****** *)

let cprint_move_con_arg_list (out: out_channel)
  (tmp: tmpvar) (hit_sum: hityp) (vps_arg: valprim list): unit =
  let rec aux i = function
    | vp :: vps -> begin match vp.valprim_node with
	| VPtop -> aux (i+1) vps
	| _ -> begin
	    PR.fprintf out "((%a)%a)->atslab_%i = %a ;\n"
	      cprint_hityp hit_sum cprint_tmpvar_val tmp i cprint_valprim vp;
	    aux (i+1) vps
	  end
      end (* end of [::] *)
    | [] -> () in
    aux 0 vps_arg
(* end of [cprint_move_con_arg_list] *)

(* ****** ****** *)

let rec cprint_instr (out: out_channel) (i: instr_t): unit =
  match i with
    | Iarray (tmp_res, hit_elt, vps_elt) -> begin
	cprint_instr_array out tmp_res hit_elt vps_elt
      end
    | Icall (tmp_res, hit_fun, vp_fun, vps_arg) -> begin
	match vp_fun.valprim_node with
	  | VPcst d2c -> begin
	      let is_var_fun = sexp2_is_var_fun d2c.dcst2_type in
	      let () =
		if is_var_fun || hityp_fun_is_void hit_fun then begin
		  PR.fprintf out "/* %a = */ " cprint_tmpvar_val tmp_res
		end else begin
		  PR.fprintf out "%a = " cprint_tmpvar_val tmp_res
		end in begin
		if dcst2_is_funcst d2c then
		  PR.fprintf out "%a (%a) ;"
		    cprint_cst d2c cprint_valprim_list vps_arg
		else
		  PR.fprintf out "%a_fun (%a) ;"
		    cprint_cst d2c cprint_valprim_list vps_arg
		end
	    end
	  | VPclo (i, fl, ctx) -> begin
              let envmap =
		let f = function_store_find fl in f.function_envmap in
	      let () =
		if hityp_fun_is_void fl.funlab_type then begin
		  PR.fprintf out "/* %a = */ " cprint_tmpvar_val tmp_res
		end else begin
		  PR.fprintf out "%a = " cprint_tmpvar_val tmp_res
		end in begin
		  PR.fprintf out "%a (%a"
		    cprint_funlab fl (cprint_envmap ctx) envmap;
		  if VarTypMap.is_empty envmap then cprint_valprim_list out vps_arg
		  else cprint_valprim_list_with_comma out vps_arg;
		  PR.fprintf out ") ;"
		end
	    end
	  | VPfun fl -> begin
	      let () =
		if hityp_fun_is_void fl.funlab_type then begin
		  PR.fprintf out "/* %a = */ " cprint_tmpvar_val tmp_res
		end else begin
		  PR.fprintf out "%a = " cprint_tmpvar_val tmp_res
		end in begin
		  PR.fprintf out "%a (%a) ;"
		    cprint_funlab fl cprint_valprim_list vps_arg
		end
	    end
	  | _ -> cprint_apply out tmp_res hit_fun vp_fun vps_arg
      end
    | Icall_tail (tmp_res, fl, tmps_arg, vps_arg) -> begin
	let rec aux1 n = function
	  | vp :: vps -> begin
	      PR.fprintf out
		"%a = %a ;\n" cprint_valprim_arg n cprint_valprim vp;
	      aux1 (n+1) vps
	    end
	  |  _ -> begin
	       PR.fprintf out "goto __ats_lab_%a ;" cprint_funlab fl
	     end in
	let rec aux2 n tmps vps = match tmps, vps with
	  | tmp :: tmps, vp :: vps -> begin
	      PR.fprintf out "%a = %a ;\n" cprint_tmpvar_val tmp cprint_valprim vp;
	      aux2 (n+1) tmps vps
	    end
	  | _, _ -> aux1 n vps in
	  aux2 0 tmps_arg vps_arg
      end
    | Icond (vp, is1, is2) -> PR.fprintf out "if (%a) {\n%a} else {\n%a} /* if */"
	cprint_valprim vp cprint_instr_list is1 cprint_instr_list is2
    | Idefine_clo (d2c, fl) -> begin
	PR.fprintf out "ats_gc_markroot (&%a, sizeof(ats_ptr_type)) ;\n" cprint_cst d2c;
	PR.fprintf out "%a = %a_clo_make () ;" cprint_cst d2c cprint_funlab fl
      end
    | Idefine_fun (d2c, fl) ->
	PR.fprintf out "%a = &%a ;" cprint_cst d2c cprint_funlab fl
    | Idefine_val (d2c, vp) -> begin
	PR.fprintf out "ats_gc_markroot (&%a, sizeof(%a)) ;\n"
	  cprint_cst d2c cprint_hityp vp.valprim_type;
	PR.fprintf out "%a = %a ;" cprint_cst d2c cprint_valprim vp
      end
    | Iextern code -> PR.fprintf out "%s ;" code
    | Ifunction (tmp_res, vps_arg, res_body, tmp_ret) -> begin
	let () = funarg_list_set vps_arg in
	let () = cprint_instr_list out res_body in
	let () = funarg_list_reset () in begin
	  if tmpvar_is_void tmp_ret then
	    if tmp_res.tmpvar_isret then PR.fprintf out "return ;\n"
	    else
	      PR.fprintf out "/* %a = %a */ ;\n"
		cprint_tmpvar_val tmp_res cprint_tmpvar_val tmp_ret
	  else
	    if tmp_res.tmpvar_isret then
	      PR.fprintf out "return %a ;\n" cprint_tmpvar_val tmp_ret
	    else
	      PR.fprintf out "%a = %a ;\n"
		cprint_tmpvar_val tmp_res cprint_tmpvar_val tmp_ret
	  end
      end
    | Ifreeptr vp ->
	PR.fprintf out "ATS_FREE(%a) ;" cprint_valprim vp
    | Ilabel_fun fl -> PR.fprintf out "__ats_lab_%a:" cprint_funlab fl
    | Iload_file filename ->
	PR.fprintf out "%a__dynload () ;" cprint_filename filename
    | Iload_ptr (tmp, vp_ptr) -> begin
	let hit_tmp = tmp.tmpvar_type in
	  PR.fprintf out "%a = *((%a*)%a) ;"
	    cprint_tmpvar_val tmp cprint_hityp hit_tmp cprint_valprim vp_ptr
      end
    | Iload_ptr_offs (tmp, vp_ptr, offs) -> begin
	PR.fprintf out "%a = %a ;"
	  cprint_tmpvar_val tmp (cprint_valprim_select_ptr vp_ptr) offs
      end
    | Iload_var (tmp, vp_var) -> PR.fprintf out "%a = %a ;"
	cprint_tmpvar_val tmp cprint_valprim vp_var
    | Iload_var_offs (tmp, vp_var, offs) -> begin
	PR.fprintf out "%a = %a ;"
	  cprint_tmpvar_val tmp (cprint_valprim_select_var vp_var) offs
      end
    | Iloopexn (i, tl) -> PR.fprintf out "goto %a ;" cprint_tmplab tl
    | Imove_con (tmp, hit_sum, d2c, vps) -> begin match vps with
	| _ :: _ -> begin
	    let () =
	      PR.fprintf out "%a = ATS_MALLOC(sizeof(%a)) ;\n"
		cprint_tmpvar_val tmp cprint_hityp_ptr hit_sum in
	    let () =
	      if dcon2_is_exn d2c then begin
		PR.fprintf out "((ats_exn_ptr_type)%a)->tag = %a.tag ;\n"
		    cprint_tmpvar_val tmp cprint_con d2c;
		PR.fprintf out "((ats_exn_ptr_type)%a)->name = %a.name ;\n"
		    cprint_tmpvar_val tmp cprint_con d2c;
	      end else begin
		if dcon2_is_cons_like d2c then ()
		else if dcon2_is_singular d2c then ()
		else begin
		  PR.fprintf out "((ats_sum_ptr_type)%a)->tag = %i ;\n"
		    cprint_tmpvar_val tmp d2c.dcon2_tag;
		end
	      end in
	    let () = cprint_move_con_arg_list out tmp hit_sum vps in ()
	  end
	| [] -> begin
	    let is_nil = dcon2_is_nil_like d2c in
	      if is_nil then begin
		PR.fprintf out "%a = (ats_sum_ptr_type)0 ;\n"
		  cprint_tmpvar_val tmp
	      end else begin
		PR.fprintf out "%a = (ats_sum_ptr_type)(&%a) ;\n"
		  cprint_tmpvar_val tmp cprint_con d2c
	      end
	  end
      end
    | Imove_rec_flt (tmp, hit_rec, lvps) -> begin
	let aux (l, vp) =
	  PR.fprintf out "%a.atslab_%a = %a ;\n"
	    cprint_tmpvar_val tmp cprint_label l cprint_valprim vp in
	  List.iter aux lvps
      end
    | Imove_rec_box (tmp, hit_rec, lvps) -> begin
	let aux (l, vp) =
	  PR.fprintf out "((%a)%a)->atslab_%a = %a ;\n"
	    cprint_hityp hit_rec cprint_tmpvar_val tmp
	    cprint_label l cprint_valprim vp in
	  begin
	    PR.fprintf out "%a = ATS_MALLOC(sizeof(%a)) ;\n"
              cprint_tmpvar_val tmp cprint_hityp_ptr hit_rec;
	    List.iter aux lvps
	  end
      end
    | Imove_val (tmp, vp) -> begin
	if valprim_is_void vp then
	  PR.fprintf out "/* %a = %a */ ;"
	    cprint_tmpvar_val tmp cprint_valprim vp
	else
	  PR.fprintf out "%a = %a ;"
	    cprint_tmpvar_val tmp cprint_valprim vp
      end
    | Iparallel_spawn (tmp_ret, vp_clo) -> begin
	PR.fprintf out "%a = atslib_parallel_spawn (%a) ;"
	  cprint_tmpvar tmp_ret cprint_valprim vp_clo
      end
    | Iparallel_sync (tmp_ret) -> begin
	PR.fprintf out "atslib_parallel_sync (%a) ;" cprint_tmpvar tmp_ret
      end
    | Ipatck (vp, pck, k_fail) -> cprint_patck out vp pck k_fail
    | Iraise vp -> PR.fprintf out "ats_raise_exn(%a) ;" cprint_valprim vp
    | Irefval (tmp_res, vp) -> cprint_instr_refval out tmp_res vp
    | Iselcon (tmp, vp, hit_sum, i) -> begin
	PR.fprintf out "%a = ((%a)%a)->atslab_%i ;"
	  cprint_tmpvar tmp cprint_hityp hit_sum cprint_valprim vp i
      end
    | Iselcon_ptr (tmp, vp, hit_sum, i) -> begin
	PR.fprintf out "%a = &(((%a)%a)->atslab_%i) ;"
	  cprint_tmpvar tmp cprint_hityp hit_sum cprint_valprim vp i
      end
    | Iselect (tmp, vp_root, offs) -> begin
	if tmpvar_is_void tmp then
	  PR.fprintf out "/* %a = %a */;"
	    cprint_tmpvar_val tmp (cprint_valprim_select vp_root) offs
	else
	  PR.fprintf out "%a = %a ;"
	    cprint_tmpvar_val tmp (cprint_valprim_select vp_root) offs
      end
    | Istore_ptr (vp_ptr, vp_val) -> begin
	PR.fprintf out "*((%a*)%a) = %a ;"
	  cprint_hityp vp_val.valprim_type cprint_valprim vp_ptr
	  cprint_valprim vp_val
      end
    | Istore_ptr_offs (vp_ptr, offs, vp_val) -> begin
	PR.fprintf out "%a = %a ;"
	  (cprint_valprim_select_ptr vp_ptr) offs cprint_valprim vp_val
      end
    | Istore_var (vp_var, vp_val) -> PR.fprintf out "%a = %a ;"
	cprint_valprim vp_var cprint_valprim vp_val
    | Istore_var_offs (vp_var, offs, vp_val) -> begin
	PR.fprintf out "%a = %a ;"
	  (cprint_valprim_select_var vp_var) offs cprint_valprim vp_val
      end
    | Iswitch brs -> begin
	PR.fprintf out "do {\n"; List.iter (cprint_branch out) brs;
	PR.fprintf out "} while (0) ;"
      end
    | Itrywith (res_try, tmp_exn, brs) -> begin
	PR.fprintf out "ATS_TRYWITH_TRY(%a)\n" cprint_tmpvar_val tmp_exn;
	cprint_instr_list out res_try;
	PR.fprintf out "ATS_TRYWITH_WITH(%a)\n" cprint_tmpvar_val tmp_exn;
	PR.fprintf out "do {\n"; List.iter (cprint_branch out) brs;
	PR.fprintf out "} while (0) ;\n";
	PR.fprintf out "ATS_TRYWITH_END() ;\n";
      end
    | Iwhile (blab, clab, vp_test, is_test, is_body) -> begin
	PR.fprintf out
	  "ats_while_beg_mac(%a)\n" cprint_tmplab clab;
	cprint_instr_list out is_test;
	PR.fprintf out
	  "if (!%a) break ;\n" cprint_valprim vp_test;
	cprint_instr_list out is_body;
	PR.fprintf out
	  "ats_while_end_mac(%a, %a)\n" cprint_tmplab blab cprint_tmplab clab
      end
    | Ivardec tmp -> begin
	PR.fprintf out "/* %a %a ; */"
	  cprint_hityp tmp.tmpvar_type cprint_tmpvar_val tmp
      end
    | _ -> begin
	PR.fprintf stderr "cprint_instr: %a\n" fprint_instr i;
	Err.abort ();
      end
(* end of [cprint_instr] *)

and cprint_instr_list (out: out_channel) (is: instr_t list): unit =
  List.iter (function i -> PR.fprintf out "%a\n" cprint_instr i) is

(* ****** ****** *)

and cprint_instr_array (out: out_channel)
  (tmp_res: tmpvar) (sz: int) (hit_elt: hityp): unit = begin
  PR.fprintf out "/* array allocation */\n";
  PR.fprintf out "%a.atslab_2 = atspre_array_ptr_alloc_tsz(%i, sizeof(%a)) ;\n"
    cprint_tmpvar_val tmp_res sz cprint_hityp hit_elt;
  PR.fprintf out "%a.atslab_3 = %i ;\n" cprint_tmpvar_val tmp_res sz;
end (* end of [cprint_instr_array] *)

and cprint_instr_refval
  (out: out_channel) (tmp_res: tmpvar) (vp: valprim): unit = begin
  PR.fprintf out "/* reference allocation */\n";
  PR.fprintf out "%a = ATS_MALLOC(sizeof(%a)) ;\n"
    cprint_tmpvar_val tmp_res cprint_hityp (vp.valprim_type);
  PR.fprintf out "*(ats_ptr_type*)%a = %a ;\n"
    cprint_tmpvar_val tmp_res cprint_valprim vp;
end (* end of [cprint_instr_refval] *)

(* ****** ****** *)

and cprint_patck (out: out_channel)
  (vp: valprim) (pck: patck) (k_fail: cont_t): unit =
  match pck with
    | PATCKbool b -> begin
	if b then PR.fprintf out
	  "if (!%a) { %a ; }" cprint_valprim vp cprint_cont k_fail
	else PR.fprintf out
	  "if (%a) { %a ; }" cprint_valprim vp cprint_cont k_fail
      end
    | PATCKchar c -> PR.fprintf out "if (%a != '%a') { %a ; }"
	cprint_valprim vp cprint_char c cprint_cont k_fail
    | PATCKcon d2c -> begin
	let s2c = d2c.dcon2_scst in begin match s2c with
	  | _ when scst2_is_singular s2c -> ()
	  | _ -> begin match s2c.scst2_islst with
	      | Some (d2c_nil, _) -> begin
		  if dcon2_eq d2c d2c_nil then
		    PR.fprintf out "if (%a != (ats_sum_ptr_type)0) { %a ; }"
		      cprint_valprim vp cprint_cont k_fail 
		  else
		    PR.fprintf out "if (%a == (ats_sum_ptr_type)0) { %a ; }"
		      cprint_valprim vp cprint_cont k_fail 
		end
	      | None -> begin
		  if d2c.dcon2_arity_real == 0 then
		    PR.fprintf out "if (%a != &%a) { %a ; }"
		      cprint_valprim vp cprint_con d2c cprint_cont k_fail 
		  else 
		    PR.fprintf out
		      "if (((ats_sum_ptr_type)%a)->tag != %i) { %a ; }"
		      cprint_valprim vp d2c.dcon2_tag cprint_cont k_fail
		end
	    end (* end of [_] *)
	  end (* end of [let] *)
      end (* PATCKcon *)
    | PATCKexn d2c -> begin
	if d2c.dcon2_arity_real == 0 then
	  PR.fprintf out "if (%a != &%a) { %a ; }"
	    cprint_valprim vp cprint_con d2c cprint_cont k_fail
	else
	  PR.fprintf out
	    "if (((ats_exn_ptr_type)%a)->tag != %a.tag) { %a ; }"
	    cprint_valprim vp cprint_con d2c cprint_cont k_fail
      end
    | PATCKint i -> PR.fprintf out "if (%a != %s) { %a ; }"
	cprint_valprim vp (string_of_intinf i) cprint_cont k_fail
    | PATCKstring s  -> PR.fprintf out "if (strcmp(%a, \"%a\")) { %a ; }"
	cprint_valprim vp cprint_string s cprint_cont k_fail
(* end of [cprint_patck] *)

and cprint_branch (out: out_channel) (br: branch_t): unit =
  let (br_lab, br_body) = br in
    PR.fprintf out "%a:\n%abreak ;\n\n"
      cprint_tmplab br_lab cprint_instr_list br_body
(* end of [cprint_branch] *)

(* ****** ****** *)

let cprint_tailjoin_switch_case
  (out: out_channel) (tag: int) (fl: funlab) (tmps_arg: tmpvar list): unit =
  let aux tmp =
    PR.fprintf out "%a = va_arg(funarg, %a) ;\n"
      cprint_tmpvar_val tmp cprint_hityp tmp.tmpvar_type in
    begin
      PR.fprintf out "case %i:\n" tag;
      PR.fprintf out "va_start(funarg, funtag) ;\n";
      List.iter aux tmps_arg;
      PR.fprintf out "va_end(funarg) ;\n";
      PR.fprintf out "goto __ats_lab_%a ;\n\n" cprint_funlab fl;
    end
(* end of [cprint_tailjoin_switch_case] *)

let cprint_tailjoin_switch (out: out_channel)
  (tag_fl_tmps_list: (int * funlab * tmpvar list) list): unit =
  begin
    PR.fprintf out "va_list funarg ;\n\n";
    PR.fprintf out "switch (funtag) {\n";
    List.iter
      (function (tag, fl, tmps) -> cprint_tailjoin_switch_case out tag fl tmps)
      tag_fl_tmps_list;
    PR.fprintf out "default: exit(1) ; /* deadcode */\n} /* end of switch */\n\n";
  end
(* end of [cprint_tailjoin_switch] *)

(* ****** ****** *)

let cprint_funarg
  (is_empty: bool) (out: out_channel) (hits: hityp list): unit =
  let rec aux i hit hits = match hits with
    | hit1 :: hits1 -> begin
	PR.fprintf out "%a arg%i, " cprint_hityp hit i;
	aux (i+1) hit1 hits1
      end
    | [] -> PR.fprintf out "%a arg%i" cprint_hityp hit i in
    match hits with
      | hit :: hits -> begin
	  if not (is_empty) then PR.fprintf out ", ";
	  aux 0 hit hits
	end
      | [] -> ()
(* end of [cprint_funarg] *)

let cprint_funenvarg (out: out_channel) (m: envmap_t): unit =
  let aux vt env_i =
    let d2v = vt.vartyp_var in
    let () = if env_i > 0 then PR.fprintf out ", " in
      begin
	if dvar2_is_mutable d2v then PR.fprintf out "ats_ptr_type env%i" env_i
	else PR.fprintf out "%a env%i" cprint_hityp vt.vartyp_typ env_i
      end in
    VarTypMap.iter aux m
(* end of [cprint_funenvarg] *)

(* tailjoin *)
let cprint_funarg_tj (out: out_channel) (is_empty: bool): unit =
  if is_empty then PR.fprintf out "int funtag, ..."
  else PR.fprintf out ", int funtag, ..."

(* ****** ****** *)

let cprint_tmpvar_dec_local (out: out_channel) (tmp: tmpvar): unit =
  let tmp = match tmp.tmpvar_root with None -> tmp | Some tmp -> tmp in
    if tmpvar_is_void tmp then
      PR.fprintf out "ATSlocal_void(%a) ;" cprint_tmpvar_val tmp
    else PR.fprintf out "ATSlocal(%a, %a) ;"
      cprint_hityp tmp.tmpvar_type cprint_tmpvar_val tmp
(* end of [cprint_tmpvar_dec_local] *)

let cprint_tmpset_dec_local
  (out: out_channel) (tmpset: TmpVarSet.t): unit =
  let aux tmp = PR.fprintf out "%a\n" cprint_tmpvar_dec_local tmp in
    TmpVarSet.iter aux tmpset
(* end of [cprint_tmpset_dec_local] *)

let cprint_tmpvar_dec_static (out: out_channel) (tmp: tmpvar): unit =
  let tmp = match tmp.tmpvar_root with None -> tmp | Some tmp -> tmp in
    if tmpvar_is_void tmp then
      PR.fprintf out "ATSstatic_void(tmp%a) ;" Cnt.fprint (tmp.tmpvar_stamp)
    else PR.fprintf out "ATSstatic(%a, tmp%a) ;"
      cprint_hityp (tmp.tmpvar_type) Cnt.fprint (tmp.tmpvar_stamp)
(* end of [cprint_tmpvar_dec_static] *)

let cprint_tmpset_dec_static
  (out: out_channel) (tmpset: TmpVarSet.t): unit =
  let aux tmp =
    PR.fprintf out "%a\n" cprint_tmpvar_dec_static tmp in begin
    TmpVarSet.iter aux tmpset;
    if not (TmpVarSet.is_empty tmpset) then PR.fprintf out "\n";
  end
(* end of [cprint_tmpset_dec_static] *)

let cprint_tmpset_markroot_static
  (out: out_channel) (tmpset: TmpVarSet.t): unit =
  let aux tmp =
    if not (tmpvar_is_void tmp) then begin
      PR.fprintf out "ats_gc_markroot(&tmp%a, sizeof(%a)) ;\n"
	Cnt.fprint (tmp.tmpvar_stamp) cprint_hityp (tmp.tmpvar_type)
    end in
    TmpVarSet.iter aux tmpset
(* end of [cprint_tmpset_markroot] *)

(* ****** ****** *)

let cprint_global_list (out: out_channel) (res: instr_t list): unit =
  let rec aux = function
    | i :: is -> begin
	let () = match i with
	  | Idefine_clo (d2c, fl) ->
	      PR.fprintf out "ATSglobal(ats_clo_ptr_type, %a) ;\n" cprint_cst d2c
	  | Idefine_fun (d2c, fl) ->
	      PR.fprintf out "ATSglobal(ats_fun_ptr_type, %a) ;\n" cprint_cst d2c
	  | Idefine_val (d2c, vp) -> begin
	      let hit = sexp2_tr_0 (d2c.dcst2_type) in
	      let hit = hityp_nf hit in
		PR.fprintf out "ATSglobal(%a, %a) ;\n" cprint_hityp hit cprint_cst d2c
	    end
	  | _ -> () in
	  aux is
      end
    | [] -> () in
    aux res

(* ****** ****** *)

let cprint_dyncon_list (out: out_channel): unit =
  let aux d2c =
    if dcon2_is_exn d2c then  
      PR.fprintf out "ATSextern(ats_exn_type, %a) ;\n" cprint_con d2c
    else
      PR.fprintf out "ATSextern(ats_sum_type, %a) ;\n" cprint_con d2c in
  let d2cs = dyncon_set_get () in begin
    DconSet.iter aux d2cs;
    if not (DconSet.is_empty d2cs) then PR.fprintf out "\n"
  end
(* end of [cprint_dyncon_list] *)

let cprint_dyncst_list (out: out_channel): unit =
  let aux d2c = 
    let hit = sexp2_tr_1 (d2c.dcst2_type) in
    let hit = hityp_nf hit in match hit.hityp_node with
      | HITfun (fc, hits_arg, hit_res) -> begin match fc with
	  | Syn.FUNCLOclo _ -> begin
	      PR.fprintf out "ATSextern(ats_clo_ptr_type, %a) ;\n" cprint_cst d2c;
	      PR.fprintf out "extern %a %a_fun(%a) ;\n"
		cprint_hityp hit_res cprint_cst d2c cprint_hityp_list hits_arg
	    end
	  | Syn.FUNCLOfun -> begin match d2c.dcst2_kind with
	      | Syn.DCKfun -> PR.fprintf out "extern %a %a(%a) ;\n"
		  cprint_hityp hit_res cprint_cst d2c cprint_hityp_list hits_arg
	      | _ -> begin
		  PR.fprintf out "ATSextern(ats_fun_ptr_type, %a) ;\n" cprint_cst d2c;
		  PR.fprintf out "extern %a %a_fun(%a) ;\n"
		    cprint_hityp hit_res cprint_cst d2c cprint_hityp_list hits_arg
		end
	    end
	end
      | _ -> begin
	  PR.fprintf out "ATSextern(%a, %a) ;\n" cprint_hityp_0 hit cprint_cst d2c
      end in
  let aux_if d2c = begin
    let skip =
      match d2c.dcst2_decarg with _ :: _ -> true | [] -> false in
    let skip =
      if skip then true else Syn.dcstextdef_is_mac (d2c.dcst2_extdef) in
      if not (skip) then aux d2c
  end in
  let d2cs = dyncst_set_get () in begin
    DcstSet.iter aux_if d2cs; if not (DcstSet.is_empty d2cs) then PR.fprintf out "\n"
  end
(* end of [cprint_dyncst_list] *)

(* ****** ****** *)

let cprint_sum_con_list (out: out_channel): unit =
  let aux (s2c: scst2): unit =
    let d2cs = match s2c.scst2_cons with Some d2cs -> d2cs | None -> [] in
      List.iter
	(function d2c ->
	   PR.fprintf out "ATSglobal(ats_sum_type, %a) ;\n" cprint_con d2c)
	d2cs in
  let s2cs = sum_cst_set_get () in
    (ScstSet.iter aux s2cs; if not (ScstSet.is_empty s2cs) then PR.fprintf out "\n")
(* end of [cprint_sum_con_list] *)

(* ****** ****** *)

let cprint_exn_con_list (out: out_channel): unit =
  let aux d2c =
    PR.fprintf out "ATSglobal(ats_exn_type, %a) ;\n" cprint_con d2c in
  let d2cs = exn_con_set_get () in
    (DconSet.iter aux d2cs; if not (DconSet.is_empty d2cs) then PR.fprintf out "\n")
(* end of [cprint_exn_con_list] *)

(* ****** ****** *)

let cprint_function_prototypes
  (out: out_channel) (f: function_t): unit =
  let fl = f.function_lab in
  let (fc, hits_arg, hit_res) = funlab_type_fntp_arg_res fl in
  let envmap = f.function_envmap in
  let aux_fun () =
    let is_empty = VarTypMap.is_empty envmap in
      PR.fprintf out "static %a %a (%a%a) ;\n"
	cprint_hityp hit_res cprint_funlab fl
        cprint_funenvarg envmap (cprint_funarg is_empty) hits_arg in
  let aux_fun_tj () = (* tj: tailjoin *)
    let is_empty = VarTypMap.is_empty envmap in
      PR.fprintf out "static %a %a (%a%a) ;\n"
	cprint_hityp hit_res cprint_funlab fl
        cprint_funenvarg envmap cprint_funarg_tj is_empty in
  let aux_clofun () =
    begin
      PR.fprintf out "static %a %a_clofun (ats_clo_ptr_type clo%a) ;\n"
	cprint_hityp hit_res cprint_funlab fl
	(cprint_funarg false) hits_arg;
    end in
  let aux_clo_make () =
    begin
      PR.fprintf out "static ats_clo_ptr_type %a_clo_make (" cprint_funlab fl;
      cprint_funenvarg out envmap;
      PR.fprintf out ") ;\n"
    end in 
    match fl.funlab_global with
      | Some d2c -> begin match fc with
	  | Syn.FUNCLOclo _ ->
	      (aux_clofun (); aux_clo_make (); PR.fprintf out "\n")
	  | Syn.FUNCLOfun -> ()
	end (* end of [Some] *)
      | None -> begin match fc with
	  | Syn.FUNCLOclo _ -> begin
	      if function_is_tailjoin f then (aux_fun_tj (); PR.fprintf out "\n")
	      else (aux_fun (); aux_clofun (); aux_clo_make (); PR.fprintf out "\n")
	    end
	  | Syn.FUNCLOfun -> (aux_fun (); PR.fprintf out "\n")
	end (* end of [None] *)
(* end of [cprint_function_prototypes] *)

(* ****** ****** *)

let cprint_time_stamp (out: out_channel): unit =
  let tm = Unix.localtime (Unix.time ()) in begin
    PR.fprintf out
      "/*\n *\n * This C code is generated by ATS/Geizella\n";
    PR.fprintf out
      " * The compilation time is: %i-%i-%i: %i:%i\n *\n */\n\n"
      (1900+tm.Unix.tm_year) (1+tm.Unix.tm_mon) tm.Unix.tm_mday
      tm.Unix.tm_hour tm.Unix.tm_min;
  end (* end of [let] *)
(* end of [cprint_time_stamp] *)

(* ****** ****** *)

let cprint_include_h (out: out_channel): unit = begin
  PR.fprintf out "#include \"ats_config.h\"\n";
  PR.fprintf out "#include \"ats_basics.h\"\n";
  PR.fprintf out "#include \"ats_types.h\"\n";
  PR.fprintf out "#include \"ats_exception.h\"\n";
  PR.fprintf out "#include \"ats_memory.h\"\n";
  PR.fprintf out "\n"
end (* end of [cprint_include_h] *)

let cprint_include_cats (out: out_channel): unit = begin
  PR.fprintf out "#include \"prelude/CATS/array.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/basics.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/bool.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/byte.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/char.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/float.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/integer.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/pointer.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/printf.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/reference.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/sizetype.cats\"\n";
  PR.fprintf out "#include \"prelude/CATS/string.cats\"\n";
  PR.fprintf out "\n"
end (* end of [cprint_include_cats] *)

(* ****** ****** *)

let cprint_extypes (out: out_channel): unit = begin
  let aux (name, hit) =
    PR.fprintf out "typedef %a %s ;\n\n" cprint_hityp hit name in
  let name_hit_list = extype_list_get () in
    List.iter aux name_hit_list
end (* end of [cprint_extypes] *)

(* ****** ****** *)

let cprint_extcodes_top (out: out_channel): unit =
  let aux (position, code) =
    if (position == 0) then PR.fprintf out "%s\n" code in
    List.iter aux (extcode_list_get ())
(* end of [cprint_extcodes_top] *)

let cprint_extcodes_mid (out: out_channel): unit =
  let aux (position, code) =
    if (position == 1) then PR.fprintf out "%s\n" code in
    List.iter aux (extcode_list_get ())
(* end of [cprint_extcodes_mid] *)

let cprint_extcodes_bot (out: out_channel): unit =
  let aux (position, code) =
    if (position > 1) then PR.fprintf out "%s\n" code in
    List.iter aux (extcode_list_get ())
(* end of [cprint_extcodes_bot] *)

(* ****** ****** *)

let cprint_hityp_definitions (out: out_channel): unit =
  let aux (tk, name_def) = match tk with
    | TYKEYrec lnames ->
	PR.fprintf out "%a %s ;\n\n" cprint_hityp_rec lnames name_def
    | TYKEYsum (tag, names) ->
	PR.fprintf out "%a %s ;\n\n" (cprint_hityp_sum_con tag) names name_def
    | _ -> () in
    List.iter aux (typedef_list_get ())
(* end of [cprint_hityp_definitions] *)

(* ****** ****** *)

let cprint_function_clo_type
  (out: out_channel) (fl: funlab) (envmap: envmap_t): unit =
  let aux vt i =
    let d2v = vt.vartyp_var in
    let hit = vt.vartyp_typ in
      begin
	if dvar2_is_mutable d2v then
	  PR.fprintf out "ats_ptr_type closure_env_%i ;\n" i
	else
	  PR.fprintf out "%a closure_env_%i ;\n" cprint_hityp hit i
      end in
    begin
      PR.fprintf out "typedef struct {\nats_fun_ptr_type closure_fun ;\n";
      VarTypMap.iter aux envmap;
      PR.fprintf out "} %a_clo_type ;\n\n" cprint_funlab fl
    end
(* end of [cprint_function_clo_type] *)

let cprint_function_clo_make
  (out: out_channel) (fl: funlab) (envmap: envmap_t): unit =
  let aux1 vt i =
    let d2v = vt.vartyp_var in
    let hit = vt.vartyp_typ in
    let () = if i > 0 then PR.fprintf out ", " in
      begin
	if dvar2_is_mutable d2v then PR.fprintf out "ats_ptr_type env%i" i
	else PR.fprintf out "%a env%i" cprint_hityp hit i
      end in
  let aux2 vt i = PR.fprintf out "p->closure_env_%i = env%i ;\n" i i in
    begin
      PR.fprintf out "ats_clo_ptr_type\n";
      PR.fprintf out "%a_clo_make (" cprint_funlab fl;
      VarTypMap.iter aux1 envmap;
      PR.fprintf out ") {\n";
      PR.fprintf out
	"%a_clo_type *p = ATS_MALLOC(sizeof(%a_clo_type)) ;\n"
        cprint_funlab fl cprint_funlab fl;
      PR.fprintf out "p->closure_fun = (ats_fun_ptr_type)&%a_clofun ;\n"
        cprint_funlab fl;
      VarTypMap.iter aux2 envmap;
      PR.fprintf out "return (ats_clo_ptr_type)p ;\n";
      PR.fprintf out "}\n\n"
    end
(* end of [cprint_function_clo_make] *)

let cprint_function_clofun (out: out_channel) (fl: funlab): unit =
  let (hits_arg, hit_res) = funlab_type_arg_res fl in
  let () =
    PR.fprintf out "%a\n%a_clofun (ats_clo_ptr_type clo%a) {\n"
      cprint_hityp hit_res cprint_funlab fl (cprint_funarg false) hits_arg in
  let env_pr (envmap: envmap_t): unit =
    let aux vt i =
      if i > 0 then PR.fprintf out ", ";
      PR.fprintf out "((%a_clo_type *)clo)->closure_env_%i"
	cprint_funlab fl i in
      VarTypMap.iter aux envmap in
  let arg_pr is_empty hits: unit =
    let rec aux i hits = match hits with
      | hit :: hits -> begin
	  if i > 0 then PR.fprintf out ", arg%i" i
	  else if is_empty then PR.fprintf out "arg0"
	  else PR.fprintf out ", arg0";
	  aux (i+1) hits
	end
      | [] -> () in
      aux 0 hits in
  let envmap =
    let f = function_store_find fl in f.function_envmap in
    if hityp_is_void hit_res then begin
      PR.fprintf out "%a (" cprint_funlab fl;
      env_pr envmap; arg_pr (VarTypMap.is_empty envmap) hits_arg;
      PR.fprintf out ") ; return ;\n}\n\n";
    end else begin
      PR.fprintf out "return %a (" cprint_funlab fl;
      env_pr envmap; arg_pr (VarTypMap.is_empty envmap) hits_arg;
      PR.fprintf out ") ;\n}\n\n";
    end
(* end of [cprint_function_clofun] *)

(* ****** ****** *)

let cprint_function (out: out_channel) (f: function_t): unit = begin
  let fl = f.function_lab in
(*
  let () =
    PR.fprintf stdout "cprint_function: fl = %a\n" fprint_funlab fl in
  let () =
    PR.fprintf stdout "cprint_function: fls = %a\n" fprint_funlab_list f.function_fls in
  let () =
    PR.fprintf stdout
      "cprint_function: env = %a\n" fprint_dvar2_list (VarTypSet.elements env) in
*)
  let (fc, hits_arg, hit_res) = funlab_type_fntp_arg_res fl in
  let envmap = f.function_envmap in
  let is_tailjoin = function_is_tailjoin f in
  let tmp_ret = f.function_ret in
  let tmpset =
    TmpVarSet.add tmp_ret (tmpset_of_function f) in
  let () = envmap_set envmap in
  let is_empty = VarTypMap.is_empty envmap in
  let () = (* function header *)
    if is_tailjoin then
      begin
	PR.fprintf out "%a\n%a (%a%a) {\n"
	  cprint_hityp hit_res cprint_funlab fl
	  cprint_funenvarg envmap cprint_funarg_tj is_empty
      end else begin
	PR.fprintf out "%a\n%a (%a%a) {\n"
	  cprint_hityp hit_res cprint_funlab fl
	  cprint_funenvarg envmap (cprint_funarg is_empty) hits_arg
      end in
  let () = (* function body *)
    begin
      cprint_tmpset_dec_local out tmpset;
      if is_tailjoin then
	cprint_tailjoin_switch out f.function_tailjoin;
      cprint_instr_list out f.function_body;
      if tmpvar_is_void tmp_ret then
	PR.fprintf out "return ;\n} /* fun */\n\n"
      else PR.fprintf out "return %a ;\n} /* fun */\n\n"
	cprint_tmpvar_val tmp_ret;
      envmap_reset ()
    end in
  let () = (* clo_type and clo_make and clofun *)
    if not (is_tailjoin) then
      begin match fc with
	| Syn.FUNCLOclo _ -> begin
	    cprint_function_clo_type out fl envmap;
	    cprint_function_clo_make out fl envmap;
	    cprint_function_clofun out fl
	  end
	| Syn.FUNCLOfun -> ()
      end in
    ()
end (* end of [cprint_function] *)

(* ****** ****** *)

let cprint_function_store_prototypes (out: out_channel): unit =
  FunLabMap.iter
    (fun fl f -> cprint_function_prototypes out f) !the_function_store
let cprint_function_store (out: out_channel): unit =
  FunLabMap.iter (fun fl f -> cprint_function out f) !the_function_store

(* ****** ****** *)

let cprint_staload_fun
  (out: out_channel) (filename: Fil.filename): unit =
  let aux_file_dec (file_sta: Fil.filename): unit =
    PR.fprintf out "extern ats_void_type\n%a__staload () ;\n"
      cprint_filename file_sta in
  let aux_file (file_sta: Fil.filename): unit =
    PR.fprintf out "%a__staload () ;\n" cprint_filename file_sta in
  let aux_sum_cst (s2c: scst2): unit =
    if not (scst2_is_list_like s2c) then
      begin
	let d2cs =
	  match s2c.scst2_cons with
	    | Some d2cs -> d2cs | None -> [] in
	  List.iter
	    (function d2c ->
	       PR.fprintf out "%a.tag = %i ;\n" cprint_con d2c d2c.dcon2_tag)
	    d2cs
      end in
  let aux_exn_con (d2c: dcon2): unit =
    begin
      PR.fprintf out "%a.tag = ats_exception_con_tag_new () ;\n"
	cprint_con d2c;
      PR.fprintf out "%a.name = \"%a\" ;\n"
	cprint_con d2c cprint_con d2c
    end in
  let files_sta = stafile_list_get () in
  let s2cs = sum_cst_set_get () in
  let d2cs = exn_con_set_get () in
    begin
      List.iter aux_file_dec files_sta;
      PR.fprintf out "static int %a__staload_flag = 0 ;\n"
	cprint_filename filename;
      PR.fprintf out "ats_void_type %a__staload () {\n"
	cprint_filename filename;
      PR.fprintf out "if (%a__staload_flag) return ;\n"
	cprint_filename filename;
      PR.fprintf out "%a__staload_flag = 1 ;\n"
	cprint_filename filename;
      List.iter aux_file files_sta;
      ScstSet.iter aux_sum_cst s2cs;
      DconSet.iter aux_exn_con d2cs;
      PR.fprintf out "}\n\n";
    end
(* end of [cprint_staload_fun] *)

let cprint_dynload_fun (out: out_channel) (flag: int)
  (filename: Fil.filename) (tmpset: TmpVarSet.t) (res: instr_t list): unit =
  let aux_dynfile (dynfile: Fil.filename): unit =
    begin
      PR.fprintf out "int %a__dynload_flag = 0 ;\n"
	cprint_filename dynfile;
      PR.fprintf out "extern ats_void_type\n%a__dynload () ;\n\n"
	cprint_filename dynfile
    end in
  let aux_extval_dec ((name: string), (vp: valprim)): unit =
    begin
      PR.fprintf out "%a %s ;\n" cprint_hityp vp.valprim_type name
    end in
  let aux_extval ((name: string), (vp: valprim)): unit =
    begin
      PR.fprintf out "ats_gc_markroot (&%s, sizeof(%a)) ;\n"
	name cprint_hityp vp.valprim_type;
      PR.fprintf out "%s = %a;\n" name cprint_valprim vp
    end in
  let dynfiles = dynfile_list_get () and extvals = extval_list_get () in
    begin
      List.iter aux_dynfile dynfiles;
      List.iter aux_extval_dec extvals;
      if flag <> 0 then begin
	PR.fprintf out "extern int %a__dynload_flag ;\n" cprint_filename filename;
      end;
      PR.fprintf out "ats_void_type %a__dynload () {\n" cprint_filename filename;
      if flag <> 0 then begin
        PR.fprintf out "%a__dynload_flag = 1 ;\n" cprint_filename filename;
      end;
      PR.fprintf out "%a__staload () ;\n" cprint_filename filename;
      cprint_tmpset_markroot_static out tmpset ;
      cprint_instr_list out res;
      List.iter aux_extval extvals;
      PR.fprintf out "}\n\n";
  end
(* end of [cprint_dynload_fun] *)

(* ****** ****** *)

let cprint_main_fun_default
  (out: out_channel) (filename: Fil.filename): unit = begin
  PR.fprintf out "int main () {\n";
  PR.fprintf out "ats_gc_init () ;\n";
  PR.fprintf out "mainats_prelude ();\n";
  PR.fprintf out "%a__dynload () ;\n" cprint_filename filename;
  PR.fprintf out "return 0 ;\n";
  PR.fprintf out "} /* end of main */\n\n";
end (* end of [cprint_main_fun_default] *)

let cprint_main_fun_implemented
  (out: out_channel) (filename: Fil.filename): unit = begin
  PR.fprintf out "int main (int argc, char *argv[]) {\n";
  PR.fprintf out "ats_gc_init () ;\n";
  PR.fprintf out "mainats_prelude ();\n";
  PR.fprintf out "%a__dynload () ;\n" cprint_filename filename;
  PR.fprintf out "mainats ((ats_int_type)argc, (ats_ptr_type)argv) ;\n";
  PR.fprintf out "return 0 ;\n";
  PR.fprintf out "} /* end of main */\n";
end (* end of [cprint_main_fun_implemented] *)

(* ****** ****** *)

(* end of [ats_ccomp_cprint.ml] *)
