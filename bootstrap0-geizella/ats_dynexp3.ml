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
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2
open Ats_dynexp2_util
open Ats_dyncst2
open Ats_patcst2

module PR = Printf

module Eff = Ats_effect
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module Syn = Ats_syntax

(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location

(* ****** ****** *)

type pat3 = { (* type for dynamic patterns *)
  pat3_loc: loc; (* location locmation *)
  pat3_node: pat3_node; (* actual representation *)
  mutable pat3_type: sexp2;
  mutable pat3_type_left: sexp2 option;
}

and labpat3 = lab * pat3

and int_pat3_list = int (* arity_p *) * pat3 list
and int_labpat3_list = int (* arity_p *) * labpat3 list

and pat3_node =
  | PT3any of (* wildcard *)
      dvar2
  | PT3bool of (* boolean pattern *)
      bool
  | PT3char of (* character pattern *)
      char
  | PT3con of (* constructor pattern *)
      int (* is_ref *) * dcon2 * int_pat3_list
  | PT3empty (* empty pattern *)
  | PT3int of (* integer pattern *)
      intinf
  | PT3lst of (* list pattern *)
      pat3 list
  | PT3rec of (* record pattern *)
      bool (* is_flat *) * int_labpat3_list
  | PT3string of (* string pattern *)
      string
  | PT3var of (* variable pattern *)
      bool(*isref*) * dvar2 * pat3 option
  | PT3vbox of (* vbox pattern *)
      dvar2

(* ****** ****** *)

let rec fprint_pat3 (out: out_channel) (p3t0: pat3): unit =
  match p3t0.pat3_node with
    | PT3any d2v -> PR.fprintf out "PT3any(%a)" fprint_dvar2 d2v
    | PT3bool b -> PR.fprintf out "PT3bool(%b)" b
    | PT3char c -> PR.fprintf out "PT3char(%c)" c
    | PT3con (freeknd, d2c, (npf, p3ts)) -> PR.fprintf out
	"PT3con(%a; %i; %a)" fprint_dcon2 d2c npf fprint_pat3_list p3ts
    | PT3empty -> PR.fprintf out "PT3empty"
    | PT3int i -> PR.fprintf out "PT3int(%a)" fprint_intinf i
    | PT3lst p3ts -> PR.fprintf out "PT3lst(%a)" fprint_pat3_list p3ts
    | PT3rec (is_flat, (npf, lp3ts)) ->
	PR.fprintf out "PT3rec{%i; %a}" npf fprint_labpat3_list lp3ts
    | PT3string s -> PR.fprintf out "PT3string(%s)" s
    | PT3var (isref, d2v, op3t) -> begin match op3t with
        | Some p3t -> begin
            PR.fprintf out "PT3var(";
            if isref then PR.fprintf out "!";
            fprint_dvar2 out d2v;
            PR.fprintf out ":";
            fprint_sexp2 out p3t0.pat3_type;
            PR.fprintf out ";";
            fprint_pat3 out p3t;
            PR.fprintf out ")";
          end
	| None -> begin
            PR.fprintf out "PT3var(";
            if isref then PR.fprintf out "!";
            fprint_dvar2 out d2v;
            PR.fprintf out ":";
            fprint_sexp2 out p3t0.pat3_type;
            PR.fprintf out ")";
	  end
      end
    | PT3vbox d2v -> PR.fprintf out "PT3vbox(%a)" fprint_dvar2 d2v 
(* end of [fprint_pat3] *)

and fprint_pat3_list (out: out_channel) (p3ts: pat3 list): unit =
  fprint_list_with_sep fprint_pat3 out p3ts ","

and fprint_labpat3 (out: out_channel) ((l, p3t): labpat3): unit =
  PR.fprintf out "%a= %a" Lab.fprint l fprint_pat3 p3t

and fprint_labpat3_list (out: out_channel) (lp3ts: labpat3 list): unit =
  fprint_list_with_sep fprint_labpat3 out lp3ts ";"

(* ****** ****** *)

let pat3_is_proof (p3t: pat3): bool = sexp2_is_proof (p3t.pat3_type)

(* ****** ****** *)

let pat3_any loc (s2e: sexp2) (d2v: dvar2): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3any d2v;
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_bool loc (s2e: sexp2) (b: bool): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3bool b;
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_char loc (s2e: sexp2) (c: char): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3char c;
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_con loc (s2e: sexp2) (freeknd: int)
  (d2c: dcon2) (npf: int) (p3ts: pat3 list): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3con (freeknd, d2c, (npf, p3ts));
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_empty loc = {
  pat3_loc= loc;
  pat3_node= PT3empty;
  pat3_type= sexp2_void_t0ype ();
  pat3_type_left= None;
}

let pat3_int loc (s2e: sexp2) (i: intinf): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3int i;
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_lst loc (s2e: sexp2) (p3ts: pat3 list): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3lst p3ts;
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_rec loc (s2e: sexp2)
  (is_flat: bool) (npf: int) (lp3ts: labpat3 list): pat3 = {
    pat3_loc= loc;
    pat3_node= PT3rec (is_flat, (npf, lp3ts));
    pat3_type= s2e;
    pat3_type_left= None;
  }

let pat3_string loc (s2e: sexp2) (s: string): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3string s;
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_var loc
  (s2e: sexp2) (isref: bool) (d2v: dvar2) (op3t: pat3 option) = {
  pat3_loc= loc;
  pat3_node= PT3var (isref, d2v, op3t);
  pat3_type= s2e;
  pat3_type_left= None;
}

let pat3_vbox loc (s2e: sexp2) (d2v: dvar2): pat3 = {
  pat3_loc= loc;
  pat3_node= PT3vbox d2v;
  pat3_type= Vbox_view_prop.make_exp (Some [s2e]);
  pat3_type_left= None;
}

(* ****** ****** *)

type dexp3 = { (* type for dynamic expressions *)
  dexp3_loc: loc; (* location information *)
  dexp3_node: dexp3_node; (* actual representation *)
  dexp3_is_proof: bool;
  mutable dexp3_seff: seff2; (* effects *)
  mutable dexp3_type: sexp2; (* assigned type *)
} 

and labdexp3 = lab * dexp3

and int_dexp3_list = int (* arity *) * dexp3 list
and int_labdexp3_list = int (* arity *) * labdexp3 list

and dlab3_nt = { (* without type *)
  dlab3_nt_lab: lab option;
  dlab3_nt_ind: dexp3 list list option
}

and dlab3 = { (* with type *)
  dlab3_lab: (lab * sexp2) option;
  dlab3_ind: (dexp3 list list * sexp2) option
}

and dexp3_node =
  | DE3app_dyn of (* dynamic application *)
      dexp3 * int_dexp3_list
  | DE3app_sta of (* static application *)
      dexp3
  | DE3arr of (* array expression *)
      sexp2 (* elt type *) * dexp3 list (* elts *)
  | DE3assgn_ptr of (* assignment to a pointer *)
      dexp3 * dlab3 list * dexp3
  | DE3assgn_var of (* assignment to a variable *)
      dvar2 * dlab3 list * dexp3
  | DE3case of (* linear case-expressions *)
      int * dexp3 list * cla3 list
  | DE3char of char (* dynamic character *)
  | DE3con of (* dynamic constructor *)
      dcon2 * int_dexp3_list
  | DE3cst of (* dynamic constant *)
      dcst2
  | DE3crypt of (* cryption *)
      int(*knd*) * dexp3 (* 1/~1: encrypt/decrypt *)
  | DE3delay of (* delayed computation *)
      int(*lin*) * dexp3
  | DE3dynload of (* dynamic loading *)
      Fil.filename
  | DE3empty (* empty expression *)
  | DE3extval of (* external code *)
      string
  | DE3fix of (* dynamic fixed-point expression *)
      dvar2 * dexp3 
  | DE3float of string (* dynamic float *)
  | DE3fold of dexp3
  | DE3foldat of dexp3 (* linear datatype folding *)
  | DE3freeat of dexp3 (* linear datatype freeing *)
  | DE3for of (* for-loop *)
      dexp3 (*init*) * dexp3 (*test*) * dexp3 (*post*) * dexp3 (*body*)
  | DE3if of dexp3 * dexp3 * dexp3 (* conditional expression *)
  | DE3int of (* dynamic integer *)
      Syn.intkind * intinf
  | DE3lam_dyn of (* dynamic abstraction *)
      bool (* is_linear *) * int_pat3_list * dexp3
  | DE3lam_sta of svar2 list * sexp2 list * dexp3
  | DE3lam_sta_para of svar2 list * sexp2 list * dexp3
  | DE3let of (* dynamic let-expression *)
      dec3 list * dexp3
  | DE3loopexn of (* local loop exception: 0: break and 1: continue *)
      int 
  | DE3lst of (* dynamic list expression *)
      dexp3 list
  | DE3mod of (* module expression *)
      dec3 list
  | DE3ptrof_ptr of (* address of a pointer selection *)
      dexp3 * dlab3 list
  | DE3ptrof_var of (* address of a variable selection *)
      dvar2 * dlab3 list
  | DE3raise of (* raised exception *)
      dexp3
  | DE3rec of (* record expression *)
      bool (* is_flat *) * int_labdexp3_list (* dynamic record *)
  | DE3refarg of (* call-by-reference argument *)
      int(*refval*) * int(*freeknd*) * dexp3
  | DE3sel of (* dynamic record selection *)
      dexp3 * dlab3 list
  | DE3sel_ptr of (* dynamic linear record ptr selection *)
      dexp3 * dlab3 list
  | DE3sel_var of (* dynamic linear record var selection *) 
      dvar2 * dlab3 list
  | DE3seq of (* dynamic sequencing *)
      dexp3 list
  | DE3sif of (* static conditional dynamic expression *)
      sexp2 * dexp3 * dexp3
  | DE3string of string (* dynamic string *)
  | DE3struct of labdexp3 list (* dynamic structure *)
  | DE3template_cst of dcst2 * (sexp2 list) list
  | DE3template_var of dvar2 * (sexp2 list) list
  | DE3top (* uninitialized value *)
  | DE3trywith of (* exception handling *)
      dexp3 * cla3 list
  | DE3unfold of dexp3
  | DE3var of (* dynamic variable *)
      dvar2
  | DE3viewat_assgn_ptr of (* viewat assignment through a pointer *)
      dexp3 * dlab3 list * dexp3
  | DE3viewat_assgn_var of (* viewat assignment through a variable *)
      dvar2 * dlab3 list * dexp3
  | DE3viewat_ptr of (* viewat access through a pointer *)
      dexp3 * dlab3 list * dvar2 (* view *) * slab2 list (* view path *)
  | DE3viewat_var of (* viewat access through a variable *)
      dvar2 * dlab3 list * dvar2 (* view *) * slab2 list (* view path *)
  | DE3while of (* while-loop *)
      dexp3 (*test*) * dexp3 (*body*) (* while loop *)

and cla3 = { (* type for clauses *)
  cla3_loc: loc; (* location information *)
  cla3_pat: pat3 list; (* pattern list *)
  cla3_gua: dexp3 option; (* clause guard *)
  cla3_isseq: (patcst2 list list) option; (* sequential *)
  cla3_isneg: bool; (* negative *)
  cla3_body: dexp3; (* expression body *)
}

(* ****** ****** *)

and dec3 = {
  dec3_loc: loc;
  dec3_node: dec3_node;
}

and dec3_fun = {
  dec3_fun_loc: loc;
  dec3_fun_name: dvar2;
  dec3_fun_def: dexp3;
}

and dec3_val = {
  dec3_val_loc: loc;
  dec3_val_pat: pat3;
  dec3_val_def: dexp3;
}

and dec3_var = {
  dec3_var_loc: loc;
  dec3_var_ptr: dvar2;
  dec3_var_view: dvar2;
  dec3_var_ini: dexp3 option;
}

and dec3_impl = { (* dynamic implementation *)
  dec3_impl_loc: loc;
  dec3_impl_cst: dcst2;
  dec3_impl_decarg: decarg2;
  dec3_impl_def: dexp3;
}

and dec3_node =
  | DC3extype of string (* name *) * sexp2 (* definition *)
  | DC3extval of string (* name *) * dexp3 (* definition *)
  | DC3dyncsts of Syn.dcstkind * dcst2 list (* dynamic constants *)
  | DC3data of Syn.datakind * scst2 list
  | DC3exns of dcon2 list (* exception constructors *)
  | DC3impls of dec3_impl list (* dynamic implementation *)
  | DC3funs of (* function *)
      bool (*is_template*) * Syn.funkind * dec3_fun list
  | DC3vals of Syn.valkind * dec3_val list
  | DC3valpars of dec3_val list
  | DC3valrecs of dec3_val list
  | DC3vars of bool (* is_stack *) * dec3_var list
  | DC3local of dec3 list (* head *) * dec3 list (* body *)
  | DC3staload of Fil.filename * (dec3 list) option
  | DC3dynload of Fil.filename
  | DC3extern of (* external code *)
      int (* position: 0/1 : top/end *) * string (* code *)

(* ****** ****** *)

let rec fprint_dexp3 (out: out_channel) (d3e0: dexp3): unit =
  match d3e0.dexp3_node with
    | DE3app_dyn (d3e_fun, (npf, d3es_arg)) ->
	PR.fprintf out "DE3app_dyn(%a; %i; %a)"
	  fprint_dexp3 d3e_fun npf fprint_dexp3_list d3es_arg
    | DE3app_sta d3e -> PR.fprintf out "DE3app_sta(%a)" fprint_dexp3 d3e
    | DE3arr _ -> PR.fprintf out "DE3arr(...)"
    | DE3assgn_ptr (d3e_ptr, d3labs, d3e_val) ->
	PR.fprintf out "DE3assgn_ptr(%a; ...)" fprint_dexp3 d3e_ptr
    | DE3assgn_var (d2v_ptr, d3labs, d3e_val) ->
	PR.fprintf out "DE3assgn_var(%a; ...)" fprint_dvar2 d2v_ptr
    | DE3case (sgn, d3es, c3ls) -> PR.fprintf out "DE3case(%a; %a)"
	fprint_dexp3_list d3es fprint_cla3_list c3ls
    | DE3char c -> PR.fprintf out "DE3char(%c)" c
    | DE3con (d2c, (npf, d3es)) -> PR.fprintf out "DE3con(%a; %i; %a)"
	fprint_dcon2 d2c npf fprint_dexp3_list d3es
    | DE3cst d2c -> PR.fprintf out "DE3cst(%a)" fprint_dcst2 d2c
    | DE3crypt (knd, d3e) -> PR.fprintf out "DE3crypt(%i; %a)" knd fprint_dexp3 d3e
    | DE3delay (lin, d3e) -> PR.fprintf out "DE3delay(%i; %a)" lin fprint_dexp3 d3e
    | DE3dynload f -> PR.fprintf out "DE3dynload(%a)" Fil.fprint f
    | DE3empty -> PR.fprintf out "DE3empty"
    | DE3extval code -> PR.fprintf out "DE3extval(%s)" code
    | DE3fix (d2v_fun, d3e_body) -> PR.fprintf out "DE3fix(%a; %a)"
	fprint_dvar2 d2v_fun fprint_dexp3 d3e_body
    | DE3float s -> PR.fprintf out "DE3float(%s)" s
    | DE3fold d3e -> PR.fprintf out "DE3fold(%a)" fprint_dexp3 d3e
    | DE3foldat d3e -> PR.fprintf out "DE3foldat(%a)" fprint_dexp3 d3e
    | DE3freeat d3e -> PR.fprintf out "DE3freeat(%a)" fprint_dexp3 d3e
    | DE3for (d3e_init, d3e_test, d3e_post, d3e_body) ->
	PR.fprintf out "DE3for(%a; %a; %a; %a)"
	  fprint_dexp3 d3e_init fprint_dexp3 d3e_test
	  fprint_dexp3 d3e_post fprint_dexp3 d3e_body
    | DE3if (d3e_cond, d3e_then, d3e_else) -> PR.fprintf out "DE3if(%a; %a; %a)"
	fprint_dexp3 d3e_cond fprint_dexp3 d3e_then fprint_dexp3 d3e_else
    | DE3int (ik, i) -> PR.fprintf out "DE3int(%a)" fprint_intinf i
    | DE3lam_dyn (is_lin, (npf, p3ts_arg), d3e_body) ->
	PR.fprintf out "DE3lam_dyn(%b; %i; %a; %a)"
	  is_lin npf fprint_pat3_list p3ts_arg fprint_dexp3 d3e_body
    | DE3lam_sta (s2vs, s2ps, d3e) -> PR.fprintf out "DE3lam_sta(%a; %a; %a)"
	fprint_svar2_list s2vs fprint_sexp2_list s2ps fprint_dexp3 d3e
    | DE3lam_sta_para (s2vs, s2ps, d3e) -> PR.fprintf out "DE3lam_sta_para(%a; %a; %a)"
	fprint_svar2_list s2vs fprint_sexp2_list s2ps fprint_dexp3 d3e
    | DE3let (d3cs, d3e) -> PR.fprintf out "DE3let(%a; %a)"
	fprint_dec3_list d3cs fprint_dexp3 d3e
    | DE3loopexn i ->
	if i > 0 then PR.fprintf out "break" else PR.fprintf out "continue"
    | DE3lst d3es -> PR.fprintf out "DE3lst(%a)" fprint_dexp3_list d3es
    | DE3mod _ -> PR.fprintf out "DE3mod(...)"
    | DE3ptrof_ptr (d3e_ptr, d3labs) ->
	PR.fprintf out "DE3ptrof_ptr(%a; ...)" fprint_dexp3 d3e_ptr
    | DE3ptrof_var (d2v_ptr, d3labs) ->
	PR.fprintf out "DE3ptrof_var(%a; ...)" fprint_dvar2 d2v_ptr
    | DE3raise d3e_exn -> PR.fprintf out "DE3raise(%a)" fprint_dexp3 d3e_exn
    | DE3rec (is_flat, (npf, ld3es)) ->
	PR.fprintf out "DE3rec{%i; %a}" npf fprint_labdexp3_list ld3es
    | DE3refarg (refval, freeknd, d3e) -> PR.fprintf out "DE3refarg(%i; %i; %a)"
	refval freeknd fprint_dexp3 d3e
    | DE3sel (d3e, d3labs) -> PR.fprintf out "DE3sel(%a; ...)" fprint_dexp3 d3e
    (* dynamic linear record ptr selection *) 
    | DE3sel_ptr (d3e, d3labs) -> PR.fprintf out "DE3sel_ptr(%a; ...)"
	fprint_dexp3 d3e
    | DE3sel_var (d2v, d3labs) ->
	PR.fprintf out "DE3sel_var(%a; ...)" fprint_dvar2 d2v
    | DE3seq d3es -> PR.fprintf out "DE3seq(%a)" fprint_dexp3_list d3es
    | DE3sif (s2e_cond, d3e_then, d3e_else) -> PR.fprintf out "DE3sif(%a; %a; %a;)"
	fprint_sexp2 s2e_cond fprint_dexp3 d3e_then fprint_dexp3 d3e_else	
    | DE3string s -> PR.fprintf out "DE3string(%s)" s
    | DE3struct (ld3es) -> PR.fprintf out "DE3struct{%a}" fprint_labdexp3_list ld3es
    | DE3template_cst (d2c, s2ess) -> PR.fprintf out "DE3template_cst(%a; %a)"
	fprint_dcst2 d2c fprint_sexp2_list_list s2ess
    | DE3template_var (d2v, s2ess) -> PR.fprintf out "DE3template_var(%a; %a)"
	fprint_dvar2 d2v fprint_sexp2_list_list s2ess
    | DE3top -> PR.fprintf out "DE3top"
    | DE3trywith (d3e, c3ls) -> PR.fprintf out "DE3trywith(%a; %a)"
	fprint_dexp3 d3e fprint_cla3_list c3ls
    | DE3unfold d3e -> PR.fprintf out "DE3unfold(%a)" fprint_dexp3 d3e
    | DE3var d2v -> PR.fprintf out "DE3var(%a)" fprint_dvar2 d2v
    | DE3viewat_assgn_ptr (d3e_ptr, d3labs, d3e_val) ->
	PR.fprintf out "DE3viewat_assgn_ptr(%a; ...)" fprint_dexp3 d3e_ptr
    | DE3viewat_assgn_var (d2v_ptr, d3labs, d3e_val) ->
	PR.fprintf out "DE3viewat_assgn_var(%a; ...)" fprint_dvar2 d2v_ptr
    | DE3viewat_ptr (d3e, d3labs, d2v_view, s2labs_view) ->
	PR.fprintf out "DE3viewat_ptr(%a; ...)" fprint_dexp3 d3e
    | DE3viewat_var (d2v, d3labs, d2v_view, s2labs_view) ->
	PR.fprintf out "DE3viewat_var(%a; ...)" fprint_dvar2 d2v
    | DE3while (d3e_test, d3e_body) -> PR.fprintf out
	"DE3while(%a; %a)" fprint_dexp3 d3e_test fprint_dexp3 d3e_body
(* end of [fprint_dexp3] *)

and fprint_dexp3_list (out: out_channel) (d3es: dexp3 list): unit =
  fprint_list_with_sep fprint_dexp3 out d3es ","

and fprint_labdexp3 (out: out_channel) ((l, d3e): labdexp3): unit =
  PR.fprintf out "%a= %a" Lab.fprint l fprint_dexp3 d3e

and fprint_labdexp3_list (out: out_channel) (ld3es: labdexp3 list): unit =
  fprint_list_with_sep fprint_labdexp3 out ld3es ","

(* ****** ****** *)

and fprint_cla3 (out: out_channel) (c3l: cla3): unit =
  let sep = match c3l.cla3_isseq, c3l.cla3_isneg with
    | None, false -> "=>"
    | None, true -> "=/=>"
    | Some _, false -> "=>>"
    | Some _, true -> "=/=>>" in
    PR.fprintf out "%a %s %a"
      fprint_pat3_list c3l.cla3_pat sep fprint_dexp3 c3l.cla3_body

and fprint_cla3_list (out: out_channel) (c3ls: cla3 list): unit =
  fprint_list_with_sep fprint_cla3 out c3ls "; "

(* ****** ****** *)

and fprint_dec3 (out: out_channel) (d: dec3): unit =
  match d.dec3_node with
    | DC3extype (name, s2e_def) ->
	PR.fprintf out "DC3extype(%s, %a)" name fprint_sexp2 s2e_def
    | DC3extval (name, d3e_def) ->
	PR.fprintf out "DC3extval(%s, %a)" name fprint_dexp3 d3e_def
    | DC3dyncsts _ -> PR.fprintf out "DC3dyncsts(...)" 
    | DC3data _ -> PR.fprintf out "DC3data(...)" 
    | DC3exns _ -> PR.fprintf out "DC3exns(...)" 
    | DC3impls _ -> PR.fprintf out "DC3impls(...)" 
    | DC3funs _ -> PR.fprintf out "DC3funs(...)"  
    | DC3vals _ -> PR.fprintf out "DC3vals(...)"  
    | DC3valpars _ -> PR.fprintf out "DC3valpars(...)"  
    | DC3valrecs _ -> PR.fprintf out "DC3valrecs(...)"  
    | DC3vars _ -> PR.fprintf out "DC3vars(...)"
    | DC3local _ -> PR.fprintf out "DC3local(...)"
    | DC3staload (f, _) -> PR.fprintf out "DC3staload(%a)" Fil.fprint f
    | DC3dynload f -> PR.fprintf out "DC3dynload(%a)" Fil.fprint f
    | DC3extern _ -> PR.fprintf out "DC3extern(...)"
(* end of [fprint_dec3] *)

and fprint_dec3_list (out: out_channel) (d3cs: dec3 list): unit =
  fprint_list_with_sep fprint_dec3 out d3cs "; "

(* ****** ****** *)

let seff2_dexp3_union (sf2e: seff2) (d3e: dexp3): seff2 =
  seff2_union sf2e d3e.dexp3_seff

let seff2_dexp3_list_union (sf2e: seff2) (d3es: dexp3 list): seff2 =
  List.fold_left seff2_dexp3_union sf2e d3es

let seff2_labdexp3_union (sf2e: seff2) ((l, d3e): labdexp3): seff2 =
  seff2_union sf2e d3e.dexp3_seff

let seff2_labdexp3_list_union (sf2e: seff2) (ld3es: labdexp3 list): seff2 =
  List.fold_left seff2_labdexp3_union sf2e ld3es

let seff2_dlab3_union (sf2e: seff2) (d3l: dlab3): seff2 =
  match d3l.dlab3_ind with
    | Some (d3ess_ind, s2e_elt) ->
	List.fold_left seff2_dexp3_list_union sf2e d3ess_ind
    | None -> sf2e
(* end of [seff2_dlab3_union] *)

let seff2_dlab3_list_union (sf2e: seff2) (d3labs: dlab3 list): seff2 =
  List.fold_left seff2_dlab3_union sf2e d3labs

let seff2_cla3_union (sf2e: seff2) (c3l: cla3): seff2 =
  seff2_dexp3_union sf2e c3l.cla3_body

let seff2_cla3_list_union (sf2e: seff2) (c3ls: cla3 list): seff2 =
  List.fold_left seff2_cla3_union sf2e c3ls

(* ****** ****** *)

let seff2_dec3_val_union (sf2e: seff2) (d: dec3_val): seff2 =
  seff2_dexp3_union sf2e d.dec3_val_def

let seff2_dec3_val_list_union (sf2e: seff2) (ds: dec3_val list): seff2 =
  List.fold_left seff2_dec3_val_union sf2e ds

let seff2_dec3_var_union
  (sf2e: seff2) (d: dec3_var): seff2 =
  match d.dec3_var_ini with
    | None -> sf2e | Some d3e -> seff2_dexp3_union sf2e d3e
(* end of [seff2_dec3_var_union] *)

let seff2_dec3_var_list_union
  (sf2e: seff2) (ds: dec3_var list): seff2 =
  List.fold_left seff2_dec3_var_union sf2e ds

let rec seff2_dec3_union (sf2e: seff2) (d3c: dec3): seff2 =
  match d3c.dec3_node with
    | DC3extype _ -> sf2e
    | DC3extval (name, d3e_def) -> seff2_dexp3_union sf2e d3e_def
    | DC3dyncsts _ -> sf2e
    | DC3data _ -> sf2e
    | DC3exns _ -> sf2e
    | DC3impls _ -> sf2e
    | DC3funs _ -> sf2e
    | DC3vals (vk, ds) ->
	if Syn.valkind_is_proof vk then sf2e
	else seff2_dec3_val_list_union sf2e ds
    | DC3valpars _ -> sf2e
    | DC3valrecs _ -> sf2e
    | DC3vars (is_stack, ds) -> seff2_dec3_var_list_union sf2e ds
    | DC3local (d3cs_head, d3cs_body) ->
	let sf2e = seff2_dec3_list_union sf2e d3cs_head in
	  seff2_dec3_list_union sf2e d3cs_body
    | DC3staload _ -> sf2e
    | DC3dynload _ -> seff2_all
    | DC3extern _ -> seff2_all
(* end of [seff2_dec3_union] *)

and seff2_dec3_list_union (sf2e: seff2) (ds: dec3 list): seff2 =
  List.fold_left seff2_dec3_union sf2e ds

(* ****** ****** *)

let dexp3_is_empty (d3e: dexp3): bool =
  match d3e.dexp3_node with DE3empty -> true | _ -> false

let dexp3_is_proof (d3e: dexp3): bool =
  let s2e = d3e.dexp3_type in sexp2_is_proof s2e

let dexp3_arglist_is_proof (npf: int) (d3es_arg: dexp3 list): bool =
  let rec aux i = function
    | d3e :: d3es ->
	if i < npf then aux (i+1) d3es else
	  (d3e.dexp3_is_proof && aux (i+1) d3es)
    | [] -> true in
    aux 0 d3es_arg
(* end of [dexp3_arglist_is_proof] *)

let dexp3_list_is_proof (d3es: dexp3 list): bool =
  let rec aux = function
    | d3e :: d3es -> (d3e.dexp3_is_proof && aux d3es)
    | [] -> true in
    aux d3es

let labdexp3_arglist_is_proof (npf: int) (ld3es: labdexp3 list): bool =
  let rec aux i = function
    | (l, d3e) :: ld3es ->
	if i < npf then aux (i+1) ld3es else
	  (d3e.dexp3_is_proof && aux (i+1) ld3es)
    | [] -> true in
    aux 0 ld3es
(* end of [labdexp3_arglist_is_proof] *)

let labdexp3_list_is_proof (ld3es: labdexp3 list): bool =
  let rec aux = function
    | (l, d3e) :: ld3es -> (d3e.dexp3_is_proof && aux ld3es)
    | [] -> true in
    aux ld3es
(* end of [labdexp3_list_is_proof] *)

let dexp3_app_dyn_with_type loc
  (s2e: sexp2) (sf2e_app: seff2)
  (d3e_fun: dexp3) (nd3es_arg: int_dexp3_list): dexp3 =
  let (npf, d3es_arg) = nd3es_arg in
  let sf2e = seff2_dexp3_union sf2e_app d3e_fun in
  let sf2e = seff2_dexp3_list_union sf2e d3es_arg in
  let is_prf = d3e_fun.dexp3_is_proof in {
      dexp3_loc= loc;
      dexp3_node= DE3app_dyn (d3e_fun, nd3es_arg);
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= s2e;
    }
(* end of [dexp3_app_dyn_with_type] *)

let dexp3_app_sta_with_type loc s2e d3e: dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3app_sta d3e;
  dexp3_is_proof= d3e.dexp3_is_proof;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e;
}

let dexp3_arr_with_type loc (s2e_arr: sexp2)
  (s2e_elt: sexp2) (d3es_elt: dexp3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_list_union sf2e d3es_elt in
  let is_prf = dexp3_list_is_proof d3es_elt in {
      dexp3_loc= loc;
      dexp3_node= DE3arr (s2e_elt, d3es_elt);
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= s2e_arr;
    }
(* end of [dexp3_arr_with_type] *)

let dexp3_assgn_ptr loc
  (d3e1: dexp3) (d3labs: dlab3 list) (d3e2: dexp3): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e d3e1 in
  let sf2e = seff2_dlab3_list_union sf2e d3labs in
  let sf2e = seff2_dexp3_union sf2e d3e2 in
  let is_prf = d3e2.dexp3_is_proof in {
      dexp3_loc= loc;
      dexp3_node= DE3assgn_ptr (d3e1, d3labs, d3e2);
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= sexp2_void_t0ype ();
    }
(* end of [dexp3_assgn_ptr] *)

let dexp3_assgn_var loc
  (d2v1: dvar2) (d3labs: dlab3 list) (d3e2: dexp3): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dlab3_list_union sf2e d3labs in
  let sf2e = seff2_dexp3_union sf2e d3e2 in
  let is_prf = d3e2.dexp3_is_proof in {
      dexp3_loc= loc;
      dexp3_node= DE3assgn_var (d2v1, d3labs, d3e2);
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= sexp2_void_t0ype ();
    }
(* end of [dexp3_assgn_var] *)

(* ****** ****** *)

let dexp3_case loc (sgn: int)
  (s2e: sexp2) (d3es: dexp3 list) (c3ls: cla3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_list_union sf2e d3es in
  let sf2e = seff2_cla3_list_union sf2e c3ls in
  let is_prf = dexp3_list_is_proof d3es in {
      dexp3_loc= loc;
      dexp3_node= DE3case (sgn, d3es, c3ls);
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= s2e;
    }
(* end of [dexp3_case] *)

(* ****** ****** *)

let dexp3_char_with_type loc (s2e: sexp2) (c: char): dexp3 = {
    dexp3_loc= loc;
    dexp3_node= DE3char c;
    dexp3_is_proof= false;
    dexp3_seff= seff2_nil;
    dexp3_type= s2e;
  }
(* end of [dexp3_char_with_type] *)

let dexp3_char loc (c: char): dexp3 =
  let s2e = sexp2_char_char_t0ype c in
    dexp3_char_with_type loc s2e c
(* end of [dexp3_char] *)

(* ****** ****** *)

let dexp3_con loc
  (s2e_res: sexp2) (d2c: dcon2) (nd3es_arg: int_dexp3_list): dexp3 =
  let (npf, d3es_arg) = nd3es_arg in
  let isuni =
    let rec aux d3es = match d3es with
      | d3e :: d3es -> begin
	  match d3e.dexp3_node with DE3top -> true | _ -> aux d3es
	end
      | [] -> false in
      aux d3es_arg in
    if isuni then begin
      let s2es_arg =
	List.map (function d3e -> d3e.dexp3_type) d3es_arg in
      let s2e_res = sexp2_datuni d2c s2es_arg in {
	  dexp3_loc= loc;
	  dexp3_node= DE3con (d2c, nd3es_arg);
	  dexp3_is_proof= false;
	  dexp3_seff= seff2_nil;
	  dexp3_type= s2e_res;
	}
    end else begin
      let sf2e = seff2_nil in
      let sf2e = seff2_dexp3_list_union sf2e d3es_arg in
      let is_prf = sexp2_is_proof s2e_res in {
	  dexp3_loc= loc;
	  dexp3_node= DE3con (d2c, nd3es_arg);
	  dexp3_is_proof= is_prf;
	  dexp3_seff= sf2e;
	  dexp3_type= s2e_res;
	}
    end (* end of [if] *)
(* end of [dexp3_con] *)

let dexp3_cst loc (d2c: dcst2): dexp3 =
  let is_prf = Syn.dcstkind_is_proof d2c.dcst2_kind in {
      dexp3_loc= loc;
      dexp3_node= DE3cst d2c;
      dexp3_is_proof= is_prf;
      dexp3_seff= seff2_nil;
      dexp3_type= d2c.dcst2_type;
    }
(* end of [dexp3_cst] *)

let dexp3_crypt loc
  (s2e: sexp2) (knd: int) (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3crypt (knd, d3e);
  dexp3_is_proof= d3e.dexp3_is_proof;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e;
} (* end of [dexp3_crypt] *)

let dexp3_delay loc (s2e: sexp2) (lin: int) (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3delay (lin, d3e);
  dexp3_is_proof= false;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e;
} (* end of [dexp3_delay] *)

let dexp3_dynload loc (f: Fil.filename): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3dynload f;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil ;
  dexp3_type= sexp2_void_t0ype ();
} (* end of [dexp3_dynload] *)

let dexp3_empty loc: dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3empty;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
} (* end of [dexp3_empty] *)

let dexp3_extval loc (s2e: sexp2) (code: string) = {
  dexp3_loc= loc;
  dexp3_node= DE3extval code;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_extval] *)

let dexp3_fix loc
  (d2v_fun: dvar2) (d3e_def: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3fix (d2v_fun, d3e_def);
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= d3e_def.dexp3_type;
} (* end of [dexp3_fix] *)

(* ****** ****** *)

(* double precision floats *)
let dexp3_float_with_type loc
  (s2e: sexp2) (f: string): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3float f;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_float_with_type] *)

let dexp3_float loc (f: string): dexp3 =
  let s2e = Double_t0ype.make_exp None in
    dexp3_float_with_type loc s2e f
(* end of [dexp3_float] *)

(* ****** ****** *)

let dexp3_fold loc (s2e: sexp2) (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3fold d3e;
  dexp3_is_proof= d3e.dexp3_is_proof;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e;
}

let dexp3_foldat loc (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3foldat d3e;
  dexp3_is_proof= true; (* it is a proof *)
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
}

let dexp3_freeat loc (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3freeat d3e;
  dexp3_is_proof= false; (* it is a proof *)
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
}

let dexp3_for loc
  (init: dexp3) (test: dexp3) (post: dexp3) (body: dexp3): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e init in
  let sf2e = seff2_dexp3_union sf2e test in
  let sf2e = seff2_dexp3_union sf2e body in
  let sf2e = seff2_dexp3_union sf2e post in {
      dexp3_loc= loc;
      dexp3_node= DE3for (init, test, post, body);
      dexp3_is_proof= false;
      dexp3_seff= sf2e;
      dexp3_type= sexp2_void_t0ype ();
    }
(* end of [dexp3_for] *)

let dexp3_if loc (s2e: sexp2)
  (d3e_cond: dexp3) (d3e_then: dexp3) (d3e_else: dexp3): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e d3e_cond in
  let sf2e = seff2_dexp3_union sf2e d3e_then in
  let sf2e = seff2_dexp3_union sf2e d3e_else in
  let is_prf = d3e_cond.dexp3_is_proof in {
      dexp3_loc= loc;
      dexp3_node= DE3if (d3e_cond, d3e_then, d3e_else);
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= s2e;
    }
(* end of [dexp3_if] *)

(* ****** ****** *)

let dexp3_int_with_type loc
  (ik: Syn.intkind) (s2e: sexp2) (i: intinf): dexp3 = {
    dexp3_loc= loc;
    dexp3_node= DE3int (ik, i);
    dexp3_is_proof= false;
    dexp3_seff= seff2_nil;
    dexp3_type= s2e;
  }
(* end of [dexp3_int_with_type] *)

let dexp3_int loc (ik: Syn.intkind) (i: intinf): dexp3 =
  let s2e = sexp2_int_t0ype_with_kind ik i in
    dexp3_int_with_type loc ik s2e i
(* end of [dexp3_int] *)

(* ****** ****** *)

let dexp3_lam_dyn_with_type loc
  (is_lin: bool) (s2e_fun: sexp2)
  (np3ts_arg: int_pat3_list) (d3e_body: dexp3): dexp3 = {
    dexp3_loc= loc;
    dexp3_node= DE3lam_dyn (is_lin, np3ts_arg, d3e_body);
    dexp3_is_proof= false;
    dexp3_seff= seff2_nil;
    dexp3_type= s2e_fun;
  }
(* end of [dexp3_lam_dyn_with_type] *)

let dexp3_lam_dyn loc (fc: Syn.funclo) (is_lin: bool)
  (sf2e: seff2) (np3ts: int_pat3_list) (d3e: dexp3): dexp3 = 
  let (npf, p3ts) = np3ts in
  let s2es_arg = List.map (function p3t -> p3t.pat3_type) p3ts in
  let s2e_res = d3e.dexp3_type in
  let is_prf = sexp2_is_proof s2e_res in
  let s2t_fun = srt2_fun_lin_prf is_lin is_prf in
  let lin = if is_lin then 1 else 0 in
  let s2e_funclo =
    sexp2_funclo_with_sort s2t_fun fc lin sf2e (npf, s2es_arg) s2e_res in
    dexp3_lam_dyn_with_type loc is_lin s2e_funclo np3ts d3e
(* end of [dexp3_lam_dyn] *)

(* ****** ****** *)

let dexp3_sif loc
  (s2e: sexp2) (s2p1: sexp2) (d3e2: dexp3) (d3e3: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3sif (s2p1, d3e2, d3e3);
  dexp3_is_proof= true;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_sif] *)

let dexp3_lam_sta_with_type loc
  (s2e: sexp2) (s2vs: svar2 list) (s2ps: sexp2 list) (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3lam_sta (s2vs, s2ps, d3e);
  dexp3_is_proof= d3e.dexp3_is_proof;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_lam_sta_with_type] *)


let dexp3_lam_sta loc
  (s2vs: svar2 list) (s2ps: sexp2 list) (d3e: dexp3): dexp3 =
  let s2e = sexp2_uni s2vs s2ps d3e.dexp3_type in
    dexp3_lam_sta_with_type loc s2e s2vs s2ps d3e
(* end of [dexp3_lam_sta] *)

(*
 *
 * Attention:
 *   parametric sorts need to be introduced to support
 *   a correct implementation
 *
 *)
let dexp3_lam_sta_para loc
  (s2vs0: svar2 list) (s2ps0: sexp2 list) (d3e: dexp3): dexp3 =
  let rec aux s2e =
    let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2exi (s2vs1, s2ps1, s2e1) ->
	sexp2_exi s2vs1 s2ps1 (aux s2e1)
    | _ -> sexp2_uni s2vs0 s2ps0 s2e in
    {
      dexp3_loc= loc;
      dexp3_node= DE3lam_sta_para (s2vs0, s2ps0, d3e);
      dexp3_is_proof= d3e.dexp3_is_proof;
      dexp3_seff= seff2_nil;
      dexp3_type= aux d3e.dexp3_type
    }
(* end of [dexp3_lam_sta_para] *)

(* ****** ****** *)

let dexp3_let loc (d3cs: dec3 list) (d3e: dexp3): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dec3_list_union sf2e d3cs in
  let sf2e = seff2_dexp3_union sf2e d3e in {
      dexp3_loc= loc;
      dexp3_node= DE3let (d3cs, d3e);
      dexp3_is_proof= false;
      dexp3_seff= sf2e;
      dexp3_type= d3e.dexp3_type;
    }
(* end of [dexp3_let] *)

let dexp3_let_simplify loc
  (d3cs: dec3 list) (d3e: dexp3): dexp3 = begin
  match d3cs with [] -> d3e | _ :: _ -> dexp3_let loc d3cs d3e
end (* end of [dexp3_let_simplify] *)


let dexp3_lst loc (s2e_lst: sexp2) (d3es_elt: dexp3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_list_union sf2e d3es_elt in {
      dexp3_loc= loc;
      dexp3_node= DE3lst d3es_elt;
      dexp3_is_proof= false;
      dexp3_seff= sf2e;
      dexp3_type= s2e_lst;
    }
(* end of [dexp3_lst] *)

let dexp3_loopexn loc (i: int): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3loopexn i;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
}

let dexp3_ptrof_ptr loc s2e d3e d3labs: dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3ptrof_ptr (d3e, d3labs);
  dexp3_is_proof= false;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e;
}

let dexp3_ptrof_var loc s2e d2v d3labs: dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3ptrof_var (d2v, d3labs);
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
}

let dexp3_raise loc (d3e: dexp3): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e d3e in
  let sf2e = seff2_add_eff sf2e Syn.EFFexn in {
      dexp3_loc= loc;
      dexp3_node= DE3raise d3e;
      dexp3_is_proof= false;
      dexp3_seff= sf2e;
      dexp3_type= sexp2_none_viewt0ype ();
    }
(* end of [dexp3_raise] *)

let dexp3_rec loc
  (s2e_rec: sexp2) (is_flat: bool) (npf: int) (ld3es: labdexp3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_labdexp3_list_union sf2e ld3es in
  let is_prf = labdexp3_arglist_is_proof npf ld3es in {
      dexp3_loc= loc;
      dexp3_node= DE3rec (is_flat, (npf, ld3es));
      dexp3_is_proof= is_prf;
      dexp3_seff= sf2e;
      dexp3_type= s2e_rec;
    }
(* end of [dexp3_rec] *)

let dexp3_rec_simplify loc
  (s2e: sexp2) (is_flat: bool) (npf: int) (ld3es: labdexp3 list): dexp3 =
  if is_flat then begin match ld3es with
    | [] -> dexp3_empty loc
    | [(l, d3e)] when npf == 0 -> d3e
    | _ -> dexp3_rec loc s2e is_flat npf ld3es
  end else begin
    dexp3_rec loc s2e is_flat npf ld3es
  end
(* end of [dexp3_rec_simplify] *)


(* ****** ****** *)

let dexp3_refarg loc
  (s2e0: sexp2) (refval: int) (freeknd: int) (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3refarg (refval, freeknd, d3e);
  dexp3_is_proof= d3e.dexp3_is_proof;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e0;
} (* end of [dexp3_refarg] *)

(* ****** ****** *)

let dlab3_nt_olab_oind
  (olab: lab option) (oind: (dexp3 list list) option): dlab3_nt = {
  dlab3_nt_lab= olab; dlab3_nt_ind= oind;
} (* end of [dlab3_nt_olab_oind] *)

let dlab3_olab_oind
  (olab: (lab * sexp2) option) (oind: (dexp3 list list * sexp2) option): dlab3 =
  { dlab3_lab= olab; dlab3_ind= oind; }
(* end of [dlab3_olab_oind] *)

(* ****** ****** *)

let dexp3_sel loc
  (s2e: sexp2) (d3e: dexp3) (d3labs: dlab3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e d3e in
  let sf2e = seff2_dlab3_list_union sf2e d3labs in {
      dexp3_loc= loc;
      dexp3_node= DE3sel (d3e, d3labs);
      dexp3_is_proof= sexp2_is_proof s2e;
      dexp3_seff= sf2e;
      dexp3_type= s2e;
    }
(* end of [dexp3_sel] *)

let dexp3_sel_ptr loc
  (s2e: sexp2) (d3e_ptr: dexp3) (d3labs: dlab3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e d3e_ptr in
  let sf2e = seff2_dlab3_list_union sf2e d3labs in {
      dexp3_loc= loc;
      dexp3_node= DE3sel_ptr (d3e_ptr, d3labs);
      dexp3_is_proof= sexp2_is_proof s2e;
      dexp3_seff= sf2e;
      dexp3_type= s2e;
    }
(* end of [dexp3_sel_ptr] *)

let dexp3_sel_var loc
  (s2e: sexp2) (d2v: dvar2) (d3labs: dlab3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dlab3_list_union sf2e d3labs in {
      dexp3_loc= loc;
      dexp3_node= DE3sel_var (d2v, d3labs);
      dexp3_is_proof= sexp2_is_proof s2e;
      dexp3_seff= sf2e;
      dexp3_type= s2e;
    }
(* end of [dexp3_sel_var] *)

(* ****** ****** *)

let dexp3_seq_with_type loc (s2e: sexp2) (d3es: dexp3 list): dexp3 =
  match d3es with
    | [] -> dexp3_empty loc
    | [d3e] -> d3e
    | _ -> begin
	let sf2e = seff2_nil in
	let sf2e = seff2_dexp3_list_union sf2e d3es in
	let is_prf = dexp3_list_is_proof d3es in {
	    dexp3_loc= loc;
	    dexp3_node= DE3seq d3es;
	    dexp3_is_proof= is_prf;
	    dexp3_seff= sf2e;
	    dexp3_type= s2e;  
	  }
      end
(* end of [dexp3_seq_with_type] *)

let dexp3_seq loc (d3es0: dexp3 list): dexp3 =
  let rec aux d3e d3es: sexp2 = match d3es with
    | [] -> d3e.dexp3_type
    | d3e :: d3es -> aux d3e d3es in begin
      match d3es0 with
	| d3e :: d3es ->
	    let s2e = aux d3e d3es in
	      dexp3_seq_with_type loc s2e d3es0
	| [] -> dexp3_empty loc
    end
(* end of [dexp3_seq] *)

let dexp3_string loc (s: string): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3string s;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_string_int_type s
}

let dexp3_special_string loc s2e (s: string): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3string s;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e
}

(* ****** ****** *)

let dexp3_struct_with_type loc
  (s2e: sexp2) (ld3es: labdexp3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_labdexp3_list_union sf2e ld3es in
  let is_prf = labdexp3_list_is_proof ld3es in {
    dexp3_loc= loc;
    dexp3_node= DE3struct ld3es;
    dexp3_is_proof= is_prf;
    dexp3_seff= sf2e;
    dexp3_type= s2e;
  }
(* end of [dexp3_struct_with_type] *)

let dexp3_template_cst loc
  (s2e: sexp2) (d2c: dcst2) (s2ess: sexp2 list list): dexp3 =
  let is_prf = Syn.dcstkind_is_proof d2c.dcst2_kind in {
    dexp3_loc= loc;
    dexp3_node= DE3template_cst (d2c, s2ess);
    dexp3_is_proof= is_prf;
    dexp3_seff= seff2_nil;
    dexp3_type= s2e;
  }
(* end of [dexp3_template_cst] *)

let dexp3_template_var loc
  (s2e: sexp2) (d2v: dvar2) (s2ess: sexp2 list list): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3template_var (d2v, s2ess);
  dexp3_is_proof= d2v.dvar2_is_proof;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_template_var] *)

let dexp3_top loc (s2e0: sexp2): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3top;
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e0;
} (* end of [dexp3_top] *)

let dexp3_trywith_with_seff loc
  (sf2e: seff2) (d3e: dexp3) (c3ls: cla3 list): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3trywith (d3e, c3ls);
  dexp3_is_proof= false;
  dexp3_seff= sf2e;
  dexp3_type= d3e.dexp3_type;
} (* end of [dexp3_trywith_with_seff] *)

let dexp3_trywith loc (d3e: dexp3) (c3ls: cla3 list): dexp3 =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e d3e in
  let sf2e = seff2_cla3_list_union sf2e c3ls in
    dexp3_trywith_with_seff loc sf2e d3e c3ls
(* end of [dexp3_trywith] *)

let dexp3_unfold loc (s2e: sexp2) (d3e: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3unfold d3e;
  dexp3_is_proof= d3e.dexp3_is_proof;
  dexp3_seff= d3e.dexp3_seff;
  dexp3_type= s2e
} (* end of [dexp3_unfold] *)

let dexp3_var_with_type loc s2e d2v: dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3var d2v;
  dexp3_is_proof= d2v.dvar2_is_proof;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_var_with_type] *)

let dexp3_var loc d2v: dexp3 = begin
  dexp3_var_with_type loc (type_of_dvar2 loc d2v) d2v
end (* end of [dexp3_var] *)

(* ****** ****** *)

let dexp3_viewat_assgn_ptr loc
  (d3e1: dexp3) (d3labs: dlab3 list) (d3e2: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3viewat_assgn_ptr (d3e1, d3labs, d3e2);
  dexp3_is_proof= true;
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
} (* end of [dexp3_viewat_assgn_ptr] *)

let dexp3_viewat_assgn_var loc
  (d2v1: dvar2) (d3labs: dlab3 list) (d3e2: dexp3): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3viewat_assgn_var (d2v1, d3labs, d3e2);
  dexp3_is_proof= true;
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
} (* end of [dexp3_viewat_assgn_var] *)

let dexp3_viewat_ptr loc (s2e: sexp2) (d3e: dexp3)
  (d3labs: dlab3 list) (d2v_view: dvar2) (s2labs_view: slab2 list): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3viewat_ptr (d3e, d3labs, d2v_view, s2labs_view);
  dexp3_is_proof= true;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_viewat_ptr] *)

let dexp3_viewat_var loc (s2e: sexp2) (d2v: dvar2)
  (d3labs: dlab3 list) (d2v_view: dvar2) (s2labs_view: slab2 list): dexp3 = {
  dexp3_loc= loc;
  dexp3_node= DE3viewat_var (d2v, d3labs, d2v_view, s2labs_view);
  dexp3_is_proof= true;
  dexp3_seff= seff2_nil;
  dexp3_type= s2e;
} (* end of [dexp3_viewat_var] *)

(* ****** ****** *)

let dexp3_while_with_seff loc
  (sf2e: seff2) (test: dexp3) (body: dexp3) = {
  dexp3_loc= loc;
  dexp3_node= DE3while (test, body);
  dexp3_is_proof= false;
  dexp3_seff= seff2_nil;
  dexp3_type= sexp2_void_t0ype ();
} (* end of [dexp3_while] *)

let dexp3_while loc (test: dexp3) (body: dexp3) =
  let sf2e = seff2_nil in
  let sf2e = seff2_dexp3_union sf2e test in
  let sf2e = seff2_dexp3_union sf2e body in
(*
  let () =
    PR.fprintf stdout
      "dexp3_while: sf2e = %a\n" Eff.fprint_seff2 sf2e in
*)
    dexp3_while_with_seff loc sf2e test body
(* end of [dexp3_while] *)

(* ****** ****** *)

let cla3 loc (p3ts: pat3 list) (gua: dexp3 option)
  (op2tcss: (patcst2 list list) option) (isneg: bool) (d3e: dexp3): cla3 = {
  cla3_loc= loc;
  cla3_pat= p3ts;
  cla3_gua= gua;
  cla3_isseq= op2tcss;
  cla3_isneg= isneg;
  cla3_body= d3e;
} (* end of [cla3] *)

(* ****** ****** *)

let dec3_extype loc (name: string) (def: sexp2): dec3 =
  { dec3_loc= loc; dec3_node= DC3extype (name, def); }

let dec3_extval loc (name: string) (def: dexp3): dec3 =
  { dec3_loc= loc; dec3_node= DC3extval (name, def); }

(* ****** ****** *)

let dec3_dyncsts loc
  (dck: Syn.dcstkind) (d2cs: dcst2 list): dec3 =
  { dec3_loc= loc; dec3_node= DC3dyncsts (dck, d2cs); }

let dec3_data loc
  (dtk: Syn.datakind) (s2cs: scst2 list): dec3 =
  { dec3_loc= loc; dec3_node= DC3data (dtk, s2cs); }

let dec3_exns loc (d2cs: dcon2 list): dec3 =
  { dec3_loc= loc; dec3_node= DC3exns d2cs; }

(* ****** ****** *)

let dec3_impl loc
  (cst: dcst2) (decarg: decarg2) (def: dexp3): dec3_impl = {
  dec3_impl_loc= loc;
  dec3_impl_cst= cst;
  dec3_impl_decarg= decarg;
  dec3_impl_def= def;
} (* end of [dec3_impl] *)

let dec3_impls loc (ds: dec3_impl list): dec3 = {
  dec3_loc= loc; dec3_node= DC3impls ds;
}

(* ****** ****** *)

let dec3_fun loc d2v d3e = {
  dec3_fun_loc= loc;
  dec3_fun_name= d2v;
  dec3_fun_def= d3e;
}

let dec3_funs loc
  (istemp: bool) (fk: Syn.funkind) (ds: dec3_fun list): dec3 =
  { dec3_loc= loc; dec3_node= DC3funs (istemp, fk, ds); }

(* ****** ****** *)

let dec3_val loc p3t d3e = {
  dec3_val_loc= loc;
  dec3_val_pat= p3t;
  dec3_val_def= d3e;
}

let dec3_vals loc
  (vk: Syn.valkind) (ds: dec3_val list): dec3 = {
  dec3_loc= loc; dec3_node= DC3vals (vk, ds);
}

let dec3_valpars loc (ds: dec3_val list): dec3 = {
  dec3_loc= loc; dec3_node= DC3valpars ds;
}

let dec3_valrecs loc (ds: dec3_val list): dec3 = {
  dec3_loc= loc; dec3_node= DC3valrecs ds;
}

(* ****** ****** *)

let dec3_var loc d2v_ptr d2v_view od3e: dec3_var = {
  dec3_var_loc= loc;
  dec3_var_ptr= d2v_ptr;
  dec3_var_view= d2v_view;
  dec3_var_ini= od3e;
} (* end of [dec3_var] *)

let dec3_vars loc
  (is_stack: bool) (ds: dec3_var list): dec3 = {
  dec3_loc= loc; dec3_node= DC3vars (is_stack, ds);
}

(* ****** ****** *)

let dec3_local loc
  (head: dec3 list) (body: dec3 list): dec3 = {
  dec3_loc= loc; dec3_node= DC3local (head, body);
} (* end of [dec3_local] *)

(* ****** ****** *)

let dec3_staload loc
  (f: Fil.filename) (ods3: (dec3 list) option): dec3 = {
  dec3_loc= loc; dec3_node= DC3staload (f, ods3);
} (* end of [dec3_staload] *)

let dec3_dynload loc
  (f: Fil.filename): dec3 = {
  dec3_loc= loc; dec3_node= DC3dynload f;
} (* end of [dec3_dynload] *)

(* ****** ****** *)

let dec3_extern loc
  (position: int) (code: string): dec3 = {
  dec3_loc= loc; dec3_node= DC3extern (position, code);
} (* end of [dec3_extern] *)

(* ****** ****** *)

type dexp23 =
    DE23dexp2 of dexp2 | DE23dexp3 of dexp3

type dexparg3 =
  | DEXPARG3sta of sexparg2 list
  | DEXPARG3dyn of int (* split *) * dexp3 list

(* ****** ****** *)

let dexp3_of_ditem2 loc (d2i: ditem2): dexp3 =
  match d2i with
    | DI2cst d2c -> dexp3_cst loc d2c
    | DI2var d2v -> dexp3_var loc d2v
    | _ -> begin
	PR.fprintf stderr "%a: dexp3_of_ditem2: %a\n"
	  Loc.fprint loc fprint_ditem2 d2i;
	Err.abort ();
      end
(* end of [dexp3_of_ditem2] *)

(* ****** ****** *)

(*

let rec dexp3_is_value (d3e0: dexp3): bool =
  match d3e0.dexp3_node with
    | DE3char _ -> true
    | DE3con (_, (npf, d3es)) -> dexp3_arg_list_is_value npf d3es
    | DE3cst _ -> true
    | DE3crypt (_, d3e) -> dexp3_is_value d3e
    | DE3delay _ -> true
    | DE3empty -> true
    | DE3fix (_, d3e) -> dexp3_is_value d3e
    | DE3float _ -> true
    | DE3fold d3e -> dexp3_is_value d3e
    | DE3int _ -> true
    | DE3lam_dyn _ -> true
    | DE3lam_sta _ -> true
    | DE3lam_sta_para _ -> true
    | DE3lst d3es -> dexp3_list_is_value d3es
    | DE3rec (_, (npf, ld3es)) -> labdexp3_arg_list_is_value npf ld3es
    | DE3seq d3es -> dexp3_list_is_value d3es
    | DE3string _ -> true
    | DE3struct ld3es -> labdexp3_list_is_value ld3es
    | DE3unfold d3e -> dexp3_is_value d3e
    | DE3var _ -> true
    | _ -> false

and dexp3_list_is_value (d3es: dexp3 list): bool =
  List.for_all dexp3_is_value d3es

and dexp3_arg_list_is_value (npf: int) (d3es: dexp3 list): bool =
  let rec aux i d3es = match d3es with
    | d3e :: d3es ->
	if i < npf then aux (i+1) d3es else
	  dexp3_is_value d3e && aux (i+1) d3es
    | [] -> true in
    aux 0 d3es

and labdexp3_list_is_value (ld3es: labdexp3 list): bool =
  List.for_all (function (l, d3e) -> dexp3_is_value d3e) ld3es

and labdexp3_arg_list_is_value (npf: int) (ld3es: labdexp3 list): bool =
  let rec aux i ld3es = match ld3es with
    | (l, d3e) :: ld3es ->
	if i < npf then aux (i+1) ld3es else
	  dexp3_is_value d3e && aux (i+1) ld3es
    | [] -> true in
    aux 0 ld3es

*)

(* ****** ****** *)

(* end of [ats_dynexp3.ml] *)
