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

(* high-level intermediate representation *)

open Ats_misc

open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2
open Ats_dyncst2

(* ****** ****** *)

module P = Printf

module Cnt = Ats_counter
module Eff = Ats_effect
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location
type symbol = Sym.symbol

(* ****** ****** *)

type hityp = {
  hityp_name: hityp_name;
  hityp_node: hityp_node;
}

and hityp_name =
  | HITNAM of string
  | HITNAM_ptr of string

and hityp_node =
  | HITextype of (* external named type *)
      string
  | HITfun of (* function type *)
      Syn.funclo * hityp list * hityp
  | HITrefarg of (* reference argument *)
      int(*refval*) * hityp * hityp
  | HITsum of (* constructor type *)
      dcon2 * hityp list
  | HITsum_tmp of (* constructor type in template *)
      dcon2 * hityp list
  | HITtyarr of (* array type *)
      hityp (* element type *) *
      sexp2 list list (* array dimension *)
  | HITtyrec_box of (* boxed record type *)
      labhityp list
  | HITtyrec_box_tmp of (* boxed record type in template *)
      labhityp list
  | HITtyrec_flt of (* flat record type *)
      labhityp list
  | HITtyrec_flt_tmp of (* flat record type in template *)
      labhityp list
  | HITtyrec_sin of (* flat singluar record type *)
      hityp
  | HITunion of (* union type *)
      labhityp list
  | HITvar of svar2
  | HITvararg (* variable argument *)

and labhityp = lab * hityp

(* ****** ****** *)

let abs_type_name = "ats_abs_type"
let bool_type_name = "ats_bool_type"
let char_type_name = "ats_char_type"
let clo_type_name = "ats_clo_ptr_type"
let double_type_name = "ats_double_type"
let float_type_name = "ats_float_type"
let int_type_name = "ats_int_type"
let ptr_type_name = "ats_ptr_type"
let string_type_name = "ats_ptr_type"
let sum_ptr_type_name = "ats_sum_ptr_type"
let var_type_name = "ats_var_type"
let void_type_name = "ats_void_type"

(* ****** ****** *)

(* for compiling templates *)

let the_svar2_hityp_list : (svar2 * hityp) list ref = ref []
let the_svar2_hityp_list_list : (svar2 * hityp) list list ref = ref []

let svar2_hityp_list_get (): (svar2 * hityp) list = !the_svar2_hityp_list

let svar2_hityp_list_push (xys: (svar2 * hityp) list): unit = begin
  the_svar2_hityp_list_list :=
    !the_svar2_hityp_list :: !the_svar2_hityp_list_list;
  the_svar2_hityp_list := xys
end

let svar2_hityp_list_pop (): unit =
  match !the_svar2_hityp_list_list with
    | xys :: xyss -> begin
	the_svar2_hityp_list_list := xyss; the_svar2_hityp_list := xys
      end
    | [] -> begin
	error_of_deadcode "ats_hiexp: svar2_hityp_list_pop"
      end

let svar2_hityp_list_find (s2v0: svar2): hityp option =
  let rec aux (xys: (svar2 * hityp) list): hityp option =
    match xys with
      | (s2v, hit) :: xys ->
	  if svar2_eq s2v0 s2v then Some hit else aux xys
      | [] -> None in
    aux !the_svar2_hityp_list

(* ****** ****** *)

let hityp_name_ptr = HITNAM ptr_type_name

let rec fprint_hityp (out: out_channel) (hit: hityp): unit =
  match hit.hityp_node with
    | HITfun (ft, hits_arg, hit_res) -> P.fprintf out
	"ats_fun_type(%a; %a)" fprint_hityp_list hits_arg fprint_hityp hit_res
    | HITsum_tmp (d2c, hits) -> P.fprintf out
	"ats_sumtemp_ptr_type(%a; %a)" fprint_dcon2 d2c fprint_hityp_list hits
    | HITtyrec_box_tmp (lhits) -> P.fprintf out "ats_rectemp_ptr_type(...)"
    | HITtyrec_flt_tmp (lhits) -> P.fprintf out "ats_rectemp_type(...)"
    | HITvar s2v -> P.fprintf out "ats_var_type(%a)" fprint_svar2 s2v
    | _ -> begin match hit.hityp_name with
	| HITNAM name -> P.fprintf out "%s" name
	| HITNAM_ptr name -> P.fprintf out "%s*" ptr_type_name
      end

and fprint_hityp_list
  (out: out_channel) (hits: hityp list): unit =
  fprint_list_with_sep fprint_hityp out hits ","

let fprint_hityp_list_list
  (out: out_channel) (hitss: hityp list list): unit =
  fprint_list_with_sep fprint_hityp_list out hitss ";"

let fprint_hityp_ptr (out: out_channel) (hit: hityp): unit =
  match hit.hityp_name with
    | HITNAM_ptr name -> P.fprintf out "%s" name
    | HITNAM name -> begin
	P.eprintf "ats_hiexp: fprint_hityp_ptr";
	Err.abort ();
      end

let name_of_hityp (hit: hityp): string =
  match hit.hityp_name with
    | HITNAM name -> name | HITNAM_ptr name -> ptr_type_name

let labname_of_labhityp ((l, hit): labhityp): lab * string =
  match hit.hityp_name with
    | HITNAM name -> (l, name) | HITNAM_ptr name -> (l, ptr_type_name)

(* ****** ****** *)

let hityp_extype (name: string): hityp =
  { hityp_name= HITNAM name; hityp_node= HITextype name; }

let hityp_fun (fc: Syn.funclo)
  (hits_arg: hityp list) (hit_res: hityp): hityp =
  { hityp_name= hityp_name_ptr;
    hityp_node= HITfun (fc, hits_arg, hit_res); }

let hityp_refarg
  (refval: int) (hit_in: hityp) (hit_out: hityp): hityp =
  { hityp_name= HITNAM "ats_ref_type";
    hityp_node= HITrefarg (refval, hit_in, hit_out); }

let hityp_sum (name: string) (d2c: dcon2) (hits_arg: hityp list): hityp =
  { hityp_name= HITNAM_ptr name; hityp_node= HITsum (d2c, hits_arg); }

let hityp_sum_tmp (d2c: dcon2) (hits_arg: hityp list): hityp =
  { hityp_name= HITNAM_ptr "ats_sumtemp_type";
    hityp_node= HITsum_tmp (d2c, hits_arg); }

let hityp_tyarr
  (hit_elt: hityp) (s2ess_dim: sexp2 list list): hityp =
  let name_elt =
    P.sprintf "[%s]" (name_of_hityp hit_elt) in
  { hityp_name= HITNAM name_elt;
    hityp_node= HITtyarr (hit_elt, s2ess_dim); }

let hityp_tyrec_box (name: string) (lhits: labhityp list): hityp =
  { hityp_name= HITNAM_ptr name; hityp_node= HITtyrec_box lhits; }

let hityp_tyrec_box_tmp (lhits: labhityp list): hityp =
  { hityp_name= HITNAM_ptr "ats_rectemp_type";
    hityp_node= HITtyrec_box_tmp lhits; }

let hityp_tyrec_flt (name: string) (lhits: labhityp list): hityp =
  { hityp_name= HITNAM name; hityp_node= HITtyrec_flt lhits; }

let hityp_tyrec_flt_tmp (lhits: labhityp list): hityp =
  { hityp_name= HITNAM "ats_rectemp_type";
    hityp_node= HITtyrec_flt_tmp lhits; }

let hityp_tyrec_sin (hit: hityp): hityp =
  { hityp_name= hit.hityp_name; hityp_node= HITtyrec_sin hit; }

let hityp_union (name: string) (lhits: labhityp list): hityp =
  { hityp_name= HITNAM name; hityp_node= HITunion lhits; }

let hityp_var (s2v: svar2): hityp =
  if svar2_is_boxed s2v then
    { hityp_name= HITNAM "ats_ptr_type"; hityp_node= HITvar s2v; }
  else
    { hityp_name= HITNAM "ats_var_type"; hityp_node= HITvar s2v; }

let hityp_vararg: hityp =
  { hityp_name= HITNAM "..."; hityp_node= HITvararg; }

(* ****** ****** *)

let hityp_bool = hityp_extype bool_type_name
let hityp_char = hityp_extype char_type_name
let hityp_clo = hityp_extype clo_type_name
let hityp_double = hityp_extype double_type_name
let hityp_float = hityp_extype float_type_name
let hityp_int = hityp_extype int_type_name
let hityp_ptr = hityp_extype ptr_type_name
let hityp_string = hityp_extype string_type_name
let hityp_sum_ptr = hityp_extype sum_ptr_type_name
let hityp_abs = hityp_extype abs_type_name
let hityp_void = hityp_extype void_type_name

(* ****** ****** *)

type hipat = {
  hipat_loc: loc;
  hipat_node: hipat_node;
  hipat_type: hityp;
}

and hipat_node =
  | HIPany (* wildcard *)
  | HIPbool of bool (* boolean pattern *)
  | HIPchar of char (* character pattern *)
  | HIPcon of (* constructor pattern *)
      int (* is_ref *) * hityp * dcon2 * hipat list
  | HIPempty (* empty pattern *)
  | HIPint of intinf (* integer pattern *)
  | HIPlst of hipat list (* list pattern *)
  | HIPrec of (* record pattern *)
      bool (* is_flat *) * hityp * labhipat list
  | HIPstring of string (* string pattern *)
  | HIPvar of bool(*isref*) * dvar2 * hipat option

and labhipat = lab * hipat

let rec fprint_hipat (out: out_channel) (hip0: hipat): unit =
  match hip0.hipat_node with
    | HIPany -> P.fprintf out "HIPany"
    | HIPbool b -> P.fprintf out "HIPbool(%b)" b
    | HIPchar c -> P.fprintf out "HIPchar(%c)" c
    | HIPcon (is_ref, hit_sum, d2c, hips) ->
	P.fprintf out "HIPcon(%a; %a)" fprint_dcon2 d2c fprint_hipat_list hips
    | HIPempty -> P.fprintf out "HIPempty"
    | HIPint i -> P.fprintf out "HIPint(%a)" fprint_intinf i
    | HIPlst hips -> P.fprintf out "HIPlst(%a)" fprint_hipat_list hips
    | HIPrec (is_flat, hit_rec, lhips) ->
	P.fprintf out "HIPrec{%a}" fprint_labhipat_list lhips
    | HIPstring s -> P.fprintf out "HIPstring(%s)" s
    | HIPvar (isref, d2v, ohip) -> begin match ohip with
	| Some hip -> begin
	    P.fprintf out "HIPvar(";
	    if isref then P.fprintf out "!";
	    fprint_dvar2 out d2v;
	    P.fprintf out "; ";
	    fprint_hipat out hip;
	    P.fprintf out ")";	    
	  end
	| None -> begin
	    P.fprintf out "HIPvar(";
	    if isref then P.fprintf out "!";
	    fprint_dvar2 out d2v;
	    P.fprintf out ")";
	  end
      end

and fprint_hipat_list (out: out_channel) (hips: hipat list): unit =
  fprint_list_with_sep fprint_hipat out hips ","

and fprint_labhipat (out: out_channel) ((l, hip): labhipat): unit =
  P.fprintf out "%a= %a" Lab.fprint l fprint_hipat hip

and fprint_labhipat_list (out: out_channel) (lhips: labhipat list): unit =
  fprint_list_with_sep fprint_labhipat out lhips ";"

(* ****** ****** *)

let hipat_any loc (hit: hityp): hipat = {
  hipat_loc= loc;
  hipat_node= HIPany;
  hipat_type= hit;
}

let hipat_bool loc (hit: hityp) (b: bool): hipat = {
  hipat_loc= loc;
  hipat_node= HIPbool b;
  hipat_type= hit;
}

let hipat_char loc (hit: hityp) (c: char): hipat = {
  hipat_loc= loc;
  hipat_node= HIPchar c;
  hipat_type= hit;
}

(* ****** ****** *)

let hipat_con loc (hit: hityp) (is_ref: int)
  (hit_sum: hityp) (d2c: dcon2) (hips: hipat list): hipat = {
  hipat_loc= loc;
  hipat_node= HIPcon (is_ref, hit_sum, d2c, hips);
  hipat_type= hit;
}

(* ****** ****** *)

let hipat_empty loc (hit: hityp): hipat = {
  hipat_loc= loc;
  hipat_node= HIPempty;
  hipat_type= hit;
}

let hipat_int loc (hit: hityp) (i: intinf): hipat = {
  hipat_loc= loc;
  hipat_node= HIPint i;
  hipat_type= hit;
}

let hipat_lst loc (hit: hityp) (hips: hipat list): hipat = {
  hipat_loc= loc;
  hipat_node= HIPlst hips;
  hipat_type= hit;
}

let hipat_rec loc (hit: hityp) (is_flat: bool)
  (hit_rec: hityp) (lhips: labhipat list): hipat = {
    hipat_loc= loc;
    hipat_node= HIPrec (is_flat, hit_rec, lhips);
    hipat_type= hit;
  }

let hipat_string loc (hit: hityp) (s: string): hipat = {
  hipat_loc= loc;
  hipat_node= HIPstring s;
  hipat_type= hit;
}

let hipat_var loc
  (hit: hityp) (isref: bool) (d2v: dvar2) (ohip: hipat option): hipat = {
  hipat_loc= loc;
  hipat_node= HIPvar (isref, d2v, ohip);
  hipat_type= hit;
}

(* ****** ****** *)

type hiexp = { 
  hiexp_loc : loc;
  hiexp_node : hiexp_node;
  hiexp_type : hityp;
}

and labhiexp = lab * hiexp

and hiexp_node =
  | HIEapp of hityp * hiexp * hiexp list
  | HIEarr of (* array construction *)
      hityp (* element type *) * hiexp list (* elements *)
  | HIEassgn_ptr of (* assignment to a pointer with offsets *)
      hiexp * hilab list * hiexp
  | HIEassgn_var of (* assignment to a variable with ofsets *)
      dvar2 * hilab list * hiexp
  | HIEbool of bool
  | HIEcase of (* case expression *)
      bool (* is_exhaustive *) * hiexp list * hicla list
  | HIEcastfn of dcst2 * hiexp
  | HIEchar of char
  | HIEcon of hityp * dcon2 * hiexp list
  | HIEcst of dcst2
  | HIEdelay of (* delayed computation *)
      int(*lin*) * hiexp
  | HIEdynload of Fil.filename (* dynamic loading *)
  | HIEempty
  | HIEextval of string
  | HIEfix of dvar2 * hiexp
  | HIEfloat of string
  | HIEfreeat of hiexp
  | HIEif of hiexp * hiexp * hiexp
  | HIEint of Syn.intkind * intinf
  | HIElam of hipat list * hiexp
  | HIElet of hidec list * hiexp
  | HIEloopexn of int (* break: 0 and continue: 1 *)
  | HIElst of hiexp list
  | HIEptrof_ptr of hiexp * hilab list
  | HIEptrof_var of dvar2 * hilab list
  | HIEraise of hiexp
  | HIErec of bool (*is_flat*) * hityp * labhiexp list
  | HIErefarg of int(*refval*) * int(*freeknd*) * hiexp
  | HIEsel of hiexp * hilab list
  | HIEsel_ptr of hiexp * hilab list
  | HIEsel_var of dvar2 * hilab list
  | HIEseq of hiexp list
  | HIEsizeof of (* size of type *)
      hityp (* type *)
  | HIEstring of (* string *)
      string
  | HIEtemplate_cst of dcst2 * (hityp list) list
  | HIEtemplate_var of dvar2 * (hityp list) list
  | HIEtop (* uninitialized value *)
  | HIEtrywith of hiexp * hicla list
  | HIEvar of dvar2
  | HIEwhile of hiexp (* test *) * hiexp (* loop body *)

(* ****** ****** *)

and hilab = {
  hilab_loc: loc;
  hilab_node: hilab_node;
}

and hilab_node =
  | HILlab of (* record selection *)
      lab (* label *) * hityp (* record type *)
  | HILind of (* array subscription *)
      hityp (* element type *) * hiexp list list (* index(es) *)

(* ****** ****** *)

and hicla = { (* type for clauses *)
  hicla_loc : loc; (* location information *)
  hicla_pat : hipat list; (* pattern list *)
  hicla_gua : hiexp option; (* clause guard *)
  hicla_body: hiexp; (* expression body *)
}

and hidec = {
  hidec_loc : loc;
  hidec_node : hidec_node;
}

and hidec_fun = {
  hidec_fun_loc: loc;
  hidec_fun_name: dvar2;
  hidec_fun_def: hiexp;
}

and hidec_val = {
  hidec_val_loc: loc;
  hidec_val_pat: hipat;
  hidec_val_def: hiexp;
}

and hidec_var = {
  hidec_var_loc: loc;
  hidec_var_ptr: dvar2;
  hidec_var_ini: hiexp option;
}

and hidec_impl = { (* dynamic implementation *)
  hidec_impl_loc: loc;
  hidec_impl_cst: dcst2;
  hidec_impl_istemp: bool;
  hidec_impl_decarg: (svar2 list * sexp2 list) list;
  hidec_impl_def: hiexp;
}

and hidec_node =
  | HIDextype of string (* name *) * hityp (* definition *)
  | HIDextval of string (* name *) * hiexp (* definition *)
  | HIDdyncsts of (* dynamic constant *)
      Syn.dcstkind * dcst2 list
  | HIDdata of (* datatype declaration *)
      Syn.datakind * scst2 list
(* exception constructors are erased:
  | HIDexns of (* exception constructor *)
      dcon2 list
*)
  | HIDimpls of hidec_impl list
  | HIDfuns of (* function *)
      bool (*is_template*) * Syn.funkind * hidec_fun list
  | HIDvals of Syn.valkind * hidec_val list
  | HIDvalpars of hidec_val list
  | HIDvalrecs of hidec_val list
  | HIDvars of bool (* is_stack *) * hidec_var list
  | HIDlocal of hidec list (* head *) * hidec list (* body *)
  | HIDstaload of Fil.filename * (hidec list) option
  | HIDdynload of Fil.filename
  | HIDextern of (* external code *)
      int (* position: 0/1 : top/end *) * string (* code *)

let rec fprint_hiexp (out: out_channel) (hie0: hiexp): unit =
  match hie0.hiexp_node with
    | HIEapp (hit_fun, hie_fun, hies_arg) -> P.fprintf out "HIEapp(%a, %a)"
	fprint_hiexp hie_fun fprint_hiexp_list hies_arg
    | HIEarr (hit_elt, hies_elt) -> P.fprintf out "HIEarr(%a; %a)"
	fprint_hityp hit_elt fprint_hiexp_list hies_elt
    | HIEassgn_ptr (hie_ptr, hils, hie_val) ->
        P.fprintf out "HIEassgn_ptr(%a; %a; %a)"
          fprint_hiexp hie_ptr fprint_hilab_list hils fprint_hiexp hie_val
    | HIEassgn_var (d2v, hils, hie_val) ->
        P.fprintf out "HIEassgn_var(%a; %a; %a)"
          fprint_dvar2 d2v fprint_hilab_list hils fprint_hiexp hie_val
    | HIEbool b -> P.fprintf out "HIEbool(%b)" b
    | HIEcase (is_exhaustive, hies, hicls) -> P.fprintf out "HIEcase(...)"
    | HIEcastfn (d2c, hie) ->
        P.fprintf out "HIEcastfn(%a; %a)" fprint_dcst2 d2c fprint_hiexp hie
    | HIEchar c -> P.fprintf out "HIEchar(%c)" c
    | HIEcon (hit_sum, d2c, hies) ->
	P.fprintf out "HIEcon(%a; %a)" fprint_dcon2 d2c fprint_hiexp_list hies
    | HIEcst d2c -> P.fprintf out "HIEcst(%a)" fprint_dcst2 d2c
    | HIEdelay (lin, hie) ->
	P.fprintf out "HIEdelay(%i; %a)" lin fprint_hiexp hie
    | HIEdynload f -> P.fprintf out "HIEdynload(%a)" Fil.fprint f
    | HIEempty -> P.fprintf out "HIEempty"
    | HIEextval code -> P.fprintf out "HIEextval(%s)" code
    | HIEfloat f -> P.fprintf out "HIEfloat(%s)" f
    | HIEfix (d2v_fun, hie_body) -> P.fprintf out "HIEfix(%a; %a)"
	fprint_dvar2 d2v_fun fprint_hiexp hie_body
    | HIEfreeat hie -> P.fprintf out "HIEfreeat(%a)" fprint_hiexp hie
    | HIEif (hie_cond, hie_then, hie_else) -> P.fprintf out "HIEif(%a; %a; %a)"
	fprint_hiexp hie_cond fprint_hiexp hie_then fprint_hiexp hie_else
    | HIEint (ik, i) -> P.fprintf out "HIEint(%a)" fprint_intinf i
    | HIElam (hips_arg, hie_body) -> P.fprintf out "HIElam(%a; %a)"
	fprint_hipat_list hips_arg fprint_hiexp hie_body
    | HIElet (hids, hie) -> P.fprintf out "HIElet(...; %a)" fprint_hiexp hie
    | HIEloopexn i ->
	if i > 0 then P.fprintf out "HIEcontinue" else P.fprintf out "HIEbreak"
    | HIElst hies_elt -> P.fprintf out "HIElst(%a)" fprint_hiexp_list hies_elt
    | HIEptrof_ptr (hie_ptr, hils) -> P.fprintf out "HIEptrof_ptr (%a; %a)"
	fprint_hiexp hie_ptr fprint_hilab_list hils
    | HIEptrof_var (d2v_ptr, hils) -> P.fprintf out "HIEptrof_var (%a; %a)"
	fprint_dvar2 d2v_ptr fprint_hilab_list hils
    | HIEraise hie -> P.fprintf out "HIEraise(%a)" fprint_hiexp hie
    | HIErec (is_flat, hit_rec, lhies) ->
	P.fprintf out "HIErec(%b;%a)" is_flat fprint_labhiexp_list lhies
    | HIErefarg (refval, freeknd, hie) -> P.fprintf out "HIErefarg(%i; %i; %a)"
	refval freeknd fprint_hiexp hie
    | HIEsel (hie, hils) ->
	P.fprintf out "HIEsel(%a; %a)" fprint_hiexp hie fprint_hilab_list hils
    | HIEsel_ptr (hie_ptr, hils) -> P.fprintf out "HIEsel_ptr(%a; %a)"
	fprint_hiexp hie_ptr fprint_hilab_list hils
    | HIEsel_var (d2v, hils) -> P.fprintf out "HIEsel_var(%a; %a)"
	fprint_dvar2 d2v fprint_hilab_list hils
    | HIEseq hies -> P.fprintf out "HIEseq(%a)" fprint_hiexp_list hies
    | HIEsizeof hit -> P.fprintf out "HIEsizeof(%a)" fprint_hityp hit
    | HIEstring s -> P.fprintf out "HIEstring(%s)" s
    | HIEtemplate_cst (d2c, hitss) -> P.fprintf out "HIEtemplate_cst(%a; %a)"
	fprint_dcst2 d2c fprint_hityp_list_list hitss
    | HIEtemplate_var (d2v, hitss) -> P.fprintf out "HIEtemplate_var(%a; %a)"
	fprint_dvar2 d2v fprint_hityp_list_list hitss
    | HIEtop -> P.fprintf out "HIEtop"
    | HIEtrywith (hie, cl3s) -> P.fprintf out "HIEtrywith(...)"
    | HIEvar d2v -> P.fprintf out "HIEvar(%a)" fprint_dvar2 d2v
    | HIEwhile (hie_test, hie_body) -> P.fprintf out "HIEwhile(%a; %a)" 
	fprint_hiexp hie_test fprint_hiexp hie_body

and fprint_hiexp_list (out: out_channel) (hies: hiexp list): unit =
  fprint_list_with_sep fprint_hiexp out hies ","

and fprint_hiexp_list_list (out: out_channel) (hiess: hiexp list list): unit =
  fprint_list_with_sep fprint_hiexp_list out hiess ","

and fprint_labhiexp (out: out_channel) ((l, hie): labhiexp): unit =
  P.fprintf out "%a= %a" Lab.fprint l fprint_hiexp hie

and fprint_labhiexp_list (out: out_channel) (lhies: labhiexp list): unit =
  fprint_list_with_sep fprint_labhiexp out lhies ","

and fprint_hilab (out: out_channel) (hil: hilab): unit =
  match hil.hilab_node with
    | HILlab (l, s2e_rec) -> (fprint_string out "."; Lab.fprint out l)
    | HILind (s2e_elt, hiess) -> begin
	fprint_string out "[";
	fprint_list_with_sep fprint_hiexp_list out hiess "][";
	fprint_string out "]";
      end

and fprint_hilab_list (out: out_channel) (hils: hilab list): unit =
  List.iter (fprint_hilab out) hils

(* ****** ****** *)

let hiexp_app loc (hit: hityp)
  (hit_fun: hityp) (hie_fun: hiexp) (hies_arg: hiexp list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEapp (hit_fun, hie_fun, hies_arg);
    hiexp_type= hit;
  }

let hiexp_arr loc (hit_arr: hityp)
  (hit_elt: hityp) (hies_elt: hiexp list): hiexp = {
  hiexp_loc= loc;
  hiexp_node= HIEarr (hit_elt, hies_elt);
  hiexp_type= hit_arr;
}

(* ****** ****** *)

let hiexp_assgn_ptr loc (hit: hityp)
  (hie_ptr: hiexp) (hils: hilab list) (hie_val: hiexp): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEassgn_ptr (hie_ptr, hils, hie_val);
    hiexp_type= hit;
  }

let hiexp_assgn_var loc (hit: hityp)
  (d2v: dvar2) (hils: hilab list) (hie_val: hiexp): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEassgn_var (d2v, hils, hie_val);
    hiexp_type= hit;
  }

(* ****** ****** *)

let hiexp_bool loc (hit: hityp) (b: bool): hiexp = {
  hiexp_loc= loc;
  hiexp_node= HIEbool b;
  hiexp_type= hit;
}

(* ****** ****** *)

let hiexp_case loc (hit: hityp)
  (is_exhaustive: bool) (hies: hiexp list) (hicls: hicla list): hiexp = {
  hiexp_loc= loc;
  hiexp_node= HIEcase (is_exhaustive, hies, hicls);
  hiexp_type= hit;
} (* end of [hiexp_case] *)

(* ****** ****** *)

let hiexp_castfn loc (hit: hityp)
  (d2c: dcst2) (hie_arg: hiexp): hiexp = {
  hiexp_loc= loc; hiexp_node= HIEcastfn (d2c, hie_arg); hiexp_type= hit;
} (* end of [hiexp_castfn] *)

(* ****** ****** *)

let hiexp_char loc (hit: hityp) (c: char): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEchar c; hiexp_type= hit; }

let hiexp_con loc (hit: hityp)
  (hit_sum: hityp) (d2c: dcon2) (hies: hiexp list): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEcon (hit_sum, d2c, hies); hiexp_type= hit; }

let hiexp_cst loc (hit: hityp) (d2c: dcst2): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEcst d2c; hiexp_type= hit; }

let hiexp_delay loc (hit: hityp) (lin: int) (hie: hiexp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEdelay (lin, hie); hiexp_type= hit; }

let hiexp_dynload loc (hit: hityp) (f: Fil.filename): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEdynload f; hiexp_type= hit; }

let hiexp_empty loc (hit: hityp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEempty; hiexp_type= hit; }

let hiexp_extval loc (hit: hityp) (code: string): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEextval code; hiexp_type= hit; }

let hiexp_fix loc (hit: hityp) (d2v: dvar2) (hie: hiexp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEfix (d2v, hie); hiexp_type= hit; }

let hiexp_float loc (hit: hityp) (f: string): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEfloat f; hiexp_type= hit; }

let hiexp_if loc (hit: hityp)
  (hie_cond: hiexp) (hie_then: hiexp) (hie_else: hiexp): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEif (hie_cond, hie_then, hie_else);
    hiexp_type= hit;
}

let hiexp_freeat loc (hit: hityp) (hie: hiexp): hiexp = {
  hiexp_loc= loc;
  hiexp_node= HIEfreeat hie;
  hiexp_type= hit
}

(*

let sexp2_of_intkind (ik: Syn.intkind): sexp2 =
  match ik with
    | Syn.IKint -> HITint
    | Syn.IKuint -> HITuint
    | Syn.IKlint -> HITint_long
    | Syn.IKulint -> HITuint_long
    | Syn.IKsint -> HITint_short
    | Syn.IKusint -> HITuint_short
    | Syn.IKint8 -> HITint8
    | Syn.IKuint8 -> HITuint8
    | Syn.IKint16 -> HITint16
    | Syn.IKuint16 -> HITuint16
    | Syn.IKint32 -> HITint32
    | Syn.IKuint32 -> HITuint32
    | Syn.IKint64 -> HITint64
    | Syn.IKuint64 -> HITuint64

*)

let hiexp_int loc
  (hit: hityp) (ik: Syn.intkind) (i: intinf): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEint (ik, i); hiexp_type= hit; }

let hiexp_lam loc (hit: hityp) (hips: hipat list) (hie: hiexp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIElam (hips, hie); hiexp_type= hit; }

let hiexp_let loc (hit: hityp) (hids: hidec list) (hie: hiexp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIElet (hids, hie); hiexp_type= hit; }

let hiexp_loopexn loc (hit: hityp) (i: int): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEloopexn i; hiexp_type= hit; }

let hiexp_lst loc (hit: hityp) (hies: hiexp list): hiexp =
  { hiexp_loc= loc; hiexp_node= HIElst hies; hiexp_type= hit; }

(* ****** ****** *)

let hiexp_ptrof_ptr loc
  (hit: hityp) (hie_ptr: hiexp) (hils: hilab list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEptrof_ptr (hie_ptr, hils);
    hiexp_type= hit;
  }

let hiexp_ptrof_var loc
  (hit: hityp) (d2v_ptr: dvar2) (hils: hilab list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEptrof_var (d2v_ptr, hils);
    hiexp_type= hit;
  }

(* ****** ****** *)

let hiexp_raise loc (hit: hityp) (hie: hiexp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEraise hie; hiexp_type= hit; } 

let hiexp_rec loc (hit: hityp) 
  (is_flat: bool) (hit_rec: hityp) (lhies: labhiexp list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIErec (is_flat, hit_rec, lhies);
    hiexp_type= hit;
  }

let hiexp_refarg loc (hit: hityp)
  (refval: int) (freeknd: int) (hie: hiexp): hiexp = {
  hiexp_loc= loc;
  hiexp_node= HIErefarg (refval, freeknd, hie);
  hiexp_type= hit;
}

(* ****** ****** *)

let hiexp_sel loc
  (hit: hityp) (hie: hiexp) (hils: hilab list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEsel (hie, hils);
    hiexp_type= hit;
  }

let hiexp_sel_ptr loc
  (hit: hityp) (hie_ptr: hiexp) (hils: hilab list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEsel_ptr (hie_ptr, hils);
    hiexp_type= hit;
  }

let hiexp_sel_var loc
  (hit: hityp) (d2v: dvar2) (hils: hilab list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEsel_var (d2v, hils);
    hiexp_type= hit;
  }

(* ****** ****** *)

let hiexp_seq loc (hit: hityp) (hies: hiexp list): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEseq hies; hiexp_type= hit; }

let hiexp_sizeof loc (hit: hityp) (hit_arg: hityp): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEsizeof hit_arg; hiexp_type= hit; }

let hiexp_string loc (hit: hityp) (s: string): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEstring s; hiexp_type= hit; }

(* ****** ****** *)

let hiexp_template_cst loc
  (hit: hityp) (d2c: dcst2) (hitss: hityp list list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEtemplate_cst (d2c, hitss);
    hiexp_type= hit;
  }

let hiexp_template_var loc
  (hit: hityp) (d2v: dvar2) (hitss: hityp list list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEtemplate_var (d2v, hitss);
    hiexp_type= hit;
  }

(* ****** ****** *)

let hiexp_top loc (hit: hityp): hiexp = {
  hiexp_loc= loc; hiexp_node= HIEtop; hiexp_type= hit;
}

let hiexp_trywith loc
  (hit: hityp) (hie: hiexp) (hicls: hicla list): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEtrywith (hie, hicls);
    hiexp_type= hit;
  }

let hiexp_var loc (hit: hityp) (d2v: dvar2): hiexp =
  { hiexp_loc= loc; hiexp_node= HIEvar d2v; hiexp_type= hit; }

let hiexp_while loc
  (hit: hityp) (hie_test: hiexp) (hie_body: hiexp): hiexp = {
    hiexp_loc= loc;
    hiexp_node= HIEwhile (hie_test, hie_body);
    hiexp_type= hit;
  }

(* ****** ****** *)

let hilab_lab loc (l: lab) (hit_rec: hityp): hilab =
  { hilab_loc= loc; hilab_node= HILlab (l, hit_rec) }

let hilab_ind loc (hit_elt: hityp) (hiess_ind: hiexp list list): hilab =
  { hilab_loc= loc; hilab_node= HILind (hit_elt, hiess_ind) }

(* ****** ****** *)

let hicla loc
  (hips: hipat list) (gua: hiexp option) (body: hiexp): hicla =
  { hicla_loc= loc; hicla_pat= hips; hicla_gua= gua; hicla_body= body; }

(* ****** ****** *)

let hidec_extype loc (name: string) (hit_def: hityp): hidec =
  { hidec_loc= loc; hidec_node= HIDextype (name, hit_def); }

let hidec_extval loc (name: string) (hie_def: hiexp): hidec =
  { hidec_loc= loc; hidec_node= HIDextval (name, hie_def); }

(* ****** ****** *)

let hidec_dyncsts loc
  (dck: Syn.dcstkind) (d2cs: dcst2 list): hidec =
  { hidec_loc= loc; hidec_node= HIDdyncsts (dck, d2cs); }

let hidec_data loc
  (dtk: Syn.datakind) (s2cs: scst2 list): hidec =
  { hidec_loc= loc; hidec_node= HIDdata (dtk, s2cs); }

(* ****** ****** *)

let hidec_fun loc (d2v: dvar2) (hie: hiexp): hidec_fun =
  { hidec_fun_loc= loc; hidec_fun_name= d2v; hidec_fun_def= hie; }

let hidec_funs loc
  (is_temp: bool) (fk: Syn.funkind) (hids: hidec_fun list): hidec =
  { hidec_loc= loc; hidec_node= HIDfuns (is_temp, fk, hids); }

let hidec_val loc (hip: hipat) (hie: hiexp): hidec_val =
  { hidec_val_loc= loc; hidec_val_pat= hip; hidec_val_def= hie; }

let hidec_vals loc
  (vk: Syn.valkind) (hids: hidec_val list): hidec =
  { hidec_loc= loc; hidec_node= HIDvals (vk, hids); }

let hidec_valpars loc (hids: hidec_val list): hidec =
  { hidec_loc= loc; hidec_node= HIDvalpars hids; }

let hidec_valrecs loc (hids: hidec_val list): hidec =
  { hidec_loc= loc; hidec_node= HIDvalrecs hids; }

(* ****** ****** *)

let hidec_var loc (d2v: dvar2) (ini: hiexp option): hidec_var =
  { hidec_var_loc= loc; hidec_var_ptr= d2v; hidec_var_ini= ini; }

let hidec_vars loc (is_stack: bool) (hids: hidec_var list): hidec =
  { hidec_loc= loc; hidec_node= HIDvars (is_stack, hids); }

(* ****** ****** *)

let hidec_impl loc (d2c: dcst2) (istemp: bool)
  (decarg: (svar2 list * sexp2 list) list) (hie: hiexp): hidec_impl = {
    hidec_impl_loc= loc;
    hidec_impl_cst= d2c;
    hidec_impl_istemp= istemp;
    hidec_impl_decarg= decarg;
    hidec_impl_def= hie;
  }

let hidec_impls loc (hids: hidec_impl list): hidec =
  { hidec_loc= loc; hidec_node= HIDimpls hids; }

(* ****** ****** *)

let hidec_local loc
  (head: hidec list) (body: hidec list): hidec =
  { hidec_loc= loc; hidec_node= HIDlocal (head, body); }

(* ****** ****** *)

let hidec_staload loc
  (f: Fil.filename) (ohids: (hidec list) option): hidec =
  { hidec_loc= loc; hidec_node= HIDstaload (f, ohids); }

let hidec_dynload loc (f: Fil.filename): hidec =
  { hidec_loc= loc; hidec_node= HIDdynload f; }

(* ****** ****** *)

let hidec_extern loc (position: int) (code: string): hidec =
  { hidec_loc= loc; hidec_node= HIDextern (position, code); }

(* ****** ****** *)

type vartyp = { vartyp_var: dvar2; vartyp_typ: hityp; }

let fprint_vartyp (out: out_channel) (vt: vartyp): unit =
  P.fprintf out "%a(%a)" fprint_dvar2 vt.vartyp_var fprint_hityp vt.vartyp_typ

module VarTypOrd: Map.OrderedType with type t = vartyp = struct
  type t = vartyp
  let compare vt1 vt2 = 
    let d2v1 = vt1.vartyp_var and d2v2 = vt2.vartyp_var in
      compare (d2v1.dvar2_stamp) (d2v2.dvar2_stamp)
end

module VarTypSet: Set.S with type elt = vartyp = Set.Make (VarTypOrd)
module VarTypMap: Map.S with type key = vartyp = Map.Make (VarTypOrd)

(* ****** ****** *)

(* end of [ats_hiexp.ml] *)
