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

open Ats_staexp2
open Ats_staexp2_util
open Ats_misc

module Eff = Ats_effect
module Fil = Ats_filename
module Cnt = Ats_counter
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol
module Syn = Ats_syntax

type lab = Lab.label
type loc = Loc.location

type stamp = Cnt.count
let fprint_stamp = Cnt.fprint

type dcstextdef = Syn.dcstextdef

(* ****** ****** *)

(* datatypes for dynamic expressions and declarations *)

type ditem2 =
  | DI2con of dcon2 list
  | DI2cst of dcst2
  | DI2mac of dmac2
  | DI2sym of ditem2 list (* overloaded symbol *)
  | DI2var of dvar2

and dcst2 = {
  dcst2_loc: loc;
  dcst2_name: Syn.did;
  dcst2_filename: Fil.filename;
  dcst2_fullname_id: string;
  dcst2_kind: Syn.dcstkind;
  dcst2_decarg: decarg2;
  dcst2_arity: int list; (* arity *)
  dcst2_type: sexp2; (* assigned type *)
  dcst2_extdef: dcstextdef;
  dcst2_stamp: stamp; (* uniquely determines a dynamic constant *)
  mutable dcst2_def: dexp2 option;
}

and dmac2 = {
  dmac2_loc: loc;
  dmac2_name: Syn.did;
  dmac2_abbrev: bool; (* abbreviated or full *)
  dmac2_arity: int list;
  dmac2_arg: (dvar2 list) list;
  dmac2_def: dexp2;
  dmac2_stamp: stamp  (* uniquely determines a macro constant *)
}

and dsym2 = {
  dsym2_loc: loc;
  dsym2_name: Syn.dqual_opt_id;
  dsym2_item: ditem2 list;
}

and dvar2 = {
  dvar2_loc: loc;
  dvar2_name: Syn.did; (* the name of the dynamic variable *)
  dvar2_stamp: stamp; (* uniquely determines a dynamic variable *)  
  dvar2_is_fixed: bool; (* lam-variable or fix-variable *)
  mutable dvar2_level: int; (* 0: toplevel *)
  mutable dvar2_decarg: decarg2;
  (* linear status: nonlinear (-1), linear (>=0) *)
  mutable dvar2_linear: int;
  mutable dvar2_addr: sexp2 option;
  mutable dvar2_view: dvar2 option;
  mutable dvar2_final: dvar2_final_status;
  mutable dvar2_master_type: sexp2; (* type or view *)
  mutable dvar2_type: sexp2 option; (* type or view *)
  mutable dvar2_is_proof: bool;
  mutable dvar2_ntimes: int;
}

and dvar2_final_status =
  | DVFSnone
  | DVFSsome of sexp2
  | DVFSvbox of sexp2

(* ****** ****** *)

and statype2 = { (* state type *)
  statype2_svs: svar2 list;
  statype2_gua: sexp2 list;
  statype2_met: (sexp2 list) option;
  statype2_body: statype2_body;
}

and statype2_body = (dvar2 * sexp2 option) list

(* ****** ****** *)

and pat2 = { (* type for dynamic patterns *)
  pat2_loc: loc; (* location locmation *)
  pat2_node: pat2_node; (* actual representation *)
  pat2_svs: svar2 list; (* static variables *)
  pat2_dvs: dvar2 list; (* dynamic variables *)
  mutable pat2_type: sexp2 option;
}

and labpat2 = lab * pat2

and int_pat2_list = int (* arity_p *) * pat2 list
and int_labpat2_list = int (* arity_p *) * labpat2 list

and pat2_node =
  | PT2ann of (* ascribed pattern *)
      pat2 * sexp2
  | PT2any (* wildcard *)
  | PT2bool of (* boolean pattern *)
      bool 
  | PT2char of (* character pattern *)
      char 
  | PT2con of (* constructor pattern *)
      int (* freeknd *) * dcon2 *
      (svar2 list) list * (sexp2 list) list * sexp2 *
      int_pat2_list (* arguments *)
  | PT2empty (* empty pattern *)
  | PT2exi of (* existentially quantified pattern *)
      svar2 list * pat2
  | PT2int of (* integer pattern *)
      intinf
  | PT2list of (* pattern list *)
      int_pat2_list 
  | PT2lst of (* list pattern *)
      pat2 list
  | PT2rec of (* record pattern *)
      bool (* is_flat *) * bool (* is_omit *) * int_labpat2_list
  | PT2string of (* string pattern *)
      string 
  | PT2var of (* variable pattern *)
      bool (*isref*) * dvar2 * pat2 option
  | PT2vbox of (* vbox pattern *)
      dvar2 
(* end of [pat2_node] *)

and dexp2 = { (* type for dynamic expressions *)
  dexp2_loc: loc; (* location locrmation *)
  dexp2_node: dexp2_node; (* actual representation *)
  mutable dexp2_type: sexp2 option;
} 

and labdexp2 = lab * dexp2

and int_dexp2_list = int (* arity_p *) * dexp2 list
and int_labdexp2_list = int (* arity_p *) * labdexp2 list

and dlab2 = {
  dlab2_lab: lab option;
  dlab2_ind: dexp2 list list option;
}

and dexp2_node =
  | DE2ann_type of (* ascribed dynamic expressions *)
      dexp2 * sexp2
  | DE2ann_seff of (* ascribed with effects *)
      dexp2 * seff2 
  | DE2ann_funclo of (* ascribed with fun/clo kind (funclo) *)
      dexp2 * Syn.funclo
  | DE2apps of dexp2 * dexparg2 list
  | DE2arr of (* array expression *)
      sexp2 * dexp2 list
  | DE2arrsub of (* array subscription *)
      dsym2 (* brackets overloading *) * dexp2 * dexp2 list list
  | DE2assgn of (* assignment *)
      dexp2 * dexp2
  | DE2case of (* dynamic case-expression *)
      int * statype2 option * dexp2 list * cla2 list
  | DE2char of (* dynamic character *)
      char
  | DE2con of (* dynamic constructor *)
      dcon2 * sexparg2 list * int (* pfarity *) * dexp2 list
  | DE2cst of (* dynamic constant *)
      dcst2
  | DE2crypt of (* cryption *)
      int(*kind*) * dexp2 (* 1/-1: encrypt/decrypt *)
  | DE2delay of (* lazy evaluation *)
      dexp2
  | DE2demac of (* macro *)
      dexp2
  | DE2deref of (* dereference *)
      dexp2
  | DE2dynload of (* dynamic loading *)
      Fil.filename
  | DE2effmask of (* effect masking *)
      Syn.effect * dexp2
  | DE2empty (* empty expression *)
  | DE2enmac of (* macro encoding *)
      dexp2
  | DE2exi of (* existential sum *)
      sexparg2 * dexp2
  | DE2extval of (* external code *)
      sexp2 (* type *) * string (* code *)
  | DE2fix of (* dynamic fixed-point expression *)
      dvar2 * dexp2
  | DE2float of (* dynamic float *)
      string
  | DE2fold of (* folding recursive types *)
      scst2 * dexp2
  | DE2foldat of (* fold at a given address *)
      sexparg2 list * dexp2
  | DE2freeat of (* free at a given address *)
      sexparg2 list * dexp2
  | DE2for of (* for-loop *)
      loopinv2 option * (dexp2 * dexp2 * dexp2) (* ini, test, post *) * dexp2 (*body*)
  | DE2if of (* conditional dynaimc expression *)
      statype2 option * dexp2 * dexp2 * dexp2 option
  | DE2int of (* dynamic integer *)
      Syn.intkind * intinf
  | DE2lam_dyn of (* dynamic abstraction *)
      bool (* is_linear *) * int_pat2_list * dexp2 
  | DE2lam_met of (* metric abstraction *)
      dvar2 list ref * sexp2 list * dexp2
  | DE2lam_sta of (* static lambda-abstraction *)
      svar2 list * sexp2 list * dexp2
  | DE2lam_sta_para of (* static parametric lambda-abstraction *)
      svar2 list * sexp2 list * dexp2
  | DE2let of (* dynamic let-expression *)
      dec2 list * dexp2
  | DE2loopexn of (* break: 0 and continue: 1 *)
      int
  | DE2lst of (* dynamic list expression *)
      dexp2 list
  | DE2mac of (* dynamic macro *)
      dmac2 
  | DE2mod of (* module *)
      moditemdec2 list
  | DE2ptrof of (* taking the address of *)
      dexp2
  | DE2raise of (* raised exception *)
      dexp2
  | DE2rec of (* record *)
      bool (* is_flat *) * int_labdexp2_list
  | DE2sel of (* record selection *)
      dexp2 * dlab2 list
  | DE2seq of (* sequencing *)
      dexp2 list
  | DE2sif of (* static conditional dynamic expression *)
      sexp2 * dexp2 * dexp2
  | DE2string of (* dynamic string *)
      string
  | DE2struct of (* structure *)
      labdexp2 list
  | DE2sym of (* overloaded dynamic symbol *)
      dsym2 
  | DE2template of (* template instantiation *)
      dexp2 * sexp2 list list
  | DE2top (* uninitialized value *)
  | DE2trywith of (* handling exception *)
      dexp2 * cla2 list
  | DE2unfold of (* unfolding recursive types *)
      scst2 * dexp2
  | DE2var of (* dynamic variable *)
      dvar2
  | DE2viewat of (* view at a given address *)
      dexp2
  | DE2while of (* while-loop *)
      loopinv2 option * dexp2 (* test *) * dexp2 (* body *)
(* end of [dexp2_node] *)

and dexparg2 =
  | DEXPARG2sta of sexparg2 list
  | DEXPARG2dyn of int_dexp2_list

(* datatype for declarations *)

and cla2 = { (* type for clauses *)
  cla2_loc: loc; (* location locrmation *)
  cla2_pat: pat2 list; (* pattern list *)
  cla2_gua: dexp2 option; (* pattern guard *)
  cla2_isseq: bool; (* sequential *)
  cla2_isneg: bool; (* negative *)
  cla2_body: dexp2; (* expression body *)
}

and loopinv2 = {
  loopinv2_loc: loc;
  loopinv2_svs: svar2 list;
  loopinv2_gua: sexp2 list;
  loopinv2_met: (sexp2 list) option;
  loopinv2_arg: statype2_body;
  loopinv2_res: statype2 option;
}

(* ****** ****** *)

and dec2_stavar = { (* static existential variable *)
  dec2_stavar_loc: loc;
  dec2_stavar_var: svar2;
}

and dec2_sasp = { (* static assumption *)
  dec2_sasp_loc: loc;
  dec2_sasp_cst: scst2;
  dec2_sasp_def: sexp2;  
}

and dec2_impl = { (* dynamic implementation *)
  dec2_impl_loc: loc;
  dec2_impl_cst: dcst2;
  dec2_impl_decarg: decarg2;
  dec2_impl_tmparg: sexp2 list list;
  dec2_impl_def: dexp2;  
}

and dec2_fun = {
  dec2_fun_loc: loc;
  dec2_fun_name: dvar2;
  dec2_fun_def: dexp2;
}


and dec2_val = {
  dec2_val_loc: loc;
  dec2_val_pat: pat2;
  dec2_val_def: dexp2;
  dec2_val_ann: sexp2 option;
}

and dec2_var = {
  dec2_var_loc: loc;
  dec2_var_dvar: dvar2;
  dec2_var_svar: svar2; (* address *)
  dec2_var_type: sexp2 option;
  dec2_var_ini: dexp2 option;
}

(* ****** ****** *)

and moditemdec2 = {
  moditemdec2_loc: loc;
  moditemdec2_node: moditemdec2_node;
}

and moditemdec2_node =
  | MID2funs of Syn.funkind * dec2_fun list (* function declaration *)
  | MID2vals of Syn.valkind * dec2_val list (* value declaration *)
  | MID2valrecs of dec2_val list (* recursive value declaration *)

(* ****** ****** *)

and dec2 = {
  dec2_loc: loc;
  dec2_node: dec2_node;
} 

and dec2_node =
  | DC2stavars of (* static existential variables *)
      dec2_stavar list
  | DC2sasps of (* static assumption *)
      dec2_sasp list
  | DC2extype of (* external type *)
      string (* extype name *) * sexp2 (* extype definition *)
  | DC2extval of (* external value *)
      string (* extval name *) * dexp2 (* extval definition *)
  | DC2data of (* data declaration *)
      Syn.datakind * scst2 list
  | DC2dyncsts of (* dynamic constants *)
      Syn.dcstkind * dcst2 list
  | DC2exns of (* exception constructors *)
      dcon2 list
  | DC2impls of (* dynamic implementation *)
      dec2_impl list
  | DC2funs of (* dynamic functon *)
      bool (*is_template*) * Syn.funkind * dec2_fun list
  | DC2vals of Syn.valkind * dec2_val list
  | DC2valpars of dec2_val list
  | DC2valrecs of dec2_val list
  | DC2vars of bool (* is_stack *) * dec2_var list
  | DC2local of (* local declaration *)
      dec2 list (* head *) * dec2 list (* body *)
  | DC2staload of (* dynamic load *)
      Fil.filename * (dec2 list) option
  | DC2dynload of (* dynamic load *)
      Fil.filename
  | DC2extern of (* external code *)
      int (* position: 0/1 : top/end *) * string (* code *)
(* end of [dec2_node] *)

(* ****** ****** *)

(* some print functions on dynamic experissions *)

let rec fprint_ditem2 (out: out_channel) (d2i: ditem2): unit =
  match d2i with
    | DI2con d2cs -> P.fprintf out "DI2con (%a)" fprint_dcon2_list d2cs
    | DI2cst d2c -> P.fprintf out "DI2cst (%a)" fprint_dcst2 d2c
    | DI2mac d2m -> P.fprintf out "DI2cst (%a)" fprint_dmac2 d2m
    | DI2sym d2is -> P.fprintf out "DI2sym (%a)" fprint_ditem2_list d2is
    | DI2var d2v -> P.fprintf out "DI2fil (%a)" fprint_dvar2 d2v
(* end of [fprint_ditem2] *)

and fprint_ditem2_list (out: out_channel) (d2is: ditem2 list): unit =
  fprint_list_with_sep fprint_ditem2 out d2is ","

and fprint_dcon2 (out: out_channel) (d2c: dcon2): unit =
  Syn.fprint_did out d2c.dcon2_name

and fprint_dcon2_list (out: out_channel) (d2cs: dcon2 list) =
  fprint_list_with_sep fprint_dcon2 out d2cs ","

and fprint_dcst2 (out: out_channel) (d2c: dcst2): unit =
  Syn.fprint_did out d2c.dcst2_name

and fprint_dcst2_list (out: out_channel) (d2cs: dcst2 list) =
  fprint_list_with_sep fprint_dcst2 out d2cs ","

and fprint_dmac2 (out: out_channel) (d2m: dmac2): unit =
  Syn.fprint_did out d2m.dmac2_name

and fprint_dsym2 (out: out_channel) (d2s: dsym2): unit =
  Syn.fprint_dqual_opt_id out d2s.dsym2_name

and fprint_dvar2 (out: out_channel) (d2v: dvar2): unit =
  P.fprintf out "%a(%a)"
    Syn.fprint_did d2v.dvar2_name Cnt.fprint d2v.dvar2_stamp

and fprint_dvar2_list (out: out_channel) (d2vs: dvar2 list): unit =
  fprint_list_with_sep fprint_dvar2 out d2vs ", "

(* ****** ****** *)

let fprint_statype2_body (out: out_channel) (sty_bd: statype2_body): unit =
  let aux out (d2v, os2e) = match os2e with
    | Some s2e -> P.fprintf out "%a:%a" fprint_dvar2 d2v fprint_sexp2 s2e
    | None -> fprint_dvar2 out d2v in
    fprint_list_with_sep aux out sty_bd ", "

(* ****** ****** *)

let rec fprint_pat2 (out: out_channel) (p2t: pat2): unit =
  match p2t.pat2_node with
    | PT2ann (p2t, s2e) -> P.fprintf out "PT2ann(%a : %a)"
	fprint_pat2 p2t fprint_sexp2 s2e
    | PT2any -> P.fprintf out "PT2any"
    | PT2bool b -> P.fprintf out "PT2bool(%b)" b
    | PT2char c -> P.fprintf out "PT2char(%c)" c
    | PT2con (freeknd, d2c, _, _, _, (npf, p2ts)) -> P.fprintf out
	"PT2con(%a; %i; %a)" fprint_dcon2 d2c npf fprint_pat2_list p2ts
    | PT2empty -> P.fprintf out "PT2empty()"
    | PT2exi (s2vs, p2t) -> P.fprintf out
	"PT2exi(%a;%a)" fprint_svar2_list s2vs fprint_pat2 p2t
    | PT2int i -> P.fprintf out "PT2int(%s)" (string_of_intinf i)
    | PT2list (npf, p2ts) ->
	P.fprintf out "PT2list(%i; %a)" npf fprint_pat2_list p2ts
    | PT2lst (p2ts) -> P.fprintf out "PT2lst(%a)" fprint_pat2_list p2ts
    | PT2rec (_, _, (npf, lp2ts)) ->
	P.fprintf out "PT2rec(%i; %a)" npf fprint_labpat2_list lp2ts
    | PT2string s -> P.fprintf out "PT2string(%s)" s
    | PT2var (isref, d2v, op2t) -> begin match op2t with
        | Some p2t -> begin
            P.fprintf out "PT2var(";
            if isref then P.fprintf out "!";
            fprint_dvar2 out d2v;
            P.fprintf out "; ";
            fprint_pat2 out p2t;
            P.fprintf out ")";
          end
	| None -> begin
            P.fprintf out "PT2var(";
            if isref then P.fprintf out "!";
            fprint_dvar2 out d2v;
            P.fprintf out ")";
          end
      end
    | PT2vbox d2v -> P.fprintf out "PT2vbox(%a)" fprint_dvar2 d2v
(* end of [fprint_pat2] *)

and fprint_pat2_list (out: out_channel) (p2ts: pat2 list): unit =
  fprint_list_with_sep fprint_pat2 out p2ts ","

and fprint_labpat2 (out: out_channel) (l, p2t): unit =
  P.fprintf out "%a=%a" Lab.fprint l fprint_pat2 p2t

and fprint_labpat2_list (out: out_channel) lp2ts: unit =
  fprint_list_with_sep fprint_labpat2 out lp2ts ","

(* ****** ****** *)

let rec fprint_dexp2 (out: out_channel) (d2e0: dexp2): unit =
  match d2e0.dexp2_node with
    | DE2ann_type (d2e, s2e) ->
	P.fprintf out "DE2ann_type(%a; %a)" fprint_dexp2 d2e fprint_sexp2 s2e
    | DE2ann_seff (d2e, sf2e) -> P.fprintf out "DE2ann_seff(%a; %a)"
	fprint_dexp2 d2e fprint_seff2 sf2e
    | DE2ann_funclo (d2e, fc) -> P.fprintf out "DE2ann_funclo(%a; %a)"
	fprint_dexp2 d2e Syn.fprint_funclo fc
    | DE2arr (s2e, d2es) -> P.fprintf out "DE2arr(%a; %a)"
	fprint_sexp2 s2e fprint_dexp2_list d2es
    | DE2arrsub (d2s, root, offset) -> P.fprintf out "DE2arrsub(%a; %a)"
	fprint_dexp2 root fprint_dexp2_list_list offset
    | DE2assgn (d2e1, d2e2) -> P.fprintf out "DE2assgn(%a; %a)"
	fprint_dexp2 d2e1 fprint_dexp2 d2e2
    | DE2case _ -> P.fprintf out "DE2case(...)"
    | DE2char c -> P.fprintf out "DE2char(%c)" c
    | DE2con (d2c, _, npf, d2es) -> P.fprintf out "DE2con(%a; %i; %a)"
	fprint_dcon2 d2c npf fprint_dexp2_list d2es
    | DE2cst d2c -> fprint_dcst2 out d2c
    | DE2apps (d2e, d2as) -> P.fprintf out "DE2apps(%a; %a)"
	fprint_dexp2 d2e fprint_dexparg2_list d2as
    | DE2crypt (knd, d2e) ->
	P.fprintf out "DE2crypt(%i; %a)" knd fprint_dexp2 d2e
    | DE2delay d2e -> P.fprintf out "DE2delay(%a)" fprint_dexp2 d2e
    | DE2demac d2e -> P.fprintf out "DE2demac(%a)" fprint_dexp2 d2e
    | DE2deref d2e -> P.fprintf out "DE2deref(%a)" fprint_dexp2 d2e
    | DE2dynload f -> P.fprintf out "DE2dynload(%a)" Fil.fprint f
    | DE2effmask (eff, d2e) -> P.fprintf out "DE2effmask(%a; %a)"
	Syn.fprint_effect eff fprint_dexp2 d2e
    | DE2empty -> P.fprintf out "DE2empty()"
    | DE2enmac d2e -> P.fprintf out "DE2enmac(%a)" fprint_dexp2 d2e
    | DE2exi (_, d2e) -> P.fprintf out "DE2exi (...; %a)" fprint_dexp2 d2e
    | DE2extval (s2e, code) ->
	P.fprintf out "DE2extval(%a; %s)" fprint_sexp2 s2e code
    | DE2fix (d2v, d2e) -> P.fprintf out "DE2fix(%a; %a)"
	fprint_dvar2 d2v fprint_dexp2 d2e
    | DE2float s -> P.fprintf out "DE2float(%s)" s
    | DE2fold (s2c, d2e) -> P.fprintf out "DE2fold(%a; %a)"
	fprint_scst2 s2c fprint_dexp2 d2e
    | DE2foldat (s2as, d2e) -> P.fprintf out "DE2foldat(%a)" fprint_dexp2 d2e
    | DE2freeat (s2as, d2e) -> P.fprintf out "DE2freeat(%a)" fprint_dexp2 d2e
    | DE2for _ -> P.fprintf out "DE2for(...)"
    | DE2if (osty2, d2e1, d2e2, od2e3) -> begin
	match od2e3 with
	  | None -> P.fprintf out "DE2if(%a; %a)"
	      fprint_dexp2 d2e1 fprint_dexp2 d2e2
	  | Some d2e3 -> P.fprintf out "DE2if(%a; %a; %a)"
	      fprint_dexp2 d2e1 fprint_dexp2 d2e2 fprint_dexp2 d2e3
      end
    | DE2int (ik, i) -> P.fprintf out "DE2int(%s)" (string_of_intinf i)
    | DE2lam_dyn _ -> P.fprintf out "DE2lam_dyn(...)"
    | DE2lam_sta _ -> P.fprintf out "DE2lam_sta(...)"
    | DE2lam_sta_para _ -> P.fprintf out "DE2lam_sta_para(...)"
    | DE2let (d2cs, d2e) -> P.fprintf out "DE2let(%a; %a)"
	fprint_dec2_list d2cs fprint_dexp2 d2e
    | DE2loopexn i -> P.fprintf out "DE2loopexn(%i)" i
    | DE2lst d2es -> P.fprintf out "DE2lst(%a)" fprint_dexp2_list d2es
    | DE2mac d2m -> fprint_dmac2 out d2m
    | DE2lam_met _ -> P.fprintf out "DE2lam_met(...)"
    | DE2mod _ -> P.fprintf out "DE2mod(...)"
    | DE2ptrof d2e -> P.fprintf out "DE2ptrof(%a)" fprint_dexp2 d2e
    | DE2raise (d2e) -> P.fprintf out "DE2raise(%a)" fprint_dexp2 d2e
    | DE2rec (is_flat, (npf, ld2es)) ->
	P.fprintf out "DE2rec(%i; %a)" npf fprint_labdexp2_list ld2es
    | DE2sel (d2e, les) ->
	P.fprintf out "DE2sel(%a; %a)" fprint_dexp2 d2e fprint_dlab2_list les
    | DE2seq d2es -> P.fprintf out "DE2seq(%a)" fprint_dexp2_list d2es
    | DE2sif (s2e1, d2e2, d2e3) ->
	P.fprintf out "DE2sif(%a; %a; %a)"
	  fprint_sexp2 s2e1 fprint_dexp2 d2e2 fprint_dexp2 d2e3
    | DE2string s -> P.fprintf out "DE2string(%s)" s
    | DE2struct ld2es -> P.fprintf out "DE2struct(%a)" fprint_labdexp2_list ld2es
    | DE2sym d2s -> fprint_dsym2 out d2s
    | DE2template (d2e, s2ess) -> P.fprintf out "DE2template(%a; %a)"
	fprint_dexp2 d2e fprint_sexp2_list_list s2ess
    | DE2top -> P.fprintf out "DE2top"
    | DE2trywith (d2e, _) -> P.fprintf out "DE2trywith(%a; ...)" fprint_dexp2 d2e
    | DE2unfold (s2c, d2e) -> P.fprintf out "DE2unfold(%a; %a)"
	fprint_scst2 s2c fprint_dexp2 d2e
    | DE2var d2v -> fprint_dvar2 out d2v
    | DE2viewat d2e -> P.fprintf out "DE2viewat(%a)" fprint_dexp2 d2e
    | DE2while _ -> P.fprintf out "DE2while(...)" 
(* end of [fprint_dexp2] *)

and fprint_dexp2_list (out: out_channel) (d2es: dexp2 list): unit =
    fprint_list_with_sep fprint_dexp2 out d2es ","

and fprint_dexp2_list_list (out: out_channel) (d2ess: dexp2 list list): unit =
    fprint_list_with_sep fprint_dexp2_list out d2ess ";"

and fprint_dlab2 (out: out_channel) (dl: dlab2): unit =
  match dl.dlab2_ind with
    | None -> Lab.fprint_opt out dl.dlab2_lab
    | Some d2ess -> P.fprintf out "%a[%a]"
	Lab.fprint_opt dl.dlab2_lab fprint_dexp2_list_list d2ess
(* end of [fprint_dlab2] *)

and fprint_dlab2_list (out: out_channel) (dls: dlab2 list): unit =
    fprint_list_with_sep fprint_dlab2 out dls ","  

and fprint_labdexp2 (out: out_channel) ((l, d2e): labdexp2): unit =
  P.fprintf out "%a=%a" Lab.fprint l fprint_dexp2 d2e

and fprint_labdexp2_list (out: out_channel) (ld2es: labdexp2 list): unit =
    fprint_list_with_sep fprint_labdexp2 out ld2es ","

and fprint_dexparg2 (out: out_channel) (d2a: dexparg2): unit =
  match d2a with
    | DEXPARG2sta s2as ->
	P.fprintf out "{%a}" fprint_sexparg2_list s2as
    | DEXPARG2dyn (npf, d2es) ->
	P.fprintf out "(%i; %a)" npf fprint_dexp2_list d2es
(* end of [fprint_dexparg2] *)

and fprint_dexparg2_list (out: out_channel) (d2as: dexparg2 list): unit =
    fprint_list_with_sep fprint_dexparg2 out d2as " "

and fprint_dec2 (out: out_channel) (d2: dec2): unit =
  match d2.dec2_node with
    | DC2vals (_, xs) -> P.fprintf out "DC2vals(%a)" fprint_dec2_val_list xs
    | _ -> P.fprintf out "DC2(...)"
(*
  | DC2stavars of (* static existential variable *)
      dec2_stavar list
  | DC2sasps of (* static assumption *)
      dec2_sasp list
  | DC2extype of (* external type *)
      string (* extype name *) * sexp2 (* extype definition *)
  | DC2extval of (* external value *)
      string (* extval name *) * dexp2 (* extval definition *)
  | DC2data of (* data declaration *)
      Syn.datakind * scst2 list
  | DC2dyncsts of (* dynamic constants *)
      Syn.dcstkind * dcst2 list
  | DC2exns of (* exception constructors *)
      dcon2 list
  | DC2impls of (* dynamic implementation *)
      dec2_impl list
  | DC2funs of Syn.funkind * dec2_fun list
  | DC2vals of Syn.valkind * dec2_val list
  | DC2valpars of dec2_val list
  | DC2valrecs of dec2_val list
  | DC2vars of bool (* is_stack *) * dec2_var list
  | DC2local of (* local declaration *)
      dec2 list (* head *) * dec2 list (* body *)
  | DC2staload of (* dynamic load *)
      Fil.filename * (dec2 list) option
  | DC2dynload of (* dynamic load *)
      Fil.filename
  | DC2extern of (* external code *)
      int (* position *) * string (* code *)
*)

and fprint_dec2_list (out: out_channel) (ds2: dec2 list): unit =
  fprint_list_with_sep fprint_dec2 out ds2 "; "

and fprint_dec2_val (out: out_channel) (x: dec2_val): unit =
  match x.dec2_val_ann with
    | Some s2e -> P.fprintf out "%a = %a:%a"
	fprint_pat2 x.dec2_val_pat fprint_dexp2 x.dec2_val_def fprint_sexp2 s2e
    | None -> P.fprintf out "%a = %a"
	fprint_pat2 x.dec2_val_pat fprint_dexp2 x.dec2_val_def
(* end of [fprint_dec2_val] *)

and fprint_dec2_val_list (out: out_channel) (xs: dec2_val list): unit =
  fprint_list_with_sep fprint_dec2_val out xs "; "

(* ****** ****** *)

let svar2_linear_add_list loc (s2vs1: svar2 list) (s2vs2: svar2 list)
  : svar2 list =
  let rec aux s2vs1 = function
    | [] -> s2vs1
    | s2v2 :: s2vs2 ->
	let id = s2v2.svar2_name in
	let is_nonlinear =
	  List.exists
	    (function s2v1 -> Syn.sid_eq id (s2v1.svar2_name)) s2vs1 in
	  if not (is_nonlinear) then aux (s2v2 :: s2vs1) s2vs2
	  else begin
	    P.fprintf stderr
	      "%a: the static variable <%a> occurs repeatedly in a pattern."
	      Loc.fprint loc fprint_svar2 s2v2;
	    prerr_newline ();
	    Err.abort ();
	  end in
    aux s2vs1 s2vs2
(* end of [svar2_linear_add_list] *)

let dvar2_linear_add_list loc d2vs1 d2vs2: dvar2 list =
  let rec aux d2vs1 = function
    | [] -> d2vs1
    | d2v2 :: d2vs2 ->
	let id = d2v2.dvar2_name in
	let is_nonlinear =
	  List.exists (function d2v1 -> Syn.did_eq id (d2v1.dvar2_name)) d2vs1 in
	  if not (is_nonlinear) then aux (d2v2 :: d2vs1) d2vs2
	  else begin
	    P.fprintf stderr
	      "%a: the dynamic variable <%a> occurs repeatedly in a pattern."
	      Loc.fprint loc Syn.fprint_did id;
	    prerr_newline ();
	    Err.abort ();
	  end in
    aux d2vs1 d2vs2
(* end of [dvar2_linear_add_list] *)

(* ****** ****** *)

let pat2_svar_list loc p2ts: svar2 list =
  List.fold_right
    (fun p2t res -> svar2_linear_add_list loc res p2t.pat2_svs) p2ts []

let pat2_dvar_list loc p2ts: dvar2 list =
  List.fold_right
    (fun p2t res -> dvar2_linear_add_list loc res p2t.pat2_dvs) p2ts []

let labpat2_svar_list loc (lp2ts: labpat2 list): svar2 list =
  List.fold_right
    (fun (l, p2t) res -> svar2_linear_add_list loc res p2t.pat2_svs) lp2ts []

let labpat2_dvar_list loc (lp2ts: labpat2 list): dvar2 list =
  List.fold_right
    (fun (l, p2t) res -> dvar2_linear_add_list loc res p2t.pat2_dvs) lp2ts []

(* ****** ****** *)

let pat2_ann loc p2t s2e: pat2 = {
  pat2_loc= loc;
  pat2_node= PT2ann (p2t, s2e);
  pat2_svs= p2t.pat2_svs;
  pat2_dvs= p2t.pat2_dvs;
  pat2_type= None;
}

let pat2_any loc: pat2 = {
  pat2_loc= loc;
  pat2_node= PT2any;
  pat2_svs= [];
  pat2_dvs= [];
  pat2_type= None;
} 

let pat2_char loc (c: char): pat2 = {
  pat2_loc= loc;
  pat2_node= PT2char c;
  pat2_svs= [];
  pat2_dvs= [];
  pat2_type= None;
}

(* ****** ****** *)

(*
 * freeknd =  1: linear constractor to be preserved
 * freeknd =  0: nonlinear constructor
 * freeknd = -1: linear constructor to be freed
 *)

let pat2_con loc (freeknd: int)
  (d2c: dcon2) s2vss s2pss s2e np2ts: pat2 =
  let (npf, p2ts) = np2ts in
  let s2vs = pat2_svar_list loc p2ts in
  let d2vs = pat2_dvar_list loc p2ts in {
      pat2_loc= loc;
      pat2_node= PT2con (freeknd, d2c, s2vss, s2pss, s2e, np2ts);
      pat2_svs= svar2_linear_add_list loc s2vs (List.concat s2vss);
      pat2_dvs= d2vs;
      pat2_type= None;
    }
(* end of [pat2_con] *)

(* ****** ****** *)

let pat2_empty loc: pat2 = {
  pat2_loc= loc;
  pat2_node= PT2empty;
  pat2_svs= [];
  pat2_dvs= [];
  pat2_type= None;
}

let pat2_exi loc (s2vs: svar2 list) (p2t: pat2): pat2 = {
  pat2_loc= loc;
  pat2_node= PT2exi (s2vs, p2t);
  pat2_svs= svar2_linear_add_list loc s2vs p2t.pat2_svs;
  pat2_dvs= p2t.pat2_dvs;
  pat2_type= None;
}

let pat2_int loc (i: intinf): pat2 = {
  pat2_loc= loc;
  pat2_node= PT2int i;
  pat2_svs= [];
  pat2_dvs= [];
  pat2_type= None;
}

let pat2_list loc (np2ts: int_pat2_list): pat2 =
  let (npf, p2ts) = np2ts in
  let s2vs = pat2_svar_list loc p2ts in
  let d2vs = pat2_dvar_list loc p2ts in {
      pat2_loc= loc;
      pat2_node= PT2list np2ts;
      pat2_svs= s2vs;
      pat2_dvs= d2vs;
      pat2_type= None;
    }
(* end of [pat2_list] *)

let pat2_lst loc p2ts: pat2 =
  let s2vs = pat2_svar_list loc p2ts in
  let d2vs = pat2_dvar_list loc p2ts in {
      pat2_loc= loc;
      pat2_node= PT2lst p2ts;
      pat2_svs= s2vs;
      pat2_dvs= d2vs;
      pat2_type= None;
    }
(* end of [pat2_lst] *)

let pat2_rec loc
  (is_flat: bool) (is_omit: bool) (npf: int) (lp2ts: labpat2 list): pat2 =
  let s2vs = labpat2_svar_list loc lp2ts in
  let d2vs = labpat2_dvar_list loc lp2ts in {
      pat2_loc= loc;
      pat2_node= PT2rec (is_flat, is_omit, (npf, lp2ts));
      pat2_svs= s2vs;
      pat2_dvs= d2vs;
      pat2_type= None;
    }
(* end of [pat2_rec] *)

let pat2_string loc (s: string): pat2 = {
  pat2_loc= loc;
  pat2_node= PT2string s;
  pat2_svs= [];
  pat2_dvs= [];
  pat2_type= None;
}

let pat2_tup loc
  (is_flat: bool) (is_omit: bool) (npf: int) (p2ts: pat2 list): pat2 = 
  let rec aux i lp2ts = function
    | [] -> pat2_rec loc is_flat is_omit npf (List.rev lp2ts)
    | p2t :: p2ts ->
	let lp2ts = (Lab.make_with_int i, p2t) :: lp2ts in
	  aux (i+1) lp2ts p2ts in
    aux 0 [] p2ts
(* end of [pat2_tup] *)

let pat2_var_none loc (isref: bool) (d2v: dvar2): pat2 = {
  pat2_loc= loc;
  pat2_node= PT2var (isref, d2v, None);
  pat2_svs= [];
  pat2_dvs= [d2v];
  pat2_type= None;
}

let pat2_var_some loc (isref: bool) (d2v: dvar2) (p2t: pat2): pat2 =
  let id = d2v.dvar2_name in
  let is_nonlinear = List.exists
    (function d2v -> Syn.did_eq id (d2v.dvar2_name)) p2t.pat2_dvs in
  let () =
    if is_nonlinear then begin
      P.fprintf stderr
	"%a: the dynamic variable <%a> occurs repeatedly in a pattern."
	Loc.fprint loc Syn.fprint_did id;
      prerr_newline ();
      Err.abort ()
    end in {
      pat2_loc= loc;
      pat2_node= PT2var (isref, d2v, Some p2t);
      pat2_svs= p2t.pat2_svs;
      pat2_dvs= d2v :: p2t.pat2_dvs;
      pat2_type= None;
    }
 (* end of [pat2_var_some] *)

let pat2_var loc (isref: bool) (d2v: dvar2) (op2t: pat2 option): pat2 =
  match op2t with
    | Some p2t -> pat2_var_some loc isref d2v p2t
    | None -> pat2_var_none loc isref d2v
(* end of [pat2_var] *)

let pat2_vbox loc d2v: pat2 = {
  pat2_loc= loc;
  pat2_node= PT2vbox d2v;
  pat2_svs= [];
  pat2_dvs= [d2v];
  pat2_type= None;
} (* end of [pat2_vbox] *)

(* ****** ****** *)

let dcst2_is_funcst (d2c: dcst2): bool = Syn.dcstkind_is_fun (d2c.dcst2_kind)
let dcst2_is_castfn (d2c: dcst2): bool = Syn.dcstkind_is_castfn (d2c.dcst2_kind)
let dcst2_is_proof (d2c: dcst2): bool = Syn.dcstkind_is_proof (d2c.dcst2_kind)
let dcst2_is_axiom (d2c: dcst2): bool = Syn.dcstkind_is_axiom (d2c.dcst2_kind)

let dcst2_make loc
  (name: Syn.did) (filename: Fil.filename) (dck: Syn.dcstkind)
  (decarg: decarg2) (arity: int list) (s2e: sexp2) (ext: dcstextdef): dcst2 =
  let fullname_id = match ext with
    | Syn.DCSTEXTDEFsome_fun name -> name
    | Syn.DCSTEXTDEFsome_mac name ->
	let n = String.length name in String.sub name 4(*mac#*) (n-4)
    | Syn.DCSTEXTDEFnone -> begin
	let name_id = string_identifize (Syn.string_of_did name) in
	  P.sprintf "%s__%s" (Fil.filename_fullname_id filename) name_id
      end in
(*
  let () =
    P.fprintf stdout "dcst2_make: fullname = %s\n"  fullname in
  let () =
    P.fprintf stdout "dcst2_make: fullname = %s\n"  (string_identifize fullname) in
*)
  let stamp = Cnt.dcst2_new_stamp () in {
      dcst2_loc= loc;
      dcst2_name= name;
      dcst2_filename= filename;
      dcst2_fullname_id= fullname_id;
      dcst2_kind= dck;
      dcst2_decarg= decarg;
      dcst2_arity= arity;
      dcst2_type= s2e;
      dcst2_def= None;
      dcst2_extdef= ext;
      dcst2_stamp= stamp;
    }
(* end of [dcst2_make] *)

let dmac2_make loc (name: Syn.did)
  (is_abbrev: bool) (arg: (dvar2 list) list) (d2e: dexp2): dmac2 = {
  dmac2_loc = loc;
  dmac2_name = name;
  dmac2_abbrev = is_abbrev;
  dmac2_arity = List.map List.length arg;
  dmac2_arg = arg;
  dmac2_def = d2e;
  dmac2_stamp = Cnt.dmac2_new_stamp ();
} (* end of [dmac2_make] *)

let dsym2_make loc
  (name: Syn.dqual_opt_id) (d2is: ditem2 list): dsym2 = {
  dsym2_loc= loc; dsym2_name= name; dsym2_item= d2is;
} (* end of [dsym2_make] *)

(* ****** ****** *)

let dvar2_new_with_id loc (name: Syn.did) (is_fixed: bool): dvar2 = {
  dvar2_loc= loc;
  dvar2_name= name;
  dvar2_decarg= [];
  dvar2_stamp= Cnt.dvar2_new_stamp ();
  dvar2_is_fixed= is_fixed;
  dvar2_level= -1;
  dvar2_linear= -1;
  dvar2_addr= None;
  dvar2_view= None;
  dvar2_final= DVFSnone;
  dvar2_master_type= sexp2_empty_type; (* place holder *)
  dvar2_type= None;
  dvar2_is_proof= false;
  dvar2_ntimes = 0;
} (* end of [dvar2_new_with_id] *)

let dvar2_new loc (is_fixed: bool): dvar2 =
  let id =
    Syn.make_did_with_loc_and_symbol loc (Cnt.dvar2_new_name ()) in
    dvar2_new_with_id loc id is_fixed

let dvar2_copy loc d2v0: dvar2 =
  let d2v = dvar2_new_with_id
    d2v0.dvar2_loc d2v0.dvar2_name d2v0.dvar2_is_fixed in
  let () = d2v.dvar2_ntimes <- d2v0.dvar2_ntimes in d2v

let dvar2_new_any loc =
  let id =
    Syn.make_did_with_loc_and_symbol loc Sym.symUNDERSCORE in
    dvar2_new_with_id loc id false (*is_fixed*)

let dvar2_ntimes_inc (d2v: dvar2): unit =
  d2v.dvar2_ntimes <- d2v.dvar2_ntimes + 1

let dvar2_is_used (d2v: dvar2): bool =
  if d2v.dvar2_ntimes > 0 then true else false

let dvar2_is_unused (d2v: dvar2): bool =
  if d2v.dvar2_ntimes > 0 then false else true

(* ****** ****** *)

let statype2_make
  (s2vs: svar2 list) (s2es: sexp2 list)
  (met: (sexp2 list) option) (body: statype2_body)
  : statype2 = {
    statype2_svs= s2vs;
    statype2_gua= s2es;
    statype2_met= met;
    statype2_body= body;
  }

let statype2_nil: statype2 = statype2_make [] [] None []

let loopinv2_make loc (svs: svar2 list) (gua: sexp2 list)
  (met: (sexp2 list) option) (arg: statype2_body) (res: statype2 option)
  : loopinv2 = {
    loopinv2_loc= loc;
    loopinv2_svs= svs;
    loopinv2_gua= gua;
    loopinv2_met= met;
    loopinv2_arg= arg;
    loopinv2_res= res;
  }
(* end of [loopinv2_make] *)

let loopinv2_nil: loopinv2 = loopinv2_make Loc.nonloc [] [] None [] None

(* ****** ****** *)

let dexp2_ann_type loc (d2e: dexp2) (s2e: sexp2): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2ann_type (d2e, s2e);
  dexp2_type= None;
}

let dexp2_ann_seff loc (d2e: dexp2) (sf2e: seff2): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2ann_seff (d2e, sf2e);
  dexp2_type= None;
}

let dexp2_ann_funclo loc (d2e: dexp2) (fc: Syn.funclo): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2ann_funclo (d2e, fc);
  dexp2_type= None;
}

(* ****** ****** *)

let dexp2_apps loc
  (d2e_fun: dexp2) (d2as: dexparg2 list): dexp2 = {
    dexp2_loc= loc;
    dexp2_node= DE2apps (d2e_fun, d2as);
    dexp2_type= None;
  }

let dexp2_arr loc (s2e: sexp2) (d2es: dexp2 list): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2arr (s2e, d2es); dexp2_type= None;
}

let dexp2_arrsub loc
  (d2s_brackets: dsym2) (root: dexp2) (offset: dexp2 list list)
  : dexp2 = {
    dexp2_loc= loc;
    dexp2_node= DE2arrsub (d2s_brackets, root, offset);
    dexp2_type= None;
  }

let dexp2_assgn loc (d2e1: dexp2) (d2e2: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2assgn (d2e1, d2e2); dexp2_type= None;
}

(* ****** ****** *)

let dexp2_case loc (i: int)
  (osty2: statype2 option) (d2es: dexp2 list) (c2ls: cla2 list): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2case (i, osty2, d2es, c2ls);
  dexp2_type= None;
} (* end of [dexp2_case] *)

(* ****** ****** *)

let dexp2_char loc (c: char): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2char c; dexp2_type= None;
} 

let dexp2_app_dyn loc d2e npf d2es: dexp2 =
  let d2en =
    let d2a = DEXPARG2dyn (npf, d2es) in
      match d2e.dexp2_node with
	| DE2apps (d2e1, d2as) -> DE2apps (d2e1, d2as @ [d2a])
	| _ -> DE2apps (d2e, [d2a]) in
    { dexp2_loc= loc; dexp2_node= d2en; dexp2_type= None; }
(* end of [dexp2_app_dyn] *)

let dexp2_con loc (d2c: dcon2)
  (s2as: sexparg2 list) (npf: int) (d2es: dexp2 list): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2con (d2c, s2as, npf, d2es);
  dexp2_type= None;
} (* end of [dexp2_con] *)

let dexp2_cst loc (d2c: dcst2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2cst d2c; dexp2_type= None;
} 

let dexp2_crypt loc (knd: int) (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2crypt (knd, d2e); dexp2_type= None;
}

let dexp2_delay loc (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2delay (d2e); dexp2_type= None;
}

let dexp2_demac loc (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2demac (d2e); dexp2_type= None;
}

let dexp2_deref loc (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2deref (d2e); dexp2_type= None;
}

let dexp2_dynload loc (f: Fil.filename): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2dynload f; dexp2_type= None;
}

let dexp2_dmac loc (d2m: dmac2): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2mac d2m;
  dexp2_type= None;
}

let dexp2_effmask loc (eff: Syn.effect) (d2e: dexp2): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2effmask (eff, d2e);
  dexp2_type= None;
}

let dexp2_empty loc: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2empty;
  dexp2_type= None;
}

let dexp2_enmac loc d2e: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2enmac (d2e);
  dexp2_type= None;
}

let dexp2_exi loc (s2a: sexparg2) d2e: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2exi (s2a, d2e);
  dexp2_type= None;
}

let dexp2_extval loc (s2e: sexp2) (code: string) = {
  dexp2_loc= loc;
  dexp2_node= DE2extval (s2e, code);
  dexp2_type= None;
}

let dexp2_float loc (f: string): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2float f; dexp2_type= None;
}

let dexp2_fix loc d2v d2e: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2fix (d2v, d2e);
  dexp2_type= None;
}

let dexp2_fold loc (s2c: scst2) d2e: dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2fold (s2c, d2e); dexp2_type= None;
}

let dexp2_foldat loc (s2as: sexparg2 list) (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2foldat (s2as, d2e); dexp2_type= None;
}

let dexp2_freeat loc (s2as: sexparg2 list) (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2freeat (s2as, d2e); dexp2_type= None;
}

let dexp2_for loc (oinv: loopinv2 option)
  (init: dexp2) (test: dexp2) (post: dexp2) (body: dexp2)
  : dexp2 = {
    dexp2_loc= loc;
    dexp2_node= DE2for (oinv, (init, test, post), body);
    dexp2_type= None;
  }

let dexp2_if loc (osty2: statype2 option)
  (d2e1: dexp2) (d2e2: dexp2) (od2e3: dexp2 option): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2if (osty2, d2e1, d2e2, od2e3);
  dexp2_type= None;
}

let dexp2_int loc (ik: Syn.intkind) (i: intinf): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2int (ik, i); dexp2_type= None;
}

(* ****** ****** *)

let dexp2_lam_dyn loc
  (is_lin: bool) (np2ts: int_pat2_list) (d2e: dexp2): dexp2 = {
    dexp2_loc= loc;
    dexp2_node= DE2lam_dyn (is_lin, np2ts, d2e);
    dexp2_type= None;
  }

(* ****** ****** *)

let dexp2_let loc (d2cs: dec2 list) d2e: dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2let (d2cs, d2e); dexp2_type= None;
}

let dexp2_loopexn loc (i: int): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2loopexn i; dexp2_type= None;
}

let dexp2_lst loc d2es: dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2lst d2es; dexp2_type= None;
}

let dexp2_lam_met loc
  (r: dvar2 list ref) (s2es: sexp2 list) (d2e: dexp2)
  : dexp2 = {
    dexp2_loc= loc; dexp2_node= DE2lam_met (r, s2es, d2e); dexp2_type= None;
  }

let dexp2_lam_met_new loc (s2es: sexp2 list) (d2e: dexp2): dexp2 =
  let r: dvar2 list ref = ref [] in dexp2_lam_met loc r s2es d2e

let dexp2_mod loc (m2ids: moditemdec2 list): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2mod m2ids; dexp2_type= None;
}

let dexp2_ptrof loc (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2ptrof d2e; dexp2_type= None;
}

let dexp2_rec loc
  (is_flat: bool) (npf: int) (ld2es: labdexp2 list): dexp2 = {
    dexp2_loc= loc;
    dexp2_node= DE2rec (is_flat, (npf, ld2es));
    dexp2_type= None;
  }

let dexp2_raise loc (d2e: dexp2): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2raise (d2e);
  dexp2_type= None;
}

let dexp2_app_sta loc d2e (s2as: sexparg2 list): dexp2 =
  match s2as with
    | [] -> d2e
    | _ :: _ -> begin
	let node = match d2e.dexp2_node with
	  | DE2apps (d2e, d2as) ->
	      DE2apps (d2e, d2as @ [DEXPARG2sta s2as])
	  | _ -> DE2apps (d2e, [DEXPARG2sta s2as]) in {
	    dexp2_loc= loc;
	    dexp2_node= node;
	    dexp2_type= None;
	  } 
      end
(* end of [dexp2_app_sta] *)

let dlab2_ind (ind: dexp2 list list): dlab2 =
  { dlab2_lab= None; dlab2_ind= Some ind; }

let dlab2_lab_ind
  (l: lab option) (ind: dexp2 list list option): dlab2 =
  { dlab2_lab= l; dlab2_ind= ind; }

let dexp2_tup loc (is_flat: bool) (npf: int) (d2es: dexp2 list): dexp2 = 
  let rec aux i ld2es = function
    | [] -> dexp2_rec loc is_flat npf (List.rev ld2es)
    | d2e :: d2es ->
	let ld2es = (Lab.make_with_int i, d2e) :: ld2es in
	  aux (i+1) ld2es d2es in
    aux 0 [] d2es
(* end of [dexp2_tup] *)

(* ****** ****** *)

let dexp2_sel loc (d2e: dexp2) (d2ls: dlab2 list): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2sel (d2e, d2ls);
  dexp2_type= None
}

let dexp2_selptr loc (d2e: dexp2) (d2l: dlab2): dexp2 =
  let d2e_root = dexp2_deref d2e.dexp2_loc d2e in {
      dexp2_loc= loc;
      dexp2_node= DE2sel (d2e_root, [d2l]);
      dexp2_type= None
    }
(* end of [dexp2_selptr] *)

(* ****** ****** *)

let dexp2_seq loc d2es: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2seq d2es;
  dexp2_type= None;
}

let dexp2_sif loc
  (s2p1: sexp2) (d2e2: dexp2) (d2e3: dexp2): dexp2 = {
    dexp2_loc= loc;
    dexp2_node= DE2sif (s2p1, d2e2, d2e3);
    dexp2_type= None;
  }

let dexp2_lam_sta loc s2vs s2es d2e: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2lam_sta (s2vs, s2es, d2e);
  dexp2_type= None;
}

let dexp2_lam_sta_para loc s2vs s2es d2e: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2lam_sta_para (s2vs, s2es, d2e);
  dexp2_type= None;
}

let dexp2_string loc (s: string): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2string s;
  dexp2_type= None;
}

let dexp2_struct loc (ld2es: labdexp2 list): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2struct ld2es;
  dexp2_type= None;
}

let dexp2_sym loc (d2s: dsym2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2sym d2s; dexp2_type= None;
} 

let dexp2_template loc
  (d2e: dexp2) (s2ess: sexp2 list list): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2template (d2e, s2ess);
  dexp2_type= None;
}

let dexp2_top loc = {
  dexp2_loc= loc; dexp2_node= DE2top; dexp2_type= None;
}

let dexp2_trywith loc (d2e: dexp2) (c2ls: cla2 list): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2trywith (d2e, c2ls);
  dexp2_type= None;
}

let dexp2_unfold loc (s2c: scst2) d2e: dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2unfold (s2c, d2e);
  dexp2_type= None;
}

let dexp2_var loc (d2v: dvar2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2var d2v; dexp2_type= None;
}

let dexp2_viewat loc (d2e: dexp2): dexp2 = {
  dexp2_loc= loc; dexp2_node= DE2viewat d2e; dexp2_type= None;
}

let dexp2_while loc
  (oinv: loopinv2 option) (test: dexp2) (body: dexp2): dexp2 = {
  dexp2_loc= loc;
  dexp2_node= DE2while (oinv, test, body);
  dexp2_type= None;
} (* end of [dexp2_while] *)

let cla2 loc p2ts
  (gua: dexp2 option) (isseq: bool) (isneg: bool) (d2e: dexp2): cla2 = {
  cla2_loc= loc;
  cla2_pat= p2ts;
  cla2_gua= gua;
  cla2_isseq= isseq;
  cla2_isneg= isneg;
  cla2_body= d2e;
} (* end of [cla2] *)

(* ****** ****** *)

let dec2_stavar loc (s2v: svar2): dec2_stavar = {
  dec2_stavar_loc= loc; dec2_stavar_var= s2v;
}

let dec2_stavars loc (ds: dec2_stavar list) = {
  dec2_loc= loc; dec2_node= DC2stavars ds;
}

let dec2_sasp loc (s2c: scst2) s2e: dec2_sasp = {
  dec2_sasp_loc= loc;
  dec2_sasp_cst= s2c;
  dec2_sasp_def= s2e;
}

let dec2_sasps loc (ds: dec2_sasp list): dec2 = {
  dec2_loc= loc; dec2_node= DC2sasps ds;
}

(* ****** ****** *)

let dec2_extype loc
  (name: string) (def: sexp2): dec2 = {
  dec2_loc= loc; dec2_node= DC2extype (name, def)
} (* end of [dec2_extype] *)

let dec2_extval loc
  (name: string) (def: dexp2): dec2 = {
  dec2_loc= loc; dec2_node= DC2extval (name, def)
} (* end of [dec2_extval] *)

(* ****** ****** *)

let dec2_data loc
  (dtk: Syn.datakind) (s2cs: scst2 list): dec2 = {
  dec2_loc= loc; dec2_node= DC2data (dtk, s2cs);
} (* end of [dec2_data] *)

let dec2_dyncsts loc
  (dck: Syn.dcstkind) (ds: dcst2 list): dec2 = {
  dec2_loc= loc; dec2_node= DC2dyncsts (dck, ds);
} (* end of [dec2_dyncsts] *)

let dec2_exns loc (d2cs: dcon2 list): dec2 = {
  dec2_loc= loc;
  dec2_node= DC2exns d2cs;
}

(* ****** ****** *)

let dec2_impl loc (d2c: dcst2)
  (decarg: decarg2) (tmparg: sexp2 list list) (def: dexp2): dec2_impl = {
  dec2_impl_loc= loc;
  dec2_impl_cst= d2c;
  dec2_impl_decarg= decarg;
  dec2_impl_tmparg= tmparg;
  dec2_impl_def= def;
} (* end of [dec2_impl] *)

let dec2_impls loc (ds: dec2_impl list): dec2 = {
  dec2_loc= loc;
  dec2_node= DC2impls ds;
}

(* ****** ****** *)

let dec2_fun loc (d2v: dvar2) (d2e: dexp2): dec2_fun = {
  dec2_fun_loc= loc;
  dec2_fun_name= d2v;
  dec2_fun_def= d2e;
}

let dec2_funs loc (is_temp: bool)
  (fk: Syn.funkind) (ds: dec2_fun list): dec2 = {
  dec2_loc= loc; dec2_node= DC2funs (is_temp, fk, ds);
} (* end of [dec2_funs] *)

(* ****** ****** *)

let moditemdec2_funs loc
  (fk: Syn.funkind) (ds: dec2_fun list): moditemdec2 = {
  moditemdec2_loc= loc; moditemdec2_node= MID2funs (fk, ds);
} (* end of [moditemdec2_funs] *)

let dec2_val loc
  (p2t: pat2) (d2e: dexp2) (os2e: sexp2 option): dec2_val = {
  dec2_val_loc= loc;
  dec2_val_pat= p2t;
  dec2_val_def= d2e;
  dec2_val_ann= os2e
} (* end of [dec2_val] *)

let dec2_vals loc (vk: Syn.valkind) (ds: dec2_val list): dec2 = {
  dec2_loc= loc;
  dec2_node= DC2vals (vk, ds);
}

let moditemdec2_vals loc
  (vk: Syn.valkind) (ds: dec2_val list): moditemdec2 = {
  moditemdec2_loc= loc; moditemdec2_node= MID2vals (vk, ds);
} (* end of [moditemdec2_vals] *)

let dec2_valpars loc (ds: dec2_val list): dec2 = {
  dec2_loc= loc; dec2_node= DC2valpars ds;
}

let dec2_valrecs loc (ds: dec2_val list): dec2 = {
  dec2_loc= loc; dec2_node= DC2valrecs ds;
}

let moditemdec2_valrecs loc (ds: dec2_val list): moditemdec2 = {
  moditemdec2_loc= loc;
  moditemdec2_node= MID2valrecs ds;
}

(* ****** ****** *)

let dec2_var loc d2v s2v
  (os2e: sexp2 option) (od2e: dexp2 option): dec2_var = {
  dec2_var_loc= loc;
  dec2_var_dvar= d2v;
  dec2_var_svar= s2v;
  dec2_var_type= os2e;
  dec2_var_ini= od2e;
} (* end of [dec2_var] *)

let dec2_vars loc
  (is_stack: bool) (ds: dec2_var list): dec2 = {
  dec2_loc= loc; dec2_node= DC2vars (is_stack, ds);
} (* end of [dec2_vars] *)

(* ****** ****** *)

let dec2_local loc
  (head: dec2 list) (body: dec2 list): dec2 =
  { dec2_loc= loc; dec2_node= DC2local (head, body); }

(* ****** ****** *)

let dec2_staload loc
  (f: Fil.filename) (ods: (dec2 list) option): dec2 =
  { dec2_loc= loc; dec2_node= DC2staload (f, ods); }

let dec2_dynload loc (f: Fil.filename): dec2 =
  { dec2_loc= loc; dec2_node= DC2dynload f; }

(* ****** ****** *)

let dec2_extern loc (position: int) (code: string): dec2 =
  { dec2_loc= loc; dec2_node= DC2extern (position, code); }

(* ****** ****** *)

(* special dynamic identifier *)
type specdid = SDassgn | SDderef | SDnone

let specdid_of_did (id: Syn.did): specdid =
  if Syn.did_is_bang id then SDderef
  else if Syn.did_is_assgn id then SDassgn
  else SDnone

let specdid_of_dqual_opt_id ((odq, id): Syn.dqual_opt_id): specdid =
  match odq with None -> specdid_of_did id | Some _ -> SDnone

(* ****** ****** *)

module DvarOrd: Map.OrderedType with type t = dvar2 = struct
  type t = dvar2
  let compare d2v1 d2v2 = compare (d2v1.dvar2_stamp) (d2v2.dvar2_stamp)
end

module DvarSet: Set.S with type elt = dvar2 = Set.Make (DvarOrd)
module DvarMap: Map.S with type key = dvar2 = Map.Make (DvarOrd)

(* ****** ****** *)

module DcstOrd: Map.OrderedType with type t = dcst2 = struct
  type t = dcst2
  let compare d2c1 d2c2 = compare (d2c1.dcst2_stamp) (d2c2.dcst2_stamp)
end

module DcstMap: Map.S with type key = dcst2 = Map.Make (DcstOrd)
module DcstSet: Set.S with type elt = dcst2 = Set.Make (DcstOrd)

(* ****** ****** *)

(* end of [ats_dynexp2.ml] *)
