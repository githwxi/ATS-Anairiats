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
open Ats_syntax
open Ats_staexp1

module Eff = Ats_effect
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module Env1 = Ats_env1

type lab = Lab.label
type loc = Loc.location

(* ****** ****** *)

type pat1 = {
  mutable pat1_loc: loc;
  pat1_node: pat1_node;
}

and labpat1 = lab * pat1

and int_pat1_list = int (* arity_p *) * pat1 list

and pat1_node =
  | PT1ann of (* ascribed pattern *)
      pat1 * sexp1 
  | PT1any (* (_) -> PT1any *)
  | PT1anys (* _ -> PT1anys *)
  | PT1app_dyn of (* constructor pattern *)
      pat1 * int_pat1_list 
  | PT1app_sta of (* static application: temporary *)
      pat1 * svararg1 list
  | PT1as of (* [as] pattern *)
      did * pat1 
  | PT1char of (* character pattern *)
      char 
  | PT1exi of (* existentially quantified pattern *)
      svar1 list * pat1 
  | PT1free of (* freeing constructor pattern *)
      pat1
  | PT1int of (* integer pattern *)
      intinf 
  | PT1list of (* pattern list *)
      int_pat1_list 
  | PT1lst of (* list pattern *)
      pat1 list
  | PT1qid of (* a constructor or a variable *)
      dqual_opt_id
  | PT1rec of (* record pattern *)
      bool (* is_flat *) * bool (* is_omit *) * labpat1 list 
  | PT1ref of (* refvar pattern *)
      did
  | PT1refas of (* refvar [as] pattern *)
      did * pat1
  | PT1svararg of (* temporary *)
      svararg1 
  | PT1string of (* string pattern *)
      string 
  | PT1tup of (* tuple pattern *)
      bool (* is_flat *) * int_pat1_list (* tuple pattern *)

(* ****** ****** *)

let rec fprint_pat1 (out: out_channel) (p1t: pat1): unit =
  match p1t.pat1_node with
    | PT1ann (p1t, s1e) ->
	P.fprintf out "PT1ann(%a, %a)" fprint_pat1 p1t fprint_sexp1 s1e
    | PT1any -> P.fprintf out "PT1any()"
    | PT1anys -> P.fprintf out "PT1anys()"
    | PT1app_dyn (p1t, (npf, p1ts)) -> P.fprintf out
	"PT1app_dyn(%a; %i; %a)" fprint_pat1 p1t npf fprint_pat1_list p1ts
    | PT1as (id, p1t) ->
	P.fprintf out "PT1as(%a, %a)" fprint_did id fprint_pat1 p1t
    | PT1char c -> P.fprintf out "PT1char(%c)" c
    | PT1int i -> P.fprintf out "PT1int(%s)" (string_of_intinf i)
    | PT1list (npf, p1ts) ->
	P.fprintf out "PT1list(%i; %a)" npf fprint_pat1_list p1ts
    | PT1lst p1ts -> P.fprintf out "PT1lst(%a)" fprint_pat1_list p1ts
    | PT1qid id -> fprint_dqual_opt_id out id
    | PT1rec (is_flat, is_omit, lp1ts) -> P.fprintf out "PT1rec(...)"
    | PT1ref (id) -> P.fprintf out "PT1ref(%a)" fprint_did id
    | PT1refas (id, p1t) ->
	P.fprintf out "PT1refas(%a; %a)" fprint_did id fprint_pat1 p1t
    | PT1string s -> P.fprintf out "PT1string(%s)" s
    | PT1tup (is_flat, (npf, p1ts)) ->
	P.fprintf out "PT1tup(%i; %a)" npf fprint_pat1_list p1ts
    | _ -> error "fprint_pat1: yet to be implemented!"
(* end of [fprint_pat1] *)

and fprint_pat1_list
  (out: out_channel) (p1ts: pat1 list): unit =
  fprint_list_with_sep fprint_pat1 out p1ts ","
(* end of [fprint_pat1_list] *)

(* ****** ****** *)

(* functions for constructing patterns *)

let pat1_ann loc (p1t: pat1) (s1e: sexp1): pat1 =
  { pat1_loc= loc; pat1_node= PT1ann (p1t, s1e); }

let pat1_any loc: pat1 =
  { pat1_loc= loc; pat1_node= PT1any; }

let pat1_anys loc: pat1 =
  { pat1_loc= loc; pat1_node= PT1anys; }

let pat1_app_dyn loc
  (p1t: pat1) (npf: int) (p1ts: pat1 list): pat1 = {
  pat1_loc= loc; pat1_node= PT1app_dyn (p1t, (npf, p1ts));
} (* end of [pat1_app_dyn] *)

let pat1_app_sta loc
  (p1t: pat1) (s1as: svararg1 list): pat1 = {
  pat1_loc= loc; pat1_node= PT1app_sta (p1t, s1as);
} (* end of [pat1_app_sta] *)

let pat1_as loc (name: did) (p1t: pat1): pat1 =
  { pat1_loc= loc; pat1_node= PT1as (name, p1t); }

let pat1_char loc (c: char): pat1 =
  { pat1_loc= loc; pat1_node= PT1char c; }

let pat1_free loc (p1t: pat1): pat1 =
  { pat1_loc= loc; pat1_node= PT1free p1t; }

let pat1_exi loc (s1vs: svar1 list) (p1t: pat1): pat1 =
  { pat1_loc= loc; pat1_node= PT1exi (s1vs, p1t); }

let pat1_int loc (i: intinf): pat1 =
  { pat1_loc= loc; pat1_node= PT1int i; }

let pat1_list loc (npf: int) (p1ts: pat1 list): pat1 =
  if npf = 0 then begin
    match p1ts with (* singleton elimination *)
      | [p1t] -> begin match p1t.pat1_node with
	  | PT1anys -> pat1_any loc
	  | _ -> (p1t.pat1_loc <- loc; p1t)
	end
      | _ -> { pat1_loc= loc; pat1_node= PT1list (0, p1ts); }
  end else {
    pat1_loc= loc; pat1_node= PT1list (npf, p1ts);
  } (* end of [if] *)
(* end of [pat1_list] *)

let pat1_lst loc (p1ts: pat1 list): pat1 =
  { pat1_loc= loc; pat1_node= PT1lst p1ts; }

let pat1_qid loc (qid: dqual_opt_id): pat1 =
  { pat1_loc= loc; pat1_node= PT1qid qid; }

let pat1_rec loc
  (is_flat: bool) (is_omit: bool) (lp1ts: labpat1 list): pat1 =
  { pat1_loc= loc; pat1_node= PT1rec (is_flat, is_omit, lp1ts); }

let pat1_ref loc (id: did): pat1 =
  { pat1_loc= loc; pat1_node= PT1ref (id); }

let pat1_refas loc (id: did) (p1t: pat1): pat1 =
  { pat1_loc= loc; pat1_node= PT1refas (id, p1t); }

let pat1_string loc (s: string): pat1 =
  { pat1_loc= loc; pat1_node= PT1string s; }

let pat1_svararg loc (s1a: svararg1): pat1 =
  { pat1_loc= loc; pat1_node= PT1svararg s1a; }

let pat1_tup loc
  (is_flat: bool) (npf: int) (p1ts: pat1 list): pat1 = {
  pat1_loc= loc; pat1_node= PT1tup (is_flat, (npf, p1ts));
} (* end of [pat1_tup] *)

(* ****** ****** *)

let pat1_of_e0xp1 loc (e: e0xp1): pat1 =
  let rec aux e = match e.e0xp1_node with
    | E0XP1app (e1, es2) ->
	let p1t1 = aux e1 and p1ts2 = aux_list es2 in
	  pat1_app_dyn loc p1t1 0 (* arity_p *) p1ts2
    | E0XP1char c -> pat1_char loc c
    | E0XP1float f -> begin
        P.eprintf "%a: pat1_of_e0xp1: float pattern is not supported.\n"
          Loc.fprint loc;
        Err.abort ();
      end
    | E0XP1id id -> pat1_qid loc (None, did_of_id id)
    | E0XP1int i -> pat1_int loc i
    | E0XP1list es -> pat1_list loc 0 (* arity_p *) (aux_list es)
    | E0XP1str s -> pat1_string loc s
  and aux_list es = List.map aux es in aux e
(* end of [pat1_of_e0xp1] *)

(* ****** ****** *)

type dec1 = { dec1_loc: loc; dec1_node: dec1_node; }

and dexp1 = {
  mutable dexp1_loc: loc;
  dexp1_node: dexp1_node;
}

and labdexp1 = lab * dexp1

and int_dexp1_list = int (* arity_p *) * dexp1 list

and dlab1 = {
  dlab1_lab: lab option;
  dlab1_ind: dexp1 list list option;
}

and cla1 = {
  cla1_loc: loc;
  cla1_pat: pat1 list;
  cla1_gua: dexp1 option;
  cla1_isseq: bool;
  cla1_isneg: bool;
  cla1_body: dexp1;
}

and statype1 = squas1 * statype1_body
and statype1_body = (did * sexp1 option) list

and loopinv1 = {
  loopinv1_loc: loc;
  loopinv1_qua: squas1; (* quantifier *)
  loopinv1_met: (sexp1 list) option; (* metric *)
  loopinv1_arg: statype1_body; (* argument *)
  loopinv1_res: statype1 option; (* result *)
}

and dexp1_node =
  | DE1ann_type of (* ascribed dynamic expressions *)
      dexp1 * sexp1 
  | DE1ann_effc of (* ascribed with effects *)
      dexp1 * Eff.effcst
  | DE1ann_funclo of (* ascribed with effects *)
      dexp1 * funclo
  | DE1app_dyn of (* dynamic application *)
      dexp1 * int_dexp1_list 
  | DE1app_sta of (* static application *)
      dexp1 * sexparg1 list
  | DE1arr of (* array expression *)
      sexp1 * dexp1 list
  | DE1arrsub of (* array subscription *)
      dexp1 * (dexp1 list) list
  | DE1case of (* dynamic case-expression *)
      int * statype1 option * dexp1 * cla1 list
  | DE1char of (* dynamic character *)
      char
  | DE1crypt of (* cryption *)
      int(*kind*) * dexp1 (* 1/-1: encrypt/decrypt *)
  | DE1delay of (* lazy evaluation *)
      dexp1
  | DE1demac of (* macro decoding *)
      dexp1
  | DE1dynload of (* dynamic loading *)
      Fil.filename
  | DE1effmask of (* effect masking *)
      effect * dexp1
  | DE1empty (* empty expression *)
  | DE1enmac of (* macro encoding *)
      dexp1
  | DE1exi of (* existential sum *)
      sexparg1 * dexp1
  | DE1extval of (* external code *)
      sexp1 (* type *) * string (* code *)
  | DE1fix of (* dynamic fixed-point expression *)
      did * dexp1
  | DE1float of (* dynamic floats *)
      string 
  | DE1fold of (* folding recursive type *)
      squal_opt_id * dexp1
  | DE1foldat of (* fold at a given address *)
      sexparg1 list * dexp1
  | DE1freeat of (* free at a given address *)
      sexparg1 list * dexp1
  | DE1for of (* for-loop *)
      loopinv1 option *
      (dexp1 * dexp1 * dexp1) (* ini, test, post *) * dexp1 (* body *)
  | DE1if of (* conditional dynamic expression *)
      statype1 option * dexp1 * dexp1 * dexp1 option
  | DE1int of (* dynamic integer constant *)
      intkind * intinf
  | DE1lam_dyn of (* dynamic abstraction *)
      bool (* is_linear *) * pat1 * dexp1
  | DE1lam_met of (* metric abstraction *)
      sexp1 list * dexp1
  | DE1lam_sta_ana of (* static abstraction *)
      sarg1 list * dexp1
  | DE1lam_sta_syn of (* static abstraction *)
      squas1 * dexp1
  | DE1lam_sta_para of (* parametric static abstraction *)
      squas1 * dexp1
  | DE1let of (* dynamic let-expression *)
      dec1 list * dexp1 
  | DE1list of (* dynamic expression list: temporary *)
      int_dexp1_list 
  | DE1loopexn of (* break: 0 and continue: 1 *)
      int
  | DE1lst of (* dynamic list expression *)
      dexp1 list
  | DE1mod of (* module declaration item *)
      moditemdec1 list
  | DE1qid of (* identifier: either a constructor or variable *)
      dqual_opt_id
  | DE1ptrof of (* taking the address of *)
      dexp1
  | DE1raise of (* raised exception *)
      dexp1 
  | DE1rec of (* dynamic record expression *)
      bool (* is_flat *) * labdexp1 list
  | DE1sel of (* dynamic selection *)
      int (* is_ptr *) * dexp1 * dlab1
  | DE1seq of (* dynamic sequencing *)
      dexp1 list
  | DE1sexparg of (* for temporary use *)
      sexparg1
  | DE1sif of (* static conditional dynamic expression *)
      sexp1 * dexp1 * dexp1
  | DE1string of (* dynamic string *)
      string
  | DE1struct of (* dynamic structure *)
      labdexp1 list
  | DE1template of (* template instantiation *)
      dqual_opt_id * sexp1 list list
  | DE1top (* uninitialize value *)
  | DE1trywith of (* dynamic trywith expression *)
      dexp1 * cla1 list
  | DE1tup of (* dynamic tuple expression *)
      bool (* is_flat *) * int_dexp1_list
  | DE1unfold of (* unfolding recursive type *)
      squal_opt_id * dexp1
  | DE1viewat of (* view at a given address *)
      dexp1
  | DE1where of (* where clauses *)
      dexp1 * dec1 list
  | DE1while of (* while-loop *)
      loopinv1 option * dexp1 (* test *) * dexp1 (* body *)

and dec1_srtdef = { (* (extended) sort definition *)
  dec1_srtdef_loc: loc;
  dec1_srtdef_name: srt_id;
  dec1_srtdef_def: srtext1;
}

and datsrtcon1 = {
  datsrtcon1_loc: loc;
  datsrtcon1_name: sid;
  datsrtcon1_arg: srt1 list;
}

and dec1_datsrt = {
  dec1_datsrt_loc: loc;
  dec1_datsrt_name: srt_id;
  dec1_datsrt_arg: srtarg list;
  dec1_datsrt_con: datsrtcon1 list;
}

and dec1_stacon = { (* static constant declaration *)
  dec1_stacon_loc: loc;
  dec1_stacon_name: sid;
  dec1_stacon_arg: (sid option * srt1 * int) list option;
  dec1_stacon_def: sexp1 option;
}

and dec1_stacst = {
  dec1_stacst_loc: loc;
  dec1_stacst_name: sid;
  dec1_stacst_arg: (srt1 list) list;
  dec1_stacst_sort: srt1;
}

and dec1_stavar = {
  dec1_stavar_loc: loc;
  dec1_stavar_name: sid;
  dec1_stavar_sort: srt1;
}

and dec1_dyncst = {
  dec1_dyncst_loc: loc;
  dec1_dyncst_name: did;
  dec1_dyncst_filename: Fil.filename;
  dec1_dyncst_sexp: sexp1;
  dec1_dyncst_extdef: dcstextdef;
}

and dec1_sexpdef = {
  dec1_sexpdef_loc: loc;
  dec1_sexpdef_name: sid;
  dec1_sexpdef_arg: (sarg1 list) list;
  dec1_sexpdef_res: srt1 option;
  dec1_sexpdef_def: sexp1;
}

and dec1_sasp = {
  dec1_sasp_loc: loc;
  dec1_sasp_name: squal_opt_id;
  dec1_sasp_arg: (sarg1 list) list;
  dec1_sasp_res: srt1 option;
  dec1_sasp_def: sexp1;
}

and datcon1 = {
  datcon1_loc: loc;
  datcon1_name: did;
  datcon1_qua: squas1 list;
  datcon1_arg: int_sexp1_list;
  datcon1_ind: (sexp1 list) option; (* indexes*)
}

and dec1_dat = {
  dec1_dat_loc: loc;
  dec1_dat_name: sid;
  dec1_dat_filename: Fil.filename;
  dec1_dat_arg: (sid option * srt1 * int) list option;
  dec1_dat_con: datcon1 list;
}

and dec1_exn = {
  dec1_exn_loc: loc;
  dec1_exn_name: did;
  dec1_exn_filename: Fil.filename;
  dec1_exn_qua: squas1 list;
  dec1_exn_arg: int_sexp1_list;
}

(* ****** ****** *)

and mtitemdec1_node =
  | MTID1sta of sid * srt1
  | MTID1val of bool (* is_prop *) * did * sexp1
  | MTID1sexpdefs of dec1_sexpdef list
  | MTID1typedefs of dec1_sexpdef list
  | MTID1typedefrecs of dec1_sexpdef list

and mtitemdec1 = {
  mtitemdec1_loc: loc;
  mtitemdec1_node: mtitemdec1_node;
}

(* ****** ****** *)

and dec1_macdef = {
  dec1_macdef_loc: loc;
  dec1_macdef_name: did;
  dec1_macdef_arg: (did list) list;
  dec1_macdef_def: dexp1;
}

and dec1_var = {
  dec1_var_loc: loc;
  dec1_var_name: did;
  dec1_var_type: sexp1 option;
  dec1_var_ini: dexp1 option;
}

and dec1_val = {
  dec1_val_loc: loc;
  dec1_val_pat: pat1;
  dec1_val_def: dexp1;
}

and dec1_fun = {
  dec1_fun_loc: loc;
  dec1_fun_name: did;
  dec1_fun_def: dexp1;
  dec1_fun_ann: sexp1 option (* withtype clause *)
}

(* ****** ****** *)

and dec1_impl = {
  dec1_impl_loc: loc;
  dec1_impl_name: dqual_opt_id;
  dec1_impl_tmparg: sexp1 list list;
  dec1_impl_def: dexp1;
}

(* ****** ****** *)

and moditemdec1 = { (* type for module item declaration *)
  moditemdec1_loc: Ats_location.location;
  moditemdec1_node: moditemdec1_node;
}

and moditemdec1_node =
  | MID1sexpdefs of srt1 option * dec1_sexpdef list
  | MID1typedefrecs of dec1_sexpdef list
  | MID1vals of valkind * dec1_val list
  | MID1valrecs of dec1_val list
  | MID1funs of funkind * srt_id list * dec1_fun list

(* ****** ****** *)

and dec1_modtype = {
  dec1_modtype_loc: loc;
  dec1_modtype_name: sid;
  dec1_modtype_def: mtitemdec1 list;
}

(* ****** ****** *)

and dec1_node =
  | DC1symintr of (* overloaded symbol introduction *)
      did list
  | DC1symelim of (* overloaded symbol elimiation *)
      did list
  | DC1srtdefs of (* sort definition *)
      dec1_srtdef list
  | DC1datsrts of (* datasort *)
      dec1_datsrt list      
  | DC1stacons of (* static constructor *)
      srt1 * dec1_stacon list
  | DC1stacsts of (* static constant *)
      dec1_stacst list
  | DC1stavars of (* static existential variable *)
      dec1_stavar list
  | DC1extype of (* external type *)
      string (* extype name *) * sexp1 (* extype definition *)      
  | DC1extval of (* external type *)
      string (* extval name *) * dexp1 (* extval definition *)
  | DC1dyncsts of (* dynamic constant *)
      dcstkind * squas1 list * dec1_dyncst list 
  | DC1sexpdefs of (* static expression definition *)
      srt1 option * dec1_sexpdef list
  | DC1typedefrecs of (* recursive type definition *)
      dec1_sexpdef list
  | DC1viewtypedefrecs of (* recursive viewtype definition *)
      dec1_sexpdef list
  | DC1sasps of (* static assumption *)
      dec1_sasp list    
  | DC1data of (* data declaration *)
      datakind * srtarg list * dec1_dat list * dec1_sexpdef list
  | DC1exns of (* exception constructor *)
      dec1_exn list
  | DC1overload of (* overload declaration *)
      did * dqual_opt_id
  | DC1macdefs of (* bool: simple or not *)
      bool * dec1_macdef list
  | DC1modtypes of (* module type declaration *)
      bool (* prop or type *) * dec1_modtype list
  | DC1vars of (* variable declaration *)
      bool (* is_stack *) * dec1_var list
  | DC1vals of (* value declaration *)
      valkind * dec1_val list
  | DC1valpars of (* parallel value declaration *)
      dec1_val list
  | DC1valrecs of (* recursive value declaration *)
      dec1_val list
  | DC1funs of (* function declaration *)
      funkind * srtarg list * squas1 list * dec1_fun list
  | DC1impls of (* constant implementation *)
      sarg1 list list * dec1_impl list
  | DC1local of (* local declaration *)
      dec1 list * dec1 list
  | DC1staload of (* static load *)
      sid option (* open or closed *) * Fil.filename *
      bool (* is loaded *) * trans1_res
  | DC1dynload of (* dynamic load *)
      Fil.filename
  | DC1extern of (* external code *)
      int (* position: 0/1 : top/end *) * string (* code *)

and trans1_res = {
  trans1_res_sta: bool;
  trans1_res_defs: Env1.E0xpEnv.table;
  trans1_res_decs: dec1 list;
}

(* ****** ****** *)

let rec fprint_dexp1 (out: out_channel) (d1e0: dexp1): unit =
  match d1e0.dexp1_node with
    | DE1ann_type (d1e, s1e) -> P.fprintf out "DE1ann_type(%a; %a)"
	fprint_dexp1 d1e fprint_sexp1 s1e
    | DE1ann_effc (d1e, effc) -> P.fprintf out "DE1ann_effc(%a; %a)"
	fprint_dexp1 d1e Eff.fprint_effcst effc
    | DE1ann_funclo (d1e, fc) -> P.fprintf out "DE1ann_funclo(%a; %a)"
	fprint_dexp1 d1e fprint_funclo fc
    | DE1app_dyn (d1e, (npf, d1es)) -> begin
	P.fprintf out "DE1app_dyn(%a; %i; %a)"
	  fprint_dexp1 d1e npf fprint_dexp1_list d1es
      end
    | DE1app_sta _ -> P.fprintf out "DE1app_sta(...)"
    | DE1arr (s1e, d1es) -> P.fprintf out "DE1arr(%a; %a)"
	fprint_sexp1 s1e fprint_dexp1_list d1es
    | DE1arrsub (d1e, d1ess) -> P.fprintf out "DE1arrsub(%a; %a)"
	fprint_dexp1 d1e fprint_dexp1_list_list d1ess
    | DE1case _ -> P.fprintf out "DE1case(...)"
    | DE1char c -> P.fprintf out "DE1char(%c)" c
    | DE1crypt (knd, d1e) ->
	P.fprintf out "DE1crypt(%i; %a)" knd fprint_dexp1 d1e
    | DE1delay d1e -> P.fprintf out "DE1delay(%a)" fprint_dexp1 d1e
    | DE1demac d1e -> P.fprintf out "DE1demac(%a)" fprint_dexp1 d1e
    | DE1dynload f -> P.fprintf out "DE1dynload(%a)" Fil.fprint f
    | DE1effmask (eff, d1e) -> P.fprintf out "DE1effmask(%a; %a)"
	fprint_effect eff fprint_dexp1 d1e
    | DE1empty -> P.fprintf out "DE1empty"
    | DE1enmac d1e -> P.fprintf out "DE1enmac(%a)" fprint_dexp1 d1e
    | DE1exi _ -> P.fprintf out "DE1exi(...)"
    | DE1extval (s1e, code) ->
	P.fprintf out "DE1extval(%a; %s)" fprint_sexp1 s1e code
    | DE1fix (f, d1e) ->
	P.fprintf out "DE1fix(%a; %a)" fprint_did f fprint_dexp1 d1e
    | DE1float s -> P.fprintf out "DE1float(%s)" s
    | DE1fold(tc, d1e) -> P.fprintf out "DE1fold(%a; %a)"
	fprint_squal_opt_id tc fprint_dexp1 d1e
    | DE1foldat (s1as, d1e) -> P.fprintf out "DE1foldat(%a)" fprint_dexp1 d1e
    | DE1freeat (s1as, d1e) -> P.fprintf out "DE1freeat(%a)" fprint_dexp1 d1e
    | DE1for _ -> P.fprintf out "DE1for(...)"
    | DE1if _ -> P.fprintf out "DE1if(...)"
    | DE1int (_, i) -> P.fprintf out "DE1int(%s)" (string_of_intinf i)
    | DE1lam_dyn (is_lin, p1t, d1e) -> P.fprintf out "DE1lam_dyn(%b; %a; %a)"
	is_lin fprint_pat1 p1t fprint_dexp1 d1e
    | DE1lam_met (s1es, d1e) -> P.fprintf out "DE1lam_met(%a; %a)"
	fprint_sexp1_list s1es fprint_dexp1 d1e
    | DE1lam_sta_ana _ -> P.fprintf out "DE1lam_sta_ana(...)"
    | DE1lam_sta_syn _ -> P.fprintf out "DE1lam_sta_syn(...)"
    | DE1lam_sta_para _ -> P.fprintf out "DE1lam_sta_para(...)"
    | DE1let _ -> P.fprintf out "DE1let(...)"
    | DE1list (npf, d1es) ->
	P.fprintf out "DE1list(%i; %a)" npf fprint_dexp1_list d1es
    | DE1loopexn i -> P.fprintf out "DE1loopexn(%i)" i
    | DE1lst d1es -> P.fprintf out "DE1lst(%a)" fprint_dexp1_list d1es
    | DE1mod _ -> P.fprintf out "DE1mod(...)"
    | DE1qid qid -> fprint_dqual_opt_id out qid
    | DE1ptrof d1e -> P.fprintf out "DE1ptrof(%a)" fprint_dexp1 d1e
    | DE1raise (d1e) -> P.fprintf out "DE1raise(%a)" fprint_dexp1 d1e
    | DE1rec _ -> P.fprintf out "DE1rec(...)"
    | DE1sel (is_ptr, d1e, l) ->
	P.fprintf out "DE1sel(%i; %a; %a)" is_ptr fprint_dexp1 d1e fprint_dlab1 l
    | DE1seq d1es -> P.fprintf out "DE1seq(%a)" fprint_dexp1_list d1es
    | DE1sexparg _ -> P.fprintf out "DE1sexparg(...)"
    | DE1sif _ -> P.fprintf out "DE1sif(...)"
    | DE1struct _ -> P.fprintf out "DE1struct(...)"
    | DE1string s -> P.fprintf out "DE1string(%s)" s
    | DE1template (id, s1ess) -> P.fprintf out "DE1template(%a; %a)"
	fprint_dqual_opt_id id fprint_sexp1_list_list s1ess
    | DE1top -> P.fprintf out "DE1top"
    | DE1trywith _ -> P.fprintf out "DE1trywith(...)"
    | DE1tup (is_flat, (npf, d1es)) ->
	P.fprintf out "DE1tup(%i; %a)" npf fprint_dexp1_list d1es
    | DE1unfold(tc, d1e) -> P.fprintf out "DE1unfold(%a; %a)"
	fprint_squal_opt_id tc fprint_dexp1 d1e
    | DE1viewat d1e -> P.fprintf out "DE1viewat(%a)" fprint_dexp1 d1e
    | DE1where _ -> P.fprintf out "DE1where(...)"
    | DE1while _ -> P.fprintf out "DE1while(...)"
(* end of [fprint_dexp1] *)

and fprint_dexp1_list
  (out: out_channel) (d1es: dexp1 list): unit =
  fprint_list_with_sep fprint_dexp1 out d1es ","
(* end of [fprint_dexp1_list] *)

and fprint_dexp1_list_list
  (out: out_channel) (d1ess: dexp1 list list): unit =
  fprint_list_with_sep fprint_dexp1_list out d1ess ";"
(* end of [fprint_dexp1_list_list] *)

and fprint_dlab1 (out: out_channel) (d1l: dlab1): unit =
  match (d1l.dlab1_lab, d1l.dlab1_ind) with
    | Some l, None -> Lab.fprint out l
    | None, Some d1ess ->
	P.fprintf out ".[%a]" fprint_dexp1_list_list d1ess
    | Some l, Some d1ess ->
	P.fprintf out "%a[%a]" Lab.fprint l fprint_dexp1_list_list d1ess
    | None, None -> error_of_deadcode "ats_dynexp1: fprint_dlab1"
(* end of [fprint_dlab1] *)

(* ****** ****** *)

(* functions for constructing dynamic expressions *)

let dexp1_ann_type loc (d1e: dexp1) (s1e: sexp1): dexp1 =
  { dexp1_loc= loc; dexp1_node= DE1ann_type (d1e, s1e); }

let dexp1_ann_effc loc (d1e: dexp1) (effc: Eff.effcst): dexp1 =
  { dexp1_loc= loc; dexp1_node= DE1ann_effc (d1e, effc); }

let dexp1_ann_funclo loc (d1e: dexp1) (fc: funclo): dexp1 =
  { dexp1_loc= loc; dexp1_node= DE1ann_funclo (d1e, fc); }

let dexp1_app_dyn loc
  (d1e1: dexp1) (npf: int) (d1es2: dexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1app_dyn (d1e1, (npf, d1es2));
} (* end of [dexp1_app_dyn] *)

let dexp1_app_sta loc
  (d1e: dexp1) (sa1s: sexparg1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1app_sta (d1e, sa1s);
} (* end of [dexp1_app_sta] *)

let dexp1_arr loc
  (s1e: sexp1) (d1es: dexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1arr (s1e, d1es);
} (* end of [dexp1_arr] *)

let dexp1_arrsub loc
  (s1e_arr: dexp1) (s1ess_ind: (dexp1 list) list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1arrsub (s1e_arr, s1ess_ind);
} (* end of [dexp1_arrsub] *)

(* ****** ****** *)

let dexp1_case loc (i: int)
  (sty1: statype1 option) (d1e: dexp1) (cl1s: cla1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1case (i, sty1, d1e, cl1s);
} (* end of [dexp1_case] *)

(* ****** ****** *)

let dexp1_char loc (c: char): dexp1 =
  { dexp1_loc= loc; dexp1_node= DE1char c; }

let dexp1_crypt loc (knd: int) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1crypt (knd, d1e);
}

let dexp1_delay loc (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1delay d1e;
}

let dexp1_demac loc (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1demac d1e;
}

let dexp1_dynload loc (f: Fil.filename): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1dynload f;
}

let dexp1_effmask loc (eff: effect) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1effmask (eff, d1e);
}

let dexp1_empty loc: dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1empty;
}

let dexp1_enmac loc (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1enmac d1e;
}

let dexp1_exi loc (s1a: sexparg1) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1exi (s1a, d1e);
}

let dexp1_extval loc (s1e: sexp1) (code: string): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1extval (s1e, code);
}

let dexp1_fix loc (name: did) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1fix (name, d1e);
}

let dexp1_float loc (f: string): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1float f;
}

let dexp1_fold loc (tc: squal_opt_id) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1fold (tc, d1e);
}

let dexp1_foldat loc (s1as: sexparg1 list) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1foldat (s1as, d1e);
}

let dexp1_freeat loc (s1as: sexparg1 list) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1freeat (s1as, d1e);
}

let dexp1_for loc (oinv: loopinv1 option)
  (init: dexp1) (test: dexp1) (post: dexp1) (body: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1for (oinv, (init, test, post), body);
} (* end of [dexp1_for] *)

let dexp1_if loc (sty1: statype1 option)
  (d1e1: dexp1) (d1e2: dexp1) (od1e3: dexp1 option): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1if (sty1, d1e1, d1e2, od1e3);
} (* end of [dexp1_if] *)

let dexp1_int loc (ik: intkind) (i: intinf): dexp1 =
  { dexp1_loc= loc; dexp1_node= DE1int (ik, i); }

(* ****** ****** *)

let dexp1_lam_dyn loc
  (is_lin: bool) (p1t: pat1) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1lam_dyn (is_lin, p1t, d1e);
} (* end of [dexp1_lam_dyn] *)

let dexp1_lam_met loc
  (s1es: sexp1 list) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1lam_met (s1es, d1e);
} (* end of [dexp1_lam_met] *)

let dexp1_lam_sta_ana loc
  (arg: sarg1 list) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1lam_sta_ana (arg, d1e);
} (* end of [dexp1_lam_sta_ana] *)

let dexp1_lam_sta_syn loc
  (s1qs: squas1) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1lam_sta_syn (s1qs, d1e);
} (* end of [dexp1_lam_sta_syn] *)

let dexp1_lam_sta_para loc
  (arg: squas1) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1lam_sta_para (arg, d1e);
} (* end of [dexp1_lam_sta_para] *)

(* ****** ****** *)

let dexp1_let loc (d1cs: dec1 list) d1e: dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1let (d1cs, d1e);
}

let dexp1_list loc (npf: int) (d1es: dexp1 list): dexp1 =
  if npf = 0 then begin match d1es with
    | [d1e] -> (d1e.dexp1_loc <- loc; d1e) (* singleton elimination *)
    | _ -> { dexp1_loc= loc; dexp1_node= DE1list (npf, d1es); }
  end else { dexp1_loc= loc; dexp1_node= DE1list (npf, d1es); }
(* end of [dexp1_list] *)

let dexp1_loopexn loc (i: int): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1loopexn i;
}

let dexp1_lst loc (d1es: dexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1lst d1es;
}

let dexp1_mod loc (m1ids: moditemdec1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1mod m1ids;
}

let dexp1_ptrof loc (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1ptrof d1e;
}

let dexp1_qid loc (qid: dqual_opt_id): dexp1 =
  { dexp1_loc= loc; dexp1_node=  DE1qid qid; }

let dexp1_raise loc (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1raise (d1e);
}

let dexp1_rec loc
  (is_flat: bool) (ld1es: labdexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1rec (is_flat, ld1es);
} (* end of [dexp1_rec] *)

let dlab1_of_lab_ind
  (l: lab option) (ind: dexp1 list list option): dlab1 =
  { dlab1_lab= l; dlab1_ind= ind; }

let dexp1_sel loc
  (is_ptr: int) (d1e: dexp1) (d1l: dlab1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1sel (is_ptr, d1e, d1l);
} (* end of [dexp1_sel] *)

let dexp1_seq loc (d1es: dexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1seq d1es;
}

let dexp1_sexparg loc (sa1: sexparg1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1sexparg sa1;
}

let dexp1_sif loc
  (s1p1: sexp1) (d1e2: dexp1) (d1e3: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1sif (s1p1, d1e2, d1e3);
} (* end of [dexp1_sif] *)

let dexp1_string loc (s: string): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1string s;
}

let dexp1_struct loc (ld1es: labdexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1struct ld1es;
}

let dexp1_template loc
  (id: dqual_opt_id) (s1ess: sexp1 list list) = {
  dexp1_loc= loc; dexp1_node= DE1template (id, s1ess);
} (* end of [dexp1_template] *)

let dexp1_top loc = { dexp1_loc= loc; dexp1_node= DE1top; }

let dexp1_trywith loc (d1e: dexp1) (cl1s: cla1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1trywith (d1e, cl1s);
}

let dexp1_tup loc
  (is_flat: bool) (npf: int) (d1es: dexp1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1tup (is_flat, (npf, d1es));
} (* end of [dexp1_tup] *)

let dexp1_unfold loc (tc: squal_opt_id) (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1unfold (tc, d1e);
}

let dexp1_viewat loc (d1e: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1viewat d1e;
}

let dexp1_where loc (d1e: dexp1) (d1cs: dec1 list): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1where (d1e, d1cs);
}

let dexp1_while loc
  (oinv: loopinv1 option) (test: dexp1) (body: dexp1): dexp1 = {
  dexp1_loc= loc; dexp1_node= DE1while (oinv, test, body);
} (* end of [dexp1_while] *)


let cla1 loc
  (p1ts: pat1 list) (gua: dexp1 option)
  (isseq: bool) (isneg: bool) (d1e_body: dexp1): cla1 = {
  cla1_loc= loc;
  cla1_pat= p1ts;
  cla1_gua= gua;
  cla1_isseq= isseq;
  cla1_isneg= isneg;
  cla1_body= d1e_body;
}

let loopinv1 loc
  (qua: squas1) (met: (sexp1 list) option)
  (arg: statype1_body) (res: statype1 option): loopinv1 = {
  loopinv1_loc= loc;
  loopinv1_qua= qua;
  loopinv1_met= met;
  loopinv1_arg= arg;
  loopinv1_res= res;
}

let dexp1_of_e0xp1 loc (e: e0xp1): dexp1 =
  let rec aux e =
    match e.e0xp1_node with
      | E0XP1app (e1, es2) ->
	  let d1e1 = aux e1 and d1es2 = aux_list es2 in
	    dexp1_app_dyn loc d1e1 0 (* arity_p *) d1es2
      | E0XP1char c -> dexp1_char loc c
      | E0XP1float f -> dexp1_float loc f
      | E0XP1id id -> dexp1_qid loc (None, did_of_id id)
      | E0XP1int i -> dexp1_int loc IKint i
      | E0XP1list es ->
	  dexp1_list loc 0 (* arity_p *) (aux_list es)
      | E0XP1str s -> dexp1_string loc s
  and aux_list es = List.map aux es in aux e
(* end of [dexp1_of_e0xp1] *)

(* ****** ****** *)

let dec1_symintr loc (ids: did list): dec1 =
  { dec1_loc= loc; dec1_node= DC1symintr ids; }

let dec1_symelim loc (ids: did list): dec1 =
  { dec1_loc= loc; dec1_node= DC1symelim ids; }

(* ****** ****** *)

let dec1_srtdef_errmsg loc (id: srt_id) = begin
  P.fprintf stderr
    "%a: extended sort definition for <%a> must take no arguments."
    Loc.fprint loc fprint_srt_id id;
  Err.abort ();
end (* end of [dec1_srtdef_errmsg] *)

let dec1_srtdef loc
  (name: srt_id) (args: (srtarg list) list) (def: srtext1)
  : dec1_srtdef =
  let def = match args with
    | [] -> def
    | _ :: _ -> match def.srtext1_node with
	| STE1srt res -> {
	    srtext1_loc= loc;
	    srtext1_node= STE1srt (srt1_lams loc args res);
	  }
	| _ -> dec1_srtdef_errmsg loc name in {
      dec1_srtdef_loc= loc;
      dec1_srtdef_name= name;
      dec1_srtdef_def= def
    }
(* end of [dec1_srtdef] *)

let dec1_srtdefs loc (ds: dec1_srtdef list): dec1 = {
  dec1_loc= loc; dec1_node= DC1srtdefs ds;
}

let datsrtcon1 loc
  (name: sid) (arg: srt1 list): datsrtcon1 = {
  datsrtcon1_loc= loc;
  datsrtcon1_name= name;
  datsrtcon1_arg= arg;
} (* end of [datsrtcon1] *)

let dec1_datsrt loc (name: srt_id)
  (arg: srtarg list) (con: datsrtcon1 list): dec1_datsrt = {
  dec1_datsrt_loc= loc;
  dec1_datsrt_name= name;
  dec1_datsrt_arg= arg;
  dec1_datsrt_con= con;
} (* end of [dec1_datsrt] *)

let dec1_datsrts loc (ds: dec1_datsrt list): dec1 = {
  dec1_loc= loc; dec1_node= DC1datsrts ds;
}

let dec1_stacon loc (name: sid)
  (arg: (sid option * srt1 * int) list option) (def: sexp1 option)
  : dec1_stacon = {
    dec1_stacon_loc= loc;
    dec1_stacon_name= name;
    dec1_stacon_arg= arg;
    dec1_stacon_def= def
  }
(* end of [dec1_stacon] *)

let dec1_stacons loc
  (s1t: srt1) (ds: dec1_stacon list): dec1 = {
  dec1_loc= loc; dec1_node= DC1stacons (s1t, ds);
}

let dec1_stacst loc
  (name: sid) (arg: (srt1 list) list) (s1t: srt1): dec1_stacst = {
  dec1_stacst_loc= loc;
  dec1_stacst_name= name;
  dec1_stacst_arg= arg;
  dec1_stacst_sort= s1t;
} (* end of [dec1_stacst] *)

let dec1_stacsts loc (ds: dec1_stacst list): dec1 = {
  dec1_loc= loc; dec1_node= DC1stacsts ds;
}

let dec1_stavar loc (name: sid) (s1t: srt1): dec1_stavar = {
  dec1_stavar_loc= loc; dec1_stavar_name= name; dec1_stavar_sort= s1t;
}

let dec1_stavars loc (ds: dec1_stavar list): dec1 = {
  dec1_loc= loc; dec1_node= DC1stavars ds;
}

(* ****** ****** *)

let dec1_extype loc (name: string) (def: sexp1): dec1 = {
  dec1_loc= loc; dec1_node= DC1extype (name, def);
}

let dec1_extval loc (name: string) (def: dexp1): dec1 = {
  dec1_loc= loc; dec1_node= DC1extval (name, def);
}

(* ****** ****** *)

let dec1_dyncst loc
  (name: did) (filename: Fil.filename)
  (s1e: sexp1) (ext: dcstextdef): dec1_dyncst = {
  dec1_dyncst_loc= loc;
  dec1_dyncst_name= name;
  dec1_dyncst_filename= filename;
  dec1_dyncst_sexp= s1e;
  dec1_dyncst_extdef= ext;
} (* end of [dec1_dyncst] *)

let dec1_dyncsts loc (dck: dcstkind)
  (s1qss: squas1 list) (ds: dec1_dyncst list): dec1 = {
  dec1_loc= loc; dec1_node= DC1dyncsts (dck, s1qss, ds);
} (* end of [dec1_dyncsts] *)

let dec1_sexpdef loc (name: sid)
  (arg: (sarg1 list) list) (res: srt1 option) (def: sexp1)
  : dec1_sexpdef = {
    dec1_sexpdef_loc= loc;
    dec1_sexpdef_name= name;
    dec1_sexpdef_arg= arg;
    dec1_sexpdef_res= res;
    dec1_sexpdef_def= def;
  }
(* end of [dec1_sexpdef] *)

let dec1_sexpdefs loc
  (os1t: srt1 option) (ds: dec1_sexpdef list): dec1 = {
  dec1_loc= loc; dec1_node= DC1sexpdefs (os1t, ds)
} (* end of [dec1_sexpdefs] *)

let moditemdec1_sexpdefs loc
  (os1t: srt1 option) (ds: dec1_sexpdef list): moditemdec1 = {
  moditemdec1_loc= loc; moditemdec1_node= MID1sexpdefs (os1t, ds);
} (* end of [dec1_sexpdefs] *)

let dec1_typedefrecs loc (ds: dec1_sexpdef list): dec1 = {
  dec1_loc= loc; dec1_node= DC1typedefrecs ds
}

let dec1_viewtypedefrecs loc (ds: dec1_sexpdef list): dec1 = {
  dec1_loc= loc; dec1_node= DC1viewtypedefrecs ds
}

let moditemdec1_typedefrecs loc
  (ds: dec1_sexpdef list): moditemdec1 = {
  moditemdec1_loc= loc; moditemdec1_node= MID1typedefrecs ds;
} (* end of [moditemdec1_typedefrecs] *)

let dec1_sasp loc (name: squal_opt_id)
  (arg: (sarg1 list) list) (res: srt1 option) (def: sexp1): dec1_sasp = {
  dec1_sasp_loc= loc;
  dec1_sasp_name= name;
  dec1_sasp_arg= arg;
  dec1_sasp_res= res;
  dec1_sasp_def= def;
} (* end of [dec1_sasp] *)

let dec1_sasps loc (ds: dec1_sasp list): dec1 = {
  dec1_loc= loc; dec1_node= DC1sasps ds;
}

let datcon1 loc (name: did) (qua: squas1 list)
  (arg: int_sexp1_list) (ind: (sexp1 list) option): datcon1 = {
  datcon1_loc= loc;
  datcon1_name= name;
  datcon1_qua= qua;
  datcon1_arg= arg;
  datcon1_ind= ind;
} (* end of [datcon1] *)

let dec1_dat loc (name: sid) (f: Fil.filename)
  (arg: (sid option * srt1 * int) list option)
  (con: datcon1 list): dec1_dat = {
  dec1_dat_loc= loc;
  dec1_dat_name= name;
  dec1_dat_filename= f;
  dec1_dat_arg= arg;
  dec1_dat_con= con;
} (* end of [dec1_dat] *)

let dec1_data loc
  (dtk: datakind) (arg: srt_id list)
  (ds1: dec1_dat list) (ds2: dec1_sexpdef list): dec1 = {
  dec1_loc= loc; dec1_node= DC1data (dtk, arg, ds1, ds2);
} (* end of [dec1_data] *)

let dec1_exn loc (name: did) (f: Fil.filename)
  (qua: squas1 list) (arg: int_sexp1_list): dec1_exn = {
  dec1_exn_loc= loc;
  dec1_exn_name= name;
  dec1_exn_filename= f;
  dec1_exn_qua= qua;
  dec1_exn_arg= arg;
} (* end of [dec1_exn] *)

let dec1_exns loc (ds: dec1_exn list): dec1 = {
  dec1_loc= loc; dec1_node= DC1exns ds;
}

(* ****** ****** *)

let mtitemdec1_sta loc (name: sid) (s1t: srt1): mtitemdec1 = {
  mtitemdec1_loc= loc; mtitemdec1_node= MTID1sta (name, s1t)
}

let mtitemdec1_val
  loc (is_prop: bool) (name: did) (s1e: sexp1): mtitemdec1 = {
    mtitemdec1_loc= loc;
    mtitemdec1_node= MTID1val (is_prop, name, s1e);
  }
(* end of [mtitemdec1_val] *)

let mtitemdec1_sexpdefs loc
  (ds: dec1_sexpdef list): mtitemdec1 = {
  mtitemdec1_loc= loc; mtitemdec1_node= MTID1sexpdefs ds;
}

let mtitemdec1_typedefs loc
  (ds: dec1_sexpdef list): mtitemdec1 = {
  mtitemdec1_loc= loc; mtitemdec1_node= MTID1typedefs ds;
}

let mtitemdec1_typedefrecs loc
  (ds: dec1_sexpdef list): mtitemdec1 = {
  mtitemdec1_loc= loc; mtitemdec1_node= MTID1typedefrecs ds;
}

let dec1_modtype loc
  (name: sid) (def: mtitemdec1 list): dec1_modtype = {
  dec1_modtype_loc= loc;
  dec1_modtype_name= name;
  dec1_modtype_def= def;
} (* end of [dec1_modtype] *)

let dec1_modtypes loc
  (is_prop: bool) (ds: dec1_modtype list): dec1 = {
  dec1_loc= loc; dec1_node= DC1modtypes (is_prop, ds);
} (* end of [dec1_modtypes] *)

(* ****** ****** *)

let dec1_overload loc
  (name: did) (id: dqual_opt_id): dec1 = {
  dec1_loc= loc; dec1_node= DC1overload (name, id);
} (* end of [dec1_overload] *)

let dec1_macdef loc
  (name: did) (arg: (did list) list) (def: dexp1): dec1_macdef = {
  dec1_macdef_loc = loc;
  dec1_macdef_name = name;
  dec1_macdef_arg = arg;
  dec1_macdef_def = def;
} (* end of [dec1_macdef] *)

let dec1_macdefs loc
  (is_simple: bool) (ds: dec1_macdef list): dec1 = {
  dec1_loc = loc; dec1_node = DC1macdefs (is_simple, ds);
}

let dec1_var loc
  (name: did) (os1e: sexp1 option) (od1e: dexp1 option): dec1_var = {
  dec1_var_loc= loc;
  dec1_var_name= name;
  dec1_var_type= os1e;
  dec1_var_ini= od1e;
} (* end of [dec1_val] *)

let dec1_vars loc
  (is_stack: bool) (ds: dec1_var list): dec1 = {
  dec1_loc= loc; dec1_node= DC1vars (is_stack, ds);
}

(* ****** ****** *)

let dec1_val loc (p1t: pat1) (d1e: dexp1): dec1_val = {
  dec1_val_loc= loc;
  dec1_val_pat= p1t;
  dec1_val_def= d1e;
}

let dec1_vals loc (vk: valkind) (ds: dec1_val list): dec1 = {
  dec1_loc= loc; dec1_node= DC1vals (vk, ds);
}

let moditemdec1_vals loc
  (vk: valkind) (ds: dec1_val list): moditemdec1 = {
  moditemdec1_loc= loc; moditemdec1_node= MID1vals (vk, ds);
} (* end of [moditemdec1_vals] *)

let dec1_valpars loc (ds: dec1_val list): dec1 = {
  dec1_loc= loc; dec1_node= DC1valpars ds;
}

let dec1_valrecs loc (ds: dec1_val list): dec1 = {
  dec1_loc= loc; dec1_node= DC1valrecs ds;
}

let moditemdec1_valrecs loc (ds: dec1_val list): moditemdec1 = {
  moditemdec1_loc= loc; moditemdec1_node= MID1valrecs ds;
}

let dec1_fun loc
  (name: did) (def: dexp1) (ann: sexp1 option): dec1_fun = {
  dec1_fun_loc= loc;
  dec1_fun_name= name;
  dec1_fun_def= def;
  dec1_fun_ann= ann;
} (* end of [dec1_fun] *)

let dec1_funs loc (fk: funkind)
  (srtarg: srt_id list) (decarg: squas1 list) (ds: dec1_fun list): dec1 = {
    dec1_loc= loc; dec1_node= DC1funs (fk, srtarg, decarg, ds);
  }

let moditemdec1_funs loc (fk: funkind)
  (srtarg: srt_id list) (ds: dec1_fun list): moditemdec1 = {
    moditemdec1_loc= loc;
    moditemdec1_node= MID1funs (fk, srtarg, ds);
  }

let dec1_impl loc
  (name: dqual_opt_id) (tmparg: sexp1 list list) (def: dexp1): dec1_impl = {
  dec1_impl_loc= loc;
  dec1_impl_name= name;
  dec1_impl_tmparg= tmparg;
  dec1_impl_def= def;
} (* end of [dec1_impl] *)

let dec1_impls loc
  (decarg: sarg1 list list) (ds: dec1_impl list): dec1 = {
  dec1_loc= loc; dec1_node= DC1impls (decarg, ds);
} (* end of [dec1_impls] *)

let dec1_local loc (ds1: dec1 list) (ds2: dec1 list): dec1 = {
  dec1_loc= loc; dec1_node= DC1local (ds1, ds2);
}

let dec1_staload loc (osid: sid option)
  (filename: Fil.filename) (is_loaded: bool) (res: trans1_res): dec1 = {
    dec1_loc= loc;
    dec1_node=  DC1staload (osid, filename, is_loaded, res);
  }

let dec1_dynload loc (filename: Fil.filename): dec1 = {
  dec1_loc= loc; dec1_node= DC1dynload (filename);
}

let dec1_extern loc (position: int) (code: string) =
  { dec1_loc= loc; dec1_node= DC1extern (position, code); }

(* ****** ****** *)

(* end of [ats_dynexp1.ml] *)
