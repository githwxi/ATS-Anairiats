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

open Ats_staexp1
open Ats_misc

module P = Printf

module Cnt = Ats_counter
module Eff = Ats_effect
module Err = Ats_error
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location

(* ****** ****** *)

let error (msg: string): 'a = Err.error ("ats_staexp2: " ^ msg)

(* ****** ****** *)

type stamp = Cnt.count

module Stamps: Set.S with type elt = stamp =
  Set.Make (struct type t = stamp let compare = Cnt.compare end)

type stamps = Stamps.t

(* ****** ****** *)

let fprint_stamp = Cnt.fprint
let fprint_stamps (out: out_channel) (stamps: stamps): unit =
  if not (Stamps.is_empty stamps) then
    let fst = Stamps.choose stamps in
    let rest = Stamps.remove fst stamps in
      begin
	fprint_stamp out fst;
	Stamps.iter (function s -> P.fprintf out ",%a" Cnt.fprint s) rest
      end
  else ()
(* end of [fprint_stamps] *)

(* ****** ****** *)

type srt2_bas =
  | SRT2BASpre of (* predicative sorts *)
      Syn.srt_id
  | SRT2BASimp of (* impredicative sorts *)
      Syn.srt_id * int (*prf*) * int (*lin*)
  | SRT2BASdef of (* user-defined datasorts *)
      srt2_dat
(* end of [srt2_bas] *)

and srt2_dat = {
  srt2_dat_name: Syn.srt_id;
  srt2_dat_arg: srt2_var list;
  srt2_dat_stamp: stamp; (* uniquely determined a datasort *)
  mutable srt2_dat_con: scst2 list;
} (* end of [srt2_dat] *)

and srt2_var = {
  srt2_var_name: Syn.srtarg;
}

and srt2 =
  | SRT2bas of srt2_bas (* base sort *)
  | SRT2fun of srt2 list * srt2 (* function sort *)
  | SRT2tup of srt2 list (* tuple sort *)
  | SRT2var of srt2_var (* base sort *)
  | SRT2app of srt2 * srt2 list
  | SRT2lam of srt2_var list * srt2
  | SRT2ref of (srt2 option) ref

and srtext2 = (* extended sort *)
  | STE2srt of srt2
  | STE2sub of svar2 * srt2 * sexp2 list

and sarg2 = Syn.sid * srt2 option

and scst2 = { (* builtin or abstract *)
  scst2_name (* the name of the static constant *)
    : Syn.sid; 
  scst2_sort (* the sort of the static constant *)
    : srt2; 
  scst2_isabs (* whether the constant is abstract *)
    : (sexp2 option) option;
  scst2_iscon (* whether the constant is a constructor *)
    : bool; 
  scst2_isrec (* whether the constant is recursive *)
    : bool;
  scst2_arity: int list;
  scst2_arg (* variance: -1: contravarint; 0: invariant; 1: covarint *)
    : (Syn.sid option * srt2 * int) list option;
  mutable scst2_cons (* the associated dynamic constructors *)
    : (dcon2 list) option; 
  mutable scst2_islst (* whether it is list-like *)
    : (dcon2 (* nil *) * dcon2 (* cons *)) option;
  mutable scst2_env (* environment *)
    : sexp2 list;
  mutable scst2_def (* definition *)
    : sexp2 option;
  mutable scst2_isasp (* the status of being assumed *) 
    : bool;
  mutable scst2_stamp (* uniquely determines a static constant *)
    : stamp; 
  mutable scst2_copy (* for copy *)
    : scst2 option;
} (* end of [scst2] *)

and dcon2 = {
  dcon2_loc: loc; (* location *)
  dcon2_name: Syn.did; (* name *)
  dcon2_filename: Fil.filename; (* filename *)
  dcon2_fullname_id: string; (* filename *)
  dcon2_scst: scst2; (* datatype *)
  dcon2_vwtp: bool;
  dcon2_qua: (svar2 list * sexp2 list) list; (* quantifiers *)
  dcon2_arg: int_sexp2_list; (* views or viewtypes *)
  dcon2_arity_full: int; (* full arity *)
  dcon2_arity_real: int; (* real arity after erasure *)
  dcon2_ind: (sexp2 list) option; (* indexes *)
  dcon2_type: sexp2;
  mutable dcon2_tag: int;
  dcon2_stamp: stamp (* uniquely determines a dynamic constructor *)
} (* end of [dcon2] *)

and svar2 = {
  svar2_name: Syn.sid; (* the name of the static variable *)
  svar2_stamp: stamp; (* this uniquely determines the static variable *)
  mutable svar2_sort: srt2; (* the sort of the static variable *)
} (* end of [svar2] *)

and sVar2 = {
  sVar2_loc: loc;
  sVar2_name: Cnt.count; (* the variable name *)
  sVar2_svar: svar2 option; (* the instantiated static variable *)
  sVar2_stamp: stamp; (* this uniquely determines the variable *)
  sVar2_equal: bool; (* the variable equality status *)
  mutable sVar2_sort: srt2; (* the variable sort may be lowered *)
  mutable sVar2_link: sexp2 option; 
  (* for storing the solution to the variable *)
  mutable sVar2_lbs: sexp2 list; (* lower bounds *)
  mutable sVar2_ubs: sexp2 list; (* upper bounds *)
  mutable sVar2_svs: stamps; (* occurrences of free variables *)
  mutable sVar2_arg_sort: srt2 option; (* for SE2VarApp *)
} (* end of [sVar2] *)

and sitem2 = (* static items *)
  | SI2cst of scst2 list
  | SI2datcon of dcon2
  | SI2fil of Fil.filename
  | SI2mod of (Lab.label * svar2) list * sexp2
  | SI2var of svar2

and skexp2 =
  | SKE2app of skexp2 * skexp2 list
  | SKE2bot
  | SKE2cst of scst2
  | SKE2clo of int(*knd*) * skexp2
  | SKE2fun of skexp2 list * skexp2
  | SKE2tyarr
  | SKE2tyrec of tyrec_kind * labskexp2 list
  | SKE2var of svar2

and labskexp2 = lab * skexp2

and sexp2 = {
  (* may be lowered if it is an existential variable *)
  mutable sexp2_sort: srt2;
  mutable sexp2_node: sexp2_node;
} (* end of [sexp2] *)

and labsvar2 = lab * svar2
and labsexp2 = lab * sexp2

and int_sexp2_list = int (* arity_p *) * sexp2 list
and int_labsexp2_list = int (* arity_p *) * labsexp2 list

and slab2 = 
  | SL2lab0 of lab
  | SL2lab1 of (* selection label *)
      lab * sexp2 (* record/struct/union type *)
  | SL2ind0 of sexp2 list list
  | SL2ind1 of (* array index *)
      sexp2 list list * sexp2 (* element type *)
(* end of [slab2] *)

and sexp2_node =
  | SE2app of (* static application *)
      sexp2 * sexp2 list
  | SE2char of char
  | SE2clo of int(*knd*) * sexp2 (*-1/0/1: ref/clo/ptr*)
  | SE2cst of (* either builtin or abstract *)
      scst2
  | SE2datcon of (* unfolded datatype *)
      dcon2 (* construct *) * sexp2 list (* addresses of arguments *)
  | SE2datuni of (* unfolded datatype *)
      dcon2 (* construct *) * sexp2 list (* types of arguments *)
  | SE2eff of (* effects *)
      seff2
  | SE2eqeq of (* generic equality relation *)
      sexp2 * sexp2
  | SE2exi of (* existential quantifed expression *)
      svar2 list * sexp2 list * sexp2
  | SE2extype of (* external name *)
      string
  | SE2fun of (* function type *)
      int (* linearity *) * seff2 (* effects *) *
      int_sexp2_list (* arguments *) * sexp2 (* result *)
  | SE2int of (* static integer *)
      intinf 
  | SE2lam of (* static abstraction *)
      svar2 list * sexp2
  | SE2leq of (* dynamic subprop/subtype/subview/subviewtype relation *)
      sexp2 * sexp2 
  | SE2mfun of (* metric function *)
      stamp option * sexp2 list * sexp2
  | SE2mlt of (* strict metric ordering *)
      sexp2 list * sexp2 list
  | SE2out of (* taken out *)
      sexp2
  | SE2proj of sexp2 (* address *) * slab2 (* label *)
  | SE2refarg of (* reference argument type *)
      int(*ptr*) * sexp2 * sexp2
  | SE2sel of (* selection *)
      sexp2 * int
  | SE2top of (* top type *)
      sexp2
  | SE2tup of (* tuple *)
      sexp2 list
  | SE2tyarr of (* array (element, dimension) *)
      sexp2 * sexp2 list list
  | SE2tylst of (* type list *)
      sexp2 list
  | SE2tyrec of (* record expression *)
      tyrec_kind * int_labsexp2_list 
  | SE2uni of (* universal quantified expression *)
      svar2 list * sexp2 list * sexp2
  | SE2union of (* union type *)
      sexp2 (* index *) * labsexp2 list
  | SE2var of (* static variable *)
      svar2
  | SE2Var of (* static existential variable *)
      sVar2
  | SE2VarApp of (* existential variable application *)
      sVar2 * sexp2
  | SE2vararg of (* variable argument type *)
      sexp2
(* end of [sexp2_node] *)

and seff2 =
  | SEFF2all
  | SEFF2nil
  | SEFF2set of Eff.effset * sexp2 list

and szexp2 =
  | SZE2bot
  | SZE2byte of int
  | SZE2cst of scst2
  | SZE2out of szexp2
  | SZE2tyarr of (* array size *)
      szexp2 (* element size *) * sexp2 list list (* dimension *)
  | SZE2tyrec of tyrec_kind * labszexp2 list
  | SZE2union of labszexp2 list
  | SZE2var of svar2
  | SZE2word of int

and labszexp2 = lab * szexp2

and tyrec_kind =
  | TYRECbox (* boxed *)
  | TYRECflt of stamp (* flat *)

(* ****** ****** *)

type sexparg2 =
  | SEXPARG2one (* {..} *)
  | SEXPARG2all (* {...} *)
  | SEXPARG2seq of sexp2 list

(* ****** ****** *)

type decarg2 = (svar2 list * sexp2 list (*guards*)) list

(* ****** ****** *)

(* some functions for equality test *)

let scst2_eq (s2c1: scst2) (s2c2: scst2): bool = s2c1 == s2c2
let scst2_neq (s2c1: scst2) (s2c2: scst2): bool = s2c1 != s2c2

let svar2_eq (s2v1: svar2) (s2v2: svar2): bool = s2v1 == s2v2
let svar2_neq (s2v1: svar2) (s2v2: svar2): bool = s2v1 != s2v2
let svar2_lt (s2v1: svar2) (s2v2: svar2): bool =
  s2v1.svar2_stamp < s2v2.svar2_stamp
let svar2_lte (s2v1: svar2) (s2v2: svar2): bool =
  s2v1.svar2_stamp <= s2v2.svar2_stamp
let svar2_compare (s2v1: svar2) (s2v2: svar2): int =
  Cnt.compare s2v1.svar2_stamp s2v2.svar2_stamp

let sVar2_eq (s2V1: sVar2) (s2V2: sVar2): bool = s2V1 == s2V2
let sVar2_neq (s2V1: sVar2) (s2V2: sVar2): bool = s2V1 != s2V2

let dcon2_eq (d2c1: dcon2) (d2c2: dcon2): bool = d2c1 == d2c2
let dcon2_neq (d2c1: dcon2) (d2c2: dcon2): bool = d2c1 != d2c2
 (* the tag of a exception constructor is -1 *)
let dcon2_is_exn (d2c: dcon2): bool = d2c.dcon2_tag < 0

(* ****** ****** *)

let tyrec_kind_of_flatness (is_flat: bool) =
  if is_flat then TYRECflt (Cnt.zero) else TYRECbox

let tyrec_kind_eq (k1: tyrec_kind) (k2: tyrec_kind): bool =
  match k1, k2 with
    | TYRECbox, TYRECbox -> true
    | TYRECflt s1, TYRECflt s2 -> Cnt.eq s1 s2
    | _, _ -> false
(* end of [tyrec_kind_eq] *)

(* ****** ****** *)

(* printing functions for sorts and static expressions *)

let fprint_srt2_var
  (out: out_channel) (s2tv: srt2_var): unit =
  Syn.fprint_srt_id out s2tv.srt2_var_name

let fprint_srt2_var_list
  (out: out_channel) (s2tvs: srt2_var list): unit =
  fprint_list_with_sep fprint_srt2_var out s2tvs ","

let fprint_srt2_dat
  (out: out_channel) (s2td: srt2_dat): unit =
  Syn.fprint_srt_id out s2td.srt2_dat_name

let fprint_srt2_bas (out: out_channel) (s2tb: srt2_bas): unit =
  match s2tb with
    | SRT2BASpre x -> Syn.fprint_srt_id out x
    | SRT2BASimp (x, _, _) -> Syn.fprint_srt_id out x
    | SRT2BASdef x -> fprint_srt2_dat out x
(* end of [fprint_srt2_bas] *)

let rec fprint_srt2 (out: out_channel) (s2t: srt2): unit = match s2t with
  | SRT2bas s2tb -> fprint_srt2_bas out s2tb
  | SRT2fun (s2ts, s2t) ->
      P.fprintf out "SRT2fun(%a; %a)" fprint_srt2_list s2ts fprint_srt2 s2t
  | SRT2tup s2ts -> P.fprintf out "SRT2tup(%a)" fprint_srt2_list s2ts
  | SRT2var x -> fprint_srt2_var out x
  | SRT2lam (s2tvs, s2t) ->
      P.fprintf out "SRT2lam (%a; %a)" fprint_srt2_var_list s2tvs fprint_srt2 s2t
  | SRT2app (s2t, s2ts) ->
      P.fprintf out "SRT2app(%a; %a)" fprint_srt2 s2t fprint_srt2_list s2ts
  | SRT2ref r -> begin match !r with
      | None -> P.fprintf out "SRT2ref(...)"
      | Some s2t -> P.fprintf out "SRT2ref(%a)" fprint_srt2 s2t
    end
(* end of [fprint_srt2] *)

and fprint_srt2_list
  (out: out_channel) (s2ts: srt2 list): unit =
  fprint_list_with_sep fprint_srt2 out s2ts ","

and fprint_srt2_list_list
  (out: out_channel) (s2tss: srt2 list list): unit =
  fprint_list_with_sep fprint_srt2_list out s2tss "; "

(* ****** ****** *)

let fprint_scst2 (out: out_channel) (s2c: scst2): unit =
  Syn.fprint_sid out (s2c.scst2_name)
(*
  P.fprintf out "%a(%a)"
    Syn.fprint_sid (s2c.scst2_name) Cnt.fprint s2c.scst2_stamp
*)

(* ****** ****** *)

let fprint_scst2_list (out: out_channel) (s2cs: scst2 list): unit =
  fprint_list_with_sep fprint_scst2 out s2cs ","

let fprint_scst2_with_sort (out: out_channel) (s2c: scst2): unit =
  P.fprintf out "%a(%a)" fprint_scst2 s2c fprint_srt2 s2c.scst2_sort

let fprint_scst2_with_sort_list
  (out: out_channel) (s2cs: scst2 list): unit =
  fprint_list_with_sep fprint_scst2_with_sort out s2cs ","

let fprint_svar2 (out: out_channel) (s2v: svar2): unit =
  P.fprintf out "%a(%a)[%a]"
    Syn.fprint_sid s2v.svar2_name
    fprint_stamp s2v.svar2_stamp
    fprint_srt2 s2v.svar2_sort
(* end of [fprint_svar2] *)

let fprint_svar2_list
  (out: out_channel) (s2vs: svar2 list): unit =
  fprint_list_with_sep fprint_svar2 out s2vs ","

let fprint_svar2_list_list
  (out: out_channel) (s2vss: svar2 list list): unit =
  fprint_list_with_sep fprint_svar2_list out s2vss ";"

(* ****** ****** *)

let fprint_dcon2 (out: out_channel) (d2c: dcon2): unit =
  Syn.fprint_did out d2c.dcon2_name

let fprint_dcon2_list
  (out: out_channel) (d2cs: dcon2 list): unit =
  fprint_list_with_sep fprint_dcon2 out d2cs ","
(* end of [fprint_dcon2_list] *)

(* ****** ****** *)

let fprint_sitem2 (out: out_channel) (s2i: sitem2): unit =
  match s2i with
    | SI2cst s2cs -> P.fprintf out "SI2cst (%a)" fprint_scst2_list s2cs
    | SI2datcon d2c -> P.fprintf out "SI2datcon (%a)" fprint_dcon2 d2c
    | SI2fil f -> P.fprintf out "SI2fil (%a)" Fil.fprint f
    | SI2mod _ -> P.fprintf out "SI2mod (...)"
    | SI2var s2v -> P.fprintf out "SI2fil (%a)" fprint_svar2 s2v
(* end of [fprint_sitem2] *)

let fprint_sitem2_opt
  (out: out_channel) (os2i: sitem2 option): unit =
  match os2i with None -> () | Some s2i -> fprint_sitem2 out s2i
(* end of [fprint_sitem2_opt] *)


(* ****** ****** *)

let rec fprint_sexp2 (out: out_channel) (s2e: sexp2): unit =
  match s2e.sexp2_node with
    | SE2app (s2e, s2es) ->
	P.fprintf out "SE2app(%a; %a)" fprint_sexp2 s2e fprint_sexp2_list s2es
    | SE2char c -> P.fprintf out "SE2char(%c)" c
    | SE2clo (knd, s2e) -> P.fprintf out "SE2clo(%i; %a)" knd fprint_sexp2 s2e
    | SE2cst s2c -> P.fprintf out "SE2cst(%a)" fprint_scst2 s2c
    | SE2datcon (d2c, s2es) -> P.fprintf out "SE2datcon(%a; %a)"
	fprint_dcon2 d2c fprint_sexp2_list s2es
    | SE2datuni (d2c, s2es) -> P.fprintf out "SE2datuni(%a; %a)"
	fprint_dcon2 d2c fprint_sexp2_list s2es
    | SE2eff sf2e -> P.fprintf out "SE2eff(%a)" fprint_seff2 sf2e
    | SE2eqeq (s2e1, s2e2) -> P.fprintf out "SE2eqeq(%a, %a)"
	fprint_sexp2 s2e1 fprint_sexp2 s2e2
    | SE2exi (s2vs, s2es, s2e) -> P.fprintf out "SE2exi(%a; %a; %a)"
	fprint_svar2_list s2vs fprint_sexp2_list s2es fprint_sexp2 s2e
    | SE2extype name -> P.fprintf out "SE2extype(%s)" name
    | SE2fun (lin, sf2e, (npf, s2es), s2e) -> begin
	P.fprintf out "SE2fun(%i; %a; %i; %a; %a)"
          lin fprint_seff2 sf2e npf fprint_sexp2_list s2es fprint_sexp2 s2e
      end
    | SE2int i -> fprint_intinf out i
    | SE2lam (s2vs, s2e) -> P.fprintf out "SE2lam(%a; %a)"
	fprint_svar2_list s2vs fprint_sexp2 s2e
    | SE2leq (s2e1, s2e2) -> P.fprintf out "SE2leq(%a, %a)"
	fprint_sexp2 s2e1 fprint_sexp2 s2e2
    | SE2mfun (_, s2es, s2e) -> P.fprintf out "SE2mfun(%a; %a)"
	fprint_sexp2_list s2es fprint_sexp2 s2e
    | SE2mlt (s2es1, s2es2) -> P.fprintf out "SE2mlt(%a; %a)"
	fprint_sexp2_list s2es1 fprint_sexp2_list s2es2
    | SE2out s2e -> P.fprintf out "SE2out(%a)" fprint_sexp2 s2e
    | SE2proj (s2l, s2lab) -> P.fprintf out "SE2proj(%a%a)"
	fprint_sexp2 s2l fprint_slab2 s2lab
    | SE2refarg (refval, s2e1, s2e2) -> begin
	P.fprintf out "SE2refarg(%i; %a; %a)"
	  refval fprint_sexp2 s2e1 fprint_sexp2 s2e2
      end
    | SE2sel (s2e, i) -> P.fprintf out "SE2sel(%a, %i)" fprint_sexp2 s2e i
    | SE2top s2e -> P.fprintf out "SE2top(%a)" fprint_sexp2 s2e
    | SE2tup s2es -> P.fprintf out "SE2tup(%a)" fprint_sexp2_list s2es
    | SE2tyarr (s2e_elt, s2ess_dim) -> P.fprintf out "SE2tyarr(%a; %a)"
	fprint_sexp2 s2e_elt fprint_sexp2_list_list s2ess_dim
    | SE2tylst s2es -> P.fprintf out "SE2tylst(%a)" fprint_sexp2_list s2es
    | SE2tyrec (stamp, (npf, ls2es)) ->
	P.fprintf out "SE2tyrec(%i; %a)" npf fprint_labsexp2_list ls2es
    | SE2uni (s2vs, s2es, s2e) ->
	P.fprintf out "SE2uni(%a; %a; %a)"
	fprint_svar2_list s2vs fprint_sexp2_list s2es fprint_sexp2 s2e
    | SE2union (s2e, ls2es) -> P.fprintf out "SE2union(%a; %a)"
	fprint_sexp2 s2e fprint_labsexp2_list ls2es
    | SE2var s2v -> P.fprintf out "SE2var(%a)" fprint_svar2 s2v
    | SE2Var s2V -> P.fprintf out "SE2Var(%a)" fprint_sVar2 s2V
    | SE2VarApp (s2V, s2e) -> P.fprintf out "SE2VarApp(%a, %a)"
	fprint_sVar2 s2V fprint_sexp2 s2e
    | SE2vararg s2e -> P.fprintf out "SE2vararg(%a)" fprint_sexp2 s2e
(*
    | _ -> error_of_unavailability "ats_staexp2: fprint_sexp2"
*)
(* end of [fprint_sexp2] *)

and  fprint_sexp2_list (out: out_channel) (s2es: sexp2 list): unit =
  fprint_list_with_sep fprint_sexp2 out s2es ","

and  fprint_sexp2_list_list
  (out: out_channel) (s2ess: sexp2 list list): unit =
  fprint_list_with_sep fprint_sexp2_list out s2ess ";"
(* end of [fprint_sexp2_list_list] *)

and  fprint_sexp2_opt
  (out: out_channel) (os2e: sexp2 option): unit =
  match os2e with None -> () | Some s2e -> fprint_sexp2 out s2e
(* end of [fprint_sexp2_opt] *)

(* ****** ****** *)

and fprint_seff2 (out: out_channel) (sf2e: seff2): unit =
  match sf2e with
    | SEFF2all -> P.fprintf out "<all>"
    | SEFF2nil -> P.fprintf out "<nil>"
    | SEFF2set (effs, s2es) ->
	P.fprintf out "<%a;%a>" Eff.fprint_effset effs fprint_sexp2_list s2es
(* end of [fprint_seff2] *)

(* ****** ****** *)

and fprint_szexp2 (out: out_channel) (sz2e: szexp2): unit =
  match sz2e with
    | SZE2bot -> P.fprintf out "SZE2bot"
    | SZE2byte i -> P.fprintf out "SZE2byte(%i)" i
    | SZE2cst s2c -> P.fprintf out "SZE2cst(%a)" fprint_scst2 s2c
    | SZE2out sz2e -> P.fprintf out "SZE2out(%a)" fprint_szexp2 sz2e 
    | SZE2tyarr (sz2e, s2ess_dim) -> P.fprintf out "SZE2tyarr(%a; %a)" 
	fprint_szexp2 sz2e fprint_sexp2_list_list s2ess_dim
    | SZE2tyrec (stamp, lsz2es) ->
	P.fprintf out "SZE2tyrec(%a)" fprint_labszexp2_list lsz2es
    | SZE2union lsz2es ->
	P.fprintf out "SZE2union(%a)" fprint_labszexp2_list lsz2es
    | SZE2var s2v -> P.fprintf out "SZE2var(%a)" fprint_svar2 s2v
    | SZE2word i -> P.fprintf out "SZE2word(%i)" i
(* end of [fprint_szexp2] *)

and fprint_labszexp2
  (out: out_channel) ((l, sz2e): labszexp2): unit =
  P.fprintf out "%a= %a" Lab.fprint l fprint_szexp2 sz2e

and fprint_labszexp2_list
  (out: out_channel) (lsz2es: labszexp2 list): unit =
  fprint_list_with_sep fprint_labszexp2 out lsz2es ","

(* ****** ****** *)

and fprint_labsvar2
  (out: out_channel) ((l, s2v): labsvar2): unit =
  P.fprintf out "%a= %a" Lab.fprint l fprint_svar2 s2v

and fprint_labsvar2_list
  (out: out_channel) (ls2vs: labsvar2 list): unit =
  fprint_list_with_sep fprint_labsvar2 out ls2vs ","

(* ****** ****** *)

and fprint_labsexp2
  (out: out_channel) ((l, s2e2): labsexp2): unit =
  P.fprintf out "%a= %a" Lab.fprint l fprint_sexp2 s2e2

and  fprint_labsexp2_list
  (out: out_channel) (ls2es: labsexp2 list): unit =
  fprint_list_with_sep fprint_labsexp2 out ls2es ","

(* ****** ****** *)

and fprint_slab2 (out: out_channel) (s2l: slab2): unit =
  match s2l with
    | SL2lab0 l -> P.fprintf out ".%a" Lab.fprint l
    | SL2lab1 (l, s2e) ->
	P.fprintf out ".%a(%a)" Lab.fprint l fprint_sexp2 s2e
    | SL2ind0 ind -> P.fprintf out "[%a]" fprint_sexp2_list_list ind
    | SL2ind1 (ind, s2e) ->
	P.fprintf out "[%a](%a)" fprint_sexp2_list_list ind fprint_sexp2 s2e
(* end of [fprint_slab2] *)

and fprint_slab2_list
  (out: out_channel) (s2ls: slab2 list): unit =
  fprint_list_with_sep fprint_slab2 out s2ls ""

(* ****** ****** *)

and fprint_srtext2 (out: out_channel) (s2te: srtext2): unit =
  match s2te with
    | STE2srt s2t -> fprint_srt2 out s2t
    | STE2sub (s2v, s2t, s2es) ->
	P.fprintf out "{%a: %a | %a}"
	fprint_svar2 s2v fprint_srt2 s2t fprint_sexp2_list s2es
(* end of [fprint_srtext2] *)

(* ****** ****** *)

and fprint_sVar2 (out: out_channel) (s2V: sVar2): unit =
  match s2V.sVar2_link with
(*
    | None -> P.fprintf out "%a:X[%a;%a](lbs=%a;ubs=%a)"
	Loc.fprint s2V.sVar2_loc
	Cnt.fprint s2V.sVar2_name
	fprint_stamps s2V.sVar2_svs
	fprint_sexp2_list s2V.sVar2_lbs
	fprint_sexp2_list s2V.sVar2_ubs
*)
    | None -> P.fprintf out "X(%a)[%a;%a](lbs=%a;ubs=%a)"
	fprint_srt2 s2V.sVar2_sort
	Cnt.fprint s2V.sVar2_name
	fprint_stamps s2V.sVar2_svs
	fprint_sexp2_list s2V.sVar2_lbs
	fprint_sexp2_list s2V.sVar2_ubs
    | Some s2e -> P.fprintf out "X[%a](%a)"
	Cnt.fprint s2V.sVar2_name fprint_sexp2 s2e
(* end of [fprint_sVar2] *)

(* ****** ****** *)

let rec fprint_skexp2 (out: out_channel) (sk: skexp2): unit =
  match sk with
    | SKE2app(sk, sks) ->
	P.fprintf out "app(%a;%a)" fprint_skexp2 sk fprint_skexp2_list sks
    | SKE2bot -> P.fprintf out "_"
    | SKE2cst s2c -> fprint_scst2 out s2c
    | SKE2clo (knd, sk) -> P.fprintf out "clo(%i; %a)" knd fprint_skexp2 sk
    | SKE2fun (sks, sk) ->
	P.fprintf out "(%a)->%a" fprint_skexp2_list sks fprint_skexp2 sk
    | SKE2tyarr -> P.fprintf out "tyarr"
    | SKE2tyrec (stamp, lsks) ->
	P.fprintf out "{%a}" fprint_labskexp2_list lsks
    | SKE2var s2v -> fprint_svar2 out s2v
(* end of [fprint_skexp2] *)

and fprint_labskexp2
  (out: out_channel) ((l, sk): labskexp2): unit =
  P.fprintf out "%a= %a" Lab.fprint l fprint_skexp2 sk
(* end of [fprint_labskexp2] *)

and fprint_skexp2_list
  (out: out_channel) (sks: skexp2 list): unit =
  fprint_list_with_sep fprint_skexp2 out sks ","
(* end of [fprint_skexp2_list] *)

and fprint_labskexp2_list
  (out: out_channel) (lsks: labskexp2 list): unit =
  fprint_list_with_sep fprint_labskexp2 out lsks ","
(* end of [fprint_skexp2_list] *)

let fprint_skexp2_list_list
  (out: out_channel) (skss: skexp2 list list): unit =
  fprint_list_with_sep fprint_skexp2_list out skss ";"
(* end of [fprint_skexp2_list_list] *)

(* ****** ****** *)

let fprint_sexparg2 (out: out_channel) (s2a: sexparg2): unit =
  match s2a with
    | SEXPARG2one -> P.fprintf out ".."
    | SEXPARG2all -> P.fprintf out "..."
    | SEXPARG2seq s2es -> fprint_sexp2_list out s2es
(* end of [fprint_sexparg2] *)

let fprint_sexparg2_list (out: out_channel) (s2as: sexparg2 list): unit =
  fprint_list_with_sep fprint_sexparg2 out s2as ";"
(* end of [fprint_sexparg2_list] *)

(* ****** ****** *)

let fprint_decarg2 (out: out_channel) (decarg: decarg2): unit =
  let f (s2vs, s2ps) = P.fprintf out
    "<%a;%a>" fprint_svar2_list s2vs fprint_sexp2_list s2ps in
    List.iter f decarg
(* end of [fprint_decarg2] *)

(* ****** ****** *)

(* functions for constructing sorts *)

let stb2_addr: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symADDR)
let stb2_bool: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symBOOL)
let stb2_char: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symCHAR)
let stb2_eff: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symEFF)
let stb2_int: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symINT)
let stb2_rat: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symRAT)
let stb2_reg: srt2_bas = SRT2BASpre (Syn.srt_id_of_sym Sym.symREG)

(* ****** ****** *)

let theProofLevel = 2
let stb2_prop: srt2_bas =
  SRT2BASimp (Syn.srt_id_of_sym Sym.symPROP, theProofLevel, 0)
let stb2_type: srt2_bas =
  SRT2BASimp (Syn.srt_id_of_sym Sym.symTYPE, 0, 0)
let stb2_t0ype: srt2_bas =
  SRT2BASimp (Syn.srt_id_of_sym Sym.symT0YPE, 1, 0)
let stb2_view: srt2_bas =
  SRT2BASimp (Syn.srt_id_of_sym Sym.symVIEW, theProofLevel, 1)
let stb2_viewtype: srt2_bas =
  SRT2BASimp (Syn.srt_id_of_sym Sym.symVIEWTYPE, 0, 1)
let stb2_viewt0ype: srt2_bas =
  SRT2BASimp (Syn.srt_id_of_sym Sym.symVIEWT0YPE, 1, 1)

let stb2_types: srt2_bas = (* though it is impredicative *)
  SRT2BASimp (Syn.srt_id_of_sym Sym.symTYPES, 1, 0)

(* ****** ****** *)

let srt2_any (): srt2 = SRT2ref (ref None)
let srt2_addr: srt2 = SRT2bas stb2_addr
let srt2_bool: srt2 = SRT2bas stb2_bool
let srt2_char: srt2 = SRT2bas stb2_char
let srt2_eff: srt2 = SRT2bas stb2_eff
let srt2_int: srt2 = SRT2bas stb2_int
let srt2_rat: srt2 = SRT2bas stb2_rat
let srt2_reg: srt2 = SRT2bas stb2_reg

let srt2_prop: srt2 = SRT2bas stb2_prop
let srt2_type: srt2 = SRT2bas stb2_type
let srt2_t0ype: srt2 = SRT2bas stb2_t0ype
let srt2_view: srt2 = SRT2bas stb2_view
let srt2_viewtype: srt2 = SRT2bas stb2_viewtype
let srt2_viewt0ype: srt2 = SRT2bas stb2_viewt0ype

let srt2_types: srt2 = SRT2bas stb2_types

let srt2_fun (s2ts: srt2 list) (s2t: srt2): srt2 = SRT2fun (s2ts, s2t)
let srt2_tup (s2ts: srt2 list): srt2 = SRT2tup s2ts
let srt2_unit = srt2_tup []

let srt2_app (s2t: srt2) (s2ts: srt2 list): srt2 = SRT2app (s2t, s2ts)
let srt2_lam (arg: srt2_var list) (res: srt2): srt2 = SRT2lam (arg, res)

let un_srt2_fun (s2t: srt2): (srt2 list * srt2) option = match s2t with
  | SRT2fun (s2ts, s2t) -> Some (s2ts, s2t)
  | _ -> None
(* end of [un_srt2_fun] *)

let un_srt2_tup (s2t: srt2): (srt2 list) option = match s2t with
  | SRT2tup s2ts -> Some (s2ts)
  | _ -> None
(* end of [un_srt2_tup] *)

(* ****** ****** *)

let seff2_all = SEFF2all
let seff2_nil = SEFF2nil

(* ****** ****** *)

let szexp2_byte (i: int): szexp2 = SZE2byte i
let szexp2_word (i: int): szexp2 = SZE2word i
let szexp2_zero = SZE2word 0

(* ****** ****** *)

(* functions for constructing static expressions *)

let sexp2_app_with_sort
  (s2t: srt2) (s2e_fun: sexp2) (s2es_arg: sexp2 list): sexp2 = {
  sexp2_sort= s2t;
  sexp2_node= SE2app (s2e_fun, s2es_arg);
} (* end of [sexp2_app_with_sort] *)

let sexp2_app_wind (s2e: sexp2) (s2ess: sexp2 list list): sexp2 =
  let rec aux s2t s2e s2ess = match s2ess with
    | s2es :: s2ess -> begin match un_srt2_fun s2t with
	| Some (_, s2t) ->
	    let s2e = sexp2_app_with_sort s2t s2e s2es in
	      aux s2t s2e s2ess
	| None -> error_of_deadcode "ats_staexp2: sexp2_app_wind"
      end
    | [] -> s2e in
    aux s2e.sexp2_sort s2e s2ess
(* end of [sexp2_app_wind] *)

(* ****** ****** *)

let sexp2_char (c: char): sexp2 =
  { sexp2_sort= srt2_char; sexp2_node= SE2char c; }

let sexp2_clo_with_sort
  (s2t: srt2) (knd: int) (s2e: sexp2): sexp2 = {
    sexp2_sort= s2t; sexp2_node= SE2clo (knd, s2e);
} (* end of [sexp2_clo_with_sort] *)

let sexp2_cst (s2c: scst2): sexp2 =
  { sexp2_sort= s2c.scst2_sort; sexp2_node= SE2cst s2c; }

let sexp2_cstapp (s2c: scst2) (s2es: sexp2 list): sexp2 =
  let s2t = s2c.scst2_sort in match un_srt2_fun s2t with
    | Some (_, s2t_res) ->
	sexp2_app_with_sort s2t_res (sexp2_cst s2c) s2es
    | None -> begin
	P.fprintf stderr
	  "sexp2_cstapp: not a functional sort: %a" fprint_srt2 s2t;
	Err.abort ();
      end
(* end of [sexp2_cstapp] *)

let sexp2_datcon (d2c: dcon2) (s2es_arg: sexp2 list) =
  let s2t =
    if d2c.dcon2_arity_real > 0 then srt2_viewtype else srt2_type in {
      sexp2_sort= s2t;
      sexp2_node= SE2datcon (d2c, s2es_arg);
    }
(* end of [sexp2_datcon] *)

let sexp2_datuni (d2c: dcon2) (s2es_arg: sexp2 list) = {
  sexp2_sort= srt2_viewtype;
  sexp2_node= SE2datuni (d2c, s2es_arg);
}

let sexp2_eff (sf2e: seff2): sexp2 = {
  sexp2_sort= srt2_eff; sexp2_node= SE2eff sf2e;
}

let sexp2_eqeq (s2e1: sexp2) (s2e2: sexp2): sexp2 =
  { sexp2_sort= srt2_bool; sexp2_node= SE2eqeq (s2e1, s2e2); }

let sexp2_exi
  (s2vs: svar2 list) (s2ps: sexp2 list) (s2e: sexp2): sexp2 =
  match s2vs, s2ps with
    | [], [] -> s2e
    | _, _ -> {
	sexp2_sort= s2e.sexp2_sort; sexp2_node= SE2exi (s2vs, s2ps, s2e);
      }
(* end of [sexp2_exi] *)

(* ****** ****** *)

let empty_type_name = ""

let sexp2_empty_type: sexp2 = (* used as a place holder *)
  { sexp2_sort= srt2_viewtype; sexp2_node= SE2extype empty_type_name }

let sexp2_extype (s2t: srt2) (name: string): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2extype name; }

(* ****** ****** *)

let sexp2_fun_with_sort (s2t: srt2)
  (lin: int) (sf2e: seff2) (ns2es: int_sexp2_list) (s2e: sexp2): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2fun (lin, sf2e, ns2es, s2e); }
(* end of [sexp2_fun_with_sort] *)

let sexp2_fun_con (ns2es: int_sexp2_list) (s2e: sexp2): sexp2 = {
  sexp2_sort= srt2_type;
  sexp2_node= SE2fun (0(*lin*), seff2_nil, ns2es, s2e);
} (* end of [sexp2_fun_con] *)

(* ****** ****** *)

let sexp2_int (i: int): sexp2 =
  { sexp2_sort= srt2_int; sexp2_node= SE2int (intinf_of_int i); }

let sexp2_intinf (i: intinf): sexp2 =
  { sexp2_sort= srt2_int; sexp2_node= SE2int i; }

let sexp2_intinf_zero = sexp2_intinf intinf_zero
let sexp2_is_intinf_zero (s2e: sexp2): bool =
  match s2e.sexp2_node with SE2int i -> intinf_is_zero i | _ -> false

let sexp2_lam_with_sort (s2t: srt2) s2vs s2e: sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2lam (s2vs, s2e); }

let sexp2_leq (s2e1: sexp2) (s2e2: sexp2): sexp2 =
  { sexp2_sort= srt2_bool; sexp2_node= SE2leq (s2e1, s2e2); }

let sexp2_mfun
  (d2v_stamp_opt: stamp option)
  (s2es_met: sexp2 list) (s2e_fun: sexp2): sexp2 = {
  sexp2_sort= s2e_fun.sexp2_sort;
  sexp2_node= SE2mfun (d2v_stamp_opt, s2es_met, s2e_fun);
} (* end of [sexp2_mfun] *)

let sexp2_mlt (s2es1: sexp2 list) (s2es2: sexp2 list): sexp2 =
  { sexp2_sort= srt2_bool; sexp2_node= SE2mlt (s2es1, s2es2); }

let sexp2_vararg (s2e: sexp2): sexp2 =
  { sexp2_sort= srt2_t0ype; sexp2_node= SE2vararg s2e; }

(* ****** ****** *)

let slab2_lab0 (l: lab): slab2 = SL2lab0 l
let slab2_lab1 (l: lab) (s2e: sexp2): slab2 = SL2lab1 (l, s2e)

let slab2_ind0 (s2ess_ind: sexp2 list list): slab2 =
  SL2ind0 s2ess_ind
let slab2_ind1 (s2ess_ind: sexp2 list list) (s2e_elt: sexp2): slab2 =
  SL2ind1 (s2ess_ind, s2e_elt)

let rec slab2_list_is_subscript (s2ls: slab2 list): bool =
  match s2ls with
    | SL2lab0 _ :: s2ls -> slab2_list_is_subscript s2ls
    | SL2lab1 _ :: s2ls -> slab2_list_is_subscript s2ls
    | SL2ind0 _ :: s2ls -> true
    | SL2ind1 _ :: s2ls -> true
    | [] -> false
(* end of [slab2_list_is_subscript] *)

(* ****** ****** *)

let sexp2_out (s2e: sexp2): sexp2 =
  { sexp2_sort= srt2_t0ype; sexp2_node= SE2out s2e; }

(* ****** ****** *)

let sexp2_proj (s2l: sexp2) (s2lab: slab2): sexp2 =
  { sexp2_sort= srt2_addr; sexp2_node= SE2proj (s2l, s2lab); }

(* ****** ****** *)

let sexp2_refarg (refval: int) (s2e1: sexp2) (s2e2: sexp2): sexp2 = {
  sexp2_sort= s2e1.sexp2_sort; sexp2_node= SE2refarg (refval, s2e1, s2e2);
} (* end of [sexp2_refarg] *)

let un_sexp2_refarg_arg (s2e: sexp2): sexp2 =
  match s2e.sexp2_node with
    | SE2refarg (_(*refval*), s2e_arg, _(*s2e_res*)) -> s2e_arg
    | _ -> s2e
(* end of [un_sexp2_refarg_arg] *)

(* ****** ****** *)

let sexp2_sel_with_sort
  (s2t: srt2) (s2e: sexp2) (i: int): sexp2 = {
  sexp2_sort= s2t; sexp2_node= SE2sel (s2e, i);
} (* end of [sexp2_sel_with_sort] *)

(* ****** ****** *)

let sexp2_struct_with_sort
  (s2t: srt2) (k: tyrec_kind) (ls2es: labsexp2 list): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2tyrec (k, (0, ls2es)); }
(* end of [sexp2_struct_with_sort] *)

let sexp2_struct_new_with_sort
  (s2t: srt2) (ls2es: labsexp2 list): sexp2 =
  let k = TYRECflt (Cnt.struct2_new_stamp ()) in
    sexp2_struct_with_sort s2t k ls2es
(* end of [sexp2_struct_new_with_sort] *)

(* ****** ****** *)

let sexp2_top_with_sort (s2t: srt2) (s2e: sexp2): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2top s2e; }

(* ****** ****** *)

let sexp2_tup (s2es: sexp2 list): sexp2 =
  let s2ts = List.map (function s2e -> s2e.sexp2_sort) s2es in
    { sexp2_sort= SRT2tup s2ts; sexp2_node= SE2tup s2es; }
(* end of [sexp2_tup] *)

(* ****** ****** *)

let sexp2_tyarr
  (s2e_elt: sexp2) (s2ess_dim: sexp2 list list): sexp2 = {
  sexp2_sort= s2e_elt.sexp2_sort;
  sexp2_node= SE2tyarr (s2e_elt, s2ess_dim);
} (* end of [sexp2_tyarr] *)

(* ****** ****** *)

(* sexp2_tylst: [s2es] consists of types, props, views and viewtypes *)
let sexp2_tylst (s2es: sexp2 list): sexp2 = {
  sexp2_sort= srt2_types; sexp2_node= SE2tylst s2es;
} (* end of [sexp2_list] *)

(* ****** ****** *)

let sexp2_tyrec_with_sort (s2t: srt2)
  (k: tyrec_kind) (npf: int) (ls2es: labsexp2 list): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2tyrec (k, (npf, ls2es)); }
(* end of [sexp2_tyrec_with_sort] *)

let sexp2_tytup_with_sort
  (s2t: srt2) (is_flat: bool) (npf: int) (s2es: sexp2 list): sexp2 =
  let rec aux i = function
    | s2e :: s2es -> (Lab.make_with_int i, s2e) :: aux (i+1) s2es
    | [] -> [] in
  let ls2es = aux 0 s2es in
  let k = tyrec_kind_of_flatness is_flat in
    sexp2_tyrec_with_sort s2t k npf ls2es
(* end of [sexp2_tytup_with_sort] *)

let sexp2_uni (s2vs: svar2 list) (s2ps: sexp2 list) (s2e: sexp2): sexp2 =
  match s2vs, s2ps with
    | [], [] -> s2e
    | _, _ -> {
	sexp2_sort= s2e.sexp2_sort; sexp2_node= SE2uni (s2vs, s2ps, s2e);
      }
(* end of [sexp2_uni] *)

let sexp2_union_with_sort
  (s2t: srt2) (s2i: sexp2) (ls2es: labsexp2 list): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2union (s2i, ls2es); }

let sexp2_unit: sexp2 =
  { sexp2_sort= SRT2tup []; sexp2_node= SE2tup []; }

let sexp2_var (s2v: svar2): sexp2 =
  { sexp2_sort= s2v.svar2_sort; sexp2_node= SE2var s2v; }

(* ****** ****** *)

let sexp2_Var (s2V: sVar2): sexp2 =
  { sexp2_sort= s2V.sVar2_sort; sexp2_node= SE2Var s2V; }

let sexp2_is_Var (s2e: sexp2): bool =
  match s2e.sexp2_node with SE2Var _ -> true | _ -> false

(* ****** ****** *)

let sexp2_VarApp_with_sort
  (s2t: srt2) (s2V: sVar2) (s2e: sexp2): sexp2 =
  { sexp2_sort= s2t; sexp2_node= SE2VarApp (s2V, s2e); }
(* end of [sexp2_VarApp_with_sort] *)

(* functions for constructing datasorts *)

let srt2_dat_make (name: Syn.srt_id) (arg: srt2_var list): srt2_dat = {
  srt2_dat_name= name;
  srt2_dat_arg= arg;
  srt2_dat_stamp= Cnt.srt2_dat_new_stamp ();
  srt2_dat_con= []; (* to be filled in later *)
} (* end of [srt2_dat_make] *)

let srt2_var_make (name: Syn.srtarg): srt2_var = { srt2_var_name= name }

(* function for constructing static constructors *)

let rec srt2_arity (s2t: srt2): int list = match s2t with
  | SRT2fun (s2ts, s2t) -> List.length s2ts :: srt2_arity s2t
  | _ -> []
(* end of [srt2_arity] *)

let scst2_make (name: Syn.sid) (s2t: srt2)
  (isabs: (sexp2 option) option) (iscon: bool) (isrec: bool)
  (arg: (Syn.sid option * srt2 * int) list option)
  (islst: (dcon2 * dcon2) option) (env: sexp2 list)
  (def: sexp2 option) (isasp: bool): scst2 =
  let stamp = Cnt.scst2_new_stamp () in {
      scst2_name= name;
      scst2_sort= s2t;
      scst2_isabs= isabs;
      scst2_iscon= iscon;
      scst2_isrec= isrec;
      scst2_arity= srt2_arity s2t;
      scst2_arg= arg;
      scst2_cons= None;
      scst2_islst= islst;
      scst2_env= env;
      scst2_def= def;
      scst2_isasp= isasp;
      scst2_stamp= stamp;
      scst2_copy= None;
    }
(* end of [scst2_make] *)

let dat_scst2_make (name: Syn.sid)
  (os2ts: (srt2 list) option) (s2t: srt2)
  (arg: (Syn.sid option * srt2 * int) list option): scst2 =
  let s2t = match os2ts with
    | None -> s2t | Some s2ts -> srt2_fun s2ts s2t in
    scst2_make name 
      s2t (* sort *)
      None (* isabs *)
      true (* iscon *)
      false (* isrec *)
      arg (* arguments *)
      None (* islst *)
      [] (* env: update it later *)
      None (* def: no definition *)
      false (* isasp: false *)
(* end of [dat_scst2_make] *)

let scst2_is_abstract (s2c: scst2): bool =
  match s2c.scst2_isabs with Some _ -> true | None -> false
(* end of [scst2_is_abstract] *)

let scst2_is_constructor (s2c: scst2): bool = s2c.scst2_iscon

let scst2_is_data (s2c: scst2): bool =
  match s2c.scst2_isabs with Some _ -> false | None -> s2c.scst2_iscon

let scst2_is_recursive (s2c: scst2): bool = s2c.scst2_isrec

(* function for constructing static variables *)

(* ****** ****** *)

let the_svar2_map: (svar2 Cnt.CountMap.t) ref = ref (Cnt.CountMap.empty)
let svar2_stamp_add (s2v: svar2): unit =
  the_svar2_map := Cnt.CountMap.add (s2v.svar2_stamp) s2v !the_svar2_map
let svar2_stamp_find (i: stamp): svar2 option =
  try Some (Cnt.CountMap.find i !the_svar2_map) with Not_found -> None

(* ****** ****** *)

let svar2_new_with_id (name: Syn.sid) (s2t: srt2): svar2 =
  let s2v = {
    svar2_name= name;
    svar2_sort= s2t;
    svar2_stamp= Cnt.svar2_new_stamp ();
  } in (svar2_stamp_add s2v; s2v)
(* end of [svar2_new_with_id] *)

let svar2_new (s2t: srt2): svar2 =
  let id = Syn.sid_of_sym (Cnt.svar2_new_name ()) in
    svar2_new_with_id id s2t
(* end of [svar2_new] *)

let svar2_copy (s2v: svar2): svar2 =
  let name =
    Cnt.svar2_new_name_with_prefix (Syn.string_of_sid s2v.svar2_name) in
  let id = Syn.sid_of_sym name in
    svar2_new_with_id id (s2v.svar2_sort)
(* end of [svar2_copy] *)

let svar2_copy_list s2vs: svar2 list = List.map svar2_copy s2vs

(* ****** ****** *)

let sVar2_new loc (stamps: stamps) (s2t: srt2): sVar2 = {
  sVar2_loc= loc;
  sVar2_name= Cnt.sVar2_new_name ();
  sVar2_svar= None;
  sVar2_sort= s2t;
  sVar2_stamp= Cnt.sVar2_new_stamp ();
  sVar2_equal= false;
  sVar2_link= None;
  sVar2_svs= stamps;
  sVar2_lbs= [];
  sVar2_ubs= [];
  sVar2_arg_sort= None;
} (* end of [svar2_new] *)

let sVar2_new_of_svar loc (stamps: stamps) (s2v: svar2): sVar2 = {
  sVar2_loc= loc;
  sVar2_name= Cnt.sVar2_new_name ();
  sVar2_svar= Some s2v;
  sVar2_sort= s2v.svar2_sort;
  sVar2_stamp= Cnt.sVar2_new_stamp ();
  sVar2_equal= false;
  sVar2_link= None;
  sVar2_svs= stamps;
  sVar2_lbs= [];
  sVar2_ubs= [];
  sVar2_arg_sort= None;
} (* end of [sVar2_new_of_svar] *)

let sVar2_equal_new loc (stamps: stamps) (s2t: srt2): sVar2 = {
  sVar2_loc= loc;
  sVar2_name= Cnt.sVar2_new_name ();
  sVar2_svar= None;
  sVar2_sort= s2t;
  sVar2_stamp= Cnt.sVar2_new_stamp ();
  sVar2_equal= true;
  sVar2_link= None;
  sVar2_svs= stamps;
  sVar2_lbs= [];
  sVar2_ubs= [];
  sVar2_arg_sort= None;
} (* end of [sVar2_equal_new] *)

(* ****** ****** *)

(* special static identifier *)
type specsid = SSarrow | SSnone

let specsid_of_sid (id: Syn.sid): specsid =
  if Syn.sid_is_arrow id then SSarrow else SSnone
(* end of [specsid_of_sid] *)

let specsid_of_squal_opt_id
  ((osq, id): Syn.squal_opt_id): specsid =
  match osq with
    | None -> specsid_of_sid id | Some _ -> SSnone 
(* end of [specsid_of_squal_opt_id] *)

(* ****** ****** *)

module SvarOrd: Map.OrderedType with type t = svar2 = struct
  type t = svar2
  let compare s2v1 s2v2 = compare (s2v1.svar2_stamp) (s2v2.svar2_stamp)
end

module SvarMap: Map.S with type key = SvarOrd.t = Map.Make (SvarOrd)
module SvarSet: Set.S with type elt = svar2 = Set.Make (SvarOrd)

(* ****** ****** *)

module ScstOrd: Map.OrderedType with type t = scst2 = struct
  type t = scst2
  let compare s2c1 s2c2 = compare (s2c1.scst2_stamp) (s2c2.scst2_stamp)
end

module ScstMap: Map.S with type key = ScstOrd.t = Map.Make (ScstOrd)
module ScstSet: Set.S with type elt = scst2 = Set.Make (ScstOrd)

(* ****** ****** *)

module DconOrd: Map.OrderedType with type t = dcon2 = struct
  type t = dcon2
  let compare d2c1 d2c2 = compare (d2c1.dcon2_stamp) (d2c2.dcon2_stamp)
end

module DconSet: Set.S with type elt = dcon2 = Set.Make (DconOrd)
module DconMap: Map.S with type key = dcon2 = Map.Make (DconOrd)

(* ****** ****** *)

(* end of [ats_staexp2.ml] *)
