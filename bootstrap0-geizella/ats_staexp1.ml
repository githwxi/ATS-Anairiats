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

open Ats_syntax
open Ats_misc

module P = Printf

module Eff = Ats_effect
module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol

type loc = Loc.location

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_trans1: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

type e0xp1 = { e0xp1_loc: loc; e0xp1_node: e0xp1_node; }

and e0xp1_node =
  | E0XP1app of e0xp1 * e0xp1 list
  | E0XP1char of char
  | E0XP1float of string
  | E0XP1id of id
  | E0XP1int of intinf
  | E0XP1list of e0xp1 list
  | E0XP1str of string  

let rec fprint_e0xp1 (out: out_channel) (e: e0xp1): unit =
  match e.e0xp1_node with
    | E0XP1app (e1, es2) ->
        P.fprintf out "E0XP1app(%a; %a)" fprint_e0xp1 e1 fprint_e0xp1_list es2
    | E0XP1char c -> P.fprintf out "'%c'" c
    | E0XP1float f -> P.fprintf out "%s" f
    | E0XP1id id -> fprint_id out id
    | E0XP1int i -> fprint_intinf out i
    | E0XP1list es -> P.fprintf out "E0XP1list(%a)" fprint_e0xp1_list es
    | E0XP1str s -> P.fprintf out "\"%s\"" s
(* end of [fprint_e0xp1] *)

and fprint_e0xp1_list
  (out: out_channel) (es: e0xp1 list) =
  fprint_list_with_sep fprint_e0xp1 out es ","
(* end of [fprint_e0xp1_list] *)

let e0xp1_app loc (e: e0xp1) (es: e0xp1 list): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1app (e, es)
} 

let e0xp1_char loc (c: char): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1char c;
}

let e0xp1_float loc (f: string): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1float f;
}

let e0xp1_id loc (id: id): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1id id;
}

let e0xp1_int loc (i: intinf): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1int i;
}

let e0xp1_list loc (es: e0xp1 list): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1list es;
}

let e0xp1_str loc (s: string): e0xp1 = {
  e0xp1_loc= loc;
  e0xp1_node= E0XP1str s;
}

let e0xp1_true: e0xp1 = {
  e0xp1_loc= Loc.nonloc;
  e0xp1_node= E0XP1int intinf_unit;
}

let e0xp1_false: e0xp1 = {
  e0xp1_loc= Loc.nonloc;
  e0xp1_node= E0XP1int intinf_zero;
}

type v0al1 =
  | V0AL1char of char
  | V0AL1float of float
  | V0AL1int of intinf
  | V0AL1str of string

let v0al1_true = V0AL1int intinf_unit
let v0al1_false = V0AL1int intinf_zero

let v0al1_is_zero (v: v0al1): bool = match v with
  | V0AL1char c -> c = '\000'
  | V0AL1float s -> s = 0.0
  | V0AL1int i -> intinf_is_zero i
  | V0AL1str s -> s = ""
(* end of [v0al1_is_zerp] *)

(* ****** ****** *)

type srt1 = { srt1_loc: loc; srt1_node: srt1_node; }

and srt1_node =
  | SRT1app of srt1 * srt1 list
  | SRT1id of srt_id
  | SRT1lam of srtarg list * srt1
  | SRT1list of srt1 list
  | SRT1qid of srt_qid
  | SRT1tup of srt1 list

let rec fprint_srt1 (out: out_channel) (s1t: srt1): unit =
  match s1t.srt1_node with
    | SRT1app (s1t, s1ts) ->
        P.fprintf out "SRT1app(%a; %a)" fprint_srt1 s1t fprint_srt1_list s1ts
    | SRT1lam (arg, res) ->
        P.fprintf out "SRT1lam(%a; %a)" fprint_srtarg_list arg fprint_srt1 res
    | SRT1id id -> fprint_srt_id out id
    | SRT1list s1ts -> P.fprintf out "SRT1list(%a)" fprint_srt1_list s1ts
    | SRT1qid qid -> fprint_srt_qid out qid
    | SRT1tup s1ts -> P.fprintf out "STR1tup(%a)" fprint_srt1_list s1ts
(* end of [fprint_srt1] *)

and fprint_srt1_list (out: out_channel) (s1ts: srt1 list): unit =
  fprint_list_with_sep fprint_srt1 out s1ts ","

let fprint_srt1_opt
  (out: out_channel) (os1t: srt1 option): unit = begin
  match os1t with None -> () | Some s1t -> fprint_srt1 out s1t
end (* end of [fprint_srt1_opt] *)

(* ****** ****** *)

(* functions for constructing sorts *)

let srt1_arrow: srt1 = {
  srt1_loc= Loc.nonloc;
  srt1_node= SRT1id (srt_id_of_sym Sym.symMINUSGT);
}

(* '->' is a special sort constructor *)
let srt1_is_arrow (s1t: srt1): bool =
  match s1t.srt1_node with
    | SRT1id id -> (Sym.eq Sym.symMINUSGT (sym_of_srt_id id)) | _ -> false
(* end of [srt1_is_arrow] *)

let srt1_app loc (s1t: srt1) (s1ts: srt1 list): srt1 = {
  srt1_loc= loc;
  srt1_node= SRT1app (s1t, s1ts);
} 

let srt1_fun loc (s1t1: srt1) (s1t2: srt1): srt1 = {
  srt1_loc= loc;
  srt1_node = SRT1app (srt1_arrow, [s1t1; s1t2]);
} 

let srt1_id loc (id: srt_id): srt1 = {
  srt1_loc= loc; srt1_node= SRT1id id;
}

let srt1_lam loc (arg: srtarg list) (res: srt1): srt1 = {
  srt1_loc= loc; srt1_node= SRT1lam (arg, res);
}

let rec srt1_lams loc (args: srtarg list list) (res: srt1): srt1 =
  match args with
    | [] -> res
    | arg :: args -> srt1_lam loc arg (srt1_lams loc args res)
(* end of [srt1_lams] *)

let srt1_list loc (s1ts: srt1 list): srt1 =
  match s1ts with
    | [s1t] -> s1t (* singleton elimination *)
    | _ -> { srt1_loc= loc; srt1_node= SRT1list s1ts; }
(* end of [srt1_list] *)

let srt1_qid loc (qid: srt_qid): srt1 = {
  srt1_loc= loc;
  srt1_node = SRT1qid qid;
}

let srt1_tup loc (s1ts: srt1 list): srt1 = {
  srt1_loc= loc; srt1_node = SRT1tup s1ts;
}

(* ****** ****** *)

type sexp1 = {
  mutable sexp1_loc: loc;
  sexp1_node: sexp1_node;
}

and labsexp1 =
    Lab.label * sexp1 list list option (* dimension *) * sexp1

and srtext1 = (* type for extended sorts *)
  { srtext1_loc: loc; srtext1_node: srtext1_node; }

and srtext1_node =
  | STE1srt of srt1
  | STE1sub of sid * srtext1 * sexp1 list

and squa1 =
(*
  | SQ1dvar of did * sexp1
*)
  | SQ1prop of sexp1
  | SQ1vars of sid list * srtext1

and squas1 = { squas1_loc: loc; squas1_node: squa1 list; }

and sarg1 = sid * srt1 option

and svar1 = sid * srt1

and int_sexp1_list = int (* arity_p *) * sexp1 list

and sexp1_node =
  | SE1ann of (* ascribed static expression *)
      sexp1 * srt1
  | SE1any (* omitted static expression *)
  | SE1app of (* static application *)
      sexp1 * sexp1 list 
  | SE1char of (* static character *)
      char
  | SE1exi of (* existential quantifed expression *)
      squas1 * sexp1
  | SE1extype of (* external type *)
      string
  | SE1imp of (* annotated implication *)
      funclo * int (*linear*) * int (*proof*) * Eff.effcst option
  | SE1int of (* static integer *)
      intinf
  | SE1invar of (* invariant view or viewtype *)
      int(*ref/val*) * sexp1 * sexp1 list
  | SE1lam of (* static abstraction *)
      sarg1 list * srt1 option * sexp1
  | SE1mod of (* module type *)
      squal_opt_id * labsexp1 list
  | SE1list of (* static expression list: temoprary *)
      int_sexp1_list 
  | SE1qid of squal_opt_id (* (qualified) static identifier *)
  | SE1struct of (* struct type *)
      labsexp1 list
  | SE1top of (* uninitialized viewtype *)
      sexp1 * sexp1 list
  | SE1trans of (* view or viewtype transform *)
      sexp1 * sexp1 list
  | SE1tyarr of (* array type *)
      sexp1 (* element *) * sexp1 list list (* dimension *)
  | SE1tyrec of (* record type *)
      bool (* is_flat *) * labsexp1 list
  | SE1tytup of (* tuple type *)
      bool (* is_flat *) * int_sexp1_list 
  | SE1uni of (* universal quantified expression *)
      squas1 * sexp1 
  | SE1union of (* union type *)
      sexp1 (* index *) * labsexp1 list

type sexparg1 =
  | SEXPARG1one (* {..} *)
  | SEXPARG1all (* {...} *)
  | SEXPARG1seq of sexp1 list

type svararg1 =
  | SVARARG1one (* {..} *)
  | SVARARG1all (* {...} *)
  | SVARARG1seq of sarg1 list

(* ****** ****** *)

let rec fprint_sexp1 (out: out_channel) (s1e0: sexp1): unit =
  match s1e0.sexp1_node with
    | SE1ann (s1e, s1t) ->
        P.fprintf out "SE1ann(%a, %a)" fprint_sexp1 s1e fprint_srt1 s1t
    | SE1any -> P.fprintf out "_"
    | SE1app (s1e, s1es) ->
	P.fprintf out "SE1app(%a; %a)" fprint_sexp1 s1e fprint_sexp1_list s1es
    | SE1char c -> fprint_char out c
    | SE1exi (s1qs, s1e) ->
	P.fprintf out "SE1exi(%a; %a)" fprint_squas1 s1qs fprint_sexp1 s1e
    | SE1extype name -> P.fprintf out "SE1extype(%s)" name
    | SE1imp (fc, lin, prf, oeffc) -> begin match oeffc with
	| Some effc -> begin
	    P.fprintf out "SE1imp(%a; %i; %i; %a)"
	      fprint_funclo fc lin prf Eff.fprint_effcst effc
	  end
	| None -> begin
	    P.fprintf out "SE1imp(%a; %i; %i)" fprint_funclo fc lin prf
	  end
      end
    | SE1int i -> fprint_intinf out i
    | SE1invar (refval(*ref/val*), s1e, s1es) ->
	P.fprintf out "SE1invar(%i; %a; %a)"
	  refval fprint_sexp1 s1e fprint_sexp1_list s1es
    | SE1lam (args, res, body) -> P.fprintf out "SE1lam(...)"
    | SE1list (npf, s1es) ->
	P.fprintf out "SE1list(%i; %a)" npf fprint_sexp1_list s1es
    | SE1mod (name, ls1es) -> P.fprintf out "SE1mod(%a; %a)"
	fprint_squal_opt_id name fprint_labsexp1_list ls1es
    | SE1qid qid -> fprint_squal_opt_id out qid
    | SE1struct ls1es -> P.fprintf out "SE1struct(%a)" fprint_labsexp1_list ls1es
    | SE1top (s1e, s1es) ->
	P.fprintf out "SE1top(%a; %a)" fprint_sexp1 s1e fprint_sexp1_list s1es
    | SE1trans (s1e, s1es) ->
	P.fprintf out "SE1trans(%a; %a)" fprint_sexp1 s1e fprint_sexp1_list s1es
    | SE1tyarr (s1e_elt, s1ess_dim) -> P.fprintf out "SE1tyarr(%a; %a)"
	fprint_sexp1 s1e_elt fprint_sexp1_list_list s1ess_dim
    | SE1tyrec (_, ls1es) -> P.fprintf out "SE1tyrec(%a)" fprint_labsexp1_list ls1es
    | SE1tytup (_, (npf, s1es)) ->
	P.fprintf out "SE1tytup(%i; %a)" npf fprint_sexp1_list s1es
    | SE1uni (s1qs, s1e) ->
	P.fprintf out "SE1uni(%a; %a)" fprint_squas1 s1qs fprint_sexp1 s1e
    | SE1union (s1e, ls1es) ->
	P.fprintf out "SE1union(%a; %a)" fprint_sexp1 s1e fprint_labsexp1_list ls1es
(* end of [fprint_sexp1] *)

and fprint_sexp1_list
  (out: out_channel) (s1es: sexp1 list): unit =
  fprint_list_with_sep fprint_sexp1 out s1es ","
(* end of [fprint_sexp1_list] *)

and fprint_sexp1_list_list
  (out: out_channel) (s1ess: sexp1 list list): unit =
  fprint_list_with_sep fprint_sexp1_list out s1ess ";"
(* end of [fprint_sexp1_list_list] *)

and fprint_sexp1_opt
  (out: out_channel) (os1e: sexp1 option): unit = begin
  match os1e with None -> () | Some s1e -> fprint_sexp1 out s1e
end (* end of [fprint_sexp1_out] *)

and fprint_labsexp1 (out: out_channel) ((l, os1e1, s1e2): labsexp1): unit =
  match os1e1 with
    | None -> P.fprintf out "%a= %a" Lab.fprint l fprint_sexp1 s1e2
    | Some s1ess1 -> P.fprintf out "%a[%a]= %a"
	Lab.fprint l fprint_sexp1_list_list s1ess1 fprint_sexp1 s1e2
(* end of [fprint_labsexp1] *)

and fprint_labsexp1_list (out: out_channel) (ls1es: labsexp1 list): unit =
  fprint_list_with_sep fprint_labsexp1 out ls1es ","

and fprint_squa1 (out: out_channel) (s1q: squa1): unit =
  match s1q with
    | SQ1prop s1e -> fprint_sexp1 out s1e
    | SQ1vars (ids, s1te) ->
	P.fprintf out "%a: %a" fprint_sid_list ids fprint_srtext1 s1te
(* end of [fprint_squa1] *)

and fprint_squas1 (out: out_channel) (s1qs: squas1): unit =
  fprint_list_with_sep fprint_squa1 out s1qs.squas1_node ","

and fprint_srtext1 (out: out_channel) (s1te: srtext1): unit =
  match s1te.srtext1_node with
    | STE1srt s1t -> fprint_srt1 out s1t
    | STE1sub (id, s1te, s1es) -> P.fprintf out "{%a: %a | %a}"
	fprint_sid id fprint_srtext1 s1te fprint_sexp1_list s1es
(* end of [fprint_srtext1] *)

(* ****** ****** *)

(* functions for constructing static expressions *)

let sexp1_ann loc (s1e: sexp1) (s1t: srt1): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1ann (s1e, s1t);
} 

let sexp1_any loc: sexp1 = { sexp1_loc= loc; sexp1_node= SE1any; } 

let sexp1_app loc (s1e: sexp1) (s1es: sexp1 list): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1app (s1e, s1es);
}

let sexp1_arrow: sexp1 =
  let id = sid_of_sym Sym.symMINUSGT in
    { sexp1_loc= Loc.nonloc; sexp1_node= SE1qid (None, id) }
(* end of [sexp1_arrow] *)

let sexp1_char loc (c: char): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1char c;
}

let sexp1_exi loc (s1qs: squas1) (s1e: sexp1): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1exi (s1qs, s1e);
}

let sexp1_extype loc (name: string): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1extype name;
}

let sexp1_imp loc (fc: funclo)
  (lin: int) (prf: int) (oeffc: Eff.effcst option): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1imp (fc, lin, prf, oeffc);
}

let sexp1_int loc (i: intinf): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1int i;
}

let sexp1_invar loc
  (refval: int) (s1e: sexp1) (s1es: sexp1 list): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1invar (refval, s1e, s1es);
}

let sexp1_invar_ref loc s1e s1es = sexp1_invar loc 1(*ref*) s1e s1es
let sexp1_invar_val loc s1e s1es = sexp1_invar loc 0(*val*) s1e s1es

let sexp1_lam loc (arg: sarg1 list) (res: srt1 option) (body: sexp1)
  : sexp1 = {
    sexp1_loc= loc; sexp1_node= SE1lam (arg, res, body);
  }
(* end of [sexp1_lam] *)

let sexp1_list loc npf (s1es: sexp1 list): sexp1 =
  if npf = 0 then begin match s1es with  
    | [s1e] -> (s1e.sexp1_loc <- loc; s1e)
    | _ -> { sexp1_loc= loc; sexp1_node= SE1list (npf, s1es); }
  end else { sexp1_loc= loc; sexp1_node= SE1list (npf, s1es); }
(* end of [sexp1_list] *)

let sexp1_mod loc
  (name: squal_opt_id) (ls1es: labsexp1 list): sexp1 =
  { sexp1_loc= loc; sexp1_node= SE1mod (name, ls1es); }
(* end of [sexp1_mod] *)

let sexp1_qid loc (qid: squal_opt_id): sexp1 =
  { sexp1_loc= loc; sexp1_node= SE1qid qid; } 

let sexp1_struct loc (ls1es: labsexp1 list): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1struct ls1es;
}

let sexp1_top loc (s1e: sexp1) (s1es: sexp1 list): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1top (s1e, s1es);
}

let sexp1_trans loc (s1e: sexp1) (s1es: sexp1 list): sexp1 = {
  sexp1_loc= loc; sexp1_node= SE1trans (s1e, s1es);
}

let sexp1_tyarr loc
  (s1e_elt: sexp1) (s1ess_dim: sexp1 list list): sexp1 = {
    sexp1_loc= loc; sexp1_node= SE1tyarr (s1e_elt, s1ess_dim);
  }
(* end of [sexp1_tyarr] *)

let sexp1_tyrec loc
  (is_flat: bool) (ls1es: labsexp1 list): sexp1 = {
    sexp1_loc= loc; sexp1_node= SE1tyrec (is_flat, ls1es);
  }
(* end of [sexp1_tyrec] *)

let sexp1_tytup loc
  (is_flat: bool) (npf: int) (s1es: sexp1 list): sexp1 = {
    sexp1_loc= loc; sexp1_node= SE1tytup (is_flat, (npf, s1es));
  }
(* end of [sexp1_tytup] *)

let sexp1_uni loc (s1qs: squas1) (s1e: sexp1): sexp1 = {
  sexp1_loc= loc;
  sexp1_node= SE1uni (s1qs, s1e);
}

let sexp1_union loc (index: sexp1) (ls1es: labsexp1 list): sexp1 = {
  sexp1_loc= loc;
  sexp1_node= SE1union (index, ls1es);
}

let squas1 loc (s1qs: squa1 list): squas1 = {
  squas1_loc= loc; squas1_node= s1qs;
}

(* ****** ****** *)

let sexp1_of_e0xp1 loc (e: e0xp1): sexp1 =
  let rec aux e = match e.e0xp1_node with
    | E0XP1app (e1, es2) ->
	let s1e1 = aux e1 and s1es2 = aux_list es2 in
	  sexp1_app loc s1e1 s1es2
    | E0XP1id id ->
	sexp1_qid loc (None, sid_of_sym (sym_of_id id))
    | E0XP1int i -> sexp1_int loc i
    | E0XP1list es ->
	sexp1_list loc 0 (* arity_p *) (aux_list es)
    | _ -> begin
	P.fprintf stderr
	  "%a: illegal static expression." Loc.fprint loc;
	Err.abort ();
      end

  and aux_list es = List.map aux es in aux e
(* end of [sexp1_of_e0xp1] *)

(* ****** ****** *)

(* end of [ats_staexp1.ml] *)
