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

module BI = Big_int
module PR = Printf

module Err = Ats_error
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol

(* ****** ****** *)

type label = Lab.label
type location = Loc.location

type intinf = BI.big_int
type symbol = Sym.symbol

type id = {
  id_loc: location;
  id_sym: symbol;
}

(* ****** ****** *)

type assoc = Ats_fixity.assoc
type prec = PRECint of intinf | PRECopr of id

type fixity =
  | Infix of prec * assoc
  | Postfix of prec
  | Prefix of prec

(* ****** ****** *)

let getloc = Loc.get_the_location
let getstrloc = Loc.get_the_string_location
let getextloc = Loc.get_the_extern_location

(* ****** ****** *)

type e0xp = {
  e0xp_loc: Ats_location.location;
  e0xp_node: e0xp_node;
}

and e0xp_node =
  | E0XPapp of e0xp * e0xp
  | E0XPchar of char
  | E0XPfloat of string
  | E0XPint of intinf
  | E0XPid of id
  | E0XPlist of e0xp list
  | E0XPstr of string

let e0xp_app (e1: e0xp) (e2: e0xp): e0xp = {
  e0xp_loc= getloc ();
  e0xp_node= E0XPapp (e1, e2);
} 

let rec e0xp_apps (e1: e0xp) (es2: e0xp list): e0xp =
  match es2 with
    | [] -> e1
    | e2 :: es2 -> e0xp_apps (e0xp_app e1 e2) es2
(* end of [e0xp_apps] *)

let e0xp_char (c: char): e0xp = {
  e0xp_loc= getloc ();
  e0xp_node= E0XPchar c;
} 

let e0xp_float (f: string): e0xp = {
  e0xp_loc= getloc ();
  e0xp_node= E0XPfloat f;
} 

let e0xp_id (name: id): e0xp = {
  e0xp_loc= getloc ();
  e0xp_node= E0XPid name;
} 

let e0xp_int (i: intinf): e0xp = {
  e0xp_loc= getloc ();
  e0xp_node= E0XPint i;
} 

let e0xp_list (es: e0xp list): e0xp = {
  e0xp_loc= getloc ();
  e0xp_node= E0XPlist es;
}

let e0xp_str (s: string): e0xp = {
  e0xp_loc= getstrloc ();
  e0xp_node= E0XPstr s;
} 

let e0xp_true = {
  e0xp_loc= Loc.nonloc;
  e0xp_node= E0XPint intinf_unit;
}

(* ****** ****** *)

let id_eq (id1: id) (id2: id) = Sym.eq (id1.id_sym) (id2.id_sym)
let id_neq (id1: id) (id2: id) = Sym.neq (id1.id_sym) (id2.id_sym)

let string_of_id (id: id): string = Sym.string_of (id.id_sym)
let sym_of_id (id: id): symbol = id.id_sym

let id_is_amper id = Sym.eq Sym.symAMPER (sym_of_id id)
let id_is_bang id = Sym.eq Sym.symBANG (sym_of_id id)
let id_is_backslash id = Sym.eq Sym.symBACKSLASH (sym_of_id id)

let fprint_id (out: out_channel) (id: id) = Sym.fprint out (id.id_sym)
let fprint_id_list (out: out_channel) (ids: id list): unit =
  fprint_list_with_sep fprint_id out ids ","

let make_id_with_string (s: string): id = {
  id_loc= getloc (); id_sym= Sym.make_with_string s;
}

let make_id_with_symbol (s: symbol): id = {
  id_loc= getloc (); id_sym= s;
}

let id_of_sym (s: symbol): id = {
  id_loc= Loc.nonloc; id_sym= s;
}

let loc_of_id (id: id): location = id.id_loc

(* ****** ****** *)

type srt_id = id

let make_srt_id_with_string = make_id_with_string
let make_srt_id_with_symbol = make_id_with_symbol

let string_of_srt_id = string_of_id
let sym_of_srt_id = sym_of_id

let srt_id_of_sym = id_of_sym

let srt_id_eq = id_eq
let srt_id_neq = id_neq

let fprint_srt_id = fprint_id
let fprint_srt_id_list = fprint_id_list

let srt_id_is_addr (id: srt_id): bool = Sym.eq Sym.symADDR id.id_sym
let srt_id_is_bool (id: srt_id): bool = Sym.eq Sym.symBOOL id.id_sym
let srt_id_is_int (id: srt_id): bool = Sym.eq Sym.symINT id.id_sym

let srt_id_is_prop (id: srt_id): bool = Sym.eq Sym.symPROP id.id_sym

let srt_id_is_type (id: srt_id): bool = Sym.eq Sym.symTYPE id.id_sym
let srt_id_is_t0ype (id: srt_id): bool = Sym.eq Sym.symT0YPE id.id_sym

let srt_id_is_view (id: srt_id): bool = Sym.eq Sym.symVIEW id.id_sym

let srt_id_is_viewtype (id: srt_id): bool =
  Sym.eq Sym.symVIEWTYPE id.id_sym
let srt_id_is_viewt0ype (id: srt_id): bool =
  Sym.eq Sym.symVIEWT0YPE id.id_sym

let srt_id_is_types (id: srt_id): bool = Sym.eq Sym.symTYPES id.id_sym

let srt_id_is_backslash id = Sym.eq Sym.symBACKSLASH (sym_of_srt_id id)

(* ****** ****** *)

type srt_qual =
  | STQ_filedot of Ats_filename.filename
  | STQ_symdot of Ats_symbol.symbol

let srt_qual_eq (q1: srt_qual) (q2: srt_qual): bool =
  match (q1, q1) with
    | (STQ_filedot f1, STQ_filedot f2) -> Fil.eq f1 f2
    | (STQ_symdot s1, STQ_symdot s2) -> Sym.eq s1 s2
    | (_,  _) -> false
(* end of [srt_qual_eq] *)

type srt_qid = srt_qual * srt_id

let srt_qid_eq ((q1, s1): srt_qid) ((q2, s2): srt_qid): bool =
  srt_qual_eq q1 q2 && srt_id_eq s1 s2
(* end of [srt_qid_eq] *)

let srt_qid_neq sq1 sq2 = not (srt_qid_eq sq1 sq2)

let fprint_srt_qual (out: out_channel) (sq: srt_qual): unit =
  match sq with
    | STQ_filedot f -> (Fil.fprint out f; fprint_string out ".")
    | STQ_symdot s -> (Sym.fprint out s;  fprint_string out ".")
(* end of [fprint_srt_qual] *)

let fprint_srt_qid (out: out_channel) ((q, s): srt_qid): unit = begin
  fprint_srt_qual out q; fprint_srt_id out s;
end (* end of [fprint_srt_qid] *)

(* ****** ****** *)

type srtarg = srt_id

let fprint_srtarg = fprint_id
let fprint_srtarg_list = fprint_id_list

type srt = { 
  srt_loc: Ats_location.location;
  srt_node: srt_node;
}

and srt_node =
  | SRTapp of srt * srt
  | SRTid of srt_id (* sort identifier *)
  | SRTqid of srt_qid (* qualified sort identifier *)
  | SRTlist of srt list
  | SRTtup of srt list

type srtpol = srt * int (* type for sorts with polarity *)

(* ****** ****** *)

let srt_prop = {
  srt_loc= Loc.nonloc;
  srt_node= SRTid (make_srt_id_with_symbol Sym.symPROP);
}

let srt_t0ype = {
  srt_loc= Loc.nonloc;
  srt_node= SRTid (make_srt_id_with_symbol Sym.symT0YPE);
}

let srt_type = {
  srt_loc= Loc.nonloc;
  srt_node= SRTid (make_srt_id_with_symbol Sym.symTYPE);
}

let srt_view = {
  srt_loc= Loc.nonloc;
  srt_node= SRTid (make_srt_id_with_symbol Sym.symVIEW);
}

let srt_viewt0ype = {
  srt_loc= Loc.nonloc;
  srt_node= SRTid (make_srt_id_with_symbol Sym.symVIEWT0YPE);
}

let srt_viewtype = {
  srt_loc= Loc.nonloc;
  srt_node= SRTid (make_srt_id_with_symbol Sym.symVIEWTYPE);
}

(* ****** ****** *)

let srt_app (s1: srt) (s2: srt): srt = {
  srt_loc= getloc ();
  srt_node= SRTapp (s1, s2);
} 

let rec srt_apps (s1: srt) (ss2: srt list): srt =
  match ss2 with
    | [] -> s1
    | s2 :: ss2 -> srt_apps (srt_app s1 s2) ss2
(* end of [srt_apps] *)

let srt_id (id: srt_id): srt = {
  srt_loc= getloc ();
  srt_node= SRTid (id);
}

let srt_qid (qid: srt_qid): srt = {
  srt_loc= getloc ();
  srt_node= SRTqid (qid);
}

let srt_list (ss: srt list): srt = {
  srt_loc= getloc ();
  srt_node= SRTlist (ss);
}

let srt_tup (ss: srt list): srt = {
  srt_loc= getloc ();
  srt_node= SRTtup (ss);
}

(* ****** ****** *)

type sid = id

type squal =
  | SQ_filedot of Ats_filename.filename
  | SQ_symcolon of Ats_symbol.symbol
  | SQ_symdot of Ats_symbol.symbol

type squal_id = squal * sid
type squal_opt_id = squal option * sid

let make_sid_with_string = make_id_with_string
let make_sid_with_symbol = make_id_with_symbol

let string_of_sid = string_of_id
let sym_of_sid = sym_of_id
let loc_of_sid = loc_of_id
let sid_of_id (id: sid) = id
let sid_of_sym = id_of_sym

let sid_eq = id_eq
let sid_neq = id_neq

let fprint_sid = fprint_id
let fprint_sid_list = fprint_id_list

let fprint_squal (out: out_channel) (sq: squal): unit =
  match sq with
    | SQ_filedot f -> (Fil.fprint out f; fprint_char out '.')
    | SQ_symcolon s -> (Sym.fprint out s; fprint_char out ':')
    | SQ_symdot s -> (Sym.fprint out s; fprint_char out '.')
(* end of [fprint_squal] *)

let fprint_squal_id
  (out: out_channel) ((sq, id): squal_id) =
  (fprint_squal out sq; fprint_sid out id)
(* end of [fprint_squal_id] *)

let fprint_squal_opt_id
  (out: out_channel) ((osq, id): squal_opt_id): unit =
  match osq with
    | Some sq -> (fprint_squal out sq; fprint_sid out id)
    | None -> fprint_sid out id

let sid_is_amper id = id_is_amper id

let sid_arrow = make_sid_with_symbol Sym.symMINUSGT
let sid_is_arrow (id: sid): bool = Sym.eq Sym.symMINUSGT (id.id_sym)

let sid_is_at (id: sid): bool = Sym.eq Sym.symAT (id.id_sym)

let sid_is_bang id = id_is_bang id
let sid_is_backslash id = id_is_backslash id

let sid_equal = make_sid_with_symbol Sym.symEQEQ
let sid_is_equal (id: sid): bool = Sym.eq Sym.symEQEQ (id.id_sym)

let sid_qmark = make_sid_with_symbol Sym.symQMARK
let sid_is_qmark (id: sid): bool = Sym.eq Sym.symQMARK (id.id_sym)

let sid_is_ptr (id: sid): bool = Sym.eq Sym.symPTR (id.id_sym)
let sid_is_trans (id: sid): bool = Sym.eq Sym.symGTGT (id.id_sym)

(* ****** ****** *)

type funclo = (* function or closure *)
  | FUNCLOclo of int(*-1/0/1: ref/clo/ptr*) (* closure *) 
  | FUNCLOfun (* function *)

let fprint_funclo (out: out_channel) (fc: funclo): unit =
  match fc with
    | FUNCLOclo (knd) -> PR.fprintf out "clo(%i)" knd
    | FUNCLOfun -> PR.fprintf out "fun"
(* end of [fprint_funclo] *)

let funclo_eq (fc1: funclo) (fc2: funclo): bool =
  match fc1, fc2 with
    | FUNCLOclo (knd1), FUNCLOclo (knd2) -> (knd1 = knd2)
    | FUNCLOfun, FUNCLOfun -> true
    | _, _ -> false
(* end of [funclo_eq] *)

(* ****** ****** *)

type effect =
  | EFFall (* all combined *)
  | EFFexn (* exception *)
  | EFFntm (* nontermination *)
  | EFFref (* reference *)

let effect_eq (eff1: effect) (eff2: effect): bool =
  match eff1, eff2 with
    | EFFexn, EFFexn -> true
    | EFFntm, EFFntm -> true
    | EFFref, EFFref -> true
    | _, _ -> false
(* end of [effect_eq] *)

let effect_leq (eff1: effect) (eff2: effect): bool =
  match eff1, eff2 with
    | _, EFFall -> true | _, _ -> effect_eq eff1 eff2
(* end of [effect_leq] *)

let fprint_effect (out: out_channel) (eff: effect): unit =
  match eff with
    | EFFall -> PR.fprintf out "all"
    | EFFexn -> PR.fprintf out "exn"
    | EFFntm -> PR.fprintf out "ntm"
    | EFFref -> PR.fprintf out "ref"
(* end of [fprint_effect] *)

let fprint_effect_list (out: out_channel) (effs: effect list): unit =
  fprint_list_with_sep fprint_effect out effs ","
(* end of [fprint_effect_list] *)

(* ****** ****** *)

type efftag =
  | EFFTAGcst of string
  | EFFTAGvar of sid
  | EFFTAGprf
  | EFFTAGlin of int
  | EFFTAGfun of int
  | EFFTAGclo of int
  | EFFTAGcloptr of int
  | EFFTAGcloref of int

type efftags = efftag list

(* ****** ****** *)

let name_is_proof (name: string): bool =
  name = "prf"

let name_is_linear_0 (name: string): bool =
  name = "lin0" || name = "lin"
let name_is_linear_1 (name: string): bool =
  name = "lin1"

let name_is_fun_0 (name: string): bool =
  name = "fun0" || name = "fun"
let name_is_fun_1 (name: string): bool =
  name = "fun1"

let name_is_clo_0 (name: string): bool =
  name = "clo0" || name = "clo"
let name_is_clo_1 (name: string): bool =
  name = "clo1"

let name_is_cloptr_0 (name: string): bool =
  name = "cloptr0" || name = "cloptr"
let name_is_cloptr_1 (name: string): bool =
  name = "cloptr1"

let name_is_cloref_0 (name: string): bool =
  name = "cloref0" || name = "cloref"
let name_is_cloref_1 (name: string): bool =
  name = "cloref1"

(* ****** ****** *)

let name_is_nil (name: string): bool =
  name = "0"

let name_is_all (name: string): bool =
  name = "1"

let name_is_exn (name: string): bool =
  name = "exn" || name = "exception"

let name_is_exnref (name: string): bool =
  name = "exnref"

let name_is_gc (name: string): bool =
  name = "gc"

let name_is_heap (name: string): bool =
  name = "hp" || name = "heap"

let name_is_nonterm (name: string): bool =
  name = "ntm" || name = "nonterm"

let name_is_ref (name:string): bool =
  name = "ref" || name = "reference"

let name_is_term (name: string): bool =
  name = "term"

let name_is_write (name: string): bool =
  name = "wrt" || name = "write"

let name_is_lazy (name: string): bool =
  name = "laz"

(* ****** ****** *)

let efftags_contain_term (tags: efftag list) =
  let rec aux is_term tags = match tags with
    | [] -> is_term
    | tag :: tags -> begin match tag with
      | EFFTAGcst name when name_is_term name -> aux true tags
      | EFFTAGcst name when name_is_nonterm name -> aux false tags
      | _ -> aux is_term tags
      end in
    aux true tags
(* end of [efftags_contain_term] *)

let efftag_cst (name: string) = EFFTAGcst name

let efftag_int (i: intinf) = efftag_cst (string_of_intinf i)

let efftag_var (name: string): efftag = begin
  match name with
  | _ when name_is_proof name -> EFFTAGprf
  | _ when name_is_linear_0 name -> EFFTAGlin 0
  | _ when name_is_linear_1 name -> EFFTAGlin 1
  | _ when name_is_fun_0 name -> EFFTAGfun 0
  | _ when name_is_fun_1 name -> EFFTAGfun 1
  | _ when name_is_clo_0 name -> EFFTAGclo 0
  | _ when name_is_clo_1 name -> EFFTAGclo 1
  | _ when name_is_cloptr_0 name -> EFFTAGcloptr 0
  | _ when name_is_cloptr_1 name -> EFFTAGcloptr 1
  | _ when name_is_cloref_0 name -> EFFTAGcloref 0
  | _ when name_is_cloref_1 name -> EFFTAGcloref 1
  | _ -> EFFTAGvar (make_sid_with_string name)
end (* end of [efftag_var] *)

let fprint_efftag
 (out: out_channel) (tag: efftag): unit = begin
  match tag with
  | EFFTAGcst name -> PR.fprintf out "!%s" name
  | EFFTAGvar id -> fprint_sid out id
  | EFFTAGprf -> PR.fprintf out "proof"
  | EFFTAGlin i -> PR.fprintf out "lin%i" i
  | EFFTAGfun i -> PR.fprintf out "fun%i" i
  | EFFTAGclo i -> PR.fprintf out "clo%i" i
  | EFFTAGcloptr i -> PR.fprintf out "cloptr%i" i
  | EFFTAGcloref i -> PR.fprintf out "cloref%i" i
end (* end of [fprint_efftag] *)

let fprint_efftags (out: out_channel) (tags: efftags): unit =
  fprint_list_with_sep fprint_efftag out tags ","

(* ****** ****** *)

type sexp = (* type for static expressions *)
  { sexp_loc: Ats_location.location; sexp_node: sexp_node; }

and labsexp = label * sexp list list option (* dimension *) * sexp

and srtext_node =
  | STEsrt of srt
  | STEsub of sid * srtext * sexp list

and srtext = { (* type for extended sorts *)
  srtext_loc: Ats_location.location;
  srtext_node: srtext_node;
}

and squa =
  | SQprop of sexp (* e.g., n >= i+j *)
  | SQvars of sid list * srtext (* e.g., a: type *)

and squas =
  { squas_loc: Ats_location.location; squas_node: squa list; }

and sarg = sid * srt option

and svar = sid * srt

and int_sexp_list = int (* arity_p *) * sexp list 

and sexp_node =
  | SEann of (* ascribed static expression *)
      sexp * srt 
  | SEapp of (* static application *)
      sexp * sexp 
  | SEchar of (* static character *)
      char 
  | SEexi of (* existentially quantified type *)
      squas * sexp 
  | SEextype of (* external type *)
      string
  | SEid of (* static identifier *)
      sid 
  | SEimp of (* decorated implication *)
      efftags 
  | SEint of (* static integer *)
      intinf     
  | SElam of (* static lambda abstraction *)
      sarg list * srt option * sexp
  | SElist of (* static expression list to be eliminated *)
      int_sexp_list 
  | SEmod of (* module type *)
      squal_opt_id * labsexp list
  | SEop of (* noninfix static identifier *)
      sid 
  | SEqid of (* qualified static identifier *)
      squal_id 
  | SEstruct of (* struct type *)
      labsexp list 
  | SEtyarr of (* array type *)
      sexp (* element *) * sexp list list (* dimension *)
  | SEtyrec of (* record type *)
      bool (* is_flat *) * labsexp list
  | SEtytup of (* tuple type *)
      bool (* is_flat *) * int_sexp_list
  | SEuni of (* universally quantified type *)
      squas * sexp
  | SEunion of (* union type *)
      sexp (* index *) * labsexp list

and svararg =
  | SVARARGone (* {..} *)
  | SVARARGall (* {...} *)
  | SVARARGseq of sarg list

and sexparg =
  | SEXPARGone (* {..} *)
  | SEXPARGall (* {...} *)
  | SEXPARGseq of sexp list

(* ****** ****** *)

let sexp_ann se (st: srt) = {
  sexp_loc= getloc ();
  sexp_node= SEann (se, st);
} 

let sexp_app (se1: sexp) (se2: sexp): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEapp (se1, se2);
} 

let rec sexp_apps (se1: sexp) (ses2: sexp list): sexp =
  match ses2 with
    | [] -> se1
    | se2 :: ses2 -> sexp_apps (sexp_app se1 se2) ses2
(* end of [sexp_app] *)

let sexp_char (c: char): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEchar c;
}

let sexp_exi (sqs: squas) (se: sexp): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEexi (sqs, se);
}

let sexp_extype (name: string): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEextype name;
}

let sexp_id (id: sid): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEid id;
}

let sexp_imp (effs: efftags): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEimp effs;
}

let sexp_int (i: intinf): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEint i;
}

let sexp_lam loc
  (arg: sarg list) (res: srt option) (body: sexp): sexp = {
    sexp_loc= loc;
    sexp_node= SElam (arg, res, body);
  }
(* end of [sexp_lam] *)

let sexp_lams (args: (sarg list) list) (res: srt option) (body: sexp)
  : sexp =
  let loc = getloc () in
  let rec aux (arg: sarg list) (args: (sarg list) list): sexp =
    match args with
      | [] -> sexp_lam loc arg res body
      | arg' :: args' -> sexp_lam loc arg None (aux arg' args') in
    match args with
      | [] -> body
      | arg :: args -> aux arg args
(* end of [sexp_lams] *)

let sexp_list (ses: sexp list): sexp =
  let loc = getloc () in
  let nses = (0, ses) in {
      sexp_loc= loc; sexp_node= SElist nses;
    }
(* end of [sexp_list] *)

let sexp_list2 (ses1: sexp list) (ses2: sexp list): sexp =
  let loc = getloc () in
  let nses = (List.length ses1, ses1 @ ses2) in {
      sexp_loc= loc; sexp_node= SElist nses;
    }
(* end of [sexp_list2] *)

let sexp_mod (name: squal_opt_id) (lses: labsexp list): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEmod (name, lses);
}

let sexp_op (id: sid): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEop id;
}

let sexp_qid (name: squal_id): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEqid name;
}

let sexp_struct (lses: labsexp list): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEstruct lses;
}

let sexp_tyarr
  (se_elt: sexp) (sess_dim: sexp list list): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEtyarr (se_elt, sess_dim);
}

let sexp_tyrec
  (is_flat: bool) (lses: labsexp list): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEtyrec (is_flat, lses);
}

let sexp_tytup (is_flat: bool) (ses: sexp list): sexp =
  let loc = getloc () in
  let nses = (0, ses) in {
      sexp_loc= loc; sexp_node= SEtytup (is_flat, nses);
    }
(* end of [sexp_tytup] *)

let sexp_tytup2
  (is_flat: bool) (ses1: sexp list) (ses2: sexp list): sexp =
  let loc = getloc () in
  let nses = (List.length ses1, ses1 @ ses2) in {
      sexp_loc= loc;
      sexp_node= SEtytup (is_flat, nses);
    }
(* end of [sexp_tytup2] *)

let sexp_uni (sqs: squas) se: sexp = {
  sexp_loc= getloc ();
  sexp_node= SEuni (sqs, se);
}

let sexp_union (index: sexp) (lses: labsexp list): sexp = {
  sexp_loc= getloc ();
  sexp_node= SEunion (index, lses)
}

(* ****** ****** *)

let squas (sqs: squa list): squas =
  { squas_loc= getloc (); squas_node= sqs; }

let srtext_srt st = {
  srtext_loc= getloc (); srtext_node= STEsrt st;
}

let srtext_sub (id: sid) (ste: srtext) (ps: sexp list): srtext =
  { srtext_loc= getloc (); srtext_node= STEsub (id, ste, ps) }

(* ****** ****** *)

type did = id

let make_did_with_string = make_id_with_string
let make_did_with_symbol = make_id_with_symbol

let make_did_with_loc_and_string loc (s: string): did =
  { id_loc= loc; id_sym= Sym.make_with_string s; }

let make_did_with_loc_and_symbol loc (s: symbol): did =
  { id_loc= loc; id_sym= s ; }

let string_of_did = string_of_id
let sym_of_did = sym_of_id
let loc_of_did = loc_of_id
let did_of_id id = id
let sid_of_did id = id

let did_eq = id_eq
let did_neq = id_neq

let did_is_true (id: did) = Sym.eq Sym.symTRUE (id.id_sym)
let did_is_false (id: did) = Sym.eq Sym.symFALSE (id.id_sym)
let did_is_assgn (id: did) = Sym.eq Sym.symCOLONEQ (id.id_sym)
let did_is_selptr (id: did) = Sym.eq Sym.symMINUSGT (id.id_sym)
let did_is_qmark (id: did) = Sym.eq Sym.symQMARK (id.id_sym)
let did_is_underscore (id: did) = Sym.eq Sym.symUNDERSCORE (id.id_sym)
let did_is_vbox (id: did) = Sym.eq Sym.symVBOX (id.id_sym)
			       
let did_is_backslash = id_is_backslash
let did_is_bang = id_is_bang

let fprint_did = fprint_id
let fprint_did_list = fprint_id_list

type dqual =
  | DQ_symcolon of symbol
  | DQ_filedot of Ats_filename.filename
  | DQ_filedot_symcolon of Ats_filename.filename * sid
  | DQ_symdot of Ats_symbol.symbol
  | DQ_symdot_symcolon of Ats_symbol.symbol * sid

let fprint_dqual (out: out_channel) (dq: dqual): unit =
  match dq with
    | DQ_filedot f -> (Fil.fprint out f; fprint_char out '.')
    | DQ_filedot_symcolon (f, sid) -> begin
        Fil.fprint out f; fprint_char out '.';
        fprint_sid out sid; fprint_char out ':';
      end
    | DQ_symcolon s -> (Sym.fprint out s; fprint_char out ':')
    | DQ_symdot s -> (Sym.fprint out s; fprint_char out '.')
    | DQ_symdot_symcolon (sym1, sid2) -> begin
        Sym.fprint out sym1; fprint_char out '.';
        fprint_sid out sid2; fprint_char out ':';
      end
(* end of [fprint_dqual] *)

type dqual_id = dqual * did
type dqual_opt_id = dqual option * did

let did_brackets: id = id_of_sym Sym.symBRACKETS

let fprint_dqual_id
  (out: out_channel) ((dq, id): dqual_id): unit =
  (fprint_dqual out dq; fprint_did out id)
(* end of [fprint_dqual_id] *)

let fprint_dqual_opt_id
  (out: out_channel) ((odq, id): dqual_opt_id): unit =
  match odq with
    | Some dq -> (fprint_dqual out dq; fprint_did out id)
    | None -> fprint_did out id
(* end of [fprint_dqual_opt_id] *)

(* ****** ****** *)

let svar_of_sarg ((id, ost): sarg): svar =
  match ost with
    | Some st -> (id, st)
    | None -> begin
	PR.eprintf "%a: sort annotation for <%a> is required.\n"
	  Loc.fprint id.id_loc Sym.fprint id.id_sym;
	Err.abort ();
      end

(* ****** ****** *)

type intkind =
  | IKint (* undecorated *) | IKuint (* unsigned *)
  | IKlint (* long *) | IKulint (* unsigned long *)
  | IKsint (* short *) | IKusint (* unsigned short *)
  | IKint8 | IKuint8 | IKint16 | IKuint16
  | IKint32 | IKuint32 | IKint64 | IKuint64

(* ****** ****** *)

type pat = (* the type for patterns *)
  { pat_loc: Ats_location.location; pat_node: pat_node; }

and labpat = label * pat

and int_pat_list = int (* arity_p *) * pat list

and pat_node =
  | PTann of (* annotated pattern *)
      pat * sexp
  | PTapp of (* applied pattern (a temporary form) *)
      pat * pat
  | PTas of (* [as] pattern *)
      did * pat
  | PTchar of (* character pattern *)
      char
  | PTexi of (* existentially quantified pattern *)
      svar list * pat
  | PTfree of (* freeing constructor pattern *)
      pat
  | PTid of (* pattern identifier *)
      did
  | PTint of (* integer pattern *)
      intinf
  | PTlist of (* for pattern list *)
      int_pat_list
  | PTlst of (* list pattern *)
      pat list
  | PTop of (* nonfix pattern identifier *)
      did
  | PTqid of (* qualified pattern identifier *)
      dqual_id 
  | PTrec of (* record pattern *)
      bool (* is_flat *) * bool (* is_omit *) * labpat list
  | PTref of (* refvar pattern *)
      did
  | PTrefas of (* refvar [as] pattern *)
      did * pat
  | PTstring of (* string pattern *)
      string
  | PTsvararg of (* for temporary use *)
      svararg
  | PTtup of (* tuple pattern *)
      bool (* is_flat *) * int_pat_list

(* ****** ****** *)

let pat_ann pt se: pat =
  { pat_loc= getloc (); pat_node= PTann (pt, se); }

let pat_app pt1 pt2: pat =
  { pat_loc= getloc (); pat_node= PTapp (pt1, pt2); }

let rec pat_apps pt1 pts2: pat = match pts2 with
  | [] -> pt1
  | pt2 :: pts2 -> pat_apps (pat_app pt1 pt2) pts2
(* end of [pat_apps] *)

let pat_as (id: did) (pt: pat): pat =
  { pat_loc= getloc (); pat_node= PTas (id, pt); }

let pat_char (c: char): pat =
  { pat_loc= getloc (); pat_node = PTchar c; }

let pat_exi (svs: sarg list) pt: pat =
  let svs = List.map svar_of_sarg svs in
    { pat_loc= getloc (); pat_node= PTexi (svs, pt); }
(* end of [pat_exi] *)

let pat_free (pt: pat): pat =
  { pat_loc= getloc (); pat_node= PTfree pt; }

let pat_id (id: did): pat =
  { pat_loc= getloc (); pat_node= PTid id; }

let pat_int (i: intinf): pat =
  { pat_loc= getloc (); pat_node=  PTint i; }

let pat_list pts: pat =
  let loc = getloc () in
  let npts = (0, pts) in
    { pat_loc= loc; pat_node= PTlist npts; } 
(* end of [pat_list] *)

let pat_list2 pts1 pts2: pat =
  let loc = getloc () in
  let npts = (List.length pts1, pts1 @ pts2) in
    { pat_loc= loc; pat_node= PTlist npts; } 
(* end of [pat_list2] *)

let pat_lst pts: pat =
  { pat_loc= getloc (); pat_node= PTlst pts; } 

let pat_op (id: did): pat =
  { pat_loc= getloc (); pat_node= PTop id; } 

let pat_qid (qid: dqual_id): pat =
  { pat_loc= getloc (); pat_node= PTqid qid; } 

let patrow_cons (lpt: labpat)
  ((is_omit: int), (lpts: labpat list)): int * labpat list =
  (is_omit, lpt :: lpts)

let pat_rec (is_flat: bool) (is_omit, lpts): pat = {
  pat_loc= getloc ();
  pat_node= PTrec (is_flat, is_omit > 0, lpts);
}

let pat_ref (id: did): pat =
  { pat_loc= getloc (); pat_node= PTref (id); }

let pat_refas (id: did) (pt: pat): pat =
  { pat_loc= getloc (); pat_node= PTrefas (id, pt); }

let pat_svararg (arg: svararg): pat = {
  pat_loc= getloc (); pat_node= PTsvararg arg;
}

let pat_string (s: string) =
  { pat_loc= getstrloc (); pat_node= PTstring s; }

let pat_tup (is_flat: bool) (pts: pat list): pat =
  let loc = getloc () in
  let npts = (0, pts) in
    { pat_loc= loc; pat_node= PTtup (is_flat, npts) }
(* end of [pat_tup] *)

let pat_tup2 (is_flat: bool) pts1 pts2: pat =
  let loc = getloc () in
  let npts = (List.length pts1, pts1 @ pts2) in
    { pat_loc= loc; pat_node= PTtup (is_flat, npts); } 
(* end of [pat_tup2] *)

(* ****** ****** *)

type pattern_exhaustiveness_test =
  | PETignore (* no test on nonexhaustiveness *)
  | PETwarning (* a warning is issued if nonexhaustive *)
  | PETerror (* an error is raised if nonexhaustive *)

(* ****** ****** *)

type dfarg0 = {
  dfarg0_loc: Ats_location.location;
  dfarg0_name: did;
  dfarg0_sexp: sexp option;
}

let dfarg0 (name: did) (ose: sexp option): dfarg0 = {
  dfarg0_loc= getloc ();
  dfarg0_name= name;
  dfarg0_sexp= ose;
}

type farg0_node =
  | FARG0dyn of int (* arity_p *) * dfarg0 list
  | FARG0sta of squas

type farg0 =
  { farg0_loc: Ats_location.location; farg0_node: farg0_node; }

let farg0dyn (xs: dfarg0 list): farg0 =
  let loc = getloc () in
    { farg0_loc= loc; farg0_node= FARG0dyn (0, xs); }
(* end of [farg0dyn] *)

let farg0dyn2 (xs1: dfarg0 list) (xs2: dfarg0 list): farg0 = 
  let loc = getloc () in
    { farg0_loc= loc; farg0_node= FARG0dyn (List.length xs1, xs1 @ xs2); }
(* end of [farg0dyn2] *)

let farg0sta (sqs: squas): farg0 =
  { farg0_loc= getloc (); farg0_node= FARG0sta sqs; }

type farg_node =
  | FARGsta1 of squas (* static argument (synthesis) *)
  | FARGsta2 of sarg list (* static argument (analysis) *)
  | FARGdyn of pat (* dynamic argument *)
  | FARGmet of sexp list (* metric *)

type farg =
  { farg_loc: Ats_location.location; farg_node: farg_node; }

let fargsta1 (sqs: squas): farg = {
  farg_loc= getloc (); farg_node= FARGsta1 sqs;
}

let fargsta2 (ids: sarg list): farg = {
  farg_loc= getloc (); farg_node= FARGsta2 ids;
}

let fargdyn pt: farg = {
  farg_loc= getloc (); farg_node= FARGdyn pt;
}

let fargmet (ses: sexp list): farg = {
  farg_loc= getloc (); farg_node= FARGmet ses;
}

(* ****** ****** *)

type dcstextdef =
  | DCSTEXTDEFnone
  | DCSTEXTDEFsome_fun of string
  | DCSTEXTDEFsome_mac of string
(* end of [dcstextdef] *)

let dcstextdef_is_mac (x: dcstextdef): bool =
  match x with DCSTEXTDEFsome_mac _ -> true | _ -> false
(* end of [dcstextdef_is_mac] *)

(* ****** ****** *)

type dec = (* type for declaration *)
  { dec_loc: Ats_location.location; dec_node: dec_node; }

and dexp = (* type for dynamic expressions *)
  { dexp_loc: Ats_location.location; dexp_node: dexp_node; }

and labdexp = label * dexp

and int_dexp_list = int (* arity *) * dexp list

and dlab = {
  dlab_lab: label;
  dlab_ind: dexp option;
}

and cla = {
  cla_loc: Ats_location.location;
  cla_pat: pat;
  cla_gua: dexp option;
  cla_isseq: bool;
  cla_isneg: bool;
  cla_body: dexp;
}

and statype = squas option * statype_body
and statype_body = (did * sexp option) list

and loopinv = {
  loopinv_loc: Ats_location.location;
  loopinv_qua: squas option; (* quantifier *)
  loopinv_met: (sexp list) option; (* metric *)
  loopinv_arg: statype_body; (* argument *)
  loopinv_res: statype option; (* result *)
}

and dexp_node =
  | DEann_type of (* ascribed dynamic expressions *)
      dexp * sexp
  | DEapp of (* functional application *)
      dexp * dexp
  | DEarr of (* array expression *)
      sexp * dexp list
  | DEarrsub of (* array subscription *)
      dexp * (dexp list) list
  | DEcase of (* case expression *)
      int * statype option * dexp * cla list
  | DEchar of (* dynamic characters *)
      char
  | DEcrypt of (* 1/-1: encrypt/decrypt *)
      int(*kind*) * dexp
  | DEdelay of (* lazy evaluation *)
      dexp
  | DEdemac of (* macro decoding *)
      dexp
  | DEdynload of (* dynamic loading *)
      dexp
  | DEeffmask of (* effect masking *)
      effect * dexp
  | DEempty (* empty expression *)
  | DEenmac of (* macro encoding *)
      dexp
  | DEexi of (* existential sum *)
      sexparg * dexp
  | DEextval of (* external code *)
      sexp * string
  | DEfix of (* fixed point *)
      did * farg list * sexp option * efftags option * dexp
  | DEfloat of (* dynamic floats *)
      string
  | DEfold of (* folding recursive type *)
      squal_opt_id * dexp
  | DEfoldat of (* fold at a given address *)
      sexparg list * dexp
  | DEfreeat of (* fold at a given address *)
      sexparg list * dexp
  | DEfor of (* for-loop *)
      loopinv option * (dexp * dexp * dexp) (* ini, test, pos *) * dexp (*body*)
  | DEid of (* identifier *)
      did
  | DEif of (* dynamic conditionals *)
      statype option * dexp * dexp * dexp option
  | DEint of (* dynamic integers *)
      intkind * intinf
  | DElam of (* linear/nonlinear lambda-abstraction *)
      bool (* linear *) * farg list * sexp option * efftags option * dexp
  | DElampara of (* parametric static lambda abstraction *)
      squas * sexp option * dexp
  | DElet of (* dynamic let-expression *)
      dec list * dexp
  | DElist of (* dexp list *)
      int_dexp_list
  | DEloopexn of int
      (* break: 0 and continue: 1 *)
  | DElst of (* for dexp lists *)
      dexp list      
  | DEmod of (* for modules *)
      moditemdec list
  | DEop of did (* for dynamic identifiers *)
  | DEparse of (* parse string *)
      id (* the name of parse fun *) * string (* input *)
  | DEptrof of (* taking the address of *)
      dexp
  | DEqid of (* qualified dynamic identifiers *)
      dqual_id
  | DEraise of (* raised exception *)
      dexp
  | DErec of (* dynamic record *)
      bool (* is_flat *) * labdexp list
  | DEsel of (* dot selection *)
      int (* is_ptr *) * label option * dexp list list option
  | DEseq of (* sequencing *)
      dexp list
  | DEsexparg of (* static expression sequence *)
      sexparg
  | DEsif of (* static conditionals *)
      sexp * dexp * dexp
  | DEstring of (* dynamic strings *)
      string
  | DEstruct of (* structure *)
      labdexp list
  | DEtemplate of (* template initialization *)
      dqual_opt_id * (sexp list) list
  | DEtop (* uninitialized value *)
  | DEtrywith of (* try-expression *)
      dexp * cla list
  | DEtup of (* dynamic tuple expression *)
      bool (* is_flat *) * int_dexp_list
  | DEunfold of (* unfolding recursive type *)
      squal_opt_id * dexp
  | DEviewat of (* view at a given address *)
      dexp
  | DEwhere of (* where clause *)
      dexp * dec list
  | DEwhile of (* while-loop *)
      loopinv option * dexp (*test*) * dexp (*body*)

and dec_srtdef = {
  dec_srtdef_loc: Ats_location.location;
  dec_srtdef_name: srt_id;
  dec_srtdef_arg: (srtarg list) list;
  dec_srtdef_def: srtext;
}

and datsrtcon = {
  datsrtcon_loc: Ats_location.location;
  datsrtcon_name: sid;
  datsrtcon_arg: srt option;
}

and dec_datsrt = {
  dec_datsrt_loc: Ats_location.location;
  dec_datsrt_name: srt_id;
  dec_datsrt_arg: (srtarg list) option;
  dec_datsrt_con: datsrtcon list;
}

and dec_stacon = {
  dec_stacon_loc: Ats_location.location;
  dec_stacon_name: sid;
  dec_stacon_arg: (datarg list) option;
  dec_stacon_def: sexp option;
}

and dec_stacst = {
  dec_stacst_loc: Ats_location.location;
  dec_stacst_name: sid;
  dec_stacst_arg: (srt list) list;
  dec_stacst_sort: srt;
}

and dec_stavar = {
  dec_stavar_loc: Ats_location.location;
  dec_stavar_name: sid;
  dec_stavar_sort: srt;
}

and dec_dyncst = {
  dec_dyncst_loc: Ats_location.location;
  dec_dyncst_name: did;
  dec_dyncst_filename: Fil.filename;
  dec_dyncst_arg: farg0 list;
  dec_dyncst_eff: efftags option;
  dec_dyncst_res: sexp;
  dec_dyncst_extdef: string option;
}

and dec_sexpdef = {
  dec_sexpdef_loc: Ats_location.location;
  dec_sexpdef_name: sid;
  dec_sexpdef_arg: (sarg list) list;
  dec_sexpdef_res: srt option;
  dec_sexpdef_def: sexp;
}

and dec_exn = {
  dec_exn_loc: Ats_location.location;
  dec_exn_name: did;
  dec_exn_filename: Fil.filename;
  dec_exn_qua: squas list;
  dec_exn_arg: sexp option;
}

and datarg =
  | DATARGsrt of srtpol
  | DATARGidsrt of sid * srtpol

and datcon = {
  datcon_loc: Ats_location.location;
  datcon_name: did;
  datcon_qua: squas list;
  datcon_arg: sexp option;
  datcon_ind: (sexp list) option;
}

and dec_dat = {
  dec_dat_loc: Ats_location.location;
  dec_dat_name: sid;
  dec_dat_filename: Fil.filename;
  dec_dat_arg: (datarg list) option;
  dec_dat_con: datcon list;
}

and mtitemdec_node =
  | MTIDsta of sid * srt
  | MTIDval of
      bool (* is_prop *) * did * farg0 list * efftags option * sexp
  | MTIDsexpdefs of dec_sexpdef list
  | MTIDtypedefs of dec_sexpdef list
  | MTIDtypedefrecs of dec_sexpdef list

and mtitemdec = {
  mtitemdec_loc: Ats_location.location;
  mtitemdec_node: mtitemdec_node;
}

and dec_modtype = {
  dec_modtype_loc: Ats_location.location;
  dec_modtype_name: sid;
  dec_modtype_def: mtitemdec list;
}

and dec_sasp = {
  dec_sasp_loc: Ats_location.location;
  dec_sasp_name: squal_opt_id;
  dec_sasp_arg: (sarg list) list;
  dec_sasp_res: srt option;
  dec_sasp_def: sexp;
}

and dec_macdef = {
  dec_macdef_loc: Ats_location.location;
  dec_macdef_name: did;
  dec_macdef_arg: (did list) list;
  dec_macdef_def: dexp;
}

and dec_var = {
  dec_var_loc: Ats_location.location;
  dec_var_name: did;
  dec_var_type: sexp option;
  dec_var_ini: dexp option;
}

and dec_val = {
  dec_val_loc: Ats_location.location;
  dec_val_pat: pat;
  dec_val_def: dexp;
  dec_val_ann: (sexp * srt) option;
}

and dec_fun = {
  dec_fun_loc: Ats_location.location;
  dec_fun_name: did;
  dec_fun_arg: farg list;
  dec_fun_res: (efftags option * sexp) option;
  dec_fun_body: dexp;
  dec_fun_ann: (sexp * srt) option; (* withtype clause *)
}

and moditemdec = (* type for module item declaration *)
  { moditemdec_loc: Ats_location.location; moditemdec_node: moditemdec_node; }

and moditemdec_node =
  | MIDfixity of fixity * id list
  | MIDnonfix of id list
  | MIDsexpdefs of srt option * dec_sexpdef list
  | MIDtypedefrecs of dec_sexpdef list
  | MIDvals of valkind * dec_val list
  | MIDvalrecs of dec_val list
  | MIDfuns of funkind * srt_id list * dec_fun list

and dec_impl = {
  dec_impl_loc: Ats_location.location;
  dec_impl_name: dqual_opt_id;
  dec_impl_tmparg: sexp list list;
  dec_impl_arg: farg list;
  dec_impl_res: sexp option;
  dec_impl_body: dexp;
}

and datakind = DKprop | DKtype | DKview | DKviewtype

and funkind =
  | FKfn (* non-recursive *)
  | FKfnt (* tail-recursive *)
  | FKfun (* general recursive *)
  | FKprfn (* non-recursive *)
  | FKprfun (* general recursive *)

and valkind = VKval | VKvalminus | VKvalplus | VKprval

and dcstkind = DCKval | DCKfun | DCKcastfn | DCKprval | DCKprfun | DCKpraxi

and dec_node =
    (* fixity declaration *)
  | DCfixity of fixity * id list (* fixity introduction *)
  | DCnonfix of id list (* fixity elimination *)
    (* overloaded symbol delcaration *)
  | DCsymintr of did list (* overloaded symbol introduction *)
  | DCsymelim of did list (* overloaded symbol elimination *)
    (* static declaration and assumption *)
  | DCsrtdefs of dec_srtdef list (* (extended) sort definition *)
  | DCdatsrts of dec_datsrt list (* datasort declaration *)
  | DCstacons of srt * dec_stacon list (* static constructor *)
  | DCstacsts of dec_stacst list (* static constant *)
  | DCstavars of dec_stavar list (* static existential variable *)
  | DCextype of (* external type *)
      string (* extype name *) * sexp (* extype definition *)
  | DCextval of (* external value *)
      string (* extval name *) * dexp (* extval definition *)
  | DCdyncsts of
      dcstkind * (* dyncst kind: val, prval, and praxi *)
      squas list * (* decarg *)
      dec_dyncst list (* dynamic constants *)
    (* static declaration *)
  | DCsexpdefs of srt option * dec_sexpdef list (* static expression definition *)
  | DCtypedefrecs of dec_sexpdef list (* recursive type definition *)
  | DCviewtypedefrecs of dec_sexpdef list (* recursive viewtype definition *)
  | DCsasps of dec_sasp list (* static assumption *)
  | DCexns of dec_exn list (* exception constructor declaration *)
    (* data declaration *)
  | DCdata of datakind * srt_id list * dec_dat list * dec_sexpdef list
  | DCmodtypes of bool (* prop or type *) * dec_modtype list
    (* ****** ****** *)
  | DCe0xpdef of id * e0xp option
  | DCe0xperr of e0xp
  | DCe0xpprt of e0xp
  | (* overload declaration *)
    DCoverload of did * dqual_opt_id
    (* macro declaration *)
  | DCmacdefs of bool * dec_macdef list (* bool: simple or not *)
    (* variable declaration *)
  | DCvars of bool (* is_stack *) * dec_var list (* dynamic variable declaration *)
    (* proof/value declaration *)
  | DCvals of valkind * dec_val list (* dynamic value declaration *)
  | DCvalpars of dec_val list (* dynamic parallel value declaration *)
  | DCvalrecs of dec_val list (* dynamic recursive value declaration *)
    (* dynamic function declaration *)
  | DCfuns of funkind * srt_id list * squas list * dec_fun list
    (* local declaration *)
  | DClocal of dec list * dec list
    (* dynamic implementations *)
  | DCimpls of sarg list list * dec_impl list
    (* static loading *)
  | DCinclude of int(*0:sta/1:dyn*) * Ats_filename.filename
  | DCstaload of sid option (* open or closed *) * Ats_filename.filename
    (* dynamic loading *)
  | DCdynload of Ats_filename.filename
  | (* if ... then ... else *)
    DCifthenelse of (e0xp * dec list) list
  | DCextern of (* external code *)
      int (* position: 0/1 : top/end *) * string (* code *)

(* ****** ****** *)

let dexp_ann_type (de: dexp) (se: sexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEann_type (de, se);
}

let dexp_app (de_fun: dexp) (de_arg: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEapp (de_fun, de_arg);
}

let dexp_apps de des: dexp = 
  let rec aux de1 de2: dexp =
    let loc = Loc.combine (de1.dexp_loc) (de2.dexp_loc) in
      { dexp_loc= loc; dexp_node= DEapp (de1, de2); }

  and aux_list de1 (des2: dexp list): dexp =
    match des2 with
      | [] -> de1
      | de2 :: des2 -> aux_list (aux de1 de2) des2 in

    aux_list de des
(* end of [dexp_apps] *)

let dexp_arr (se: sexp) (des: dexp list): dexp = {
  dexp_loc= getloc (); dexp_node= DEarr (se, des);
}

let dexp_arrsub (root: dexp) (offset: (dexp list) list): dexp = {
  dexp_loc= getloc (); dexp_node= DEarrsub (root, offset)
}

let dexp_case (i: int)
  (osty: statype option) (de: dexp) (cls: cla list): dexp = {
  dexp_loc= getloc (); dexp_node= DEcase (i, osty, de, cls)
}

let dexp_char (c: char): dexp = {
  dexp_loc= getloc (); dexp_node= DEchar c;
}

let dexp_dynload (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEdynload de
}

let dexp_effmask (eff: effect) (de: dexp) = {
  dexp_loc= getloc (); dexp_node= DEeffmask (eff, de)
}

let dexp_exi (sa: sexparg) (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEexi (sa, de);
}

let dexp_extval (se: sexp) (code: string) = {
  dexp_loc= getloc (); dexp_node= DEextval (se, code)
}

let dexp_empty (): dexp = {
  dexp_loc= getloc (); dexp_node= DEempty;
}

let dexp_enmac de: dexp = {
  dexp_loc= getloc (); dexp_node= DEenmac de;
}

let dexp_crypt knd de: dexp = {
  dexp_loc= getloc (); dexp_node= DEcrypt (knd, de)
}

let dexp_delay de: dexp = {
  dexp_loc= getloc (); dexp_node= DEdelay de;
}

let dexp_demac de: dexp = {
  dexp_loc= getloc (); dexp_node= DEdemac de;
}

let dexp_fix (name: did)
  (arg: farg list) (res: sexp option)
  (oeff: efftags option) (body: dexp): dexp = {
    dexp_loc= getloc (); dexp_node= DEfix (name, arg, res, oeff, body);
  }
(* end of [dexp_fix] *)

let dexp_float (f: string): dexp = {
  dexp_loc= getloc (); dexp_node= DEfloat f;
}

let dexp_fold (name: squal_opt_id) de: dexp = {
  dexp_loc= getloc (); dexp_node= DEfold (name, de)
}

let dexp_foldat (sas: sexparg list) (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEfoldat (sas, de);
}

let dexp_freeat (sas: sexparg list) (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEfreeat (sas, de);
}

let dexp_for (oinv: loopinv option) (itp: dexp * dexp * dexp) (body: dexp)
  : dexp = { (* <itp> : ini_test_post *)
    dexp_loc= getloc (); dexp_node= DEfor (oinv, itp, body);
  }
(* end of [dexp_for] *)

let dexp_id (name: did): dexp =
  if did_is_qmark name then begin
    { dexp_loc= getloc (); dexp_node= DEtop; }
  end else begin
    { dexp_loc= getloc (); dexp_node= DEid name; }
  end
(* end of [dexp_id] *)

let dexp_if (osty: statype option)
  (de1: dexp) (de2: dexp) (ode3: dexp option): dexp = {
  dexp_loc= getloc (); dexp_node= DEif (osty, de1, de2, ode3);
} (* end of [dexp_if] *)

let dexp_int (ik: intkind) (i: intinf): dexp = {
  dexp_loc= getloc (); dexp_node= DEint (ik, i);
}

let dexp_int_0 (i: intinf): dexp = {
  dexp_loc=getloc (); dexp_node= DEint (IKint, i);
}

let dexp_lam (is_lin: bool)
  (args: farg list) (res: sexp option)
  (oeff: efftags option) (body: dexp): dexp = {
    dexp_loc= getloc ();
    dexp_node= DElam (is_lin, args, res, oeff, body);
  }
(* end of [dexp_lam] *)

let dexp_lampara loc
  (sqs: squas) (res: sexp option) (body: dexp): dexp = {
    dexp_loc= loc; dexp_node= DElampara (sqs, res, body);
  }
(* end of [dexp_lampara] *)

let dexp_lamparas_errmsg loc = begin
  Printf.eprintf
    "%a: parametric lambda abstraction can only be over static variables.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [dexp_lamparas_errmsg] *)

let dexp_lamparas
  (fargs0: farg list) (se_res: sexp option) (de_body: dexp): dexp =
  let loc = getloc () in
  let rec aux (farg0: farg) (fargs0: farg list): dexp =
    let sqs = match farg0.farg_node with
      | FARGsta1 sqs -> sqs
      | _ -> dexp_lamparas_errmsg farg0.farg_loc in
      match fargs0 with
	| farg :: fargs -> dexp_lampara loc sqs None (aux farg fargs)
	| [] -> dexp_lampara loc sqs se_res de_body in
    match fargs0 with [] -> de_body | farg :: fargs -> aux farg fargs
(* end of [dexp_lamparas] *)

let dexp_let (ds: dec list) de: dexp = {
  dexp_loc= getloc (); dexp_node= DElet (ds, de);
}

let dexp_list des: dexp =
  let loc = getloc () in
  let ndes = (0, des) in
    { dexp_loc= loc; dexp_node= DElist ndes; }
(* end of [dexp_list] *)

let dexp_list2 (des1: dexp list) (des2: dexp list) =
  let loc = getloc () in
  let ndes = (List.length des1, des1 @ des2) in
    { dexp_loc= loc; dexp_node= DElist ndes; }
(* end of [dexp_list2] *)

let dexp_loopexn (i: int) = {
  dexp_loc= getloc (); dexp_node= DEloopexn i;
}

let dexp_lst des: dexp = {
  dexp_loc= getloc (); dexp_node= DElst des;
}

let dexp_mod (mids: moditemdec list): dexp = {
  dexp_loc= getloc (); dexp_node= DEmod mids;
}

let dexp_op (name: did): dexp = {
  dexp_loc= getloc (); dexp_node= DEop name
}

let dexp_parse (parfun_name: string) (input: string): dexp =
  let parfun_id = make_id_with_string parfun_name in {
      dexp_loc= getloc ();
      dexp_node= DEparse (parfun_id, input);
    }
(* end [dexp_parse] *)

let dexp_ptrof (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEptrof de;
}

let dexp_qid (name: dqual_id): dexp = {
  dexp_loc= getloc (); dexp_node= DEqid name;
}

let dexp_raise (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEraise (de);
}

let dexp_rec (is_flat: bool) ldes: dexp = {
  dexp_loc= getloc (); dexp_node= DErec (is_flat, ldes);
}

(* ****** ****** *)

let dexp_sel_lab (is_ptr: int) (l: label): dexp =
  { dexp_loc= getloc (); dexp_node= DEsel (is_ptr, Some l, None); }

let dexp_sel_ind (is_ptr: int) (ind: dexp list list): dexp =
  { dexp_loc= getloc (); dexp_node= DEsel (is_ptr, None, Some ind); }

let dexp_sel_lab_ind
  (is_ptr: int) (l: label) (ind: dexp list list ): dexp = {
  dexp_loc= getloc (); dexp_node= DEsel (is_ptr, Some l, Some ind)
} (* end of [dexp_sel_lab_ind] *)

(* ****** ****** *)

let dexp_seq des: dexp = {
  dexp_loc= getloc (); dexp_node= DEseq des;
}

let dexp_sexparg (sa: sexparg): dexp = {
  dexp_loc= getloc (); dexp_node= DEsexparg sa;
}

let dexp_sif (sp1: sexp) (de2: dexp) (de3: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEsif (sp1, de2, de3);
}

let dexp_string (s: string): dexp = {
  dexp_loc= getstrloc (); dexp_node= DEstring s;
}

let dexp_struct (ldes: labdexp list): dexp = {
  dexp_loc= getloc (); dexp_node= DEstruct ldes;
}

let dexp_template
  (id: dqual_opt_id) (sess: sexp list list): dexp = {
    dexp_loc= getloc (); dexp_node= DEtemplate (id, sess);
  }
(* end of [dexp_template] *)

let dexp_trywith (de: dexp) (cs: cla list): dexp = {
  dexp_loc= getloc (); dexp_node= DEtrywith (de, cs);
} (* end of [dexp_trywith] *)

let dexp_tup (is_flat: bool) (des: dexp list): dexp =
  let loc = getloc () in
  let ndes = (0, des) in
    { dexp_loc= loc; dexp_node= DEtup (is_flat, ndes); }
(* end of [dexp_tup] *)

let dexp_tup2
  (is_flat: bool) (des1: dexp list) (des2: dexp list) =
  let loc = getloc () in
  let ndes = (List.length des1, des1 @ des2) in
    { dexp_loc= loc; dexp_node= DEtup (is_flat, ndes); }
(* end of [dexp_tup2] *)

let dexp_unfold (name: squal_opt_id) de: dexp = {
  dexp_loc= getloc (); dexp_node= DEunfold (name, de);
}

let dexp_viewat (de: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEviewat de;
}

let dexp_where de (ds: dec list): dexp = {
  dexp_loc= getloc (); dexp_node= DEwhere (de, ds);
}

let dexp_while (oinv: loopinv option) (test: dexp) (body: dexp): dexp = {
  dexp_loc= getloc (); dexp_node= DEwhile (oinv, test, body);
}

(* ****** ****** *)

let cla (pt, gua) (isseq: bool) (isneg: bool) (body: dexp): cla = {
  cla_loc= getloc ();
  cla_pat= pt;
  cla_gua= gua;
  cla_isseq= isseq;
  cla_isneg= isneg;
  cla_body= body;
} (* end of [cla] *)

(* ****** ****** *)

let loopinv
  (qua: squas option) (met: (sexp list) option)
  (arg: statype_body) (res: statype option): loopinv = {
  loopinv_loc= getloc ();
  loopinv_qua= qua;
  loopinv_met= met;
  loopinv_arg= arg;
  loopinv_res= res;
} (* end of [loopinv] *)

(* ****** ****** *)

let dec_infix (p: prec) (a: assoc) (ids: id list): dec =
  { dec_loc= getloc (); dec_node= DCfixity (Infix (p, a), ids); }

let dec_postfix (p: prec) (ids: id list): dec =
  { dec_loc= getloc (); dec_node= DCfixity (Postfix p, ids); }

let dec_prefix (p: prec) (ids: id list): dec =
  { dec_loc= getloc (); dec_node= DCfixity (Prefix p, ids); }

let dec_nonfix (ids: id list): dec =
  { dec_loc= getloc (); dec_node= DCnonfix ids; }

(* ****** ****** *)

let dec_symintr (ids: id list): dec =
  { dec_loc= getloc (); dec_node= DCsymintr ids; }

let dec_symelim (ids: id list): dec =
  { dec_loc= getloc (); dec_node= DCsymelim ids; }

(* ****** ****** *)

let dec_srtdef (name: srt_id) (arg: (srtarg list) list) (def: srtext)
  : dec_srtdef = {
  dec_srtdef_loc= getloc ();
  dec_srtdef_name= name;
  dec_srtdef_arg= arg;
  dec_srtdef_def= def;
} (* end of [dec_srtdef] *)

let dec_srtdefs (ds: dec_srtdef list): dec = {
  dec_loc= getloc (); dec_node= DCsrtdefs ds;
} (* end of [dec_srtdefs] *)

let datsrtcon (name: sid) (arg: srt option): datsrtcon = {
  datsrtcon_loc= getloc ();
  datsrtcon_name= name;
  datsrtcon_arg= arg;
} (* end of [datsrtcon] *)

let dec_datsrt (name: srt_id)
  (arg: (srtarg list) option) (con: datsrtcon list): dec_datsrt = {
    dec_datsrt_loc= getloc ();
    dec_datsrt_name= name;
    dec_datsrt_arg= arg;
    dec_datsrt_con= con;
} (* end of [dec_datsrt] *)

let dec_datsrts (ds: dec_datsrt list): dec = {
  dec_loc= getloc (); dec_node= DCdatsrts ds;
} (* end of [dec_datsrts] *)

(* ****** ****** *)

let dec_stacon (name: sid) (arg: (datarg list) option) (def: sexp option)
  : dec_stacon = {
    dec_stacon_loc= getloc ();
    dec_stacon_name= name;
    dec_stacon_arg= arg;
    dec_stacon_def= def;
} (* end of [dec_stacon] *)

let dec_stacons
  (loc: location) (st: srt) (ds: dec_stacon list): dec = {
  dec_loc= loc; dec_node= DCstacons (st, ds);
} (* end of [dec_stacons] *)

let dec_absprops
  (ps: (sid * (datarg list) option * sexp option) list): dec =
  let loc = getloc () in
  let f (sid, arg, def): dec_stacon = dec_stacon sid arg def in
    dec_stacons loc srt_prop (List.map f ps)
(* end of [dec_absprops] *)

let dec_abst0ypes
  (ps: (sid * (datarg list) option * sexp option) list): dec =
  let loc = getloc () in
  let f (sid, arg, def): dec_stacon = dec_stacon sid arg def in
    dec_stacons loc srt_t0ype (List.map f ps)
(* end of [dec_abst0ypes] *)

let dec_abstypes
  (ps: (sid * (datarg list) option * sexp option) list): dec =
  let loc = getloc () in
  let f (sid, arg, def): dec_stacon =
    let () = match def with
      | None -> ()
      | Some _ -> begin
	  PR.eprintf "%a: abstype cannot have external definition.\n"
	    Loc.fprint loc;
	  Err.abort ()
	end in
      dec_stacon sid arg def in
    dec_stacons loc srt_type (List.map f ps)
(* end of [dec_abstypes] *)

let dec_absviews
  (ps: (sid * (datarg list) option * sexp option) list): dec =
  let loc = getloc () in
  let f (sid, arg, def): dec_stacon = dec_stacon sid arg def in
    dec_stacons loc srt_view (List.map f ps)
(* end of [dec_absviews] *)

let dec_absviewt0ypes
  (ps: (sid * (datarg list) option * sexp option) list): dec =
  let loc = getloc () in
  let f (sid, arg, def): dec_stacon = dec_stacon sid arg def in
    dec_stacons loc srt_viewt0ype (List.map f ps)
(* end of [dec_absviewt0ypes] *)

let dec_absviewtypes
  (ps: (sid * (datarg list) option * sexp option) list): dec =
  let loc = getloc () in
  let f (sid, arg, def): dec_stacon =
    let () = match def with
      | None -> ()
      | Some _ -> begin
	  PR.eprintf "%a: absviewtype cannot have external definition.\n"
	    Loc.fprint loc;
	  Err.abort ()
	end in
      dec_stacon sid arg def in
    dec_stacons loc srt_viewtype (List.map f ps)
(* end of [dec_absviewtypes] *)

(* ****** ****** *)

let dec_stacst
  (name: sid) (arg: (srt list) list) (st: srt): dec_stacst = {
    dec_stacst_loc= getloc ();
    dec_stacst_name= name;
    dec_stacst_arg= arg;
    dec_stacst_sort= st;
  }

let dec_stacsts (ds: dec_stacst list): dec = {
  dec_loc= getloc (); dec_node= DCstacsts ds;
}

(* ****** ****** *)

let dec_stavar (name: sid) (st: srt): dec_stavar = {
  dec_stavar_loc= getloc (); dec_stavar_name= name; dec_stavar_sort= st;
}

let dec_stavars (ds: dec_stavar list): dec = {
  dec_loc= getloc (); dec_node= DCstavars ds;
}

(* ****** ****** *)

let dec_extype (name: string) (def: sexp): dec = {
  dec_loc= getloc (); dec_node= DCextype (name, def);
}

let dec_extval (name: string) (def: dexp): dec = {
  dec_loc= getloc (); dec_node= DCextval (name, def);
}

(* ****** ****** *)

let datakind_is_proof (dtk: datakind): bool =
  match dtk with
    | DKprop -> true | DKview -> true
    | DKtype -> false | DKviewtype -> false

(* ****** ****** *)

let dcstkind_is_fun (dck: dcstkind): bool =
  match dck with DCKfun -> true | DCKprfun | _ -> false
(* end of [dcstkind_is_fun] *)

let dcstkind_is_castfn (dck: dcstkind): bool =
  match dck with DCKcastfn -> true | _ -> false
(* end of [dcstkind_is_castfn] *)

let dcstkind_is_proof (dck: dcstkind): bool = begin
  match dck with DCKprval -> true | DCKprfun -> true | DCKpraxi -> true | _ -> false
end (* end of [dcstkind_is_proof] *)

let dcstkind_is_axiom (dck: dcstkind): bool =
  match dck with DCKpraxi -> true | _ -> false

let dec_dyncst (name: did) (arg: farg0 list)
  (effs: efftags option) (res: sexp) (ext: string option): dec_dyncst = {
    dec_dyncst_loc= getloc ();
    dec_dyncst_name= name;
    dec_dyncst_filename= Fil.filename_get ();
    dec_dyncst_arg= arg;
    dec_dyncst_eff= effs;
    dec_dyncst_res= res;
    dec_dyncst_extdef= ext;
  }

let dec_dyncsts
  (dck: dcstkind) (sqss: squas list) (ds: dec_dyncst list): dec =
  { dec_loc= getloc (); dec_node= DCdyncsts (dck, sqss, ds) }

(* ****** ****** *)

let dec_sexpdef (name: sid) (arg: (sarg list) list) (res: srt option) (def: sexp)
  : dec_sexpdef = {
    dec_sexpdef_loc= getloc ();
    dec_sexpdef_name= name;
    dec_sexpdef_arg= arg;
    dec_sexpdef_res= res;
    dec_sexpdef_def= def;
  }

let dec_sexpdefs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCsexpdefs (None, ds);
}

let dec_propdefs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCsexpdefs (Some srt_prop, ds);
}

let dec_typedefs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCsexpdefs (Some srt_t0ype, ds);
}

let dec_typedefrecs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCtypedefrecs ds;
}

let dec_viewdefs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCsexpdefs (Some srt_view, ds);
}

let dec_viewtypedefs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCsexpdefs (Some srt_viewt0ype, ds);
}

let dec_viewtypedefrecs (ds: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCviewtypedefrecs ds;
}

(* ****** ****** *)

let datarg_srt (stp: srtpol): datarg = DATARGsrt stp

let datarg_id_srt (name: sid) (stp: srtpol): datarg = DATARGidsrt (name, stp)

let datcon (name: did) (qua: squas list)
  (arg: sexp option) (ind: (sexp list) option): datcon = {
    datcon_loc= getloc ();
    datcon_name= name;
    datcon_qua= qua;
    datcon_arg= arg;
    datcon_ind= ind;
  }

let dec_dat (name: sid) (arg: (datarg list) option) (con: datcon list)
  : dec_dat = {
  dec_dat_loc= getloc ();
  dec_dat_name= name;
  dec_dat_filename= Fil.filename_get ();
  dec_dat_arg= arg;
  dec_dat_con= con;
}

let dec_data ((dtk: datakind), (starg: srtarg list))
   (ds1: dec_dat list) (ds2: dec_sexpdef list): dec = {
  dec_loc= getloc (); dec_node= DCdata (dtk, starg, ds1, ds2)
}

let dec_exn (name: did) (qua: squas list) (arg: sexp option): dec_exn = {
  dec_exn_loc= getloc ();
  dec_exn_name= name;
  dec_exn_filename= Fil.filename_get ();
  dec_exn_qua= qua;
  dec_exn_arg= arg;
}

let dec_exns (ds: dec_exn list): dec = {
  dec_loc= getloc ();
  dec_node= DCexns ds;
}

let mtitemdec_sta (name: sid) (st: srt): mtitemdec = {
  mtitemdec_loc= getloc (); mtitemdec_node= MTIDsta (name, st)
}

let mtitemdec_val (is_prop: bool)
  (name: did) (arg: farg0 list) (eff: efftags option) (res: sexp)
  : mtitemdec = {
    mtitemdec_loc= getloc ();
    mtitemdec_node= MTIDval (is_prop, name, arg, eff, res);
  }

let mtitemdec_sexpdefs (ds: dec_sexpdef list): mtitemdec = {
  mtitemdec_loc= getloc (); mtitemdec_node= MTIDsexpdefs ds;
}

let mtitemdec_typedefs (ds: dec_sexpdef list): mtitemdec = {
  mtitemdec_loc= getloc (); mtitemdec_node= MTIDtypedefs ds;
}

let mtitemdec_typedefrecs (ds: dec_sexpdef list): mtitemdec = {
  mtitemdec_loc= getloc (); mtitemdec_node= MTIDtypedefrecs ds;
}

let dec_modtype (name: sid) (def: mtitemdec list): dec_modtype = {
  dec_modtype_loc= getloc ();
  dec_modtype_name= name;
  dec_modtype_def= def;
}

let dec_modtypes (is_prop: bool) (ds: dec_modtype list): dec = {
  dec_loc= getloc (); dec_node= DCmodtypes (is_prop, ds)
}

let dec_sasp (name: squal_opt_id)
  (arg: (sarg list) list) (res: srt option) (def: sexp): dec_sasp = {
    dec_sasp_loc= getloc ();
    dec_sasp_name= name;
    dec_sasp_arg= arg;
    dec_sasp_res= res;
    dec_sasp_def= def;
  }

let dec_sasps (ds: dec_sasp list): dec = {
  dec_loc= getloc (); dec_node= DCsasps ds;
}

(* ****** ****** *)

let dec_overload (name: did) (id: dqual_opt_id) =
  { dec_loc= getloc (); dec_node= DCoverload (name, id); }

let dec_overload_brackets (id: dqual_opt_id) =
  let name = make_did_with_symbol Sym.symBRACKETS in {
      dec_loc= getloc (); dec_node= DCoverload (name, id);
    }

(* ****** ****** *)

let dec_macdef (name: did) (arg: (did list) list) (def: dexp): dec_macdef = {
  dec_macdef_loc= getloc ();
  dec_macdef_name= name;
  dec_macdef_arg= arg;
  dec_macdef_def= def;
}

let dec_macdefs (is_simple: bool) (ds: dec_macdef list): dec = {
  dec_loc= getloc (); dec_node= DCmacdefs (is_simple, ds);
}

let dec_var (name: did) (ose: sexp option) (ode: dexp option): dec_var = {
  dec_var_loc= getloc ();
  dec_var_name= name;
  dec_var_type= ose;
  dec_var_ini= ode;
}

let dec_vars (is_stack: bool) (ds: dec_var list): dec = {
  dec_loc= getloc (); dec_node= DCvars (is_stack, ds);
}

(* ****** ****** *)

let dec_val pt (def: dexp) (ann: (sexp * srt) option): dec_val = {
  dec_val_loc= getloc ();
  dec_val_pat= pt;
  dec_val_def= def;
  dec_val_ann= ann;
}

let valkind_is_proof (vk: valkind): bool =
  match vk with VKprval -> true | _ -> false

let valkind_is_not_proof (vk: valkind): bool =
  match vk with VKprval -> false | _ -> true

let valkind_is_exhaustive (vk: valkind): bool =
  match vk with VKvalplus -> true | _ -> false

let sign_of_valkind (vk: valkind): int = match vk with
  | VKval -> 0 | VKvalminus -> -1 | VKvalplus -> 1 | VKprval -> 1

let dec_vals (vk: valkind) (ds: dec_val list): dec = {
  dec_loc= getloc (); dec_node= DCvals (vk, ds);
}

let dec_valpars (ds: dec_val list): dec = {
  dec_loc= getloc (); dec_node= DCvalpars ds;
}

let dec_valrecs (ds: dec_val list): dec = {
  dec_loc= getloc (); dec_node= DCvalrecs ds;
}

let dec_fun (name: did)
  (arg: farg list) (res: (efftags option * sexp) option)
  (body: dexp) (ann: (sexp * srt) option): dec_fun = {
  dec_fun_loc= getloc ();
  dec_fun_name= name;
  dec_fun_arg= arg;
  dec_fun_res= res;
  dec_fun_body= body;
  dec_fun_ann= ann;
}

let funkind_is_recursive (fk: funkind): bool = match fk with
  | FKfn -> false
  | FKfnt -> true
  | FKfun -> true
  | FKprfn -> false
  | FKprfun -> true

let funkind_is_recursive_tail (fk: funkind): bool =
  match fk with FKfnt -> true | _ -> false

let funkind_is_proof (fk: funkind): bool = match fk with
  | FKfn -> false
  | FKfnt -> false
  | FKfun -> false
  | FKprfn -> true
  | FKprfun -> true

let dec_funs
  ((fk: funkind), (starg: srtarg list))
  (decarg: squas list) (ds: dec_fun list): dec = {
    dec_loc= getloc ();
    dec_node= DCfuns (fk, starg, decarg, ds);
  }

let dec_local (ds1: dec list) (ds2: dec list): dec =
  { dec_loc= getloc (); dec_node= DClocal (ds1, ds2); }

let dec_impl
  ((name: dqual_opt_id), (tmparg: sexp list list))
  (arg: farg list) (res: sexp option) (body: dexp): dec_impl = {
    dec_impl_loc= getloc ();
    dec_impl_name= name;
    dec_impl_tmparg= tmparg;
    dec_impl_arg= arg;
    dec_impl_res= res;
    dec_impl_body= body;
  }

let dec_impls
  (decarg: sarg list list) (ds: dec_impl list): dec = {
    dec_loc= getloc (); dec_node= DCimpls (decarg, ds);
  }

let dec_e0xpdef (id: id) (oe: e0xp option): dec = {
  dec_loc= getloc ();
  dec_node= DCe0xpdef (id, oe);
}

let dec_e0xperr (e: e0xp): dec = {
  dec_loc= getloc ();
  dec_node= DCe0xperr e;
}

let dec_e0xpprt (e: e0xp): dec = {
  dec_loc= getloc ();
  dec_node= DCe0xpprt e;
}

let dec_ifthenelse (edss: (e0xp * dec list) list): dec = {
  dec_loc= getloc ();
  dec_node= DCifthenelse edss;
}

(* ****** ****** *)

type filename = Fil.filename

let dec_include (stadyn: int) (fname: filename): dec =
  { dec_loc= getloc (); dec_node= DCinclude (stadyn, fname); }

let dec_staload (osid: sid option) (fname: filename): dec =
  { dec_loc= getloc (); dec_node= DCstaload (osid, fname); }

let dec_dynload (fname: filename): dec =
  { dec_loc= getloc (); dec_node= DCdynload fname; }

(* ****** ****** *)

let dec_extern ((position: int), (code: string)): dec =
  { dec_loc= getextloc (); dec_node= DCextern (position, code); }

(* ****** ****** *)

let moditemdec_infix (p: prec) (a: assoc) (ids: id list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDfixity (Infix (p, a), ids); }

let moditemdec_postfix (p: prec) (ids: id list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDfixity (Postfix p, ids); }

let moditemdec_prefix (p: prec) (ids: id list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDfixity (Prefix p, ids); }

let moditemdec_nonfix (ds: id list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDnonfix ds; }

let moditemdec_sexpdefs (ds: dec_sexpdef list): moditemdec = {
  moditemdec_loc= getloc ();
  moditemdec_node= MIDsexpdefs (None, ds);
}

let moditemdec_typedefs (ds: dec_sexpdef list): moditemdec = {
  moditemdec_loc= getloc ();
  moditemdec_node= MIDsexpdefs (Some srt_type, ds);
}

let moditemdec_typedefrecs (ds: dec_sexpdef list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDtypedefrecs ds; }

let moditemdec_vals (vk: valkind) (ds: dec_val list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDvals (vk, ds); }

let moditemdec_valrecs (ds: dec_val list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDvalrecs ds; }

let moditemdec_funs
  ((fk: funkind), (starg: srtarg list))
  (ds: dec_fun list): moditemdec =
  { moditemdec_loc= getloc (); moditemdec_node= MIDfuns (fk, starg, ds); }

let dec_mod (name: did)
  (arg: farg list) (res: (efftags option * sexp) option)
  (body: moditemdec list) (ann: (sexp * srt) option): dec_fun =
  dec_fun name arg res (dexp_mod body) ann

let dec_mods (decarg: squas list) (ds: dec_fun list): dec = {
  dec_loc= getloc (); dec_node= DCfuns (FKfun, [], decarg, ds);
}

(* ****** ****** *)

(* end of [ats_syntax.ml] *)
