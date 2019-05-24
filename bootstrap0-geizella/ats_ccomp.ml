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

open Ats_hiexp
open Ats_hiexp_util
open Ats_trans4

(* ****** ****** *)

module P = Printf

module Loc = Ats_location
module Err = Ats_error
module Lab = Ats_label
module Syn = Ats_syntax

(* ****** ****** *)

type stamp = Cnt.count

(* ****** ****** *)

let the_extype_list: (string * hityp) list ref = ref []
let extype_list_add (name: string) (hit: hityp): unit =
  the_extype_list := (name, hit) :: !the_extype_list
let extype_list_get (): (string * hityp) list =
  List.rev (!the_extype_list)

(* ****** ****** *)

type extcode = int (* position *) * string (* code *)
let the_extcode_list: (extcode list) ref = ref []
let extcode_list_add (position: int) (code: string): unit =
  the_extcode_list := (position, code) :: !the_extcode_list
let extcode_list_get (): extcode list =
  List.rev (!the_extcode_list)

(* ****** ****** *)

let the_stafile_list: (Fil.filename list) ref = ref []
let stafile_list_add (f: Fil.filename): unit =
  the_stafile_list := f :: !the_stafile_list
let stafile_list_get (): Fil.filename list =
  List.rev (!the_stafile_list)

let the_dynfile_list: (Fil.filename list) ref = ref []
let dynfile_list_add (f: Fil.filename): unit =
  the_dynfile_list := f :: !the_dynfile_list
let dynfile_list_get (): Fil.filename list =
  List.rev (!the_dynfile_list)

(* ****** ****** *)

(*  used but not declared ! *)
let the_dyncon_set: (DconSet.t) ref = ref (DconSet.empty)
let dyncon_set_get (): DconSet.t = !the_dyncon_set
let dyncon_set_mem (d2c: dcon2): bool =
  DconSet.mem d2c !the_dyncon_set
let dyncon_set_add (d2c: dcon2): unit =
  the_dyncon_set := DconSet.add d2c !the_dyncon_set

(* declared or used but not implemented! *)
let the_dyncst_set: (DcstSet.t) ref = ref (DcstSet.empty)
let dyncst_set_get (): DcstSet.t = !the_dyncst_set
let dyncst_set_mem (d2c: dcst2): bool =
  DcstSet.mem d2c !the_dyncst_set
let dyncst_set_add (d2c: dcst2): unit =
  the_dyncst_set := DcstSet.add d2c !the_dyncst_set

(* ****** ****** *)

(* declared but not used *)
let the_sum_cst_set: (ScstSet.t) ref = ref (ScstSet.empty)
let sum_cst_set_get (): ScstSet.t = !the_sum_cst_set
let sum_cst_set_add (s2c: scst2): unit =
  the_sum_cst_set := ScstSet.add s2c !the_sum_cst_set

(* ****** ****** *)

type tmplab = { tmplab_stamp: stamp; }

let tmplab_new (): tmplab =
  let stamp = Cnt.tmplab_new_stamp () in { tmplab_stamp= stamp }

let fprint_tmplab (out: out_channel) (tl: tmplab): unit =
  P.fprintf out "__ats_lab_%a" Cnt.fprint tl.tmplab_stamp

(* ****** ****** *)

type tmpvar = {
  tmpvar_type: hityp;
  tmpvar_root: tmpvar option;
  tmpvar_ismut: bool; (* mutablility *)
  tmpvar_isret: bool; (* return status *)
  tmpvar_stamp: stamp; (* uniquicity *)
}

and valprim = { (* primitive values *)
  valprim_node: valprim_node;
  valprim_type: hityp; (* type erasure *)
}

and valprim_node =
  | VParg of int
  | VParg_ptr of int
  | VPbool of bool
  | VPcastfn of dcst2 * valprim
  | VPchar of char
  | VPclo of int(*ref*) * funlab * varctx
  | VPcst of dcst2
  | VPcst_val of dcst2
  | VPenv of vartyp
  | VPext of string
  | VPfloat of string
  | VPfun of funlab
  | VPint of Syn.intkind * intinf
  | VPptrof of valprim
  | VPptrof_ptr_offs of valprim * offset_t list
  | VPptrof_var_offs of valprim * offset_t list
  | VPsizeof of hityp
  | VPstring of string
  | VPtmp of tmpvar
  | VPtop
  | VPvoid

and varctx = valprim DvarMap.t

and offset_t =
  | OFFlab of Lab.label * hityp (* record type *)
  | OFFind of valprim list list * hityp (* element type *)

and labvalprim = Lab.label * valprim

and funlab = {
  funlab_name: string;
  funlab_global (* local or global *)
    : dcst2 option;
  funlab_type: (* function type *)
    hityp;
  funlab_stamp: stamp;
  mutable funlab_tailjoined: (* tail-call optimization *)
    tmpvar list;
}

(* ****** ****** *)

let valprim_is_mutable (vp: valprim): bool =
  match vp.valprim_node with
    | VParg_ptr _ -> true | VPtmp tmp -> tmp.tmpvar_ismut | _ -> false

(* ****** ****** *)

let tmpvar_is_void (tmp: tmpvar): bool = hityp_is_void (tmp.tmpvar_type)

let valprim_is_boxed (vp: valprim): bool = hityp_is_boxed (vp.valprim_type)

let valprim_is_void (vp: valprim): bool = hityp_is_void (vp.valprim_type)

(* ****** ****** *)

let valprim_arg (i: int) (hit: hityp): valprim =
  match hit.hityp_node with
    | HITrefarg (ptr, hit_in, hit_out) -> begin
	let hit_in = hityp_nf hit_in in
	  if ptr = 0 then begin (* call-by-value *)
	    { valprim_node= VParg i; valprim_type= hit_in; }
	  end else begin (* call-by-reference *)
	    { valprim_node= VParg_ptr i; valprim_type= hit_in; }
	  end
      end
    | _ -> begin
	let hit = hityp_nf hit in 
	  { valprim_node= VParg i; valprim_type= hit; }
      end

let valprim_bool (b: bool): valprim =
  { valprim_node= VPbool b; valprim_type= hityp_bool; }

let valprim_castfn
  (d2c: dcst2) (vp: valprim) (hit: hityp) = {
  valprim_node= VPcastfn (d2c, vp); valprim_type= hit
} (* end of [valprim_castfn] *)

let valprim_char (c: char): valprim =
  { valprim_node= VPchar c; valprim_type= hityp_char; }

let valprim_clo (i: int) (fl: funlab) (ctx: varctx): valprim =
  let hit = if i > 0 then hityp_ptr else hityp_clo in
    { valprim_node= VPclo (i, fl, ctx); valprim_type= hit; }

let valprim_cst (d2c: dcst2) (hit: hityp): valprim =
  { valprim_node= VPcst d2c; valprim_type= hit; }

let valprim_cst_val (d2c: dcst2) (hit: hityp): valprim = 
  { valprim_node= VPcst_val d2c; valprim_type= hit; }

let valprim_env (vt: vartyp) (hit: hityp): valprim =
  { valprim_node= VPenv vt; valprim_type= hit; }

let valprim_ext (code: string) (hit: hityp): valprim =
  { valprim_node= VPext code; valprim_type= hit; }

let valprim_float (f: string): valprim = {
  valprim_node= VPfloat f; valprim_type= hityp_double;
}

let valprim_fun (fl: funlab): valprim =
  { valprim_node= VPfun fl; valprim_type= fl.funlab_type; }

let valprim_int (i: int): valprim =
  let ik = Syn.IKint and i = intinf_of_int i in
    { valprim_node= VPint (ik, i); valprim_type= hityp_int; }

let valprim_intinf (ik: Syn.intkind) (i: intinf): valprim =
  { valprim_node= VPint (ik, i); valprim_type= hityp_int; }

let valprim_ptrof (vp: valprim): valprim =
  { valprim_node= VPptrof vp; valprim_type= hityp_ptr; }

let valprim_ptrof_ptr_offs
  (vp: valprim) (offs: offset_t list): valprim =
  { valprim_node= VPptrof_ptr_offs (vp, offs); valprim_type= hityp_ptr; }

let valprim_ptrof_var_offs
  (vp: valprim) (offs: offset_t list): valprim =
  { valprim_node= VPptrof_var_offs (vp, offs); valprim_type= hityp_ptr; }

let valprim_sizeof (hit: hityp): valprim =
  { valprim_node= VPsizeof hit; valprim_type= hityp_int; }

let valprim_string (s: string): valprim =
  { valprim_node= VPstring s; valprim_type= hityp_string; }

let valprim_tmp (tmp: tmpvar): valprim =
  { valprim_node= VPtmp tmp; valprim_type= tmp.tmpvar_type; }

let valprim_top (hit: hityp): valprim =
  { valprim_node= VPtop; valprim_type= hit; }

let valprim_void (): valprim =
  { valprim_node= VPvoid; valprim_type= hityp_void; }

(* ****** ****** *)

let rec valprim_is_const (vp: valprim): bool =
  match vp.valprim_node with
    | VPbool _ -> true
    | VPcastfn (_, vp) -> valprim_is_const (vp)
    | VPchar _ -> true
    | VPcst _ -> true
    | VPcst_val _ -> true
    | VPfloat _ -> true
    | VPfun _ -> true
    | VPint _ -> true
    | VPsizeof _ -> true
    | VPstring _ -> true
    | VPtop -> true
    | VPvoid ->true
    | _ -> false

(* ****** ****** *)

let funlab_type_arg (fl: funlab): hityp list =
  let hit = fl.funlab_type in match hit.hityp_node with
    | HITfun (_, hits_arg, _) -> hits_arg
    | _ -> error_of_deadcode "ats_ccomp: funlab_type_arg"

let funlab_type_arg_res (fl: funlab): hityp list * hityp =
  let hit = fl.funlab_type in match hit.hityp_node with
    | HITfun (_, hits_arg, hit_res) -> (hits_arg, hit_res)
    | _ -> error_of_deadcode "ats_ccomp: funlab_type_arg_res"

let funlab_type_fntp_arg_res (fl: funlab): Syn.funclo * hityp list * hityp =
  let hit = fl.funlab_type in match hit.hityp_node with
    | HITfun (fc, hits_arg, hit_res) -> (fc, hits_arg, hit_res)
    | _ -> begin
	P.fprintf stdout "funlab_type_fntp_arg_res: hit = %a\n" fprint_hityp hit;
	error_of_deadcode "ats_ccomp: funlab_type_fntp_arg_res"
      end

let funlab_eq (fl1: funlab) (fl2: funlab): bool =
  Cnt.eq fl1.funlab_stamp fl2.funlab_stamp

let funlab_compare (fl1: funlab) (fl2: funlab): int =
  String.compare (fl1.funlab_name) (fl2.funlab_name)

module FunLabOrd: Map.OrderedType with type t = funlab = struct
  type t = funlab
  let compare fl1 fl2 = compare fl1.funlab_stamp fl2.funlab_stamp
end

module FunLabMap: Map.S with type key = funlab = Map.Make (FunLabOrd)
module FunLabSet: Set.S with type elt = funlab = Set.Make (FunLabOrd)

(* ****** ****** *)

let fprint_funlab (out: out_channel) (fl: funlab): unit =
  P.fprintf out "%s" fl.funlab_name

let fprint_funlab_list (out: out_channel) (fls: funlab list): unit =
  fprint_list_with_sep fprint_funlab out fls ","

let funlab_new_with_type (hit: hityp): funlab =
  let hit = hityp_nf hit in
  let stamp = Cnt.funlab_new_stamp () in
  let name = "__ats_fun_" ^ Cnt.string_of stamp in {
      funlab_name= name;
      funlab_global= None;
      funlab_type= hit;
      funlab_stamp= stamp;
      funlab_tailjoined= [];
    }

let funlab_new_with_dcst2 (d2c: dcst2): funlab =
  let hit = sexp2_tr_1 (d2c.dcst2_type) in
  let hit = hityp_nf hit in
  let stamp = Cnt.funlab_new_stamp () in
  let name =
    if dcst2_is_funcst d2c then begin
      d2c.dcst2_fullname_id
    end else begin
      P.sprintf "%s_fun" d2c.dcst2_fullname_id
    end in {
      funlab_name= name;
      funlab_global= Some d2c;
      funlab_type= hit;
      funlab_stamp= stamp;
      funlab_tailjoined= [];
    }

let funlab_new_with_dvar2 (d2v: dvar2): funlab =
  let hit = sexp2_tr_1 d2v.dvar2_master_type in
  let hit = hityp_nf hit in
  let stamp = Cnt.funlab_new_stamp () in
  let name =
    P.sprintf "%s_%s"
      (Syn.string_of_did d2v.dvar2_name) (Cnt.string_of stamp) in {
      funlab_name= name;
      funlab_global= None;
      funlab_type= hit;
      funlab_stamp= stamp;
      funlab_tailjoined= [];
    }

let funlab_new_with_name_and_type (name: string) (hit: hityp): funlab =
  let hit = hityp_nf hit in
  let stamp = Cnt.funlab_new_stamp () in {
      funlab_name= name;
      funlab_global= None;
      funlab_type= hit;
      funlab_stamp= stamp;
      funlab_tailjoined= [];
    }    

(* ****** ****** *)

let the_vartyp_set: VarTypSet.t ref = ref VarTypSet.empty
let the_vartyp_set_list: (VarTypSet.t list) ref = ref []
let vartyp_set_pop (): VarTypSet.t =
  let vts = !the_vartyp_set in
  let () = match !the_vartyp_set_list with
    | vts :: vtss -> begin
        the_vartyp_set := vts; the_vartyp_set_list := vtss
      end
    | [] -> error_of_deadcode "ats_ccomp: vartyp_set_pop" in vts

let vartyp_set_push (): unit = begin
  the_vartyp_set_list := !the_vartyp_set :: !the_vartyp_set_list;
  the_vartyp_set := VarTypSet.empty;
end

let vartyp_set_add (vt: vartyp): unit =
  the_vartyp_set := VarTypSet.add vt !the_vartyp_set

(* ****** ****** *)

let the_dvar2_level: int ref = ref 0
let dvar2_level_get (): int = !the_dvar2_level
let dvar2_level_set (i: int): unit = the_dvar2_level := i
let dvar2_level_inc (): unit =
  let i = !the_dvar2_level in the_dvar2_level := i+1
let dvar2_level_dec (): unit =
  let i = !the_dvar2_level in the_dvar2_level := i-1
let dvar2_level_dec_and_get (): int =
  let i = !the_dvar2_level - 1 in (the_dvar2_level := i; i)

(* ****** ****** *)

let the_funlab_list: (funlab list) ref = ref []
let the_funlab_list_list: (funlab list list) ref = ref []
let funlab_list_pop (): funlab list =
  let fls = !the_funlab_list in
  let () = match !the_funlab_list_list with
    | fls :: flss ->
	(the_funlab_list := fls; the_funlab_list_list := flss)
    | [] -> error_of_deadcode "ats_ccomp: funlab_list_pop" in fls

let funlab_list_push (): unit = begin
  the_funlab_list_list := !the_funlab_list :: !the_funlab_list_list;
  the_funlab_list := [];
end

let funlab_list_add (fl: funlab): unit =
  the_funlab_list := fl :: !the_funlab_list

(* ****** ****** *)

(* for handling break/continue in loops *)
let the_loopexnlabs_list
  : (tmplab (* break *) * tmplab (* continue *)) list ref = ref []

let loopexnlabs_list_push (blab: tmplab) (clab: tmplab): unit =
  the_loopexnlabs_list := (blab, clab) :: !the_loopexnlabs_list

let loopexnlabs_list_pop (): unit =
  match !the_loopexnlabs_list with
    | bclab :: bclabs -> the_loopexnlabs_list := bclabs
    | [] -> error_of_deadcode "ats_ccomp_main: loopexnlabs_list_pop"

let loopexnlabs_list_get (i: int): tmplab =
  match !the_loopexnlabs_list with
    | (blab, clab) :: bclabs -> if i > 0 then clab else blab
    | [] -> error_of_deadcode "ats_ccomp_main: loopexnlabs_list_get"

(* ****** ****** *)

type tailjoin_item =
  | TAILJOINlab of funlab * tmpvar list
  | TAILJOINmrk


(* for handling tail calls *)
let the_tailjoin_list : tailjoin_item list ref = ref []

let tailjoin_list_pop (): unit =
  let rec aux = function
    | item :: items -> begin match item with
	| TAILJOINmrk -> items |  _ -> aux items
      end
    | [] -> [] in
    begin
      the_tailjoin_list := aux !the_tailjoin_list
    end
(* end of [tailjoin_list_pop] *)

let tailjoin_list_push_mrk (): unit =
  the_tailjoin_list := TAILJOINmrk :: !the_tailjoin_list

let tailjoin_list_push_lab (fl: funlab) (tmps: tmpvar list): unit =
  the_tailjoin_list := TAILJOINlab (fl, tmps) :: !the_tailjoin_list

let tailjoin_list_find (fl0: funlab): (funlab * tmpvar list) option =
  let rec aux = function
    | item :: items -> begin match item with
	| TAILJOINlab (fl, tmps) ->
	    if funlab_eq fl0 fl then Some (fl, tmps) else aux items
	| TAILJOINmrk -> None
      end
    | [] -> None in
    aux !the_tailjoin_list
(* end of [tailjoin_list_find] *)

(* ****** ****** *)

let tmpvar_eq (t1: tmpvar) (t2: tmpvar): bool = (t1 == t2)

let tmpvar_compare (t1: tmpvar) (t2: tmpvar): int =
  Cnt.compare (t1.tmpvar_stamp) (t2.tmpvar_stamp)

(* ****** ****** *)

let fprint_tmpvar (out: out_channel) (t: tmpvar): unit =
  let t = match t.tmpvar_root with None -> t | Some t -> t in
    P.fprintf out "tmp(%a; %a)"
      Cnt.fprint (t.tmpvar_stamp) fprint_hityp t.tmpvar_type

let fprint_tmpvar_list (out: out_channel) (ts: tmpvar list): unit =
  fprint_list_with_sep fprint_tmpvar out ts ","

let rec fprint_valprim (out: out_channel) (vp: valprim): unit =
  match vp.valprim_node with
    | VParg i -> P.fprintf out "VParg(%i)" i
    | VParg_ptr i -> P.fprintf out "VParg_ptr(%i)" i
    | VPbool b -> P.fprintf out "VPbool(%b)" b
    | VPcastfn (d2c, vp) -> begin
        P.fprintf out "VPcastfn(%a, %a)" fprint_dcst2 d2c fprint_valprim vp
      end (* end of [VPcastfn] *)
    | VPchar c -> P.fprintf out "VPchar(%c)" c
    | VPcst d2c -> P.fprintf out "VPcst(%a)" fprint_dcst2 d2c
    | VPcst_val d2c -> P.fprintf out "VPcst_val(%a)" fprint_dcst2 d2c
    | VPclo (i, fl, ctx) -> P.fprintf out "VPclo(%i; %a)" i fprint_funlab fl
    | VPenv vt -> P.fprintf out "VPenv(%a)" fprint_dvar2 vt.vartyp_var
    | VPext code -> P.fprintf out "VPext(%s)" code
    | VPfloat f -> P.fprintf out "VPfloat(%s)" f
    | VPfun fl -> P.fprintf out "VPfun(%a)" fprint_funlab fl
    | VPint (ik, i) -> P.fprintf out "VPint(%s)" (string_of_intinf i)
    | VPptrof vp -> P.fprintf out "VPptrof(%a)" fprint_valprim vp
    | VPptrof_ptr_offs (vp, offs) -> begin
        P.fprintf out "VPptrof_ptr_offs(%a;%a)"
	  fprint_valprim vp fprint_offset_list offs
      end
    | VPptrof_var_offs (vp, offs) -> begin
        P.fprintf out "VPptrof_var_offs(%a;%a)"
	  fprint_valprim vp fprint_offset_list offs
      end
    | VPsizeof t -> P.fprintf out "VPsizeof(%a)" fprint_hityp t
    | VPstring s -> P.fprintf out "VPstring(%s)" s
    | VPtmp tmp -> P.fprintf out "VPtmp(%a)" fprint_tmpvar tmp
    | VPtop -> P.fprintf out "VPtop"
    | VPvoid -> P.fprintf out "VPvoid"
(* end of [fprint_valprim] *)

and fprint_valprim_list (out: out_channel) (vps: valprim list): unit =
  fprint_list_with_sep fprint_valprim out vps ","

and fprint_labvalprim (out: out_channel) ((l, vp): labvalprim): unit =
  fprint_valprim out vp

and fprint_labvalprim_list
  (out: out_channel) (lvps: labvalprim list): unit =
  fprint_list_with_sep fprint_labvalprim out lvps ","

and fprint_offset (out: out_channel) (off: offset_t): unit =
  match off with
    | OFFlab (l, hit_rec) -> P.fprintf out ".%a" Lab.fprint l
    | OFFind (vpss, hit_elt) ->
	let aux vps = P.fprintf out "[%a]" fprint_valprim_list vps in
	  List.iter aux vpss
(* end of [fprint_offset] *)

and fprint_offset_list (out: out_channel) (offs: offset_t list): unit =
  List.iter (fprint_offset out) offs

(* ****** ****** *)

module TmpVarOrd: Map.OrderedType with type t = tmpvar = struct
  type t = tmpvar
  let compare tmp1 tmp2 = compare tmp1.tmpvar_stamp tmp2.tmpvar_stamp
end

module TmpVarSet: Set.S with type elt = tmpvar = Set.Make (TmpVarOrd)

(* ****** ****** *)

let tmpvar_new (hit: hityp): tmpvar =
  let hit = hityp_nf hit in
  let stamp = Cnt.tmpvar_new_stamp () in {
      tmpvar_type= hit;
      tmpvar_root= None;
      tmpvar_ismut= false;
      tmpvar_isret= false;
      tmpvar_stamp= stamp;
    }
(* end of [tmpvar_new] *)

let tmpvar_mut_new (hit: hityp): tmpvar =
  let hit = hityp_nf hit in
  let stamp = Cnt.tmpvar_new_stamp () in {
      tmpvar_type= hit;
      tmpvar_root= None;
      tmpvar_ismut= true;
      tmpvar_isret= false;
      tmpvar_stamp= stamp;
    }
(* end of [tmpvar_mut_new] *)

let tmpvar_ret_new (hit: hityp): tmpvar =
  let hit = hityp_nf hit in
  let stamp = Cnt.tmpvar_new_stamp () in {
      tmpvar_type= hit;
      tmpvar_root= None;
      tmpvar_ismut= false;
      tmpvar_isret= true;
      tmpvar_stamp= stamp;
    }
(* end of [tmpvar_ret_new] *)

let tmpvar_new_with_root (tmp: tmpvar): tmpvar =
  let tmp_root =
    match tmp.tmpvar_root with Some tmp_root -> tmp_root | None -> tmp in
  let stamp = Cnt.tmpvar_new_stamp () in {
      tmpvar_type= tmp_root.tmpvar_type;
      tmpvar_root= Some tmp_root;
      tmpvar_ismut= tmp_root.tmpvar_ismut;
      tmpvar_isret= tmp_root.tmpvar_isret;
      tmpvar_stamp= stamp;
    }
(* end of [tmpvar_new_with_root] *)

(* ****** ****** *)

type patck =
  | PATCKbool of bool
  | PATCKchar of char
  | PATCKcon of dcon2
  | PATCKexn of dcon2
  | PATCKint of intinf
  | PATCKstring of string

(* ****** ****** *)

let fprint_patck (out: out_channel) (pck: patck): unit =
  match pck with
    | PATCKbool b -> P.fprintf out "PATCKbool(%b)" b
    | PATCKchar c -> P.fprintf out "PATCKchar(%c)" c
    | PATCKcon d2c -> P.fprintf out "PATCKcon(%a)" fprint_dcon2 d2c
    | PATCKexn d2c -> P.fprintf out "PATCKexn(%a)" fprint_dcon2 d2c
    | PATCKint i -> P.fprintf out "PATCKint(%s)" (string_of_intinf i)
    | PATCKstring s -> P.fprintf out "PATCKstring(%s)" s

let fprint_patck_list (out: out_channel) (pcks: patck list): unit =
  fprint_list_with_sep fprint_patck out pcks ","

(* ****** ****** *)

type cont_t =
  | CONTtmplab of tmplab
  | CONTfunarg_fail of funlab
  | CONTmatch_fail
  | CONTraise of valprim

type instr_t =
  | Iarray of (* array allocation *)
      tmpvar * int (* size *) * hityp (* element type *)
  | Icall of (* non-tail call *)
      tmpvar * hityp * valprim * valprim list
  | Icall_tail of (* tail call *)
      tmpvar * funlab * tmpvar list * valprim list
  | Icond of valprim * instr_t list * instr_t list
  | Idefine_clo of dcst2 * funlab
  | Idefine_fun of dcst2 * funlab
  | Idefine_val of dcst2 * valprim
  | Iextern of string (* external instruction *)
  | Ifreeptr of valprim (* free constructor *)
  | Ifunction of (* function inline *)
      tmpvar (* result *) *
      valprim list (* function arg *) *
      instr_t list (* function body *) *
      tmpvar (* function ret *)
  | Ilabel_fun of funlab
  | Iload_file of Fil.filename
  | Iload_ptr of tmpvar * valprim
  | Iload_ptr_offs of tmpvar * valprim * offset_t list
  | Iload_var of tmpvar * valprim
  | Iload_var_offs of tmpvar * valprim * offset_t list
  | Iloopexn of int (* break/continue: 0/1 *) * tmplab
  | Imove_con of tmpvar * hityp * dcon2 * valprim list
  | Imove_rec_box of tmpvar * hityp * labvalprim list
  | Imove_rec_flt of tmpvar * hityp * labvalprim list
  | Imove_val of tmpvar * valprim
  | Ioper of tmpvar * dcst2 * valprim list
  | Iparallel_spawn of tmpvar(*ret*) * valprim(*clo*)
  | Iparallel_sync of tmpvar (*ret*)
  | Ipatck of valprim * patck * cont_t
  | Iraise of valprim
  | Irefval of tmpvar * valprim
  | Iselcon of tmpvar * valprim * hityp * int
  | Iselcon_ptr of tmpvar * valprim * hityp * int
  | Iselect of tmpvar * valprim * offset_t list
  | Istore_ptr of valprim * valprim (* !ptr := x *)
  | Istore_ptr_offs of valprim * offset_t list * valprim
  | Istore_var of valprim * valprim (* var := x *)
  | Istore_var_offs of valprim * offset_t list * valprim
  | Iswitch of branch_t list
  | Itrywith of instr_t list * tmpvar * branch_t list
  | Ivardec of tmpvar
  | Iwhile of (* while loop with break/continue labels *)
      tmplab (* break *) * tmplab (* continue *) *
      valprim * instr_t list * instr_t list
(* end of [instr_t] *)

and branch_t = tmplab * instr_t list

(* ****** ****** *)

let fprint_cont (out: out_channel) (k: cont_t): unit =
  match k with
    | CONTtmplab tl -> P.fprintf out "CONTtmplab(%a)" fprint_tmplab tl
    | CONTfunarg_fail fl -> P.fprintf out "CONTfunarg_fail(%a)" fprint_funlab fl
    | CONTmatch_fail -> P.fprintf out "CONTmatch_fail"
    | CONTraise vp -> P.fprintf out "CONTraise(%a)" fprint_valprim vp

let rec fprint_instr (out: out_channel) (i: instr_t): unit =
  match i with
    | Iarray (tmp, sz, hit_elt) -> P.fprintf out "Iarray(%a; %i; %a)"
	fprint_tmpvar tmp sz fprint_hityp hit_elt
    | Icall (tmp_res, hit_fun, vp_fun, vps_arg) -> begin
        P.fprintf out "Icall(%a; %a; %a)"
	  fprint_tmpvar tmp_res
	  fprint_valprim vp_fun fprint_valprim_list vps_arg
      end
    | Icall_tail (tmp_res, fl, tmps_arg, vps_arg) -> begin
	P.fprintf out "Icall_tail(%a; %a; %a; %a)"
	  fprint_tmpvar tmp_res fprint_funlab fl
	  fprint_tmpvar_list tmps_arg fprint_valprim_list vps_arg
      end
    | Icond (vp, is1, is2) -> P.fprintf out "Icond(%a\nIthen\n%aIelse%a)"
	fprint_valprim vp fprint_instr_list is1 fprint_instr_list is2
    | Idefine_clo (d2c, fl) -> P.fprintf out "Idefine_clo(%a, %a)"
	fprint_dcst2 d2c fprint_funlab fl
    | Idefine_fun (d2c, fl) -> P.fprintf out "Idefine_fun(%a, %a)"
	fprint_dcst2 d2c fprint_funlab fl
    | Idefine_val (d2c, vp) -> P.fprintf out "Idefine_val(%a, %a)"
	fprint_dcst2 d2c fprint_valprim vp
    | Iextern cmd -> P.fprintf out "Iextern(%s)" cmd
    | Ifreeptr vp -> P.fprintf out "Ifreeptr(%a)" fprint_valprim vp
    | Ifunction _ -> P.fprintf out "Ifunction(..)"
    | Ilabel_fun fl -> P.fprintf out "Ilabel_fun(%a)" fprint_funlab fl
    | Iload_file filename ->
	P.fprintf out "Iload_file(%a)" Fil.fprint filename
    | Iload_ptr (tmp, vp_ptr) -> P.fprintf out "Iload_ptr(%a, %a)"
	fprint_tmpvar tmp fprint_valprim vp_ptr
    | Iload_ptr_offs (tmp, vp_ptr, offs) ->
	P.fprintf out "Iload_ptr_offs(%a, %a%a)"
	  fprint_tmpvar tmp fprint_valprim vp_ptr fprint_offset_list offs
    | Iload_var (tmp, vp_var) -> P.fprintf out "Iload_var(%a, %a)"
	fprint_tmpvar tmp fprint_valprim vp_var
    | Iload_var_offs (tmp, vp_var, offs) ->
        P.fprintf out "Iload_var_offs(%a, %a%a)"
	  fprint_tmpvar tmp fprint_valprim vp_var fprint_offset_list offs
    | Iloopexn (i, tl) -> P.fprintf out "Iloopexn(%i; %a)" i fprint_tmplab tl
    | Imove_con (tmp, hit_sum, d2c, vps) ->
        P.fprintf out "Imove_con(%a; %a(%a))"
	  fprint_tmpvar tmp fprint_dcon2 d2c fprint_valprim_list vps
    | Imove_rec_box (tmp, hit_rec, lvps) ->
	P.fprintf out "Imove_rec_box(%a; %a)"
	  fprint_tmpvar tmp fprint_labvalprim_list lvps
    | Imove_rec_flt (tmp, hit_rec, lvps) ->
	P.fprintf out "Imove_rec_flt(%a; %a)"
	  fprint_tmpvar tmp fprint_labvalprim_list lvps
    | Imove_val (tmp, vp) -> P.fprintf out "Imove_val(%a; %a)"
	fprint_tmpvar tmp fprint_valprim vp
    | Ioper (tmp, d2c, vps) -> P.fprintf out "Ioper(%a; %a; %a)"
	fprint_tmpvar tmp fprint_dcst2 d2c fprint_valprim_list vps
    | Iparallel_spawn (tmp_ret, vp_clo) ->
	P.fprintf out "Iparallel_spawn(%a; %a)"
          fprint_tmpvar tmp_ret fprint_valprim vp_clo
    | Iparallel_sync tmp_ret ->
	P.fprintf out "Iparallel_sync(%a)" fprint_tmpvar tmp_ret
    | Ipatck (vp, pck, k_fail) -> P.fprintf out "Ipatck (%a; %a; %a)"
	fprint_valprim vp fprint_patck pck fprint_cont k_fail
    | Iraise vp -> P.fprintf out "Iraise(%a)" fprint_valprim vp
    | Irefval (tmp, vp) -> P.fprintf out "Irefval(%a; %a)"
	fprint_tmpvar tmp fprint_valprim vp
    | Iselcon (tmp, vp, hit, i) -> P.fprintf out "Iselcon(%a;%a;%a;%i)"
	fprint_tmpvar tmp fprint_valprim vp fprint_hityp hit i
    | Iselcon_ptr (tmp, vp, hit, i) -> P.fprintf out "Iselcon_ptr(%a;%a;%a;%i)"
	fprint_tmpvar tmp fprint_valprim vp fprint_hityp hit i
    | Iselect (tmp, vp, offs) -> P.fprintf out "Iselect(%a; %a%a)"
	fprint_tmpvar tmp fprint_valprim vp fprint_offset_list offs
    | Istore_ptr (vp_ptr, vp_val) -> P.fprintf out "Istore_ptr(%a; %a)"
	fprint_valprim vp_ptr fprint_valprim vp_val
    | Istore_ptr_offs (vp_ptr, offs, vp_val) ->
	P.fprintf out "Istore_ptr_offs(%a%a; %a)"
	  fprint_valprim vp_ptr fprint_offset_list offs fprint_valprim vp_val
    | Istore_var (vp_var, vp_val) -> P.fprintf out "Istore_var(%a; %a)"
	fprint_valprim vp_var fprint_valprim vp_val
    | Istore_var_offs (vp_var, offs, vp_val) ->
	P.fprintf out "Istore_var_offs(%a%a; %a)"
	  fprint_valprim vp_var fprint_offset_list offs fprint_valprim vp_val
    | Iswitch brs -> P.fprintf out
	"Iswitch: begin\n%aIswitch: end" fprint_branch_list brs
    | Itrywith (res_try, tmp_exn, brs) -> P.fprintf out
	"Itry: begin\n%a\nIwith(%a):\n%aItry: end"
	fprint_instr_list res_try fprint_tmpvar tmp_exn fprint_branch_list brs
    | Ivardec tmp -> P.fprintf out "Ivardec(%a)" fprint_tmpvar tmp
    | Iwhile (blab, clab, vp_test, res_test, res_body) -> P.fprintf out
	"Iwhile begin(%a):\n%a\nIwhile: test:\n%a\nIwhile: body:\n%a\nIwhile: end(%a)"
	fprint_tmplab clab
	fprint_valprim vp_test
	fprint_instr_list res_test
	fprint_instr_list res_body
	fprint_tmplab blab
(* end of [fprint_instr] *)
	
and fprint_instr_list (out: out_channel) (is: instr_t list): unit =
  List.iter (function i -> P.fprintf out "%a\n" fprint_instr i) is

and fprint_branch (out: out_channel) (br: branch_t): unit =
  let (br_lab, br_body) = br in
    P.fprintf out "%a:\n%a\n" fprint_tmplab br_lab fprint_instr_list br_body

and fprint_branch_list (out: out_channel) (brs: branch_t list): unit =
  fprint_list_with_sep fprint_branch out brs ""

(* ****** ****** *)

let iarray (res: instr_t list)
  (tmp_res: tmpvar) (sz: int) (hit_elt: hityp): instr_t list =
  Iarray (tmp_res, sz, hit_elt) :: res

let icall (res: instr_t list) (tmp_res: tmpvar)
  (hit_fun: hityp) (vp_fun: valprim) (vps_arg: valprim list): instr_t list =
  Icall (tmp_res, hit_fun, vp_fun, vps_arg) :: res

let icall_tail (res: instr_t list) (tmp_res: tmpvar)
  (fl: funlab) (tmps_arg: tmpvar list) (vps_arg: valprim list): instr_t list =
  Icall_tail (tmp_res, fl, tmps_arg, vps_arg) :: res

let idefine_clo (res: instr_t list) (d2c: dcst2) (fl: funlab): instr_t list =
  Idefine_clo (d2c, fl) :: res

let idefine_fun (res: instr_t list) (d2c: dcst2) (fl: funlab): instr_t list =
  Idefine_fun (d2c, fl) :: res

let idefine_val (res: instr_t list) (d2c: dcst2) (vp: valprim): instr_t list =
  Idefine_val (d2c, vp) :: res

let ifreeptr (res: instr_t list) (vp: valprim): instr_t list =
  Ifreeptr vp :: res

let ioper (res: instr_t list)
  (tmp_res: tmpvar) (d2c: dcst2) (vps: valprim list): instr_t list =
  Ioper (tmp_res, d2c, vps) :: res

let iloopexn (res: instr_t list) (i: int) (tl: tmplab): instr_t list =
  Iloopexn (i, tl) :: res

let imove_con (res: instr_t list) (tmp_res: tmpvar)
  (hit_sum: hityp) (d2c: dcon2) (vps: valprim list): instr_t list =
  Imove_con (tmp_res, hit_sum, d2c, vps) :: res

(* ****** ****** *)

let imove_rec (is_flat: bool)
  (res: instr_t list) (tmp_res: tmpvar)
  (hit_rec: hityp) (lvps: labvalprim list): instr_t list =
  if is_flat then begin
    Imove_rec_flt (tmp_res, hit_rec, lvps) :: res
  end else begin
    Imove_rec_box (tmp_res, hit_rec, lvps) :: res
  end
(* end of [imove_rec] *)

(* ****** ****** *)

let imove_val (res: instr_t list)
  (tmp_res: tmpvar) (vp: valprim): instr_t list =
  Imove_val (tmp_res, vp) :: res

let imove_val_bool
  (res: instr_t list) (tmp_res: tmpvar) (b: bool): instr_t list =
  let vp = valprim_bool b in imove_val res tmp_res vp

let imove_val_char
  (res: instr_t list) (tmp_res: tmpvar) (c: char): instr_t list =
  let vp = valprim_char c in imove_val res tmp_res vp

let imove_val_clo (res: instr_t list) (tmp_res: tmpvar)
  (i: int) (fl: funlab) (ctx: varctx): instr_t list =
  let vp = valprim_clo i fl ctx in imove_val res tmp_res vp

let imove_val_cst (res: instr_t list)
  (tmp_res: tmpvar) (d2c: dcst2) (hit: hityp): instr_t list =
  let vp = valprim_cst d2c hit in imove_val res tmp_res vp

let imove_val_ext (res: instr_t list)
  (tmp_res: tmpvar) (code: string) (hit: hityp): instr_t list =
  let vp = valprim_ext code hit in  imove_val res tmp_res vp

let imove_val_float
  (res: instr_t list) (tmp_res: tmpvar) (f: string): instr_t list =
  let vp = valprim_float f in imove_val res tmp_res vp

let imove_val_fun
  (res: instr_t list) (tmp_res: tmpvar) (fl: funlab): instr_t list =
  let vp = valprim_fun fl in imove_val res tmp_res vp

let imove_val_int (res: instr_t list)
  (tmp_res: tmpvar) (ik: Syn.intkind) (i: intinf): instr_t list =
  let vp = valprim_intinf ik i in imove_val res tmp_res vp

let imove_val_sizeof
  (res: instr_t list) (tmp_res: tmpvar) (t: hityp): instr_t list =
  let vp = valprim_sizeof t in imove_val res tmp_res vp

let imove_val_string
  (res: instr_t list) (tmp_res: tmpvar) (s: string): instr_t list =
  let vp = valprim_string s in imove_val res tmp_res vp

(* ****** ****** *)

let iparallel_spawn (res: instr_t list)
  (tmp_ret: tmpvar) (vp_clo: valprim) =
  Iparallel_spawn (tmp_ret, vp_clo) :: res

let iparallel_sync (res: instr_t list)  (tmp_ret: tmpvar) =
  Iparallel_sync (tmp_ret) :: res

(* ****** ****** *)

let ipatck (res: instr_t list)
  (vp: valprim) (pck: patck) (k_fail: cont_t): instr_t list =
  Ipatck (vp, pck, k_fail) :: res

let iraise (res: instr_t list) (vp: valprim): instr_t list =
  Iraise vp :: res

let irefval (res: instr_t list)
  (tmp_res: tmpvar) (vp: valprim): instr_t list =
  Irefval (tmp_res, vp) :: res

let iselcon (res: instr_t list)
  (tmp_res: tmpvar) (vp: valprim) (hit: hityp) (i: int): instr_t list =
  Iselcon (tmp_res, vp, hit, i) :: res

let iselcon_ptr (res: instr_t list)
  (tmp_res: tmpvar) (vp: valprim) (hit: hityp) (i: int): instr_t list =
  Iselcon_ptr (tmp_res, vp, hit, i) :: res

let iselect (res: instr_t list)
  (tmp_res: tmpvar) (vp: valprim) (offs: offset_t list): instr_t list =
  Iselect (tmp_res, vp, offs) :: res

let iswitch (res: instr_t list) (brs: branch_t list): instr_t list =
  Iswitch brs :: res

let ivardec (res: instr_t list) (tmp: tmpvar): instr_t list =
  Ivardec tmp :: res

let iwhile (res: instr_t list) (blab: tmplab) (clab: tmplab)
  (vp_test: valprim) (res_test: instr_t list) (res_body: instr_t list):
  instr_t list =
  Iwhile (blab, clab, vp_test, res_test, res_body) :: res

(* ****** ****** *)

let iload_ptr_offs (res: instr_t list)
  (tmp_res: tmpvar) (vp_ptr: valprim) (offs: offset_t list): instr_t list =
  match offs with
    | [] -> Iload_ptr (tmp_res, vp_ptr) :: res
    | _ :: _ -> Iload_ptr_offs (tmp_res, vp_ptr, offs) :: res
(* end of [iload_ptr_offs] *)

let iload_var_offs (res: instr_t list)
  (tmp_res: tmpvar) (vp_var: valprim) (offs: offset_t list): instr_t list =
  match offs with
    | [] -> Iload_var (tmp_res, vp_var) :: res
    | _ :: _ ->  Iload_var_offs (tmp_res, vp_var, offs) :: res
(* end of [iload_var_offs] *)

let istore_ptr_offs (res: instr_t list)
  (vp_ptr: valprim) (offs: offset_t list) (vp_val: valprim): instr_t list =
  match offs with
    | [] -> Istore_ptr (vp_ptr, vp_val) :: res
    | _ :: _ -> Istore_ptr_offs (vp_ptr, offs, vp_val) :: res
(* end of [istore_ptr_offs] *)

let istore_var_offs (res: instr_t list)
  (vp_var: valprim) (offs: offset_t list) (vp_val: valprim): instr_t list =
  match offs with
    | [] -> Istore_var (vp_var, vp_val) :: res
    | _ :: _ -> Istore_var_offs (vp_var, offs, vp_val) :: res
(* end of [istore_var_offs] *)

(* ****** ****** *)

let the_extval_list: (string * valprim) list ref = ref []
let extval_list_add (name: string) (vp_def: valprim): unit =
  the_extval_list := (name, vp_def) :: !the_extval_list
let extval_list_get (): (string * valprim) list =
  List.rev (!the_extval_list)

(* ****** ****** *)

let varctx_nil: varctx = DvarMap.empty

let varctx_add (ctx: varctx) (d2v: dvar2) (vp: valprim): varctx =
  DvarMap.add d2v vp ctx

let varctx_find (ctx: varctx) (d2v: dvar2): valprim =
  try DvarMap.find d2v ctx with Not_found -> begin
    P.fprintf stderr "varctx_find: unrecognized dynamic variable <%a>.\n"
      fprint_dvar2 d2v;
    Err.abort ();
  end
(* end of [varctx_find] *)

(* ****** ****** *)

type cstctx = valprim DcstMap.t

let the_toplevel_cstctx: cstctx ref = ref (DcstMap.empty)
let toplevel_cstctx_add (d2c: dcst2) (vp: valprim): unit =
  the_toplevel_cstctx := DcstMap.add d2c vp !the_toplevel_cstctx
let toplevel_cstctx_find (d2c: dcst2): valprim option =
  try Some (DcstMap.find d2c !the_toplevel_cstctx) with Not_found -> None

(* ****** ****** *)

(* for compiling templates *)

let the_tmpinst_cst_tbl : (string, valprim) H.t =
  let size_hint = 16 in Hashtbl.create size_hint
let tmpinst_cst_tbl_add (name: string) (vp: valprim): unit =
  Hashtbl.add the_tmpinst_cst_tbl name vp
let tmpinst_cst_tbl_find (name: string): valprim option =
  try Some (Hashtbl.find the_tmpinst_cst_tbl name)
  with Not_found -> None
let tmpinst_cst_tbl_clear (): unit =
  Hashtbl.clear the_tmpinst_cst_tbl

let the_tmpinst_var_tbl : (string, valprim) Hashtbl.t =
  let size_hint = 16 in H.create size_hint
let tmpinst_var_tbl_find (name: string): valprim option =
  try Some (Hashtbl.find the_tmpinst_var_tbl name)
  with Not_found -> None
let tmpinst_var_tbl_add (name: string) (vp: valprim): unit =
  Hashtbl.add the_tmpinst_var_tbl name vp
let tmpinst_var_tbl_clear (): unit =
  Hashtbl.clear the_tmpinst_var_tbl

(* ****** ****** *)

type envmap_t = int VarTypMap.t

let the_envmap: (envmap_t) ref = ref VarTypMap.empty
let envmap_set (m: envmap_t): unit = the_envmap := m
let envmap_reset (): unit = the_envmap := VarTypMap.empty
let envmap_find (vt: vartyp): int =
  try VarTypMap.find vt !the_envmap with Not_found -> begin
    P.fprintf stderr "envmap_find: vt = %a\n" fprint_vartyp vt;
    Err.abort ();
  end

let envmap_find_opt (vt: vartyp): int option =
  try Some (VarTypMap.find vt !the_envmap) with Not_found -> None

(* ****** ****** *)

type function_t = {
  function_loc: (* location of the function in the source *)
    Loc.location;
  function_lab: (* the function label *)
    funlab;
  function_level: int;
  function_vts: (* local variables *)
    VarTypSet.t;
  function_fl_lst: (* list of functions called *)
    funlab list;
  function_ret: (* storing the function return *)
    tmpvar;
  function_body: (* instructions of the function body *)
    instr_t list;
  mutable function_env: (* collecting variables in the environment *)
    (VarTypSet.t) option;
  mutable function_envmap: (* numbering variables in the environment *)
    envmap_t;
  mutable function_tailjoin: (* tail-call optimization *)
    (int * funlab * tmpvar list) list;
} (* end of [function_t] *)

let function_is_tailjoin (f: function_t): bool =
  match f.function_tailjoin with [] -> false | _ :: _ -> true

(* ****** ****** *)

let the_function_store: (function_t FunLabMap.t) ref = ref (FunLabMap.empty)  
  
let function_store_add (loc: Loc.location) (fl: funlab) (level: int)
  (vts: VarTypSet.t) (fls: funlab list) (tmp_ret: tmpvar) (res: instr_t list)
  : function_t =
(*
  let () =
    P.fprintf stdout
      "function_store_add: %a\n%a\n" fprint_funlab fl fprint_instr_list res in
*)
  let entry =
    { function_loc= loc;
      function_lab= fl;
      function_level= level;
      function_vts= vts;
      function_fl_lst= fls;
      function_ret= tmp_ret;
      function_body= res;
      function_env= None;
      function_envmap= VarTypMap.empty;
      function_tailjoin= [];
    } in
  let () =
    the_function_store := FunLabMap.add fl entry !the_function_store in
    entry
(* end of [function_store_add] *)

let function_store_add_cst_fun
  (d2c: dcst2) (hits_arg: hityp list) (hit_res: hityp): unit =
  let fl = funlab_new_with_dcst2 d2c in
  let vp_fun = valprim_cst_val d2c hityp_ptr in
  let vps_arg =
    let rec aux i = function
      | hit :: hits ->
	  let vp = valprim_arg i hit in vp :: aux (i+1) hits
      | [] -> [] in
      aux 0 hits_arg in
  let tmp_ret = tmpvar_ret_new hit_res in
  let i = Icall (tmp_ret, fl.funlab_type, vp_fun, vps_arg) in
  let entry =
    { function_loc= Loc.nonloc;
      function_lab= fl;
      function_level= 0;
      function_vts= VarTypSet.empty;
      function_fl_lst= [];
      function_ret= tmp_ret;
      function_body= [i];
      function_env= None;
      function_envmap= VarTypMap.empty;
      function_tailjoin= [];
    } in
    the_function_store := FunLabMap.add fl entry !the_function_store
(* end of [function_store_add_cst_fun] *)

(* ****** ****** *)

let function_store_find (fl: funlab): function_t =
  try FunLabMap.find fl !the_function_store with Not_found ->
   begin
     P.fprintf stderr "function_store_find: %a\n" fprint_funlab fl;
     Err.abort ();
   end
(* end of [function_store_find] *)

let function_envmap_set (f: function_t) (envmap: envmap_t): unit =
  let fl = f.function_lab in
  let ofc = hityp_funclo_get fl.funlab_type in 
  let isclo = match ofc with
    | Some fc -> begin match fc with
	| Syn.FUNCLOclo _ -> true | Syn.FUNCLOfun -> false
      end
    | None -> begin
	error_of_deadcode "ats_ccomp: function_envmap_set"
      end in
    if isclo then f.function_envmap <- envmap
    else if VarTypMap.is_empty envmap then ()
    else begin
      P.eprintf
	"%a: the function is required to have an empty environment.\n"
	Loc.fprint f.function_loc;
      Err.abort ();
    end
(* end of [function_envmap_set] *)

(* ****** ****** *)

let funlab_set_of_function (f0: function_t): FunLabSet.t =
  let level0 = f0.function_level in
  let rec aux flset = function
    | fl :: fls ->
	let f = function_store_find fl in
	  if f.function_level < level0 then
	    let flset = FunLabSet.add fl flset in aux flset fls
	  else begin
	    if FunLabSet.mem fl flset then aux flset fls
	    else begin
	      let flset = aux (FunLabSet.add fl flset) f.function_fl_lst in
		aux flset fls
	    end
	  end
    | [] -> flset in
    aux FunLabSet.empty f0.function_fl_lst
(* end of [funlab_set_of_function] *)

let function_environment (f0: function_t): VarTypSet.t  =
  let rec aux1 (f: function_t): VarTypSet.t =
    match f.function_env with
      | Some vts -> vts
      | None -> begin
	  let level = f.function_level in
	  let vts = f.function_vts in
	  let flset = funlab_set_of_function f in
	  let vts = aux2 level vts (FunLabSet.elements flset) in
	    (f.function_env <- Some vts; vts)
	end
  and aux2 (level: int)
    (vts: VarTypSet.t) (fls: funlab list): VarTypSet.t =
    match fls with
      | fl :: fls -> begin
	  let f = function_store_find fl in
	    if f.function_level < level then begin
	      let vts_f = aux1 f in
	      let vts = VarTypSet.union vts vts_f in
		aux2 level vts fls
	    end else begin
	      let vts = VarTypSet.union vts f.function_vts in
		aux2 level vts fls
	    end
	end
      | [] -> vts in
    aux1 f0
(* end of [function_environment] *)

(* ****** ****** *)

(* end of [ats_ccomp.ml] *)
