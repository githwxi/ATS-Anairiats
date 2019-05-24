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

(* mainly for collecting constraints during type-checking *)

open Ats_misc

open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2

open Ats_patcst2

module Loc = Ats_location
module Err = Ats_error
module Eff = Ats_effect
module Met = Ats_metric
module SB = Ats_svar_bind
module SS = Ats_svar_stamp

(* ****** ****** *)

type loc = Loc.location

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_staenv3: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

let scst2_bind_errmsg loc (s2c: scst2) = begin
  P.eprintf "%a: the static constant <%a> is already assumed.\n"
    Loc.fprint loc fprint_scst2 s2c;
  Err.abort ();
end  (* end of [scst2_bind_errmsg] *)

(* ****** ****** *)

let the_scst2_list: scst2 list ref = ref []
let the_scst2_list_list: (scst2 list list) ref = ref []

let scst2_add (s2c: scst2): unit =
  the_scst2_list := s2c :: !the_scst2_list

let scst2_list_add (s2cs: scst2 list): unit =
  the_scst2_list := s2cs @ !the_scst2_list

let scst2_bind_and_add loc (s2c: scst2) (s2e: sexp2): unit =
  if not (s2c.scst2_isasp) then begin
(*
    P.fprintf stdout "scst2_bind_and_add: s2c = %a" fprint_scst2 s2c;
    print_newline ();
*)
    s2c.scst2_def <- Some s2e; s2c.scst2_isasp <- true; scst2_add s2c
  end else begin
    scst2_bind_errmsg loc s2c
  end
(* end of [scst2_bind_and_add] *)

let scst2_pop (): scst2 list = begin
  match !the_scst2_list_list with
    | s2cs :: s2css -> let res = !the_scst2_list in
	(the_scst2_list := s2cs; the_scst2_list_list := s2css; res)
    | [] -> error "scst2_pop"
end (* end of [scst2_pop] *)

let scst2_push (): unit = begin let res = !the_scst2_list in
  (the_scst2_list_list :=  res :: !the_scst2_list_list; the_scst2_list := [])
end (* end of [scst2_push] *)

let scst2_pop_and_unbind (): unit =
(*
  let () = P.printf "scst2_pop_and_unbind: before:" in
  let () = print_newline () in
*)
  let s2cs = scst2_pop () in
(*
  let () = P.printf "scst2_pop_and_unbind: s2cs = %a"
      fprint_scst2_list s2cs in
  let () = print_newline () in
*)
  let rec aux (s2cs: scst2 list): unit = match s2cs with
    | s2c :: s2cs -> (s2c.scst2_def <- None; aux s2cs)
    | [] -> () in
    aux s2cs
(* end of [scst2_pop_and_unbind] *)

(* ****** ****** *)

type cstr3_kind =
  | CK_fatal_error
  | CK_nonexhaustive_pattern_match of
      int (* warning, error, etc. *) * patcst2 list

type sitem3 =
  | SI3cstr of cstr3
  | SI3cstr_ref of (cstr3 option) ref
  | SI3disj of (sitem3 list) list
  | SI3hypo of hypo3
  | SI3svar of svar2 
  | SI3sVar of sVar2

and cstr3 = {
  cstr3_loc: loc;
  cstr3_kind: cstr3_kind;
  cstr3_node: cstr3_node;
}

and cstr3_node =
  | CSTR3prop of sexp2
  | CSTR3itms of sitem3 list

and hypo3 = {
  hypo3_loc: loc;
  hypo3_node: hypo3_node
}

and hypo3_node =
  | HYPO3prop of sexp2
  | HYPO3eqeq of sexp2 * sexp2
  | HYPO3bind of svar2 * sexp2

(* ****** ****** *)

let rec fprint_cstr3 (out: out_channel) (c3t: cstr3): unit =
  match c3t.cstr3_node with
    | CSTR3prop s2e -> P.fprintf out "CSTR3prop(%a)" fprint_sexp2 s2e
    | CSTR3itms s3is -> P.fprintf out "CSTR3itms(%a)" fprint_sitem3_list s3is
(* end of [fprint_cstr3] *)

and fprint_cstr3_list (out: out_channel) (c3ts: cstr3 list): unit =
  List.iter (function c3t -> P.fprintf out "%a\n" fprint_cstr3 c3t) c3ts  

and fprint_hypo3 (out: out_channel) (h3p: hypo3): unit =
  match h3p.hypo3_node with
    | HYPO3prop s2e -> P.fprintf out "HYPO3prop(%a)" fprint_sexp2 s2e
    | HYPO3eqeq (s2e1, s2e2) ->
	P.fprintf out "HYPO3eqeq(%a, %a)" fprint_sexp2 s2e1 fprint_sexp2 s2e2
    | HYPO3bind (s2v1, s2e2) ->
	P.fprintf out "HYPO3bind(%a, %a)" fprint_svar2 s2v1 fprint_sexp2 s2e2
(* end of [fprint_hypo3] *)

and fprint_sitem3 (out: out_channel) (s3i: sitem3): unit = match s3i with
  | SI3cstr c3t -> P.fprintf out "SI3cstr(%a)" fprint_cstr3 c3t
  | SI3cstr_ref r -> begin match !r with
      | Some c3t -> P.fprintf out "SI3cstr_ref(%a)" fprint_cstr3 c3t
      | None -> ()
    end
  | SI3disj s3iss ->
      P.fprintf out "SI3disj(%a)" fprint_sitem3_list_list s3iss
  | SI3hypo h3p -> P.fprintf out "SI3hypo(%a)" fprint_hypo3 h3p
  | SI3svar s2v -> P.fprintf out "SI3svar(%a)" fprint_svar2 s2v
  | SI3sVar s2V -> P.fprintf out "SI3sVar(%a)" fprint_sVar2 s2V
(* end of [fprint_sitem3] *)

and fprint_sitem3_list (out: out_channel) (s3is: sitem3 list): unit =
  List.iter (function s3i -> P.fprintf out "%a\n" fprint_sitem3 s3i) s3is

and fprint_sitem3_list_list (out: out_channel) (s3iss: sitem3 list list): unit =
  fprint_list_with_sep fprint_sitem3_list out s3iss "\n||\n"

(* ****** ****** *)

let cstr3_prop loc (s2e: sexp2): cstr3 = {
  cstr3_loc= loc;
  cstr3_kind= CK_fatal_error;
  cstr3_node= CSTR3prop s2e;
}

let cstr3_itms (s3is: sitem3 list): cstr3 = {
  cstr3_loc= Loc.nonloc;
  cstr3_kind= CK_fatal_error;
  cstr3_node= CSTR3itms s3is;
}

(* ****** ****** *)

let cstr3_metric loc0
  (metric: sexp2 list) (metric_bound: sexp2 list): cstr3 =
  cstr3_prop loc0 (sexp2_mlt metric metric_bound)

(* ****** ****** *)

let hypo3_bind (s2v1: svar2) (s2e2: sexp2): hypo3 = {
  hypo3_loc= Loc.nonloc;
  hypo3_node = HYPO3bind (s2v1, s2e2);
}

let hypo3_eqeq (s2e1: sexp2) (s2e2: sexp2): hypo3 = {
  hypo3_loc= Loc.nonloc;
  hypo3_node = HYPO3eqeq (s2e1, s2e2);
}

let hypo3_prop (s2e: sexp2): hypo3 = {
  hypo3_loc= Loc.nonloc;
  hypo3_node = HYPO3prop s2e;
}

(* ****** ****** *)

let the_sitem3_list: sitem3 list ref = ref []
let the_sitem3_list_list: (sitem3 list list) ref = ref []

let svar_add (s2v: svar2): unit = begin
  SS.svar_add s2v;
  the_sitem3_list := SI3svar s2v :: !the_sitem3_list
end (* end of [svar_add] *)

let svar_list_add (s2vs: svar2 list): unit =
  List.iter svar_add s2vs

(* ****** ****** *)

let stamp_remove = SS.stamp_remove

(* ****** ****** *)

let sVar2_add (s2V: sVar2): unit =
  the_sitem3_list := SI3sVar s2V :: !the_sitem3_list

let sVar_list_add (s2Vs: sVar2 list): unit =
  List.iter sVar2_add s2Vs

(* ****** ****** *)

let hypo_bind_add (s2v1: svar2) (s2e2: sexp2): unit =
  let h3p = hypo3_bind s2v1 s2e2 in
    the_sitem3_list := SI3hypo h3p :: !the_sitem3_list

let hypo_eqeq_add (s2e1: sexp2) (s2e2: sexp2): unit =
  let h3p = hypo3_eqeq s2e1 s2e2 in
    the_sitem3_list := SI3hypo h3p :: !the_sitem3_list

let hypo_prop_add (s2e: sexp2): unit =
  let h3p = hypo3_prop s2e in
    the_sitem3_list := SI3hypo h3p :: !the_sitem3_list

let hypo_prop_list_add (s2es: sexp2 list): unit =
  List.iter hypo_prop_add s2es

(* ****** ****** *)

let cstr_add (c3t: cstr3): unit =
  the_sitem3_list := SI3cstr (c3t) :: !the_sitem3_list

let cstr_list_add (c3ts: cstr3 list): unit =
  List.iter cstr_add c3ts

let cstr_ref_add (c3t_r: cstr3 option ref): unit =
  the_sitem3_list := SI3cstr_ref c3t_r :: !the_sitem3_list

let cstr_nonexhaustive_pattern_match_add
  loc (i: int) (p2tcs: patcst2 list) : unit =
  let c3t = {
    cstr3_loc= loc;
    cstr3_kind= CK_nonexhaustive_pattern_match (i, p2tcs);
    cstr3_node= CSTR3prop (sexp2_bool false)
  } in cstr_add c3t
(* end of [cstr_nonexhaustive_pattern_match_add] *)

(* ****** ****** *)

let prop_add loc (s2e: sexp2): unit = cstr_add (cstr3_prop loc s2e)

let prop_eqeq_add loc (s2e1: sexp2) (s2e2: sexp2): unit =
  if not (sexp2_syneq s2e1 s2e2) then prop_add loc (sexp2_eqeq s2e1 s2e2)
	  
let prop_list_add loc (s2es: sexp2 list): unit =
  List.iter (prop_add loc) s2es

let prop_add_sizeof_eq loc (s2e1: sexp2) (s2e2: sexp2): unit =
  let s2p =
    sexp2_eqeq
      (sexp2_sizeof_viewt0ype_int s2e1)
      (sexp2_sizeof_viewt0ype_int s2e2) in
    cstr_add (cstr3_prop loc s2p)
(* end of [prop_add_sizeof_eq] *)

(* ****** ****** *)

let disj_add (s3iss: sitem3 list list): unit =
  the_sitem3_list := SI3disj s3iss :: !the_sitem3_list

(* ****** ****** *)

let metric_check loc (metric: sexp2 list): unit =
  let f s2e =
    if srt2_is_int s2e.sexp2_sort then
      cstr_add (cstr3_prop loc (sexp2_igte_zero s2e)) in
    List.iter f metric

let metric_add loc
  (metric: sexp2 list) (metric_bound: sexp2 list): unit =
  cstr_add (cstr3_metric loc metric metric_bound)

(* ****** ****** *)

type effenv_item = (* effect environment item *)
  | EFFENVeff of Eff.effect
  | EFFENVeffmask of Eff.effect
  | EFFENVlam of seff2

let fprint_effenv_item (out: out_channel) (efi: effenv_item): unit =
  match efi with
    | EFFENVeff eff ->
	P.fprintf out "EFFENVeff(%a)" Syn.fprint_effect eff
    | EFFENVeffmask eff ->
	P.fprintf out "EFFENVeffmask(%a)" Syn.fprint_effect eff
    | EFFENVlam sf2e ->
	P.fprintf out "EFFENVlam(%a)" fprint_seff2 sf2e
(* end of [fprint_effenv_item] *)

let fprint_effenv_item_list (out: out_channel) (efis: effenv_item list): unit =
  fprint_list_with_sep fprint_effenv_item out efis ";"

let the_effenv_item_list: effenv_item list ref = ref []
let the_effenv_item_list_list: effenv_item list list ref = ref []

let fprint_the_effenv_item_list (out: out_channel): unit =
  P.fprintf out "the_effenv_item_list = %a\n"
    fprint_effenv_item_list !the_effenv_item_list

(* ****** ****** *)

let effenv_check_eff loc0 (eff0: Eff.effect): unit =
(*
  let () =
    P.fprintf stdout "effenv_check_eff: eff0 = %a\n"
      Syn.fprint_effect eff0 in
*)
  let rec aux xs = match xs with
    | x :: xs -> begin match x with
	| EFFENVeff eff ->
	    if Syn.effect_leq eff0 eff then false else aux xs
	| EFFENVeffmask eff -> begin
	    if Syn.effect_leq eff0 eff then true else aux xs
	  end
	| EFFENVlam sf2e -> seff2_contain_eff sf2e eff0
      end
    | [] -> true in
  if not (aux !the_effenv_item_list) then begin
    P.fprintf stderr "%a: effect <%a> is disallowed.\n"
      Loc.fprint loc0 Syn.fprint_effect eff0;
    Err.abort ();
  end
(* end of [effenv_check_eff] *)

let effenv_check_exn loc0: unit =
  effenv_check_eff loc0 Syn.EFFexn

let effenv_check_ref loc0: unit =
  effenv_check_eff loc0 Syn.EFFref

let effenv_check_all loc0: unit = begin
  effenv_check_eff loc0 Syn.EFFexn;
  effenv_check_eff loc0 Syn.EFFntm;
  effenv_check_eff loc0 Syn.EFFref;
end (* end of [effenv_check_all] *)

let effenv_check_effset loc0
  (effs: Eff.effset): unit = begin
  Eff.effset_iter (effenv_check_eff loc0) effs
end (* end of [effenv_check_effset] *)

let effenv_check_var loc0 (s2v0: svar2): unit =
(*
  let () =
    P.fprintf stdout "effenv_check_var: s2v0 = %a\n" fprint_svar2 s2v0 in
  let () = fprint_the_effenv_item_list stdout in
*)
  let rec aux xs = match xs with
    | x :: xs -> begin match x with
	| EFFENVeff eff -> false
	| EFFENVeffmask eff -> aux xs
	| EFFENVlam sf2e -> seff2_contain_var sf2e s2v0
      end
    | [] -> true in
  if not (aux !the_effenv_item_list) then begin
    P.fprintf stderr "%a: effect <%a> is disallowed.\n"
      Loc.fprint loc0 fprint_svar2 s2v0;
    Err.abort ();
  end
(* end of [effenv_check_var] *)

let rec effenv_check_seff2 loc0 (sf2e0: seff2): unit =
(*
  let () =
    P.fprintf stdout "effenv_check_seff2: sf2e0 = %a\n"
      fprint_seff2 sf2e0 in
*)
  match sf2e0 with
    | SEFF2all -> effenv_check_all loc0
    | SEFF2nil -> ()
    | SEFF2set (effs, s2es) -> begin
	effenv_check_effset loc0 effs;
	effenv_check_sexp2_list loc0 s2es
      end
(* end of [effenv_check_seff2] *)

and effenv_check_sexp2 loc0 (s2e: sexp2): unit =
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2eff sf2e -> effenv_check_seff2 loc0 sf2e
    | SE2var s2v -> effenv_check_var loc0 s2v
    | _ -> begin
	P.fprintf stderr "%a: effenv_check_sexp2: s2e = %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end
(* end of [effenv_check_sexp2] *)

and effenv_check_sexp2_list loc0 (s2es: sexp2 list): unit =
  List.iter (effenv_check_sexp2 loc0) s2es

let effenv_add_eff (eff: Eff.effect): unit = begin
  the_effenv_item_list := EFFENVeff eff :: !the_effenv_item_list
end (* end of [effenv_add_eff] *)

let effenv_add_lam (sf2e: seff2): unit = begin
  the_effenv_item_list := EFFENVlam sf2e :: !the_effenv_item_list
end (* end of [effenv_add_lam] *)

let effenv_pop (): unit =
  let efiss = !the_effenv_item_list_list in match efiss with
    | efis :: efiss -> begin
	the_effenv_item_list := efis;
	the_effenv_item_list_list := efiss
      end
    | [] -> error_of_deadcode "ats_staenv3: effenv_pop"
(* end of [effenv_pop] *)

let effenv_push (): unit = begin
  the_effenv_item_list_list :=
    !the_effenv_item_list :: !the_effenv_item_list_list;
end (* end of [effenv_push] *)

let effenv_push_with_eff (eff: Eff.effect): unit = begin
  the_effenv_item_list_list :=
    !the_effenv_item_list :: !the_effenv_item_list_list;
  the_effenv_item_list := EFFENVeff eff :: !the_effenv_item_list;
end (* end of [effenv_push_with_eff] *)

let effenv_push_with_effmask (eff: Eff.effect): unit = begin
  the_effenv_item_list_list :=
    !the_effenv_item_list :: !the_effenv_item_list_list;
  the_effenv_item_list := EFFENVeffmask eff :: !the_effenv_item_list;
end (* end of [effenv_push_with_effmask] *)

let effenv_push_with_lam (sf2e: seff2): unit = begin
  the_effenv_item_list_list :=
    !the_effenv_item_list :: !the_effenv_item_list_list;
  the_effenv_item_list := EFFENVlam sf2e :: !the_effenv_item_list;
end (* end of [effenv_push_with_lam] *)

(* ****** ****** *)

let sitem3_list_get (): sitem3 list = !the_sitem3_list
let sitem3_list_set (s3is: sitem3 list): unit = (the_sitem3_list := s3is)

(* ****** ****** *)

let env_push (): unit = begin
(*
  P.fprintf stdout "env_push: before\n";
  fprint_sitem3_list stdout !the_sitem3_list;
  P.fprintf stdout "env_push: after\n";
*)
  SS.push (); SB.push ();
  the_sitem3_list_list := !the_sitem3_list :: !the_sitem3_list_list;
  the_sitem3_list := [];
end (* end of [env_push] *)

let env_pop (): sitem3 list =
(*
  let () = begin
    P.fprintf stdout "env_pop: before\n";
    fprint_sitem3_list stdout !the_sitem3_list;
    P.fprintf stdout "env_pop: after\n";
  end in
*)
  match !the_sitem3_list_list with
    | [] -> error "env_pop"
    | s3is :: s3iss ->
	let s3is0 = List.rev !the_sitem3_list in
	let () = begin
	  SS.pop (); SB.pop ();
	  the_sitem3_list := s3is;
	  the_sitem3_list_list := s3iss;
	end in s3is0
(* end of [env_pop] *)

let env_pop_and_add (): unit = begin
  let s3is = env_pop () in cstr_add (cstr3_itms s3is)
end (* end of [env_pop_and_add] *)

(* ****** ****** *)

let sexp2_Var_new loc (s2t: srt2): sexp2 =
  let s2V = sVar2_new loc (SS.stamps_get ()) s2t in
  let () = sVar2_add s2V in sexp2_Var s2V
(* end of [sexp2_Var_new] *)

let sexp2_Var_new_of_svar loc (s2v: svar2): sexp2 =
  let s2V = sVar2_new_of_svar loc (SS.stamps_get ()) s2v in
(*
  let () =
    P.fprintf stdout "sexp2_Var_new_of_svar: %a.sVar2_svs = (%a)\n"
      fprint_sVar2 s2V fprint_stamps s2V.sVar2_svs in
*)
  let () = sVar2_add s2V in
    sexp2_Var s2V

let sexp2_Var_new_with_stamps loc
  (s2t: srt2) (stamps: SS.stamps): sexp2 =
  let s2V = sVar2_new loc stamps s2t in
  let () = sVar2_add s2V in sexp2_Var s2V
(* end of [sexp2_Var_new_with_stamps] *)

(* ****** ****** *)

let sexp2_VarApp_new_with_stamps loc
  (stamps: SS.stamps) (s2t_res: srt2): sexp2 =
  let s2t_arg = srt2_any () in
  let s2t_fun = srt2_fun [s2t_arg] s2t_res in
  let s2V = sVar2_new loc stamps s2t_fun in
  let () = s2V.sVar2_arg_sort <- Some s2t_arg in
  let () = sVar2_add s2V in
  let s2v =  svar2_new s2t_arg in
    sexp2_exi [s2v] []
      (sexp2_VarApp_with_sort s2t_res s2V (sexp2_var s2v))
(* end of [sexp2_VarApp_new_with_stamps] *)

let sexp2_VarApp_new loc (s2t_res: srt2): sexp2 =
  sexp2_VarApp_new_with_stamps loc (SS.stamps_get ()) s2t_res

(* ****** ****** *)

let scst2_closure loc
  (stamps: SS.stamps) (s2c: scst2): svar2 * sexp2 list =
  let (s2ts, s2t_res) = match s2c.scst2_sort with
    | SRT2fun (s2ts, s2t) -> (s2ts, s2t)
    | _ -> begin
        P.eprintf "%a: scst2_closure: s2c = %a\n" Loc.fprint loc fprint_scst2 s2c;
        Err.abort ()
      end in
  let s2t_arg =
    let s2ts =
      List.filter
	(function s2t -> not (srt2_is_impredicative s2t)) s2ts in
      SRT2tup s2ts in
  let s2v =  svar2_new s2t_arg in
  let arg = sexp2_var s2v in
  let rec aux s2es i = function
    | [] -> List.rev s2es
    | s2t :: s2ts ->
	if srt2_is_impredicative s2t then
	  let s2e = sexp2_VarApp_new_with_stamps loc stamps s2t in
	    aux (s2e :: s2es) i s2ts
	else
	  let s2e = sexp2_sel_with_sort s2t arg i in
	    aux (s2e :: s2es) (i+1) s2ts in
    (s2v, aux [] 0 s2ts)
(* end of [scst2_closure] *)


let sexp2_metric_inst loc0
  (od2v: stamp option) (metric: sexp2 list): unit =
  match od2v with
    | None -> ()
    | Some d2v -> begin
	let metric_bound = match Met.metric_get d2v with
	  | Some s2es -> s2es
	  | None -> begin
	      P.fprintf stderr "%a: sexp2_metric_inst: no metric bound"
		Loc.fprint loc0;
	      Err.abort ();
	    end in
	  metric_add loc0 metric metric_bound
      end
(* end of [sexp2_metric_inst] *)

(* ****** ****** *)

let sexp2_inst_and_add loc0
  (s2vs: svar2 list) (s2ps: sexp2 list): subst =
  let sub =
    List.map (function s2v -> (s2v, sexp2_Var_new_of_svar loc0 s2v)) s2vs in
  let s2ps = sexp2_list_subst sub s2ps in
  let () = prop_list_add loc0 s2ps in sub
(* end of [sexp2_inst_and_add] *)

let sexp2_inst_with_and_add loc0
  (s2vs: svar2 list) (s2ps: sexp2 list) (s2es: sexp2 list): subst =
  let rec aux sub s2vs s2es = match s2vs, s2es with
    | [], [] -> List.rev sub
    | s2v :: s2vs, s2e :: s2es ->
	let s2vs2e = sexp2_bind loc0 s2v s2e in
	  aux (s2vs2e :: sub) s2vs s2es
    | _, _ -> begin
	P.fprintf stderr "%a: static arity error." Loc.fprint loc0;
	Err.abort ();
      end in
  let sub = aux [] s2vs s2es in
  let s2ps = sexp2_list_subst sub s2ps in
  let () = prop_list_add loc0 s2ps in sub
(* end of [sexp2_inst_with_and_add] *)

let sexp2_hypo_inst_and_add loc0 (s2vs: svar2 list) (s2ps: sexp2 list): subst =
  let (sub, s2vs_new) = subst_extend [] s2vs in
  let s2ps_new = sexp2_list_subst sub s2ps in
  let () = svar_list_add s2vs_new in
  let () = hypo_prop_list_add s2ps_new in sub
(* end of [sexp2_hypo_inst_and_add] *)

(* ****** ****** *)

let sexp2_template_inst loc0 (s2ess: sexp2 list list)
  (s2vpss: (svar2 list * sexp2 list) list) (s2e: sexp2): subst list * sexp2 =
  let f sub (s2vs, s2ps) = (s2vs, sexp2_list_subst sub s2ps) in
  let rec aux1 subs s2vpss s2e = match s2vpss with
    | [] -> (List.rev subs, s2e)
    | (s2vs, s2ps) :: s2vpss ->
	let sub = sexp2_inst_and_add loc0 s2vs s2ps in
	let s2vpss = List.map (f sub) s2vpss in
	let s2e = sexp2_subst sub s2e in
	  aux1 (sub :: subs) s2vpss s2e in
  let rec aux2 subs s2ess s2vpss s2e = match s2ess with
      | s2es :: s2ess -> begin match s2vpss with
	  | (s2vs, s2ps) :: s2vpss ->
	      let sub = sexp2_inst_with_and_add loc0 s2vs s2ps s2es in
	      let s2vpss = List.map (f sub) s2vpss in
	      let s2e = sexp2_subst sub s2e in
		aux2 (sub :: subs) s2ess s2vpss s2e
	  | [] -> begin
	      P.fprintf stderr
		"%a: sexp2_template_inst: too many template arguments.\n"
		Loc.fprint loc0;
	      Err.abort ();
	    end
	end
      | [] -> aux1 subs s2vpss s2e in
    aux2 [] s2ess s2vpss s2e
(* end of [sexp2_template_inst] *)

(* ****** ****** *)

let sexp2_uni_inst_one loc0 (s2e0: sexp2): sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2uni (s2vs, s2ps, s2e) ->
	let sub = sexp2_inst_and_add loc0 s2vs s2ps in sexp2_subst sub s2e
    | _ -> begin
	P.fprintf stderr "%a: sexp2_uni_inst_one: not a universal type."
	  Loc.fprint loc0;
	Err.abort ();	
      end
(* end of [sexp2_uni_inst_one] *)

let rec sexp2_uni_inst_all loc0 (s2e0: sexp2): sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2uni (s2vs, s2ps, s2e)->
	let sub = sexp2_inst_and_add loc0 s2vs s2ps in
	  sexp2_uni_inst_all loc0 (sexp2_subst sub s2e)
    | SE2mfun (od2v, s2es_metric, s2e) ->
	let () = sexp2_metric_inst loc0 od2v s2es_metric in
	  sexp2_uni_inst_all loc0 s2e
    | _ -> s2e0
(* end of [sexp2_uni_inst_all] *)

let sexp2_uni_inst_seq loc0 s2e0 s2es0: sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2uni (s2vs, s2ps, s2e) ->
	let sub = sexp2_inst_with_and_add loc0 s2vs s2ps s2es0 in
	  sexp2_subst sub s2e
    | _ -> begin
	P.fprintf stderr "%a: sexp2_uni_inst_seq: not a universal type."
	  Loc.fprint loc0;
	prerr_newline ();
	Err.abort ();	
      end
(* end of [sexp2_uni_inst_seq] *)

let sexp2_uni_inst_sexparg2 loc0 s2e s2a: sexp2 =
  match s2a with
    | SEXPARG2one -> sexp2_uni_inst_one loc0 s2e
    | SEXPARG2all -> sexp2_uni_inst_all loc0 s2e
    | SEXPARG2seq s2es -> sexp2_uni_inst_seq loc0 s2e s2es
(* end of [sexp2_uni_inst_sexparg2] *)

let rec sexp2_uni_inst_sexparg2_list loc0 s2e s2as: sexp2 =
  match s2as with
    | s2a :: s2as ->
	let s2e = sexp2_uni_inst_sexparg2 loc0 s2e s2a in
	  sexp2_uni_inst_sexparg2_list loc0 s2e s2as
    | [] -> s2e
(* end of [sexp2_uni_inst_sexparg2_list] *)

(* ****** ****** *)

let sexp2_exi_inst_one loc0 (s2e0: sexp2): sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2exi (s2vs, s2ps, s2e) ->
	let sub = sexp2_inst_and_add loc0 s2vs s2ps in sexp2_subst sub s2e
    | _ -> begin
	P.fprintf stderr "%a: sexp2_exi_inst_one: not an existential type."
	  Loc.fprint loc0;
	Err.abort ();	
      end
(* end of [sexp2_exi_inst_one] *)

let rec sexp2_exi_inst_all loc0 (s2e0: sexp2): sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2exi (s2vs, s2ps, s2e)->
	let sub = sexp2_inst_and_add loc0 s2vs s2ps in
	  sexp2_exi_inst_all loc0 (sexp2_subst sub s2e)
    | _ -> s2e0
(* end of [sexp2_exi_inst_all] *)

let sexp2_exi_inst_seq loc0 s2e0 s2es0: sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2exi (s2vs, s2ps, s2e) ->
	let sub = sexp2_inst_with_and_add loc0 s2vs s2ps s2es0 in
	  sexp2_subst sub s2e
    | _ -> begin
	P.fprintf stderr "%a: sexp2_exi_inst_seq: not an existential type."
	  Loc.fprint loc0;
	prerr_newline ();
	Err.abort ();	
      end
(* end of [sexp2_exi_inst_seq] *)

let sexp2_exi_inst_sexparg2 loc0 s2e s2a: sexp2 =
  match s2a with
    | SEXPARG2one -> sexp2_exi_inst_one loc0 s2e
    | SEXPARG2all -> sexp2_exi_inst_all loc0 s2e
    | SEXPARG2seq s2es -> sexp2_exi_inst_seq loc0 s2e s2es
(* end of [sexp2_exi_inst_sexparg2] *)

(* ****** ****** *)

let sexp2_open_and_add (s2e: sexp2): sexp2 =
(*
  let () =
    P.fprintf stdout "sexp2_open_and_add: before: s2e = %a\n"
      fprint_sexp2 s2e in
*)
  let (s2vs, s2ps, s2e) = sexp2_open s2e in
(*
  let () =
    P.fprintf stdout "sexp2_open_and_add: after: s2vs = %a\n"
      fprint_svar2_list s2vs in
  let () =
    P.fprintf stdout "sexp2_open_and_add: after: s2e = %a\n"
      fprint_sexp2 s2e in
*)
  let () = svar_list_add s2vs in
  let () = hypo_prop_list_add s2ps in
    s2e
(* end of [sexp2_open_and_add] *)

let sexp2_list_open_and_add (s2es: sexp2 list): sexp2 list =
  let (s2vs, s2ps, s2es) = sexp2_list_open s2es in
  let () = svar_list_add s2vs in
  let () = hypo_prop_list_add s2ps in
    s2es
(* end of [sexp2_list_open_and_add] *)

let labsexp2_list_open_and_add (ls2es: labsexp2 list): labsexp2 list =
  let (s2vs, s2ps, ls2es) = labsexp2_list_open ls2es in
  let () = svar_list_add s2vs in
  let () = hypo_prop_list_add s2ps in
    ls2es
(* end of [labsexp2_list_open_and_add] *)

(* ****** ****** *)

let sVar2_assign_with_warning loc0 s2V1 s2e1 s2e2: unit =
  if Stamps.subset (sexp2_fvs_0 s2e2) s2V1.sVar2_svs then
    s2V1.sVar2_link <- Some s2e2
  else begin
    P.fprintf stderr "%a: sexp2_Var_assign: <%a> <!- <%a>.\n" 
      Loc.fprint loc0 fprint_sVar2 s2V1 fprint_sexp2 s2e2;
    prop_add loc0 (sexp2_eqeq s2e1 s2e2)
  end
(* end of [sVar2_assign_with_warning] *)

let sVar2_assign_with_error loc0 s2V1 s2e2: unit =
  if Stamps.subset (sexp2_fvs_0 s2e2) s2V1.sVar2_svs then
    s2V1.sVar2_link <- Some s2e2
  else begin
    P.fprintf stderr "%a: sexp2_Var_assign: <%a> <!- <%a>.\n" 
      Loc.fprint loc0 fprint_sVar2 s2V1 fprint_sexp2 s2e2;
    Err.abort ();
  end
(* end of [sVar2_assign_with_error] *)

(* ****** ****** *)

let initialize () = begin
  Met.initialize ();
  SS.initialize ();
  SB.initialize ();
  the_scst2_list := [];
  the_scst2_list_list := [];
  the_sitem3_list := [];
  the_sitem3_list_list := [];
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_staenv3.ml] *)
