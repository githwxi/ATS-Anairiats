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

module Loc = Ats_location

open Ats_staexp2
open Ats_staexp2_util
open Ats_dynexp2

(* some type abbreviations *)

type loc = Loc.location

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_metric: "; Err.error s;
end

(* ****** ****** *)

let metric_list: (dvar2 list * sexp2 list) list ref = ref []
let metric_get (d2v_fun: stamp): (sexp2 list) option =
  let rec aux (xs: (dvar2 list * sexp2 list) list) = match xs with
    | [] -> None
    | (d2vs, s2es) :: xs ->
	if List.exists (function d2v -> d2v.dvar2_stamp = d2v_fun) d2vs then
	  Some (s2es)
	else aux xs in
    aux !metric_list
(* end of [metric_get] *)

let pop (): unit =
  match !metric_list with
    | met :: mets -> metric_list := mets
    | [] -> error "ats_metric: pop: metric_list is empty!"
(* end of [pop] *)

let push (d2vs_fun: dvar2 list) (s2es_metric: sexp2 list): unit =
  metric_list := (d2vs_fun, s2es_metric) :: !metric_list

(* ****** ****** *)

let sexp2_mfun_load (s2e0: sexp2) (d2v0: stamp): (srt2 list * sexp2) option =
  let rec aux s2e0 = match s2e0.sexp2_node with
    | SE2clo (knd, s2e) -> begin match aux s2e with
	| Some (s2ts, s2e) ->
	    Some (s2ts, sexp2_clo_with_sort s2e0.sexp2_sort knd s2e)
	| None -> None
      end
    | SE2fun (lin, sf2e, ns2es, s2e) -> begin match aux s2e with
	| Some (s2ts, s2e) ->
	    Some (s2ts, sexp2_fun_with_sort s2e0.sexp2_sort lin sf2e ns2es s2e)
	| None -> None
      end
    | SE2mfun (od2v, s2es, s2e) ->
	let s2ts = List.map (function s2e -> s2e.sexp2_sort) s2es in
	  Some (s2ts, sexp2_mfun (Some d2v0) s2es s2e)
    | SE2uni (s2vs, s2ps, s2e) -> begin match aux s2e with
	| Some (s2ts, s2e) -> Some (s2ts, sexp2_uni s2vs s2ps s2e) 
	| None -> None
      end
    | _ -> None in
    aux s2e0
(* end of [sexp2_mfun_load] *)

(* ****** ****** *)

let initialize (): unit = (metric_list := [])

(* ****** ****** *)

(* end of [ats_metric.ml] *)
