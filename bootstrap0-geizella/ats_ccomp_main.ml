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
open Ats_dyncst2

open Ats_hiexp
open Ats_hiexp_util
open Ats_trans4

open Ats_ccomp
open Ats_ccomp_util
open Ats_ccomp_cprint
open Ats_ccomp_trans

(* ****** ****** *)

module Tr1 = Ats_trans1

(* ****** ****** *)

let main_fun_is_implemented () =
  if dcst2_fun_main_is_implemented () then true
  else dcst2_fun_main_dummy_is_implemented ()

(* flag: 0= static; 1= dynamic; 2= dynamic and main *)
let ccomp_main (out: out_channel) (flag: int)
  (filename: Fil.filename) (ds: hidec list): unit =
  let (ctx, res) = ccomp_dec_list varctx_nil [] ds in
  let res = List.rev res in
  let tmpset = tmpset_of_instr_list res in
  let () =
    let aux fl f =
      let r = ref 0 in
      let add vt map =
	let n = !r in (r := n+1; VarTypMap.add vt n map) in
      let envmap =
	VarTypSet.fold add (function_environment f) VarTypMap.empty in
	function_envmap_set f envmap in
      FunLabMap.iter aux !the_function_store in
    begin
      cprint_time_stamp out;
      P.fprintf out "#define _ATS_GEIZELLA 1\n\n";
      cprint_include_h out;
      if (flag > 0) then begin
	P.fprintf out "/* include some .cats files */\n\n";
	cprint_include_cats out;
      end;
      P.fprintf out "/* external codes at top */\n\n";
      cprint_extcodes_top out;
      P.fprintf out "/* type definitions */\n\n";
      cprint_hityp_definitions out;
      if (flag > 0) then begin
	P.fprintf out
	  "/* external dynamic constructor declarations */\n\n";
	cprint_dyncon_list out;
      end;
      if (flag > 0) then begin
	P.fprintf out
	  "/* external dynamic constant declarations */\n\n";
	cprint_dyncst_list out;
      end;
      if (flag > 0) then begin 
	P.fprintf out "/* internal function declarations */\n\n";
	cprint_function_store_prototypes out;
      end;
      P.fprintf out "/* sum constructor declarations */\n\n";
      cprint_sum_con_list out;
      P.fprintf out "/* exception constructor declarations */\n\n";
      cprint_exn_con_list out;
      if (flag > 0) then begin
	P.fprintf out "/* global dynamic constant declarations */\n\n";
	cprint_global_list out res;
      end;
      if (flag > 0) then begin
	P.fprintf out "/* static temporary variable declarations */\n\n";
	cprint_tmpset_dec_static out tmpset;
      end;
      if (flag > 0) then begin
	P.fprintf out "/* function implementations */\n\n";
	cprint_function_store out;
      end;
      P.fprintf out "/* static load function */\n\n";
      cprint_staload_fun out filename;
      if (flag > 0) then begin
	P.fprintf out "/* dynamic load function */\n\n";
        let dynloadflag = Tr1.dynloadflag_get () in
	  cprint_dynload_fun out dynloadflag filename tmpset res;
      end;
      if main_fun_is_implemented () then begin
	P.fprintf out "/* main function */\n\n";
	P.fprintf out "int %a__dynload_flag = 0 ;\n"
	  cprint_filename filename;
	cprint_main_fun_implemented out filename;
      end;
      P.fprintf out "/* external types */\n\n";
      cprint_extypes out;
      P.fprintf out "/* external codes at mid */\n\n";
      cprint_extcodes_mid out;
      P.fprintf out "/* external codes at bot */\n\n";
      cprint_extcodes_bot out;
    end
(* end of [ccomp_main] *)

(* ****** ****** *)

let initialize () = begin
  the_extype_list := [];
  the_extcode_list := [];
  the_stafile_list := [];
  the_dynfile_list := [];

  the_dyncst_set := DcstSet.empty;
  the_sum_cst_set := ScstSet.empty;
  the_vartyp_set := VarTypSet.empty;
  the_dvar2_level := 0;
  the_loopexnlabs_list := [];
  the_funlab_list := [];
  the_tailjoin_list := [];
  the_toplevel_cstctx := DcstMap.empty;

  (* compiling templates *)
  the_svar2_hityp_list := [];
  (* compiling templates *)
  tmpinst_cst_tbl_clear ();
  tmpinst_var_tbl_clear ();
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_ccomp_main.ml] *)
