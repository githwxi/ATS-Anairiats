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

module Arg = Ats_arg
module Cnt = Ats_counter
module Err = Ats_error
module Fil = Ats_filename
module Par = Ats_parser
module StrPar = Ats_string_parser
module Env1 = Ats_env1
module Tr1 = Ats_trans1
module Env2 = Ats_stadynenv2
module Tr2 = Ats_trans2
module Env3 = Ats_staenv3
module Tr3 = Ats_trans3
module Tr4 = Ats_trans4

module CS = Ats_constraint
module CC = Ats_ccomp_main

(* ****** ****** *)

let atshome_dir = 
  try Sys.getenv "ATSHOME" with Not_found -> begin
    Printf.eprintf "The environment variable ATSHOME is undefined.\n";
    Err.abort ();
  end

(* ****** ****** *)

let initialize () = begin
  Cnt.initialize ();
  StrPar.initialize ();
  Tr1.initialize ();
  Tr2.initialize ();
end

(* ****** ****** *)

let fixity_load (): unit = (* load in built-in fixity declarations *)
  let name = Filename.concat atshome_dir "prelude/fixity.ats" in
  let f = Fil.filename_make name in
  let prompt: out_channel -> unit =
    function out -> (fprint_string out name; fprint_string out ": ") in
  let ic = open_in name in
  let () = Fil.filename_push f in
  let ds = Par.parse_dec_from_channel true prompt ic in
  let () = Fil.filename_pop () in
  let _ (* ds1 *) = Tr1.dec_list_tr ds in
    Env1.env_make_top_pervasive ()

let stafile_load (filename: string): unit =
  let name = Filename.concat atshome_dir filename in
  let f = Fil.filename_make name in
  let prompt: out_channel -> unit =
    function out -> (fprint_string out name; fprint_string out ": ") in
  let ic = open_in name in
  let () = Fil.filename_push f in
  let ds = Par.parse_dec_from_channel true prompt ic in
  let () = Fil.filename_pop () in
  let () = close_in ic in
  let ds1 = Tr1.dec_list_tr ds in
  let _ (* ds2 *) = Tr2.dec1_list_tr ds1 in
    Env2.stadynenv2_pervasive ()

let usage (cmd: string): unit = begin
  Printf.printf "usage: %s <command> ... <command>\n\n" cmd;
  print_string "where a <command> is of one of the following forms:\n\n";
  print_string "  -s filename (for statically loading <filename>)\n";
  print_string "  --static filename (for statically loading <filename>)\n";
  print_string "  -d filename (for dynamically loading <filename>)\n";
  print_string "  --dynamic filename (for dynamically loading <filename>)\n";
  print_string "  -o filename (output into <filename>)\n";
  print_string "  --output filename (output into <filename>)\n";
  print_string "  -h (for printing the usage)\n";
  print_string "  --help (for printing the usage)\n";
  print_newline ()
end (* end of [let] *)

let
prelude_stafiles
  : string list = [
  "prelude/GEIZELLA/basics_sta.sats";
  "prelude/GEIZELLA/sortdef.sats";
  "prelude/GEIZELLA/basics_dyn.sats";
  "prelude/GEIZELLA/macrodef.sats";

  "prelude/SATS/arith.sats";
  "prelude/SATS/vsubrw.sats";

  "prelude/SATS/bool.sats";
  "prelude/SATS/byte.sats";
  "prelude/GEIZELLA/SATS/char.sats";
  "prelude/GEIZELLA/SATS/file.sats";
  "prelude/GEIZELLA/SATS/float.sats";
  "prelude/GEIZELLA/SATS/integer.sats";
  "prelude/GEIZELLA/SATS/memory.sats";
  "prelude/GEIZELLA/SATS/pointer.sats";
  "prelude/GEIZELLA/SATS/printf.sats";
  "prelude/GEIZELLA/SATS/reference.sats";
  "prelude/GEIZELLA/SATS/sizetype.sats";
  "prelude/GEIZELLA/SATS/string.sats";

  "prelude/GEIZELLA/SATS/array.sats";
  "prelude/GEIZELLA/SATS/list.sats";
  "prelude/GEIZELLA/SATS/list_vt.sats";
  "prelude/GEIZELLA/SATS/matrix.sats";
  "prelude/GEIZELLA/SATS/option.sats";
  "prelude/GEIZELLA/SATS/ptrarr.sats";
]

let prelude_load () =
  let () = fixity_load () in
    List.iter stafile_load prelude_stafiles
(* end of [prelude_load] *)

(* ****** ****** *)

let the_out_channel: (out_channel option) ref = ref None
let out_channel_get (): out_channel =
  match !the_out_channel with Some out -> out | None -> stdout
let out_channel_set (out: out_channel) =
  let () = match !the_out_channel with
    | Some out -> close_out out | None -> () in
    the_out_channel := Some out
let out_channel_reset () =
  let () = match !the_out_channel with
    | Some out -> close_out out | None -> () in
    the_out_channel := None

type command_kind =
  | CKnone
  | CKinput of int (* 0: static; 1: dynamic; 2: dynamic and main *)
  | CKoutput

(* ****** ****** *)

let () = Fil.path_list_push atshome_dir

(* ****** ****** *)

let main (argv: string array): unit =
  let is_prelude: bool ref = ref false in
  let the_command_kind: command_kind ref = ref CKnone in
  let is_typecheck: bool ref = ref false in
  let is_wait: bool ref = ref true in
  let () = initialize () in
  let rec loop (args: Arg.arg_t list): unit = match args with
    | arg :: args -> begin match arg with
        | Arg.Key (0, name) -> begin match !the_command_kind with
	    | CKinput flag ->
		let () = is_wait := false in
		let prompt out = begin
		  (fprint_string out name; fprint_string out ": ")
		end in
		let () = begin
		  if not (!is_prelude) then (is_prelude := true; prelude_load ())
		end in
		let () = Tr3.initialize () in
		let filename = Fil.filename_make name in
		let in_channel = open_in name in
		let () = Fil.filename_push filename in
(*
		let () =
		  Printf.print stdout "The phase of parsing is started!" in
                let () = print_newline () in
*)
		let ds =
		  let is_static = (flag == 0) in
		    Par.parse_dec_from_channel is_static prompt in_channel in
		let () = Fil.filename_pop () in
		let () = close_in in_channel in
(*
		let () =
		  Printf.print "The phase of parsing is successfully completed!" in
                let () = print_newline () in
*)
		let ds1 = Tr1.dec_list_tr ds in
                let () = Tr1.finalize () in
(*
		let () =
		  Printf.print
		    "The phase of 1st translation is successfully completed!" in
                let () = print_newline () in
*)

		let ds2 = Tr2.dec1_list_tr ds1 in
(*
		let () =
		  Printf.printf
		    "The phase of 2nd translation is successfully completed!" in
                let () = print_newline () in
*)
		let ds3 = Tr3.dec2_list_tr ds2 in
(*
		let () =
		  Printf.print stdout
		    "The phase of 3rd translation is successfully completed!\n" in
                let () = print_newline () in
*)
		let c3t = Tr3.finalize () in
(*
	        let () = Printf.print stdout "the constraint is:" in
                let () = print_newline () in
                let () = Ats_staenv3.fprint_cstr3 stdout c3t in
                let () = print_newline () in
*)
		let () = CS.cstr3_solve_init c3t in
(*
		let () =
		  Printf.printf
		    "The phase of constrain-solving is successfully completed!" in
                let () = print_newline () in
*)
		let () =
		  Printf.printf
		    "The phase of type inference of [%s] is successfully completed!"
		    (Fil.filename_basename filename) in
                let () = print_newline () in
		let () =
		  if not (!is_typecheck) then begin
		    let () = Tr4.initialize (filename) in
		    let hids = Tr4.dec3_list_tr ds3 in
		    let out = out_channel_get () in
		    let () = CC.initialize () in
		      CC.ccomp_main out flag filename hids
		  end in
		  loop args
	    | CKoutput ->
		let () = the_command_kind := CKnone in
		let out = open_out name in (out_channel_set out; loop args)
	    | CKnone -> loop args
	  end

        | Arg.Key (1, s) ->
	    let () =  match s with
	      | "s" -> (the_command_kind := CKinput 0; is_wait := true)
	      | "d" -> (the_command_kind := CKinput 1; is_wait := true)
              | "tc" -> (the_command_kind := CKnone; is_typecheck := true)
	      | "o" -> the_command_kind := CKoutput
	      | "h" -> (the_command_kind := CKnone; usage (argv.(0)))
	      | _ -> () in
              loop args

        | Arg.Key (2, s) ->
	    let () =  match s with
	      | "static" ->
                (the_command_kind := CKinput 0; is_wait := true)
	      | "dynamic" ->
                (the_command_kind := CKinput 1; is_wait := true)
	      | "typecheck" ->
                (the_command_kind := CKnone; is_typecheck := true)
	      | "output" -> the_command_kind := CKoutput
	      | "help" ->
                (the_command_kind := CKnone; usage (argv.(0)))
	      | _ -> () in
              loop args

        | _ -> loop args
      end

    | [] when !is_wait -> begin match !the_command_kind with
	| CKinput flag ->
	    let prompt out = fprint_string out "stdin: " in
	    let () = begin
	      if not (!is_prelude) then (is_prelude := true; prelude_load ())
	    end in
	    let () = Tr3.initialize () in
	    let () = Fil.filename_push Fil.stdin in
	    let ds =
	      let is_static = (flag == 0) in
		Par.parse_dec_from_channel is_static prompt stdin in
	    let () = Fil.filename_pop () in
	    let ds1 = Tr1.dec_list_tr ds in
            let () = Tr1.finalize () in
	    let ds2 = Tr2.dec1_list_tr ds1 in
	    let ds3 = Tr3.dec2_list_tr ds2 in
	    let c3t = Tr3.finalize () in
	    let () = CS.cstr3_solve_init c3t in
	    let () =
	      Printf.fprintf stdout
		"The phase of type inference is successfully completed!" in
            let () = print_newline () in
	    let () =
	      if not (!is_typecheck) then begin
		let () = Tr4.initialize (Fil.stdin) in
		let hids = Tr4.dec3_list_tr ds3 in
		let () = CC.initialize () in
		let out = out_channel_get () in
		  CC.ccomp_main out flag Fil.stdin hids
	      end in
	      ()
	| _ -> ()
      end

    | [] -> () in

    match Arg.args_parse argv with
      | [] -> error_of_deadcode "ats_main.ml: argv is empty!"
      | _ :: args -> loop args

let () =
  try (main Sys.argv; out_channel_reset ())
  with exn -> (out_channel_reset (); raise exn)

(* ****** ****** *)

(* end of [ats_main_cc.ml] *)
