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

(* ats_filename: handling filenames *)

(* ****** ****** *)

open Ats_misc

(* ****** ****** *)

exception FilenameException

let abort (): 'a = (flush stderr; raise FilenameException)

type filename = {
  basename: string;
  fullname: string;
  fullname_id: string;
}

let nonfile = let name = "" in
  { basename=name; fullname=name; fullname_id= name }

let stdin = let name = "stdin" in
  { basename=name; fullname=name; fullname_id= name }

let filename_basename f = f.basename
let filename_fullname f = f.fullname
let filename_fullname_id f = f.fullname_id

(* ****** ****** *)

type path = string

let the_path_list: (path list) ref = ref []

let path_list_pop (): unit = match !the_path_list with
  | [] -> begin
      prerr_line "Fatal: path_list_pop: <the_path_list> is empty!";
      abort ();
    end
  | p :: ps -> the_path_list := ps
(* end of [path_list_pop] *)

let path_list_push (p: path): unit =
  the_path_list := p :: !the_path_list

let path_list_reset (): unit = the_path_list := []

(* ****** ****** *)

let filename_normalize (s0: string): string =
  let unfold dirs n s: (string * string list) =
    let len = String.length s in
    let rec aux dirs n =
      if n < len then
        try
          let n' = String.index_from s n '/' in
          let dir = String.sub s n (n' - n + 1) in
            match dir with
              | "./" -> aux dirs (n'+1)
              | "../" -> begin
                 match dirs with
                   | [] -> aux (dir :: dirs) (n'+1)
                   | dir' :: dirs' -> begin
                     match dir' with
                       | "../" -> aux (dir :: dirs) (n'+1)
                       | _ -> aux dirs' (n'+1)
                     end
               end
              | _ -> aux (dir :: dirs) (n'+1)
        with Not_found -> (String.sub s n (len - n), dirs)
      else begin
        prerr_string "filename_normalize: unfold: ill-formed file name: ";
        prerr_line s0;
        abort ()
      end in
      aux [] 0 in
  let rec fold s = function
    | [] -> s
    | dir :: dirs -> fold (dir ^ s) dirs in
  let (base, dirs) = unfold [] 0 s0 in
    fold base dirs
(* end of [filename_normalize] *)

let filename_make (name: string): filename =
  let dirs = !the_path_list in
  let rec aux = function
    | [] -> None
    | dir :: dirs ->
        let fullname = Filename.concat dir name in
          if Sys.file_exists fullname then Some fullname else aux dirs in
  let ofilename =
    if Sys.file_exists name then
      if Filename.is_relative name then
        Some (Filename.concat Filename.current_dir_name name)
      else Some name
    else (if Filename.is_relative name then aux dirs else None) in
    match ofilename with
      | Some fullname -> begin
          let fullname = filename_normalize fullname in
          let fullname =
            if Filename.is_relative fullname then
              Filename.concat (Sys.getcwd ()) fullname
            else fullname in
          let fullname_id = string_identifize fullname in {
              basename= name;
              fullname= fullname;
              fullname_id= fullname_id;
            }
        end
      | None -> begin
          Printf.eprintf
            "ats_filename: filename_make: unavailable file: [%s]\n" name;
          abort ()
        end
(* end of [filename_make] *)

(* ****** ****** *)

let compare (f1: filename) (f2: filename) =
  String.compare f1.fullname f2.fullname

let eq (f1: filename) (f2: filename): bool =
  (String.compare f1.fullname f2.fullname) == 0
let neq (f1: filename) (f2: filename): bool =
  (String.compare f1.fullname f2.fullname) <> 0

let lt (f1: filename) (f2:filename): bool =
  (String.compare f1.fullname f2.fullname) < 0
let lte (f1: filename) (f2:filename): bool = 
  (String.compare f1.fullname f2.fullname) <= 0
let gt (f1: filename) (f2:filename): bool = 
  (String.compare f1.fullname f2.fullname) > 0
let gte (f1: filename) (f2:filename): bool = 
  (String.compare f1.fullname f2.fullname) >= 0

(* ****** ****** *)

let fprint (out: out_channel) (f: filename) = fprint_string out f.fullname
let prerr (f: filename) = fprint stderr f
let print (f: filename) = fprint stdout f

(* ****** ****** *)

let the_filename: filename ref = ref nonfile
let the_filename_stack: (filename list) ref = ref []

let filename_get (): filename = !the_filename

let filename_pop (): unit = match !the_filename_stack with
  | f :: fs -> (the_filename := f; the_filename_stack := fs)
  | [] -> begin
      prerr_line "Fatal: filename_pop: <the_filename_stack> is empty!";
      abort ();
    end
(* end of [filename_pop] *)

let filename_push (f: filename): unit = begin
  the_filename_stack := !the_filename :: !the_filename_stack;
  the_filename := f;
end (* end of [filename_push] *)

(* ****** ****** *)

(* end of [ats_filename.ml] *)
