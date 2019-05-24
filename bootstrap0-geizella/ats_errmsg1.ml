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

module Err = Ats_error
module Loc = Ats_location

module P = Printf

open Ats_syntax

(* ****** ****** *)

let sexp_tr_errmsg () = begin
  P.eprintf "sexp_tr: The fixity of -> is not available.\n";
  Err.abort ();
end (* end of [sexp_tr_errmsg] *)

let e0xp_tr_errmsg loc = begin
  P.eprintf "%a: e0xp_tr: the operator needs to be applied.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [e0xp_tr_errmsg] *)

(* ****** ****** *)

let e0xp1_eval_errmsg_app loc = begin
  P.eprintf "%a: e0xp1_eval: an identifier is required.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [e0xp1_eval_errmsg_app] *)

let e0xp1_eval_errmsg_id loc id = begin
  P.eprintf "%a: e0xp1_eval: unrecognized identifier <%a>.\n"
    Loc.fprint loc fprint_id id;
  Err.abort ();
end (* end of [e0xp1_eval_errmsg_id] *)

let e0xp1_eval_errmsg_list loc = begin
  P.eprintf "%a: e0xp1_eval: illegal list expression.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [e0xp1_eval_errmsg_list] *)

let e0xp1_eval_appid_errmsg_arity loc = begin
  P.eprintf "%a: e0xp1_eval_appid: wrong arity.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [e0xp1_eval_appid_errmsg_arity] *)

let e0xp1_eval_appid_errmsg_id loc (id: id) = begin
  P.eprintf "%a: e0xp1_eval_appid: unrecognized operation <%a>.\n"
    Loc.fprint loc fprint_id id;
  Err.abort ();
end (* end of [e0xp1_eval_appid_errmsg_id] *)

let e0xp1_eval_oper_errmsg loc = begin
  P.eprintf "%a: illegal argument.\n" Loc.fprint loc;
  Err.abort ();
end (* end of [e0xp1_eval_eval_oper_errmsg] *)

(* ****** ****** *)

let srt_tr_errmsg_opr loc = begin
  P.eprintf "%a: the operator needs to be applied.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [srt_tr_errmsg] *)

let sexp_tr_errmsg_opr loc = begin
  P.eprintf "%a: the operator needs to be applied.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [srt_tr_errmsg_opr] *)

let pat_tr_errmsg_opr loc = begin
  P.eprintf "%a: the operator needs to be applied.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [pat_tr_errmsg_opr] *)

let dexp_tr_errmsg_opr loc = begin
  P.eprintf "%a: the operator needs to be applied.\n"
    Loc.fprint loc;
  Err.abort ();
end (* end of [dexp_tr_errmsg_opr] *)

(* ****** ****** *)

let dec_dyncst_tr_aux1_errmsg (x: dfarg0) = begin
  P.eprintf "%s%a: unascribed variable: <%a>\n"
    Err.prompt Loc.fprint x.dfarg0_loc fprint_did x.dfarg0_name;
  Err.abort ();
end (* end of [dec_dyncst_tr_aux1_errmsg] *)

(* ****** ****** *)

(* end of [ats_errmsg1.ml] *)
