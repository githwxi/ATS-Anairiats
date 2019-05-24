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

(* ats_counter: implementing some counters *)

(* ****** ****** *)

module PR = Printf
module Sym = Ats_symbol

(* ****** ****** *)

type count = int64

let zero = 0L

let eq (c1: count) (c2: count): bool = (c1 = c2)
let neq (c1: count) (c2: count): bool = (c1 <> c2)
let compare (c1: count) (c2: count): int = compare c1 c2

let fprint (out: out_channel) (c: count) = PR.fprintf out "%Li" c
let string_of (c: count) = PR.sprintf "%Li" c

(* ****** ****** *)

module CountOrd: Map.OrderedType with type t = count = struct
  type t = count
  let compare = compare
end (* end of [module] *)

module CountMap: Map.S with type key = count = Map.Make (CountOrd)

(* ****** ****** *)

type counter = {
  counter_get: unit -> count;
  counter_get_and_inc: unit -> count;
  counter_inc: unit -> unit;
  counter_reset: unit -> unit;
  counter_set: count -> unit;
}

let make_counter () = begin
  let count: count ref = ref Int64.zero in
    {
      counter_get= (function () -> !count);
      counter_get_and_inc= (function () -> let n = !count in count := Int64.succ n; n);
      counter_inc= (function () -> count := !count);
      counter_reset= (function () -> count := Int64.zero);
      counter_set= (function n -> count := n);
    }
end (* end of [make_counter] *)

(* ****** ****** *)

let srt2_dat_counter = make_counter ()
let srt2_dat_new_stamp () = srt2_dat_counter.counter_get_and_inc ()

let scst2_stamp_counter = make_counter ()
let scst2_new_stamp () = scst2_stamp_counter.counter_get_and_inc ()

(* ****** ****** *)

let struct2_stamp_counter = make_counter ()
let struct2_new_stamp () = struct2_stamp_counter.counter_get_and_inc ()

(* ****** ****** *)

let svar2_stamp_counter = make_counter ()

let svar2_new_stamp () = svar2_stamp_counter.counter_get_and_inc ()

let svar2_name_counter = make_counter ()

let svar2_new_name () = Sym.make_with_string
  (Int64.format "$%d" (svar2_name_counter.counter_get_and_inc ()))

let svar2_new_name_with_prefix (name) = Sym.make_with_string
  (name ^ Int64.format "$%d" (svar2_name_counter.counter_get_and_inc ()))

(* ****** ****** *)

let sVar2_stamp_counter = make_counter ()
let sVar2_new_stamp () = sVar2_stamp_counter.counter_get_and_inc ()

let sVar2_name_counter = make_counter ()
let sVar2_new_name () = sVar2_name_counter.counter_get_and_inc ()

(* ****** ****** *)

let dcon2_stamp_counter = make_counter ()
let dcon2_new_stamp () = dcon2_stamp_counter.counter_get_and_inc ()

let dcst2_stamp_counter = make_counter ()
let dcst2_new_stamp () = dcst2_stamp_counter.counter_get_and_inc ()

let dmac2_stamp_counter = make_counter ()
let dmac2_new_stamp () = dmac2_stamp_counter.counter_get_and_inc ()

let dvar2_stamp_counter = make_counter ()
let dvar2_new_stamp () = dvar2_stamp_counter.counter_get_and_inc ()

let dvar2_name_counter = make_counter ()
let dvar2_new_name () = 
  Sym.make_with_string
    (Int64.format "$%d" (dvar2_name_counter.counter_get_and_inc ()))

(* ****** ****** *)

let funlab_stamp_counter = make_counter ()
let funlab_new_stamp () = funlab_stamp_counter.counter_get_and_inc ()

let tmplab_stamp_counter = make_counter ()
let tmplab_new_stamp () = tmplab_stamp_counter.counter_get_and_inc ()

let tmpvar_stamp_counter = make_counter ()
let tmpvar_new_stamp () = tmpvar_stamp_counter.counter_get_and_inc ()

(* ****** ****** *)

let initialize () = begin
  srt2_dat_counter.counter_reset ();
  scst2_stamp_counter.counter_reset ();
  svar2_stamp_counter.counter_reset ();
  svar2_name_counter.counter_reset ();

  dcon2_stamp_counter.counter_reset ();
  dcst2_stamp_counter.counter_reset ();
  dmac2_stamp_counter.counter_reset ();
  dvar2_stamp_counter.counter_reset ();
  dvar2_name_counter.counter_reset ();

  funlab_stamp_counter.counter_reset ();
  tmplab_stamp_counter.counter_reset ();
  tmpvar_stamp_counter.counter_reset ();
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_counter.ml] *)
