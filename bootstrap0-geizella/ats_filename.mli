(*******************************************************************)
(*                                                                 *)
(*                        Applied Type System                      *)
(*                                                                 *)
(*                          (c) Hongwei Xi                         *)
(*                                                                 *)
(*                            2002 - 2007                          *)
(*                                                                 *)
(*                         Boston University                       *)
(*                                                                 *)
(*                   Distributed by permission only.               *)
(*                                                                 *)
(*******************************************************************)

(* ats_filename: handling filenames *)

type filename

val nonfile : filename
val stdin : filename

val filename_make : string -> filename

val filename_basename : filename -> string
val filename_fullname : filename -> string
val filename_fullname_id : filename -> string

val compare : filename -> filename -> int

val eq : filename -> filename -> bool
val neq : filename -> filename -> bool

val lt : filename -> filename -> bool
val lte : filename -> filename -> bool
val gt : filename -> filename -> bool
val gte : filename -> filename -> bool


val filename_get : unit -> filename
val filename_pop : unit -> unit
val filename_push : filename -> unit

val fprint : out_channel -> filename -> unit
val prerr : filename -> unit
val print : filename -> unit

type path = string

val path_list_pop : unit -> unit
val path_list_push : path -> unit
val path_list_reset : unit -> unit
