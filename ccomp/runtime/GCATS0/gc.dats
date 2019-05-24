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

%{^

#include "prelude/CATS/array.cats"

#include "gc.cats"
#include "globals.cats"
#include "block0.cats"
#include "block1.cats"
#include "marking.cats"
#include "sweeping.cats"
#include "collecting.cats"

%}

(* ****** ****** *)

#include "gc.hats"
staload "gc.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

implement gcats0_malloc_err (bsz) = let
  val [l:addr] (pf | ptr) = block0_malloc_err bsz
in
  if ptr > null then let
    prval block0_malloc_succ (pf1, pf2) = pf
    val () = the_blocklst0_cons (pf1 | ptr)
  in
    #[l+sizeof(block0) | (Some_v pf2 | ptr + sizeof<block0>)]
  end else let
    prval block0_malloc_fail () = pf
  in
    #[l | (None_v () | ptr)]
  end
end

implement gcats0_malloc (bsz) = let
  val (pf | ptr) = block0_malloc_err bsz
in
  if ptr > null then
    let
       prval block0_malloc_succ (pf1, pf2) = pf
    in
       the_blocklst0_cons (pf1 | ptr); (pf2 | ptr + sizeof<block0>)
    end
  else begin
    let prval block0_malloc_fail () = pf in
      exit_errmsg (1, "Exit: [gcats0_malloc] failed.\n")
    end
  end
end // end of [gcats0_malloc]

%{

ats_ptr_type
gcats0_calloc (n, sz) {
 int nsz = n * sz ;
 ats_ptr_type p = gcats0_malloc(nsz) ;
 return memset(p, 0, nsz) ;
}

%}

extern prval resource_discharge {v:view} (pf: v):<> void

implement gcats0_free (pf_bytes | ptr) = let
  val (pf0 | p) = the_blocklst0_take_err ptr
in
  if p <> null then
    let prval blocklst0_take_succ pf_block = pf0 in
      block0_free (pf_block, pf_bytes | p)
    end
  else let
    prval blocklst0_take_fail () = pf0
    prval _ = resource_discharge pf_bytes // memory leak
  in
(*
    exit_prerrf {void}
      (1, "Exit: gcats0_free(%p): invalid pointer\n", @(ptr))
*)
    exit (1)
  end
end // end of [gcats0_free]

implement gcats0_realloc_err (pf_bytes | ptr, bsz) =
  the_blocklst0_realloc_err (pf_bytes | ptr, bsz)

implement gcats0_realloc (pf_bytes | ptr, bsz) = let
  val (pf_realloc | ptr_new) = the_blocklst0_realloc_err (pf_bytes | ptr, bsz)
in
  if ptr_new > null then
    let prval realloc_succ pf_bytes_new = pf_realloc in
      (pf_bytes_new | ptr_new)
    end
  else let
    prval realloc_fail pf_bytes = pf_realloc
    prval _ = resource_discharge pf_bytes // memory leak
  in
    exit_errmsg (1, "Exit: [gcats0_realloc] failed.\n")
  end
end // end of [gcats0_realloc]

(* ****** ****** *)

(* end of gc.dats *)
