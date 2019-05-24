(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

absviewtype
nref_viewt0ype_viewtype (a:viewt@ype) = ptr // non-reentrant
stadef nref = nref_viewt0ype_viewtype

(* ****** ****** *)

fun{a:viewt@ype}
refcount_make (x: a):<> nref (a)

fun{a:viewt@ype}
refcount_ref (r: !nref a):<!ref> nref a

fun{a:viewt@ype}
refcount_unref (
  r: nref a, x: &a? >> opt (a, b)
) :<!ref> #[b: bool] bool(b) // end of [fun]

fun{a:viewt@ype}
refcount_unref_fun
  (r: nref a, f: (&a >> a?) -<fun> void):<!ref> void
// end of [refcount_unref_fun]

fun{a:viewt@ype}
refcount_get_count (r: !nref a):<!ref> uint

(* ****** ****** *)

absviewtype
nrefout (a:viewt@ype, l:addr) = nref (a)

prfun refcount_addback
  {a:viewt@ype} {l:addr}
  (pf: a @ l | r: !nrefout (a, l) >> nref (a)): void
// end of [refcount_addback]

fun{a:viewt@ype}
refcount_takeout
  (r: !nref a >> nrefout (a, l)):<!ref> #[l:addr] (a @ l | ptr l)
// end of [refcount_takeout]

(* ****** ****** *)

(* end of [refcount.sats] *)
