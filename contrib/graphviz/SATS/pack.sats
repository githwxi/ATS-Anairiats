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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: October, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)
//
staload "contrib/graphviz/SATS/types.sats"
//
(* ****** ****** *)

/*
Agraph_t **ccomps(Agraph_t*, int*, char*);
*/
//
// HX:
// In order to free the returned array, one needs
// to call [agdelete(g, sg)] for each sg in it and
// then to call [free] on the array
//
fun ccomps {l1:agz} (
  g: !pgraph l1, ncc: &int? >> int n, pfx: Stropt
) : #[n:nat;l2:addr] pgrapharr (n, l2)
  = "mac#atsctrb_ccomps"

(* ****** ****** *)

(* end of [pack.sats] *)
