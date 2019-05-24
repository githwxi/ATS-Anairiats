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

(*
typedef struct graph_t graph_t;
*)
viewtypedef graph_t =
$extype_struct "graph_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef graph = graph_t

viewtypedef node_t =
$extype_struct "node_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef node = node_t

viewtypedef edge_t =
$extype_struct "edge_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef edge = edge_t

absviewtype
pgraph_viewtype (l:addr) = ptr
stadef pgraph = pgraph_viewtype
viewtypedef pgraph0 = [l:addr] pgraph (l)
viewtypedef pgraph1 = [l:addr | l > null] pgraph (l)
//
absviewtype
pnode_viewtype (l1:addr, l2:addr) = ptr // l1:graph; l2:node
stadef pnode = pnode_viewtype
viewtypedef pnode0 (l1:addr) = [l2:addr] pnode (l1, l2)
viewtypedef pnode1 (l1:addr) = [l2:addr | l2 > null] pnode (l1, l2)
//
absviewtype
pedge_viewtype (l1:addr, l2:addr) = ptr // l1:graph; l2:edge
stadef pedge = pedge_viewtype
viewtypedef pedge0 (l1:addr) = [l2:addr] pedge (l1, l2)
viewtypedef pedge1 (l1:addr) = [l2:addr | l2 > null] pedge (l1, l2)
//
absviewtype pgrapharr (n:int, l:addr)
//
(* ****** ****** *)

prfun pnode_free
  {l1,l2:addr} (
  g: !pgraph l2, pn: pnode (l1, l2)
) : void // end of [pnode_free]

prfun pedge_free
  {l1,l2:addr} (
  g: !pgraph l2, pe: pedge (l1, l2)
) : void // end of [pedge_free]

(* ****** ****** *)

fun pnode_get_name
  {l1,l2:addr | l2 > null}
  (pn: !pnode (l1, l2))
  : [l:agz] (minus (pnode (l1,l2), strptr l) | strptr l)
// end of [pnode_get_name]

fun pedge_get_head
  {l1,l2:addr | l2 > null}
  (pe: !pedge (l1, l2)): pnode1 (l1)
// end of [pedge_get_head]

fun pedge_get_tail
  {l1,l2:addr | l2 > null}
  (pe: !pedge (l1, l2)): pnode1 (l1)
// end of [pedge_get_tail]

(* ****** ****** *)
//
fun aginit (): void = "mac#atsctrb_aginit"
//
macdef AGRAPH = $extval (int, "AGRAPH")
macdef AGRAPHSTRICT = $extval (int, "AGRAPHSTRICT")
macdef ADIGRAPH = $extval (int, "ADIGRAPH")
macdef ADIGRAPHSTRICT = $extval (int, "ADIGRAPHSTRICT")
//
fun agopen (
  name: string, type: int
) : pgraph0 = "mac#atsctrb_agopen"
fun agopen_exn (
  name: string, type: int
) : pgraph1 = "mac#atsctrb_agopen_exn"
//
fun agclose {l:agz}
  (g: pgraph l): void = "mac#atsctrb_agclose"
//
fun agread (
  filr: FILEref
) : pgraph0 = "mac#atsctrb_agread"
fun agread_exn (
  filr: FILEref
) : pgraph1 = "mac#atsctrb_agread_exn"
//
fun agwrite {l:agz}
  (g: !pgraph l, filr: FILEref): [i:int | i <= 0] int(*err*)
//
(* ****** ****** *)

fun agdelete
  {l1,l2:agz}
  (g: !pgraph l1, obj: ptr l2): void = "mac#atsctrb_agdelete"
// end of [agdelete]

fun agdelete_graph
  {l1,l2:agz}
  (g: !pgraph l1, sg: pgraph l2): void = "mac#atsctrb_agdelete"
// end of [agdelete_graph]

(* ****** ****** *)

absview agstrdup_v
  (l1:addr, l2:addr) // l1: graph; l2: string
// end of [agstrdup_v]

fun agstrdup {l1:agz} (
  g: !pgraph l1, x: string
) : [l2:agz] (agstrdup_v (l1, l2) | strptr l2)
  = "mac#atsctrb_agstrdup"

fun agstrdup_html {l1:agz} (
  g: !pgraph l1, x: string
) : [l2:agz] (agstrdup_v (l1, l2) | strptr l2)
  = "mac#atsctrb_agstrdup_html"

fun agstrfree {l1,l2:addr} (
  pf: agstrdup_v (l1, l2) | g: !pgraph l1, x: strptr l2
) : void = "mac#atsctrb_agstrfree"

(* ****** ****** *)

(* end of [types.sats] *)
