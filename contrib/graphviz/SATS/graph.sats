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

(*
typedef struct Agraph_t Agraph_t;
*)
viewtypedef Agraph_t =
  $extype_struct "Agraph_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agraph = Agraph_t

absviewtype Agraph_ptr (l:addr) = ptr

(* ****** ****** *)

(*
typedef struct Agnode_t Agnode_t;
*)
viewtypedef Agnode_t =
  $extype_struct "Agnode_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agnode = Agnode_t

(*
typedef struct Agedge_t Agedge_t;
*)
viewtypedef Agedge_t =
  $extype_struct "Agedge_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agedge = Agedge_t

(*
typedef struct Agdict_t Agdict_t;
*)
viewtypedef Agdict_t =
  $extype_struct "Agdict_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agdict = Agdict_t

(*
typedef struct Agsym_t Agsym_t;
*)
viewtypedef Agsym_t =
  $extype_struct "Agsym_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agsym = Agsym_t

(*
typedef struct Agdata_t Agdata_t;
*)
viewtypedef Agdata_t =
  $extype_struct "Agdata_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agdata = Agdata_t

(*
typedef struct Agproto_t Agproto_t;
*)
viewtypedef Agproto_t =
  $extype_struct "Agproto_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agproto = Agproto_t

(* ****** ****** *)

(* end of [graph.sats] *)
