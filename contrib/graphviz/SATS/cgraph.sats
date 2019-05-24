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
typedef struct Agtag_s Agtag_t;
*)
viewtypedef Agtag_t =
  $extype_struct "Agtag_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agtag = Agtag_t

(*
typedef struct Agobj_s Agobj_t;	/* generic object header */
*)
viewtypedef Agobj_t =
  $extype_struct "Agobj_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agobj = Agobj_t

(*
typedef struct Agraph_s Agraph_t;	/* graph, subgraph (or hyperedge) */
*)
viewtypedef Aggraph_t =
  $extype_struct "Aggraph_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Aggraph = Aggraph_t

(*
typedef struct Agnode_s Agnode_t;	/* node (atom) */
*)
viewtypedef Agnode_t =
  $extype_struct "Agnode_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agnode = Agnode_t

(*
typedef struct Agedge_s Agedge_t;	/* node pair */
*)
viewtypedef Agedge_t =
  $extype_struct "Agedge_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agedge = Agedge_t

(*
typedef struct Agdesc_s Agdesc_t;	/* graph descriptor */
*)
viewtypedef Agdesc_t =
  $extype_struct "Agdesc_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agdesc = Agdesc_t

(*
typedef struct Agmemdisc_s Agmemdisc_t;	/* memory allocator */
*)
viewtypedef Agmemdisc_t =
  $extype_struct "Agmemdisc_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agmemdisc = Agmemdisc_t

(*
typedef struct Agiddisc_s Agiddisc_t;	/* object ID allocator */
*)
viewtypedef Agiddisc_t =
  $extype_struct "Agiddisc_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agiddisc = Agiddisc_t

(*
typedef struct Agiodisc_s Agiodisc_t;	/* IO services */
*)
viewtypedef Agiodisc_t =
  $extype_struct "Agiodisc_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agiodisc = Agiodisc_t

(*
typedef struct Agdisc_s Agdisc_t;	/* union of client discipline methods */
*)
viewtypedef Agdisc_t =
  $extype_struct "Agdisc_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agdisc = Agdisc_t

(*
typedef struct Agdstate_s Agdstate_t;	/* client state (closures) */
*)
viewtypedef Agdstate_t =
  $extype_struct "Agdstate_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agdstate = Agdstate_t

(*
typedef struct Agsym_s Agsym_t;	/* string attribute descriptors */
*)
viewtypedef Agsym_t =
  $extype_struct "Agsym_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agsym = Agsym_t

(*
typedef struct Agattr_s Agattr_t;	/* string attribute container */
*)
viewtypedef Agattr_t =
  $extype_struct "Agattr_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agattr = Agattr_t

(*
typedef struct Agcbdisc_s Agcbdisc_t;	/* client event callbacks */
*)
viewtypedef Agcbdisc_t =
  $extype_struct "Agcbdisc_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agcbdisc = Agcbdisc_t

(*
typedef struct Agcbstack_s Agcbstack_t;	/* enclosing state for cbdisc */
*)
viewtypedef Agcbstack_t =
  $extype_struct "Agcbstack_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agcbstack = Agcbstack_t

(*
typedef struct Agclos_s Agclos_t;	/* common fields for graph/subgs */
*)
viewtypedef Agclos_t =
  $extype_struct "Agclos_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agclos = Agclos_t

(*
typedef struct Agrec_s Agrec_t;	/* generic runtime record */
*)
viewtypedef Agrec_t =
  $extype_struct "Agrec_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agrec = Agrec_t

(*
typedef struct Agdatadict_s Agdatadict_t;	/* set of dictionaries per graph */
*)
viewtypedef Agdatadict_t =
  $extype_struct "Agdatadict_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agdatadict = Agdatadict_t

(*
typedef struct Agedgepair_s Agedgepair_t;	/* the edge object */
*)
viewtypedef Agedgepair_t =
  $extype_struct "Agedgepair_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agedgepair = Agedgepair_t

(*
typedef struct Agsubnode_s Agsubnode_t;
*)
viewtypedef Agsubnode_t =
  $extype_struct "Agsubnode_t" of {
  _rest= undefined_vt // HX: no manual initialization 
}
stadef Agsubnode = Agsubnode_t

(* ****** ****** *)

(* end of [cgraph.sats] *)
