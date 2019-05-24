(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: July 2007
//
(* ****** ****** *)

(* ats_global: handling some global variables *)

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anon*) = "ats_reference.dats"

(* ****** ****** *)

staload "ats_global.sats"

(* ****** ****** *)

local

typedef dirlst = List (string)

val the_IATSdirlst =
  ref_make_elt<dirlst> (list_nil ())
// end of [the_IATSdirlst]

in // in of [local]

implement
the_IATSdirlst_get () = !the_IATSdirlst

implement
the_IATSdirlst_push (dir) =
  !the_IATSdirlst := list_cons (dir, !the_IATSdirlst)
// end of [the_IATSdirlst_push]

end // end of [local]

(* ****** ****** *)

val () = initialize () where {
  extern fun initialize (): void = "atsopt_global_initialize"
} // end of [val]

(* ****** ****** *)

%{$

static
ats_int_type the_dynloadflag = 0 ;

ats_int_type
atsopt_dynloadflag_get
  () { return the_dynloadflag ; }
// end of [atsopt_dynloadflag_get]

ats_void_type
atsopt_dynloadflag_set
  (ats_int_type flag) {
  the_dynloadflag = flag ; return ;
} // end of [atsopt_dynloadflag_set]

/* ****** ****** */

static
ats_ptr_type
the_dynloadfun_name = (ats_ptr_type)0 ;

ats_ptr_type
atsopt_dynloadfun_name_get
  () { return the_dynloadfun_name ; }
// end of ...

ats_void_type
atsopt_dynloadfun_name_set
  (ats_ptr_type name) {
  the_dynloadfun_name = name ; return ;
} // end of [atsopt_dynloadfun_name_set]

%} // end of [%{$]

(* ****** ****** *)


%{$

static
ats_ptr_type
the_atsopt_namespace = (ats_ptr_type)0 ;

ats_ptr_type
atsopt_namespace_get
  () { return the_atsopt_namespace ; }
// end of [atsopt_namespace_get]

ats_void_type
atsopt_namespace_set
  (ats_ptr_type prfx) {
  the_atsopt_namespace = prfx ; return ;
} // end of [atsopt_namespace_set]

%} // end of [%{$]

(* ****** ****** *)

%{$

ats_void_type
atsopt_global_initialize () {
  ATS_GC_MARKROOT (&the_dynloadfun_name, sizeof(ats_ptr_type)) ;
  ATS_GC_MARKROOT (&the_atsopt_namespace, sizeof(ats_ptr_type)) ;
  return ;
} // end of [atsopt_global_initialize]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_global.dats] *)
