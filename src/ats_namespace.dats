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
// Time: November 2007
//
(* ****** ****** *)

staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_namespace.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

#define THIS_FILE "ats_namespace.dats"

(* ****** ****** *)

(*
typedef name = $Sym.symbol_t // HX: defined in [ats_namespace.sats]
*)
typedef namelst = List name
typedef namelstlst = List namelst
typedef saved = @(namelst, namelstlst)
typedef savedlst = List saved

(* ****** ****** *)

val the_namelst: ref namelst = ref_make_elt (list_nil ())
val the_namelstlst: ref namelstlst = ref_make_elt (list_nil ())
val the_savedlst: ref savedlst = ref_make_elt (list_nil ())

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_namespace)"

(* ****** ****** *)

implement
the_namespace_add name = begin
  !the_namelst := list_cons (name, !the_namelst)
end // end of [the_namespace_add]

(* ****** ****** *)

implement
the_namespace_search {a} (f) = let
//
  fun auxlst (f: !name -<cloptr1> Option_vt a, ns: namelst): Option_vt a =
    case+ ns of
    | list_cons (n, ns) => begin
        case+ f (n)  of ~None_vt () => auxlst (f, ns) | ans => ans
      end // end of [list_cons]
    | list_nil () => None_vt () // end of [list_nil]
  // end of [auxlst]
//
  fun auxlstlst (f: !name -<cloptr1> Option_vt a, nss: namelstlst): Option_vt a =
    case+ nss of
    | list_cons (ns, nss) => begin
        case+ auxlst (f, ns) of ~None_vt () => auxlstlst (f, nss) | ans => ans
      end // end of [auxlstlst]
    | list_nil () => None_vt () // end of [list_nil]
  // end of [auxlstlst]
//
in
//
  case+ auxlst (f, !the_namelst) of
  | ~None_vt () => auxlstlst (f, !the_namelstlst) | ans => ans
//
end // end of [the_namespace_search]

(* ****** ****** *)

implement
the_namespace_pop () = let
//
fn pop_err (): void = begin
  prerr_interror ();
  prerr ": pop_err: the_namlstlst is empty"; prerr_newline ();
  exit (1)
end // end of [pop_err]
//
in
//
  case+ !the_namelstlst of
  | list_cons (ns: namelst, nss: namelstlst) =>
      (!the_namelst := ns; !the_namelstlst := nss)
  | list_nil () => pop_err ()
//
end // end of [the_namespace_pop]

implement
the_namespace_push () = begin
  !the_namelstlst := list_cons (!the_namelst, !the_namelstlst);
  !the_namelst := list_nil (); 
end // end of [the_namespace_push]

(* ****** ****** *)

implement
the_namespace_save () = let
//
val ns: namelst = !the_namelst
val () = !the_namelst := list_nil ()
val nss: namelstlst = !the_namelstlst
val () = !the_namelstlst := list_nil ()
//
in
//
!the_savedlst := list_cons (@(ns, nss), !the_savedlst)
//
end // end of [the_namespace_save]

(* ****** ****** *)

implement
the_namespace_restore () = let
//
fn err (): void = begin
  prerr_interror ();
  prerr ": the_namespace_restore: the_savedlst is empty"; prerr_newline ();
  exit (1)
end // end of [err]
//
in
//
  case+ !the_savedlst of
  | list_cons (x, xs) => begin
      !the_savedlst := xs; !the_namelst := x.0; !the_namelstlst := x.1
    end // end of [list_cons]
  | list_nil () => err () // end of [list_nil]
//
end // end of [the_namespace_restore]

(* ****** ****** *)

implement
the_namespace_localjoin () = let
//
fn err (): void = begin
  prerr_interror ();
  prerr ": the_namespace_localjoin: the_namelstlst is too short";
  prerr_newline ();
  exit (1)
end // end of [err]
//
in
//
  case+ !the_namelstlst of
  | list_cons (_, list_cons (ns, nss)) => begin
      !the_namelst := $Lst.list_append (!the_namelst, ns);
      !the_namelstlst := nss
    end // end of [list_cons]
  | _ => err () // nil or singleton
//
end // end of [the_namespace_localjoin]

(* ****** ****** *)

implement
the_namespace_initialize () = let
  val () = !the_namelst := list_nil ()
  val () = !the_namelstlst := list_nil ()
  val () = !the_savedlst := list_nil ()
in
  // empty
end // end of [the_namespace_initialize]

(* ****** ****** *)

(* end of [ats_namespace.dats] *)
