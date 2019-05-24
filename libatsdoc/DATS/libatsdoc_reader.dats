(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustworthy Software, Inc.
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
// Start Time: July, 2011
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

staload "libatsdoc/SATS/libatsdoc_reader.sats"

(* ****** ****** *)

viewtypedef
freader (v:view) =
$extype_struct
"libatsdoc_reader_struct" of {
  pfres= v
, getchar= (!v | (*none*)) -<cloptr1> int
, freeres= ( v | (*none*)) -<cloptr1> void  
} // end of [freader]

(* ****** ****** *)

absviewt@ype reader0 = reader? // for initialization

(* ****** ****** *)

local

staload "libc/SATS/stdio.sats"

assume reader0 = freader (unit_v)?
assume reader_vt0ype = [v:view] freader (v)

in // in of [local]

(* ****** ****** *)

implement
reader_get_char (r) = r.getchar (r.pfres | (*none*))

(* ****** ****** *)

fun reader0_initialize_filp
  {m:file_mode}
  {l:addr} (
  pfmod: file_mode_lte (m, r)
, pffil: FILE m @ l
| r: &reader0 >> reader, p: ptr l
) : void = () where {
  viewdef v = FILE m @ l
  val getchar = lam
    (pffil: !v | (*none*)): int =<cloptr1> fgetc_err (pfmod | !p)
  // end of [getchar]
  val freeres = lam
    (pffil: v | (*none*)): void =<cloptr1> fclose_exn (pffil | p)
  prval () = r.pfres := pffil
  val () = r.getchar := getchar
  val () = r.freeres := freeres  
} // end of [reader0_initialize_filp]

(* ****** ****** *)

fun reader0_initialize_getc (
  r: &reader0 >> reader, getc: () -<cloptr1> int
) : void = () where {
  viewdef v = unit_v
  val getchar = __cast (getc) where {
    extern castfn __cast
      (f: () -<cloptr1> int): (!v | (*none*)) -<cloptr1> int
    // end of [extern]
  } // end of [val]
  val freeres = lam (
    pf: v | (*none*)
  ) : void =<cloptr1> let prval unit_v () = pf in (*none*) end 
  val () = r.pfres := unit_v ()
  val () = r.getchar := getchar
  val () = r.freeres := freeres
} // end of [reader0_initialize_getc]

(* ****** ****** *)

fun reader0_initialize_string
  {n:nat} {l:addr} (
  pfgc: free_gc_v (size_t?, l)
, pfat: sizeLte n @ l
| r: &reader0 >> reader, inp: string n, p: ptr l
) : void = () where {
//
  viewdef v = (
    free_gc_v (size_t?, l), sizeLte n @ l
  ) // end of [viewdef]
//
  val getchar = lam
    (pf: !v | (*none*)): int =<cloptr1> let
    prval pf1 = pf.1
    val i = !p
    prval () = pf.1 := pf1
  in
    if string_isnot_atend (inp, i) then let
      val c = string_get_char_at (inp, i)
      prval pf1 = pf.1      
      val () = !p := i + 1
      prval () = pf.1 := pf1
    in
      (int_of_char)c
    end else ~1 (*EOF*) // end of [if]
  end // end of [val]
//
  val freeres = lam
    (pf: v | (*none*)): void =<cloptr1> ptr_free {size_t?} (pf.0, pf.1 | p)
  // end of [freeres]
//
  val () = r.pfres := (pfgc, pfat)
  val () = r.getchar := getchar
  val () = r.freeres := freeres
} // end of [reader0_initialize_string]

(* ****** ****** *)

fun reader0_uninitialize (
  r: &reader >> reader0
) : void = () where {
  stavar v: view
  prval pf = r.pfres : v
  val () = r.freeres (pf | (*none*))
  val () = cloptr_free (r.getchar)
  val () = cloptr_free (r.freeres)
  prval () = __assert (r) where {
    extern prfun __assert (r: &freader(v)? >> reader0): void
  } // end of [prval]
} // end of [reader0_uninitialize]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

local

extern
prfun reader0_encode (r: &reader? >> reader0): void
extern
prfun reader0_decode (r: &reader0 >> reader?): void

in // in of [local]

(* ****** ****** *)

implement
reader_initialize_filp
  (pfmod, pffil | r, p) = () where {
  prval () = reader0_encode (r)
  val () = reader0_initialize_filp (pfmod, pffil | r, p)
} // end of [reader_initialize_filp]

implement
reader_initialize_getc
  (r, getc) = () where {
  prval () = reader0_encode (r)
  val () = reader0_initialize_getc (r, getc)
} // end of [reader_initialize_getc]

implement
reader_initialize_string
  (r, inp) = () where {
  val [n:int] inp = (string1_of_string)inp
  val (pfgc, pfat | p) = ptr_alloc<size_t> ()
  val () = !p := (size1_of_int1)0
  prval () = reader0_encode (r)
  val () = reader0_initialize_string (pfgc, pfat | r, inp, p)
} // end of preader_initialize_string]

(* ****** ****** *)

implement
reader_uninitialize
  (r) = () where {
  val () = reader0_uninitialize (r)
  prval () = reader0_decode (r)
} // end of [reader_uninitialize]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

(* end of [libatsdoc_reader.dats] *)
