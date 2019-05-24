(* ******************************************************************* *)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(* ******************************************************************* *)

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
// Start time: July 2013
//
(* ****** ****** *)
//
// For generating various tagging information on declarations
//
(* ****** ****** *)

extern
castfn cast2ptr {a:type} (x: a):<> ptr
extern
castfn cast2fileref {a:type} (x: a):<> FILEref
extern
castfn ptr0_vtake
  {a:viewt@ype} (p: ptr):<> [l:addr] (a@l, a@l -<lin,prf> void | ptr l)

(* ****** ****** *)

staload "ats_syntax.sats"

(* ****** ****** *)

typedef symbol = $Sym.symbol_t
typedef location = $Loc.location_t

(* ****** ****** *)

extern
fun fprint_symbol
  (out: FILEref, sym: symbol): void
overload fprint with fprint_symbol

(* ****** ****** *)

implement
fprint_symbol
  (out, sym) = let
//
val p = cast2ptr (out)
val (pf, fpf | p) = ptr0_vtake (p)
val () = $Sym.fprint_symbol (file_mode_lte_refl () | !p, sym)
prval () = fpf (pf)
//
in
  // nothing
end // end of [fprint_symbol]

(* ****** ****** *)

extern
fun taggen_symloc
  (out: FILEref, sym: symbol, loc: location): void
// end of [taggen_symloc]

implement
taggen_symloc
(
  out, sym, loc
) = () where {
//
val () = fprint_string (out, "{\n")
//
val () = fprint_string (out, "\"name\" : ")
val () =
(
  fprint_string (out, "\"");
  fprint_symbol (out, sym);
  fprint_string (out, "\"");
)
val () = fprint_string (out, ", \"nline\" : ")
val () = fprint_int (out, $Loc.location_begpos_line (loc))
val () = fprint_string (out, ", \"nchar\" : ")
val () = fprint_lint (out, $Loc.location_begpos_toff (loc))
val () = fprint_string (out, "\n")
//
val () = fprint_string (out, "}\n")
//
} (* end of [taggen_symloc] *)

(* ****** ****** *)

local

fun aux
(
  out: FILEref, d0c: d0ec, i: int
) : int = let
in
//
case+
  d0c.d0ec_node of
//
| D0Csexpdefs
  (
    opt, df, dfs
  ) => let
    val i = auxsexpdef (out, df, i)
    val i = auxsexpdeflst (out, dfs, i) in i
  end // end of [D0Csexpdefs]
//
| D0Csaspdec (d) => auxsaspdec (out, d, i)
//
| D0Cdatdecs
  (
    knd, dt, dts, dfs
  ) => let
    val i = auxdatdec (out, dt, i)
    val i = auxdatdeclst (out, dts, i)
    val i = auxsexpdeflst (out, dfs, i) in i
  end // end of [D0Cdatdecs]
//
| D0Cexndecs (d, ds) => let
    val i = auxexndec (out, d, i)
    val i = auxexndeclst (out, ds, i) in i
  end // end of [D0Cexndecs]
//
| D0Cdcstdecs
  (
    knd, s0qss, dc, dcs
  ) => let
    val i = auxdcstdec (out, dc, i)
    val i = auxdcstdeclst (out, dcs, i) in i
  end // end of [D0Cdcstdecs]
//
| D0Coverload (id, _) => auxi0de (out, id, i)
//
| D0Cfundecs
  (
    knd, s0qss, fd, fds
  ) => let
    val i = auxfundec (out, fd, i)
    val i = auxfundeclst (out, fds, i) in i
  end // end of [D0Cfundecs]
//
| D0Cimpdec (_, imp) => auximpdec (out, imp, i)
//
| _(*skipped*) => (i)
//
end (* end of [aux] *)

and auxlst
(
  out: FILEref, d0cs: d0eclst, i: int
) : int = let
in
//
case+ d0cs of
| list_cons
    (d0c, d0cs) => let
    val i = aux (out, d0c, i) in auxlst (out, d0cs, i)
  end // end of [list_cons]
| list_nil ((*void*)) => (i)
//
end (* end of [auxlst] *)

(* ****** ****** *)

and auxi0de
(
  out: FILEref, id: i0de, i: int
) : int = let
//
val sym = id.i0de_sym
val (
) = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, id.i0de_loc)
//
in
  i + 1
end // end of [auxi0de]

(* ****** ****** *)

and auxsexpdef
(
  out: FILEref, df: s0expdef, i: int
) : int = let
//
val sym = df.s0expdef_sym
val () = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, df.s0expdef_loc)
//
in
  i + 1
end // end of [auxsexpdef]

and auxsexpdeflst
(
  out: FILEref, dfs: s0expdeflst, i: int
) : int = let
in
//
case+ dfs of
| list_cons
    (df, dfs) => let
    val i = auxsexpdef (out, df, i) in auxsexpdeflst (out, dfs, i)
  end // end of [list_cons]
| list_nil ((*void*)) => (i)
//
end // end of [auxsexpdeflst]

(* ****** ****** *)

and auxsaspdec
(
  out: FILEref, d: s0aspdec, i: int
) : int = let
//
val qid = d.s0aspdec_qid
val sym = qid.sqi0de_sym
val () = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, qid.sqi0de_loc)
//
in
  i + 1
end // end of [auxsaspdec]

(* ****** ****** *)

and auxdatdec
(
  out: FILEref, dt: d0atdec, i: int
) : int = let
//
val sym = dt.d0atdec_sym
val () = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, dt.d0atdec_loc)
//
in
  i + 1
end // end of [auxdatdec]

and auxdatdeclst
(
  out: FILEref, dts: d0atdeclst, i: int
) : int = let
in
//
case+ dts of
| list_cons
    (dt, dts) => let
    val i = auxdatdec (out, dt, i) in auxdatdeclst (out, dts, i)
  end // end of [list_cons]
| list_nil ((*void*)) => (i)
//
end // end of [auxdatdeclst]

(* ****** ****** *)

and auxexndec
(
  out: FILEref, d: e0xndec, i: int
) : int = let
//
val sym = d.e0xndec_sym
val (
) = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, d.e0xndec_loc)
//
in
  i + 1
end // end of [auxexndec]

and auxexndeclst
(
  out: FILEref, ds: e0xndeclst, i: int
) : int = let
in
//
case+ ds of
| list_cons
    (d, ds) => let
    val i = auxexndec (out, d, i) in auxexndeclst (out, ds, i)
  end // end of [list_cons]
| list_nil ((*void*)) => (i)
//
end // end of [auxexndeclst]

(* ****** ****** *)

and auxdcstdec
(
  out: FILEref, dc: d0cstdec, i: int
) : int = let
//
val sym = dc.d0cstdec_sym
val () = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, dc.d0cstdec_loc)
//
in
  i + 1
end // end of [auxdcstdec]

and auxdcstdeclst
(
  out: FILEref, dcs: d0cstdeclst, i: int
) : int = let
in
//
case+ dcs of
| list_cons
    (dc, dcs) => let
    val i = auxdcstdec (out, dc, i) in auxdcstdeclst (out, dcs, i)
  end // end of [list_cons]
| list_nil ((*void*)) => (i)
//
end // end of [auxdcstdeclst]

(* ****** ****** *)

and auxfundec
(
  out: FILEref, fd: f0undec, i: int
) : int = let
//
val sym = fd.f0undec_sym
val () = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, fd.f0undec_loc)
//
in
  i + 1
end // end of [auxfundec]

and auxfundeclst
(
  out: FILEref, fds: f0undeclst, i: int
) : int = let
in
//
case+ fds of
| list_cons
    (fd, fds) => let
    val i = auxfundec (out, fd, i) in auxfundeclst (out, fds, i)
  end // end of [list_cons]
| list_nil ((*void*)) => (i)
//
end // end of [auxfundeclst]

and auximpdec
(
  out: FILEref, imp: i0mpdec, i: int
) : int = let
//
val qid = imp.i0mpdec_qid
val sym = qid.impqi0de_sym
val () = if i > 0 then fprint_string (out, ",\n")
val () = taggen_symloc (out, sym, imp.i0mpdec_loc)
//
in
  i + 1
end // end of [auximpdec]

in (* in of [local] *)

implement
fprint_taggen
(
  pf | fil, basename, d0cs
) = let
//
val out = cast2fileref(&fil)
//
val () = fprint_string (out, "{\n")
val () = fprint_string (out, "\"tagfile\" : \"")
val () = fprint_string (out, basename)
val () = fprint_string (out, "\",\n")
val () = fprint_string (out, "\"tagentarr\" : [\n")
//
val ntot = auxlst (out, d0cs, 0)
//
val () = fprint_string (out, "]\n")
val () = fprint_string (out, "}\n")
//
in
  // nothing
end // end of [fprint_taggen]

end // end of [local]

(* ****** ****** *)

(* end of [ats_syntax_taggen.dats] *)
