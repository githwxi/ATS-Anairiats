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
// Start time: June 2010
//
(* ****** ****** *)

staload Lst = "ats_list.sats"

(* ****** ****** *)

staload REF = "ats_reference.sats"
staload _(*anon*) = "ats_reference.dats"

(* ****** ****** *)

staload Glo = "ats_global.sats"
staload Fil = "ats_filename.sats"
staload Par = "ats_parser.sats"

(* ****** ****** *)

staload "ats_syntax.sats"
staload COMARG = "ats_comarg.sats"

(* ****** ****** *)

typedef comarg = $COMARG.comarg

(* ****** ****** *)

extern
fun fprint_target
  {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, basename: string
) : void // end of [fprint_target]

(* ****** ****** *)

extern fun depgen_d0ec (d: d0ec): void
extern fun depgen_d0eclst (ds: d0eclst): void
extern fun depgen_d0exp (d0e: d0exp): void

(* ****** ****** *)

local

viewtypedef
deplst = List_vt (string)

val the_deplst
  : ref (deplst) =
  $REF.ref_make_elt<deplst> (list_vt_nil)
// end of [val]

in (* in of [local] *)

fun the_deplst_get
  (): deplst = xs where
{
//
val
(
  vbox pf | p
) =
  $REF.ref_get_view_ptr (the_deplst)
//
val xs = !p
val () = !p := list_vt_nil ()
//
} // end of [the_deplst_get]

fun the_deplst_push
  (dep: string) = () where
{
//
val
(
  vbox pf | p
) =
  $REF.ref_get_view_ptr (the_deplst)
//
val () = !p := list_vt_cons (dep, !p)
//
} // end of [the_deplst_push]

(* ****** ****** *)
//
// HX-2010-07-19: for ATS/GEIZELLA only
//
extern
fun string_index_of_char_from_right
  {n:nat} (str: string n, c: char):<> ssizeBtw (~1, n)
  = "atspre_string_index_of_char_from_right"
// end of [string_index_of_char_from_right]

(* ****** ****** *)

implement
fprint_target{m}
(
  pf | out, basename
) = let
//
val [n:int]
  basename = string1_of_string (basename)
val k = string_index_of_char_from_right (basename, '.')
val (
) = (
  case+ 0 of
  | _ when k >= 0 => let
      val k = size_of_ssize (k)
      fun pr {i:nat | i <= n} .<n-i>. (
          out: &FILE m
        , basename: string n, k: size_t, i: size_t i
        ) : void =
        if string_isnot_atend (basename, i) then let
          val c =  if i = k then '_' else basename[i]
          val () = fprint_char (pf | out, c)
        in
          pr (out, basename, k, i+1)
        end // end of [if]
      val () = pr (out, basename, k, 0)
      val () = fprint_string (pf | out, ".c")
    in
      // nothing
    end // end of [_ when ...]
  | _ => fprint_string (pf | out, basename)
) (* end of [val] *)
//
in
  // nothing
end // end of [fprint_target]

(* ****** ****** *)

implement
fprint_depgen {m}
(
  pf | out, basename, d0cs
) = let
//
val () = depgen_d0eclst (d0cs)
//
val deplst = the_deplst_get ()
val deplst = $Lst.list_vt_reverse (deplst)
val () = fprint_target (pf | out, basename)
val () = fprint_string (pf | out, " :")
val () = let
  fun loop
  (
    out: &FILE m, xs: deplst
  ) : void =
  (
    case+ xs of
    | ~list_vt_cons
        (x, xs) => let
        val () = fprintf1_exn (pf | out, " %s", @(x)) in loop (out, xs)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  )
in
  loop (out, deplst)
end // end of [val]
//
val () = fprint_newline (pf | out)
//
in
  // nothing
end // end of [fprint_depgen]

end // end of [local]

(* ****** ****** *)

fun depgen_d0explst
  (d0es: d0explst): void =
  $Lst.list_foreach_fun (d0es, depgen_d0exp)
// end of [depgen_d0explst]

fun depgen_d0explstlst
  (d0ess: d0explstlst): void =
  $Lst.list_foreach_fun (d0ess, depgen_d0explst)
// end of [depgen_d0explstlst]

fun depgen_d0expopt
  (x: d0expopt): void = case+ x of
  | Some d0e => depgen_d0exp (d0e) | None () => ()
// end of [depgen_d0expopt]

fun depgen_labd0explst
  (ld0es: labd0explst): void = case+ ld0es of
  | LABD0EXPLSTnil () => ()
  | LABD0EXPLSTcons (_, d0e, ld0es) => (
      depgen_d0exp (d0e); depgen_labd0explst (ld0es)
    ) // end of [LABD0EXPLSTcons]
// end of [depgen_labd0explst]

(* ****** ****** *)

fun depgen_c0lau (c0l: c0lau)
  : void = depgen_d0exp (c0l.c0lau_body)
fun depgen_c0laulst (c0ls: c0laulst)
  : void = $Lst.list_foreach_fun (c0ls, depgen_c0lau)
// end of [depgen_c0laulst]

(* ****** ****** *)

fun depgen_v0aldec
  (v0d: v0aldec) = depgen_d0exp (v0d.v0aldec_def)
// end of [depgen_v0aldec]

fun depgen_f0undec
  (f0d: f0undec) = depgen_d0exp (f0d.f0undec_def)
// end of [depgen_f0undec]

fun depgen_v0ardec
  (v0d: v0ardec) = depgen_d0expopt (v0d.v0ardec_ini)
// end of [depgen_v0ardec]

fun depgen_guad0ec_node
  (node: guad0ec_node): void =
  case+ node of
  | GD0Cone (_, d0cs) => depgen_d0eclst (d0cs)
  | GD0Ctwo (_, d0cs1, d0cs2) => (
      depgen_d0eclst (d0cs1); depgen_d0eclst (d0cs2)
    ) // end of [GD0Ctwo]
  | GD0Ccons (_, d0cs, _, gd0cnode) => (
      depgen_d0eclst (d0cs); depgen_guad0ec_node gd0cnode
    ) // end of [GD0Ccons]
// end of [depgen_guad0ec_node]

(* ****** ****** *)

implement
depgen_d0exp (d0e0) =
  case+ d0e0.d0exp_node of
  | D0Eann (d0e, _) => depgen_d0exp (d0e)
  | D0Eapp (d0e1, d0e2) => (
      depgen_d0exp (d0e1); depgen_d0exp (d0e2)
    )
  | D0Earrinit (_, od0e, d0es) => (
      depgen_d0expopt (od0e); depgen_d0explst (d0es)
    ) // end of [D0Earrinit]
  | D0Earrpsz (_, d0e_elts) => depgen_d0exp (d0e_elts)
  | D0Earrsub (_, _, d0ess) => depgen_d0explstlst (d0ess)
  | D0Ecaseof (_, d0e, c0ls) => (
      depgen_d0exp (d0e); depgen_c0laulst (c0ls)
    ) // end of [D0Ecaseof]
(*
  | D0Echar _ => ()
  | D0Ecstsp _ => ()
  | D0Ecrypt _ => ()
  | D0Edelay _ => ()
  | D0Edynload _ => ()
  | D0Eeffmask _ => ()
  | D0Eempty _ => ()
*)
  | D0Eexist (_, _, d0e) => depgen_d0exp (d0e)
(*
  | D0Eextval _ => ()
*)
  | D0Efix (_, _, _, _, _, d0e) => depgen_d0exp (d0e)
(*
  | D0Efloat _ => ()
  | D0Efloatsp _ => ()
*)
  | D0Efoldat (d0es) => depgen_d0explst (d0es)
  | D0Efor (
      _, _, d0e_ini, d0e_test, d0e_post, d0e_body
    ) => () where {
      val () = depgen_d0exp (d0e_ini)
      val () = depgen_d0exp (d0e_test)
      val () = depgen_d0exp (d0e_post)
      val () = depgen_d0exp (d0e_body)
    } // end of [D0Efor]
  | D0Efreeat d0es => depgen_d0explst (d0es)
(*
  | D0Eide _ => ()
*)
  | D0Eif (
      _, d0e_test, d0e_then, od0e_else
    ) => () where {
      val () = depgen_d0exp (d0e_test)
      val () = depgen_d0exp (d0e_then)
      val () = depgen_d0expopt (od0e_else)
    } // end of [D0Eif]
(*
  | D0Eint _ => ()
  | D0Eintsp _ => ()
*)
  | D0Elam (_, _, _, _, d0e) => depgen_d0exp (d0e)
  | D0Elet (d0cs, d0e) => (
      depgen_d0eclst (d0cs); depgen_d0exp (d0e)
    ) // end of [D0Elet]
  | D0Elist d0es => depgen_d0explst (d0es)
  | D0Elist2 (d0es1, d0es2) => (
      depgen_d0explst (d0es1); depgen_d0explst (d0es2)
    ) // end of [D0Elist2]
(*
  | D0Eloopexn _ => ()
*)
  | D0Elst (_, _, d0e) => depgen_d0exp (d0e)
  | D0Emacsyn (_, d0e) => depgen_d0exp (d0e)
(*
  | D0Eopide _ => ()
  | D0Eptrof _ => ()
  | D0Eqid _ => ()
*)
  | D0Eraise d0e => depgen_d0exp (d0e)
  | D0Erec (_, ld0es) => depgen_labd0explst (ld0es)
(*
  | D0Escaseof _ => ()
  | D0Esel_lab _ => ()
*)
  | D0Esel_ind (_, d0ess) => depgen_d0explstlst (d0ess)
  | D0Eseq (d0es) => depgen_d0explst (d0es)
(*
  | D0Esexparg _ => ()
*)
  | D0Esif (_, _, d0e_then, d0e_else) => (
      depgen_d0exp (d0e_then); depgen_d0exp (d0e_else)
    ) // end of [D0Esif]
(*
  | D0Estring _ => ()
*)
  | D0Estruct (ld0es) => depgen_labd0explst (ld0es)
(*
  | D0Etmpid _ => ()
  | D0Etop _ => ()
*)
  | D0Etrywith (_, d0e, c0ls) => begin
      depgen_d0exp (d0e); depgen_c0laulst (c0ls)
    end // end of [D0Etrywith]
  | D0Etup (_, d0es) => depgen_d0explst (d0es)
  | D0Etup2 (_, d0es1, d0es2) => (
      depgen_d0explst (d0es1); depgen_d0explst (d0es2)
    ) // end of [D0Etup2]
  | D0Eviewat _ => ()
  | D0Ewhere (d0e, d0cs) => (
      depgen_d0exp (d0e); depgen_d0eclst (d0cs)
    ) // end of [D0Ewhere]
  | D0Ewhile (_, _, d0e_test, d0e_body) => (
      depgen_d0exp (d0e_test); depgen_d0exp (d0e_body)
    ) // end of [D0Ewhile]
  | _ => ()
// end of [depgen_d0exp]

(* ****** ****** *)

fun try_path_basename
  (name: string): Option_vt (string) = let
(*
val () = printf ("try_path_basename: name = %s\n", @(name))
*)
//
fun loop (
  ps: List (string), name: string
) : Option_vt(string) =
  case+ ps of
  | list_cons (p, ps) => let
      val pname =
        $Fil.filename_append (p, name)
      val test = test_file_exists (pname)
    in
      if test then let
        val pname = $Fil.path_normalize (pname)
      in
        Some_vt (pname)
      end else
        loop (ps, name)
      // end of [if]
    end // end of [list_cons]
  | list_nil () => None_vt ()
// end of [loop]
//
val filename = $Fil.the_filename_get ()
val partname = $Fil.filename_part (filename)
val partname2 = $Fil.filename_merge (partname, name)
val isexi = test_file_exists (partname2)
//
in
  if isexi then let
    val partname2 =
      $Fil.path_normalize (partname2)
    // end of [val]
  in
    Some_vt (partname2)
  end else
    loop ($Glo.the_IATSdirlst_get (), name)
  // end of [if]
end // end of [try_path_basename]

(* ****** ****** *)

implement
depgen_d0ec (d) = let
in
//
case+ d.d0ec_node of
(*
| D0Cfixity _ => ()
| D0Cnonfix _ => ()
*)
| D0Cinclude
    (stadyn, basename) => let
    val opt = try_path_basename (basename)
  in
    case+ opt of
    | ~Some_vt (pname) => the_deplst_push (pname)
    | ~None_vt () => ()
  end // end of [DOCinclude]
(*
| D0Csymintr _ => ()
| D0Ce0xpdef _ => ()
| D0Ce0xpact _ => ()
| D0Cdatsrts _ => ()
| D0Csrtdefs _ => ()
| D0Cstacons _ => ()
| D0Cstacsts _ => ()
| D0Cstavars _ => ()
| D0Csexpdefs _ => ()
| D0Csaspdec _ => ()
| D0Cdcstdecs _ => ()
| D0Cdatdecs _ => ()
| D0Cexndecs _ => ()
| D0Cclassdec _ => ()
| D0Coverload _ => ()
| D0Cextype _ => ()
| D0Cextval _ => ()
| D0Cextcode _ => ()
*)
| D0Cvaldecs (_, v0d, v0ds) => let
    val () = depgen_v0aldec (v0d)
    val () = $Lst.list_foreach_fun (v0ds, depgen_v0aldec)
  in
    // nothing
  end // end of [D0Cvaldecs]
| D0Cvaldecs_rec (v0d, v0ds) => let
    val () = depgen_v0aldec (v0d)
    val () = $Lst.list_foreach_fun (v0ds, depgen_v0aldec)
  in
    // nothing
  end // end of [D0Cvaldecs]
| D0Cfundecs (_, _, f0d, f0ds) => let
    val () = depgen_f0undec (f0d)
    val () = $Lst.list_foreach_fun (f0ds, depgen_f0undec)
  in
    // nothing
  end // end of [D0Cfundecs]
| D0Cvardecs (v0d, v0ds) => let
    val () = depgen_v0ardec (v0d)
    val () = $Lst.list_foreach_fun (v0ds, depgen_v0ardec)
  in
    // nothing
  end // end of [D0Cvardecs]
(*
| D0Cmacdefs _ => ()
*)
| D0Cimpdec (_, i0d) => depgen_d0exp (i0d.i0mpdec_def)
(*
| D0Cdynload _ => ()
*)
| D0Cstaload (_, basename) => let
    val opt = try_path_basename (basename)
  in
    case+ opt of
    | ~Some_vt (pname) => the_deplst_push (pname)
    | ~None_vt () => ()
  end // end of [D0Cstaload]
| D0Clocal (ds1, ds2) => () where {
    val () = depgen_d0eclst (ds1); val () = depgen_d0eclst (ds2)
  } // end of [D0Clocal]
| D0Cguadec (_, gd0c) => depgen_guad0ec_node (gd0c.guad0ec_node)
| _ => ()
//
end // end of [depgen_d0ec]

(* ****** ****** *)

implement
depgen_d0eclst (ds) = $Lst.list_foreach_fun (ds, depgen_d0ec)

(* ****** ****** *)

(* end of [ats_syntax_depgen.dats] *)
