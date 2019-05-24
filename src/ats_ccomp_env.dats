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
// Time: April 2008
//
(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Glo = "ats_global.sats"
staload Lst = "ats_list.sats"
staload _(*anon*) = "ats_list.dats"
staload Map = "ats_map_lin.sats"
staload Set = "ats_set_fun.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_trans4.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_set_fun.dats"

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_ccomp_env)"

(* ****** ****** *)

extern
fun compare_strlst_strlst
  (ss1: strlst, ss2: strlst):<> Sgn
overload compare with compare_strlst_strlst

implement
compare_strlst_strlst (ss1, ss2) = begin
  case+ (ss1, ss2) of
  | (list_cons (s1, ss1), list_cons (s2, ss2)) => let
      val sgn = compare (s1, s2)
    in
      if sgn <> 0 then sgn else compare (ss1, ss2)
    end // end of [list_cons, list_cons]
  | (list_cons _, list_nil ()) =>  1
  | (list_nil (), list_cons _) => ~1
  | (list_nil (), list_nil ()) =>  0
end // end [compare_strlst_strlst]

extern
fun compare_labstrlst_labstrlst
  (lss1: labstrlst, lss2: labstrlst):<> Sgn
overload compare with compare_labstrlst_labstrlst

implement
compare_labstrlst_labstrlst
  (lss1, lss2) = begin case+ (lss1, lss2) of
  | (LABSTRLSTcons (l1, s1, lss1),
     LABSTRLSTcons (l2, s2, lss2)) => let
      val sgn = $Lab.compare_label_label (l1, l2)
    in
      if sgn <> 0 then sgn else let
        val sgn = compare_string_string (s1, s2)
      in
        if sgn <> 0 then sgn else compare (lss1, lss2)
      end
    end
  | (LABSTRLSTcons _, LABSTRLSTnil ()) =>  1
  | (LABSTRLSTnil (), LABSTRLSTnil ()) =>  0
  | (LABSTRLSTnil (), LABSTRLSTcons _) => ~1
end // end [compare_labstrlst_labstrlst]

extern
fun compare_typkey_typkey
  (tk1: typkey, tk2: typkey):<> Sgn
overload compare with compare_typkey_typkey

implement
compare_typkey_typkey (tk1, tk2) = begin
  case+ (tk1, tk2) of
  | (TYPKEYrec lss1, TYPKEYrec lss2) => compare (lss1, lss2)
  | (TYPKEYrec _, _) => ~1
  | (TYPKEYsum (i1, ss1), TYPKEYsum (i2, ss2)) =>
      let val sgn = compare (i1, i2) in
        if sgn <> 0 then sgn else compare (ss1, ss2)
      end
  | (TYPKEYsum _, TYPKEYrec _) =>  1
  | (TYPKEYsum _, TYPKEYuni _) => ~1
  | (TYPKEYuni lss1, TYPKEYuni lss2) => compare (lss1, lss2)
  | (TYPKEYuni _, _) =>  1
end // end of [compare_typkey_typkey]

(* ****** ****** *)

local

val the_typdef_base = ref_make_elt<string> ("anairiats")
val the_typdef_count = ref_make_elt<int> (0)

in // in of [local]

extern fun typdef_base_get (): string
extern fun typdef_base_set (base: string): void

implement typdef_base_get () = !the_typdef_base
implement typdef_base_set (base) = !the_typdef_base := base

extern fun typdef_count_get_and_inc (): int

implement
typdef_count_get_and_inc () = begin
  (!the_typdef_count := n+1; n) where { val n = !the_typdef_count }
end // end of [typdef_count_get]

end // end of [local]

(* ****** ****** *)

local

val the_typdeflst = ref_make_elt<typdeflst> (TYPDEFLSTnil ())

fn typdeflst_reverse
  (xs: typdeflst): typdeflst = let
  fun aux (xs: typdeflst, ys: typdeflst)
    : typdeflst = begin case+ xs of
    | TYPDEFLSTcons (_(*tk*), _(*name*), !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end // end of [TYPDEFLSTcons]
    | ~TYPDEFLSTnil () => ys
  end // end of [aux]
in
  aux (xs, TYPDEFLSTnil ())
end // end of [typdeflst_reverse]

in

extern
fun typdeflst_add (tk: typkey, name: string): void

implement
typdeflst_add (tk, name) = let
  val (pfbox | p) = ref_get_view_ptr (the_typdeflst)
  prval vbox pf = pfbox
in
  !p := TYPDEFLSTcons (tk, name, !p)
end // end of [local]

implement typdeflst_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_typdeflst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := TYPDEFLSTnil (); res
  end // end of [val]
in
  typdeflst_reverse (res)
end // end of [typdeflst_get]

end // end of [local]

(* ****** ****** *)

local

viewtypedef
typdefmap = $Map.map_vt (typkey, string)

fn typdefmap_nil () =
  $Map.map_make (compare_typkey_typkey)
// end of [typdefmap_nil]

val the_typdefmap =
  ref_make_elt<typdefmap> (typdefmap_nil ())
// end of [the_typdefmap]

in // in of [local]

(* ****** ****** *)

extern fun typdefmap_add_rec (tk: typkey): string
extern fun typdefmap_add_sum (tk: typkey): string
extern fun typdefmap_add_uni (tk: typkey): string

(* ****** ****** *)

implement
typdefmap_add_rec (tk) = let
  val base = typdef_base_get ()
  val n = typdef_count_get_and_inc ()
  val name_rec = let
    val prfx = $Glo.atsopt_namespace_get ()
  in
    if stropt_is_some prfx then let
      val prfx = stropt_unsome prfx
      val name = tostringf ("%s%s_rec_%i", @(prfx, base, n)) in
      string_of_strptr (name)
    end else let
      val name = tostringf ("%s_rec_%i", @(base, n)) in
      string_of_strptr (name)
    end // end of [if]
  end // end of [val]
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_insert (!p, tk, name_rec)
  end // end of [val]
in
  name_rec
end // end of [typdefmap_add_rec]

implement
typdefmap_add_sum (tk) = let
  val base = typdef_base_get ()
  val n = typdef_count_get_and_inc ()
  val name_sum = let
    val prfx = $Glo.atsopt_namespace_get ()
  in
    if stropt_is_some prfx then let
      val prfx = stropt_unsome prfx
      val name = tostringf ("%s%s_sum_%i", @(prfx, base, n)) in
      string_of_strptr (name)
    end else let
      val name = tostringf ("%s_sum_%i", @(base, n)) in
      string_of_strptr (name)
    end // end of [if]
  end // end of [val]
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_insert (!p, tk, name_sum)
  end // end of [val]
in
  name_sum
end // end of [typdefmap_add_sum]

implement
typdefmap_add_uni (tk) = let
  val base = typdef_base_get ()
  val n = typdef_count_get_and_inc ()
  val name_uni = let // union
    val prfx = $Glo.atsopt_namespace_get ()
  in
    if stropt_is_some prfx then let
      val prfx = stropt_unsome prfx
      val name = tostringf ("%s%s_uni_%i", @(prfx, base, n)) in
      string_of_strptr (name)
    end else let
      val name = tostringf ("%s_uni_%i", @(base, n)) in
      string_of_strptr (name)
    end // end of [if]
  end // end of [val]
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_insert (!p, tk, name_uni)
  end // end of [val]
in
  name_uni
end // end of [typdefmap_add_uni]

implement
typdefmap_find (tk) = let
  val oname = let
    val (pfbox | p) = ref_get_view_ptr (the_typdefmap)
    prval vbox pf = pfbox
  in
    $Map.map_search (!p, tk)
  end // end of [val]
in
  case+ oname of
  | ~Some_vt name => name
  | ~None_vt () => let
      val name = (case+ tk of
        | TYPKEYrec _ => typdefmap_add_rec (tk)
        | TYPKEYsum _ => typdefmap_add_sum (tk)
        | TYPKEYuni _ => typdefmap_add_uni (tk)
      ) : string
      val () = typdeflst_add (tk, name)
    in
      name
    end // end of [None]
end // end of [typdefmap_find]

end // end of [local]

(* ****** ****** *)

local

val the_saspcstlst = ref_make_elt<saspcstlst> (list_vt_nil)

in

implement
saspcstlst_free (xs) = $Lst.list_vt_free (xs)

implement
the_saspcstlst_add (s2c) = let
  val (pfbox | p) = ref_get_view_ptr (the_saspcstlst)
  prval vbox pf = pfbox
in
 !p := list_vt_cons (s2c, !p)
end // end of [the_saspcstlst_add]

implement
the_saspcstlst_get () = s2cs where {
  val (pfbox | p) = ref_get_view_ptr (the_saspcstlst)
  prval vbox pf = pfbox
  val s2cs = !p
  val () = !p := list_vt_nil ()
} // end of [the_saspcstlst_get]

end // end of [local]

(* ****** ****** *)

local

val the_datcstlst =
  ref_make_elt<datcstlst> (DATCSTLSTnil ())
// end of [val]

fn datcstlst_reverse
  (xs: datcstlst): datcstlst = let
  fun aux (xs: datcstlst, ys: datcstlst)
    : datcstlst = begin case+ xs of
    | DATCSTLSTcons (_, !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end
    | ~DATCSTLSTnil () => ys
  end // end of [aux]
in
  aux (xs, DATCSTLSTnil ())
end // end of [datcstlst_reverse]

in

implement
datcstlst_free (s2cs) = begin
  case+ s2cs of
  | ~DATCSTLSTcons (_, s2cs) => datcstlst_free s2cs
  | ~DATCSTLSTnil () => ()
end // end of [datcstlst_free]

implement
the_datcstlst_add (s2c) = let
  val (pfbox | p) = ref_get_view_ptr (the_datcstlst)
  prval vbox pf = pfbox
in
 !p := DATCSTLSTcons (s2c, !p)
end // end of [the_datcstlst_add]

implement
the_datcstlst_adds (s2cs) = begin
  case+ s2cs of
  | S2CSTLSTcons (s2c, s2cs) => begin
      the_datcstlst_add s2c; the_datcstlst_adds s2cs
    end
  | S2CSTLSTnil () => ()
end // end of [the_datcstlst_adds]

implement
the_datcstlst_get () = let
  val s2cs = let
    val (pfbox | p) = ref_get_view_ptr (the_datcstlst)
    prval vbox pf = pfbox
    val s2cs = !p
  in
    !p := DATCSTLSTnil (); s2cs
  end
in
  datcstlst_reverse (s2cs)
end // end of [the_datcstlst_get]

end // end of [local]

(* ****** ****** *)

local

val the_exnconlst =
  ref_make_elt<exnconlst> (EXNCONLSTnil ())
// end of [val]

fn exnconlst_reverse
  (xs: exnconlst): exnconlst = let
  fun aux (xs: exnconlst, ys: exnconlst)
    : exnconlst = begin case+ xs of
    | EXNCONLSTcons (_, !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end
    | ~EXNCONLSTnil () => ys
  end // end of [aux]
in
  aux (xs, EXNCONLSTnil ())
end // end of [exnconlst_reverse]

in // in of [local]

implement
exnconlst_free (d2cs) = begin
  case+ d2cs of
  | ~EXNCONLSTcons (_, d2cs) => exnconlst_free d2cs
  | ~EXNCONLSTnil () => ()
end // end of [exnconlst_free]

implement
the_exnconlst_add (d2c) = let
  val (pfbox | p) = ref_get_view_ptr (the_exnconlst)
  prval vbox pf = pfbox
in
 !p := EXNCONLSTcons (d2c, !p)
end // end of [the_exnconlst_add]

implement
the_exnconlst_adds (d2cs) = begin
  case+ d2cs of
  | D2CONLSTcons (d2c, d2cs) => begin
      the_exnconlst_add d2c; the_exnconlst_adds d2cs
    end
  | D2CONLSTnil () => ()
end // end of [the_exnconlst_adds]

implement
the_exnconlst_get () = let
  val d2cs = let
    val (pfbox | p) = ref_get_view_ptr (the_exnconlst)
    prval vbox pf = pfbox
    val d2cs = !p
  in
    !p := EXNCONLSTnil (); d2cs
  end // end of [val]
in
  exnconlst_reverse (d2cs)
end // end of [the_exnconlst_get]

end // end of [local]

(* ****** ****** *)

local

viewtypedef vartypsetlst = List_vt (vartypset)

val the_vartypset =
  ref_make_elt<vartypset> ($Set.set_nil)
// end of [val]

val the_vartypsetlst =
  ref_make_elt<vartypsetlst> (list_vt_nil ())
// end of [val]

in // in of [local]

implement
the_vartypset_pop () = let
  var err: int = 0
  val x0 = !the_vartypset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_vartypsetlst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~list_vt_cons (x, xs) => begin
        $effmask_ref (!the_vartypset := x); !p := (xs: vartypsetlst)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ (!p); err := 1)
  end // end of [val]
  val () = if err > 0 then begin // error reporting
    prerr_interror (); prerr ": the_vartypset_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
in
  x0
end // end of [the_vartypset_pop]

implement
the_vartypset_push () = let
  val vts = !the_vartypset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_vartypsetlst)
    prval vbox pf = pfbox
  in
    !p := list_vt_cons (vts, !p);
  end // end of [val]
in
  !the_vartypset := $Set.set_nil
end // end of [the_vartypset_push]

implement
the_vartypset_add (vtp) = let
  val _new = $Set.set_insert<vartyp_t>
    (!the_vartypset, vtp, compare_vartyp_vartyp)
in
  !the_vartypset := _new
end // end of [the_vartypset_add]

end // end of [local]

implement
vartypset_d2varlst_make (vtps) = let
  viewtypedef d2varlst_vt = List_vt d2var_t
  var d2vs: d2varlst_vt = list_vt_nil ()
  viewdef V = d2varlst_vt @ d2vs; viewtypedef VT = ptr d2vs
  fn f (pf: !V | vtp: vartyp_t, env: !VT)
    :<> void = begin
    !env := list_vt_cons (vartyp_get_var vtp, !env)
  end // end of [fn]
  val () = vartypset_foreach_main {V} {VT} (view@ d2vs | vtps, f, &d2vs)
in
  $Lst.list_vt_reverse (d2vs)
end // end of [vartypset_d2varlst_make]

//

implement
vartypset_union (vtps1, vtps2) =
  $Set.set_union (vtps1, vtps2, compare_vartyp_vartyp)
// end of [vartypset_union]

implement
vartypset_foreach_main
  (pf | vtps, f, env) = $Set.set_foreach_main (pf | vtps, f, env)
// end of [vartypset_foreach_main]

implement
vartypset_foreach_cloptr
  (vtps, f) = $Set.set_foreach_cloptr (vtps, f)
// end of [vartypset_foreach_cloptr]

//

implement
print_vartypset (vtps) = let
  var i: int = 0
  fn f (
      pf: !int @ i
    | vtp: vartyp_t, p: !ptr i
    ) : void =
    let val i = !p; val () = !p := i + 1 in
      if i > 0 then print (", "); print_vartyp vtp
    end
  // end of [fn f]
  val () = begin
    vartypset_foreach_main {int @ i} {ptr i} (view@ i | vtps, f, &i)
  end // end of [val]
in
  // empty
end // end of [print_vartypset]

(*
//
// HX: this one is not used
//
implement
prerr_vartypset (vtps) = let
  var i: int = 0
  fn f (pf: !int @ i | vtp: vartyp_t, p: !ptr i): void =
    let val i = !p; val () = !p := i + 1 in
      if i > 0 then prerr (", "); prerr_vartyp vtp
    end
  val () = begin
    vartypset_foreach_main {int @ i} {ptr i} (view@ i | vtps, f, &i)
  end // end of [val]
in
  // empty
end // end of [prerr_vartypset]
*)

(* ****** ****** *)

local

viewtypedef funlabsetlst = List_vt (funlabset)

val the_funlabset = ref_make_elt<funlabset> ($Set.set_nil)
val the_funlabsetlst = ref_make_elt<funlabsetlst> (list_vt_nil ())

in // in of [local]

implement
the_funlabset_pop () = let
  var err: int = 0
  val x0 = !the_funlabset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_funlabsetlst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~list_vt_cons (x, xs) => begin
        $effmask_ref (!the_funlabset := x); !p := (xs: funlabsetlst)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ (!p); err := 1)
  end // end of [val]
  val () = if err > 0 then begin // error reporting
    prerr_interror (); prerr ": the_funlabset_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
in
  x0
end // end of [the_funlabset_pop]

implement
the_funlabset_push () = let
  val fls = !the_funlabset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_funlabsetlst)
    prval vbox pf = pfbox
  in
    !p := list_vt_cons (fls, !p);
  end // end of [val]
in
  !the_funlabset := $Set.set_nil
end // end of [the_funlabset_push]

implement
the_funlabset_add (fl) = let
  val _new = begin
    $Set.set_insert<funlab_t> (!the_funlabset, fl, compare_funlab_funlab)
  end // end of [val]
in
  !the_funlabset := _new
end // end of [the_funlabset_add]

implement
the_funlabset_mem (fl) = begin
  $Set.set_member<funlab_t> (!the_funlabset, fl, compare_funlab_funlab)
end // end of [the_funlabset_mem]

implement
funlabset_foreach_main
  (pf | fls, f, env) = $Set.set_foreach_main (pf | fls, f, env)
// end of [funlabset_foreach_main]

implement
funlabset_foreach_cloptr (fls, f) = $Set.set_foreach_cloptr (fls, f)

end // end of [local]

implement
print_funlabset (fls) = let
  var i: int = 0
  fn f (pf: !int @ i | fl: funlab_t, p: !ptr i): void =
    let val i = !p; val () = !p := i + 1 in
      if i > 0 then print (", "); print_funlab fl
    end
  val () = begin
    funlabset_foreach_main {int @ i} {ptr i} (view@ i | fls, f, &i)
  end // end of [val]
in
  // empty
end // end of [print_funlabset]

(*
//
// HX: this one is not used
//
implement
prerr_funlabset (fls) = let
  var i: int = 0
  fn f (pf: !int @ i | fl: funlab_t, p: !ptr i): void =
    let val i = !p; val () = !p := i + 1 in
      if i > 0 then prerr (", "); prerr_funlab fl
    end
  // end of [fn f]
  val () = begin
    funlabset_foreach_main {int @ i} {ptr i} (view@ i | fls, f, &i)
  end // end of [val]
in
  // empty
end // end of [prerr_funlabset]
*)

(* ****** ****** *)

local

assume dynconset_type = $Set.set_t (d2con_t)

val the_dynconset = ref_make_elt<dynconset> ($Set.set_nil)

in // in of [local]

implement
dynconset_foreach_main
  (pf | d2cs, f, env) = $Set.set_foreach_main (pf | d2cs, f, env)
// end of [dynconset_foreach_main]

implement
the_dynconset_add (d2c) = let
  val _new = $Set.set_insert<d2con_t> (!the_dynconset, d2c, compare_d2con_d2con)
in
  !the_dynconset := _new
end // end of [the_dynconset_add]

implement the_dynconset_get () = !the_dynconset

end // end of [local]

(* ****** ****** *)

local

assume dyncstset_type = $Set.set_t (d2cst_t)

viewtypedef dyncstsetlst = List_vt (dyncstset)

val the_dyncstset = ref_make_elt<dyncstset> ($Set.set_nil)
val the_dyncstsetlst = ref_make_elt<dyncstsetlst> (list_vt_nil ())

fn dyncstset_add (
  d2cset_ref: ref dyncstset, d2c: d2cst_t
) : void = let
  val loc0 = d2cst_get_loc d2c
  val hit0 = (if d2cst_is_proof (d2c)
    then hityp_proof else s2exp_tr (loc0, 1(*deep*), d2cst_get_typ d2c)
  ) : hityp
  val hit0 = hityp_normalize hit0
  val () = d2cst_set_hityp (d2c, Some hit0)
  val d2cset = !d2cset_ref
in
  !d2cset_ref := $Set.set_insert<d2cst_t> (d2cset, d2c, compare_d2cst_d2cst)
end // end of [the_dyncstset_add]

fn dyncstset_add_if
  (d2cset_ref: ref (dyncstset), d2c: d2cst_t): void =
  // a template constant should not be added!
  if d2cst_is_temp d2c then () else let
    val d2cset = !d2cset_ref
    val ismem = begin
      $Set.set_member<d2cst_t> (!d2cset_ref, d2c, compare_d2cst_d2cst)
    end // end of [val]
  in
    if ismem then () (*already added*) else dyncstset_add (d2cset_ref, d2c)
  end // end of [if]
// end of [dyncstset_add_if]

in // in of [local]

implement
dyncstset_foreach_main
  (pf | d2cs, f, env) = $Set.set_foreach_main (pf | d2cs, f, env)
// end of [dyncstset_foreach_main]

implement the_dyncstset_get () = !the_dyncstset

implement
the_dyncstset_add_if (d2c) =
  // a template constant should not be added!
  if d2cst_is_temp d2c then () else let
    val ismem = begin
      $Set.set_member<d2cst_t> (!the_dyncstset, d2c, compare_d2cst_d2cst)
    end // end of [val]
  in
    if ismem then () (*already added*) else dyncstset_add (the_dyncstset, d2c)
  end // end of [if]
// end of [the_dyncstset_add_if]

implement
the_dyncstsetlst_push () = let
  val d2cs = !the_dyncstset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_dyncstsetlst)
    prval vbox pf = pfbox
  in
    !p := list_vt_cons (d2cs, !p)
  end // end of [val]
  val () = !the_dyncstset := $Set.set_nil
in
  // empty
end // end of [the_dyncstsetlst_push]

implement
the_dyncstsetlst_pop () = let
  var err: int = 0
  val d2cs = !the_dyncstset
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_dyncstsetlst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~list_vt_cons (d2cs1, d2cslst1) => let
        val () = $effmask_ref (!the_dyncstset := d2cs1) in
        !p := (d2cslst1: dyncstsetlst)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ (!p); err := 1)
  end // end of [val]
  val () = if (err > 0) then begin
    prerr_interror (); prerr ": the_dyncstsetlst_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
in
  d2cs
end // end of [the_dyncstsetlst_pop]

end // end of [local]

(* ****** ****** *)

local

val the_extypelst = ref_make_elt<extypelst> (EXTYPELSTnil ())

in // in of [local]

implement
the_extypelst_add (name, hit) = let
  val (pfbox | p) = ref_get_view_ptr (the_extypelst)
  prval vbox pf = pfbox
in
  !p := EXTYPELSTcons (name, hit, !p)
end // end of [the_extypelst_add]

implement
the_extypelst_get () = let
  val (pfbox | p) = ref_get_view_ptr (the_extypelst)
  prval vbox pf = pfbox
  val res = !p; val () = !p := EXTYPELSTnil ()
in
  res
end // end of [the_extypelst_add]

end // end of [local]

(* ****** ****** *)

local

val the_extvalist = ref_make_elt<extvalist> (EXTVALLSTnil ())

fn extvalist_reverse
  (xs: extvalist): extvalist = let
  fun aux (xs: extvalist, ys: extvalist)
    : extvalist = begin case+ xs of
    | EXTVALLSTcons (_(*name*), _(*vp*), !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end
    | ~EXTVALLSTnil () => ys
  end // end of [aux]
in
  aux (xs, EXTVALLSTnil ())
end // end of [extvalist_reverse]

in // in of [local]

implement
the_extvalist_add (name, hit) = let
  val (pfbox | p) = ref_get_view_ptr (the_extvalist)
  prval vbox pf = pfbox
in
  !p := EXTVALLSTcons (name, hit, !p)
end // end of [the_extvalist_add]

implement
the_extvalist_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_extvalist)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := EXTVALLSTnil (); res
  end // end of [val]
in
  extvalist_reverse (res)
end // end of [the_extvalist_get]

implement
extvalist_free (exts) = begin case+ exts of
  | ~EXTVALLSTcons (_(*name*), _(*vp*), exts) => extvalist_free exts
  | ~EXTVALLSTnil () => ()
end // end of [extvalist_free]

end // end of [local]

(* ****** ****** *)

local

val the_extcodelst = ref_make_elt<extcodelst> (EXTCODELSTnil ())

fn extcodelst_reverse
  (xs: extcodelst): extcodelst = let
  fun aux (xs: extcodelst, ys: extcodelst)
    : extcodelst = begin case+ xs of
    | EXTCODELSTcons (
        _(*loc*), _(*pos*), _(*code*), !p_xs1
      ) => let
        val xs1_v = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1_v, xs)
      end
    | ~EXTCODELSTnil () => ys
  end // end of [aux]
in
  aux (xs, EXTCODELSTnil ())
end // end of [extcodelst_reverse]

in // in of [local]

implement
the_extcodelst_add (loc, pos, code) = let
  val (pfbox | p) = ref_get_view_ptr (the_extcodelst)
  prval vbox pf = pfbox
in
  !p := EXTCODELSTcons (loc, pos, code, !p)
end // end of [the_extcodelst_add]

implement
the_extcodelst_get () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_extcodelst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := EXTCODELSTnil (); res
  end // end of [res]
in
  extcodelst_reverse (res)
end // end of [the_extcodelst_get]

implement
extcodelst_free (codes) = begin case+ codes of
  | ~EXTCODELSTcons (_, _, _, codes) => extcodelst_free (codes)
  | ~EXTCODELSTnil () => ()
end // end of [extcodelst_free]

end // end of [local]

(* ****** ****** *)

local

val the_stafilelst =
  ref_make_elt<stafilelst> (STAFILELSTnil ())
// end of [val]

fn stafilelst_reverse
  (xs: stafilelst): stafilelst = let
  fun aux (xs: stafilelst, ys: stafilelst)
    : stafilelst = begin case+ xs of
    | STAFILELSTcons (_fil, _loadflag, !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end // end of [STAFILELSTcons]
    | ~STAFILELSTnil () => ys
  end // end of [aux]
in
  aux (xs, STAFILELSTnil ())
end // end of [stafilelst_reverse]

in // in of [local]

implement
the_stafilelst_add (fil, loadflag) = let
  val (pfbox | p) = ref_get_view_ptr (the_stafilelst)
  prval vbox pf = pfbox
in
  !p := STAFILELSTcons (fil, loadflag, !p)
end // end of [the_stafilelst_add]

implement
the_stafilelst_get () = let
  val res = res where {
    val (vbox pf | p) = ref_get_view_ptr (the_stafilelst)
    val res = !p; val () = !p := STAFILELSTnil ()
  } // end of [val]
in
  stafilelst_reverse (res)
end // end of [the_stafilelst_get]

implement
stafilelst_free (fils) = begin
  case+ fils of
  | ~STAFILELSTcons (_fil, _loadflag, fils) => stafilelst_free fils
  | ~STAFILELSTnil () => ()
end // end of [stafilelst_free]

end // end of [local]

(* ****** ****** *)

local

val the_dynfilelst =
  ref_make_elt<dynfilelst> (DYNFILELSTnil ())

in // in of [local]

implement
the_dynfilelst_add (fil) = let
  val (pfbox | p) = ref_get_view_ptr (the_dynfilelst)
  prval vbox pf = pfbox
in
  !p := DYNFILELSTcons (fil, !p)
end // end of [the_dynfilelst_add]

implement
the_dynfilelst_get () = let
  val (pfbox | p) = ref_get_view_ptr (the_dynfilelst)
  prval vbox pf = pfbox
  val res = !p; val () = !p := DYNFILELSTnil ()
in
  res
end // end of [the_dynfilelst_get]

implement
dynfilelst_free (fils) = begin
  case+ fils of
  | ~DYNFILELSTcons (fil, fils) => dynfilelst_free fils
  | ~DYNFILELSTnil () => ()
end // end of [dynfilelst_free]

end // end of [local]

(* ****** ****** *)

local

assume funlab_token = unit_v
val the_funlablst = ref_make_elt<funlablst_vt> (list_vt_nil ())

in // in of [local]

implement
funlab_pop (pf | (*none*)) = let
  prval unit_v () = pf
  var err: int = 0; val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_funlablst)
  in
    case+ !p of
    | ~list_vt_cons (_, fls) => !p := (fls: funlablst_vt)
    | list_vt_nil () => (fold@ (!p); err := 1)
  end // end of [val]
in
  if err > 0 then begin
    prerr_interror (); prerr ": funlab_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [funlab_pop]

implement
funlab_push (fl) = let
  val (vbox pf | p) = ref_get_view_ptr (the_funlablst)
  val () = !p := list_vt_cons (fl, !p)
in
  (unit_v () | ())
end // end of [funlab_push]

implement
funlab_top () = let
  fn err (): funlab_t = begin
    prerr_interror (); prerr ": funlab_top"; prerr_newline ();
    $Err.abort {funlab_t} ()
  end // end of [err]
  val (vbox pf | p) = ref_get_view_ptr (the_funlablst)
in
  case+ !p of
  | list_vt_cons (fl, _) => begin
      fold@ (!p); fl
    end // end of [list_vt_cons]
  | list_vt_nil () => begin
      fold@ (!p); $effmask_ref (err ())
    end // end of [list_vt_nil]
end // end of [funlab_top]

end // end of [local]

(* ****** ****** *)

local

typedef funentry = '{
  funentry_loc= loc_t // location of the function in the source
, funentry_lab= funlab_t // the funentry label
, funentry_lev= int
, funentry_vtps= vartypset // local variables
, funentry_vtps_flag= int // 0/1: changeable/finalized
, funentry_labset= funlabset // list of funentrys called
, funentry_ret= tmpvar_t // storing the funentry return
, funentry_body= instrlst // instructions of the funentry body
, funentry_tailjoin= tailjoinlst // mutual tail-recursion
} // end of [funentry]

assume funentry_t = funentry

in

extern typedef "funentry_t" = funentry

fn _funentry_make (
    loc: loc_t
  , fl: funlab_t
  , level: int
  , fls: funlabset
  , vtps: vartypset
  , tmp_ret: tmpvar_t
  , inss: instrlst
  ) : funentry = '{
  funentry_loc= loc
, funentry_lab= fl
, funentry_lev= level
, funentry_vtps= vtps
, funentry_vtps_flag= 0 // it needs to be finalized
, funentry_labset= fls
, funentry_ret= tmp_ret
, funentry_body= inss
, funentry_tailjoin= TAILJOINLSTnil ()
} // end of [_funentry_make]

implement funentry_make
   (loc, fl, level, fls, vtps, tmp_ret, inss) = begin
  _funentry_make (loc, fl, level, fls, vtps, tmp_ret, inss)
end // end of [funentry_make]

implement funentry_get_loc (entry) = entry.funentry_loc
implement funentry_get_lab (entry) = entry.funentry_lab
implement funentry_get_lev (entry) = entry.funentry_lev
implement funentry_get_vtps (entry) = entry.funentry_vtps
implement funentry_get_vtps_flag (entry) = entry.funentry_vtps_flag
implement funentry_get_labset (entry) = entry.funentry_labset
implement funentry_get_ret (entry) = entry.funentry_ret
implement funentry_get_body (entry) = entry.funentry_body
implement funentry_get_tailjoin (entry) = entry.funentry_tailjoin

end // end of [local]

implement
funentry_associate (entry) = let
  val fl = funentry_get_lab (entry)
in
  funlab_set_entry (fl, Some entry)
end // end of [funentry_associate]

local
//
// HX: transitive closure
//
fn funentry_get_labset_all
  (entry0: funentry_t): funlabset = let
  val level0 = funentry_get_lev (entry0)
  fun aux (fl: funlab_t):<cloptr1> void = let
    val entry = funlab_get_entry_some fl
    val level = funentry_get_lev (entry)
(*
    val () = begin
      print "funentry_labset_get_all: aux: fl = "; print fl; print_newline ();
      print "funentry_labset_get_all: aux: level = "; print level; print_newline ();
    end // end of [val]
*)
  in
    case+ 0 of
    | _ when level >= level0 => begin
        if the_funlabset_mem fl then () else begin
          let val () = the_funlabset_add (fl) in
            funlabset_foreach_cloptr (funentry_get_labset entry, aux)
          end // end of [let]
        end // end of [if]
      end // end of [_ when ...]
    | _ => the_funlabset_add (fl)
  end // end of [aux]
  val () = the_funlabset_push ()
  val fls0 = funentry_get_labset (entry0)
(*
  val () = begin
    print "funentry_labset_get_all: fls0 = "; print_funlabset fls0; print_newline ()
  end // end of [val]
*)
  val () = funlabset_foreach_cloptr (fls0, aux)
in
  the_funlabset_pop ()
end // end of [funentry_labset_get_all]

dataviewtype ENV (l:addr) = ENVcon (l) of (ptr l, int)

in (* in of [local] *)

implement
funentry_get_vtps_all (entry0) = let
(*
  val fl0 = funentry_lab_get entry0
  val () = begin
    print "funentry_vtps_get_all: entry0 = "; print fl0; print_newline ()
  end // end of [val]
*)
  val vtps_flag = funentry_get_vtps_flag (entry0)
  var vtps_all: vartypset = funentry_get_vtps (entry0)
  viewdef V = vartypset @ vtps_all
  viewtypedef VT = ENV (vtps_all)
  fun aux
    (pf: !V | fl: funlab_t, env: !VT)
    : void = let
    val+ ENVcon (p, level0) = env
    val entry = funlab_get_entry_some (fl)
    val level = funentry_get_lev (entry)
    val vtps = (
      if level < level0 then begin
        // higher-level should be handled earlier
        funentry_get_vtps_all (entry)
      end else begin // [level = level0]
        funentry_get_vtps (entry)
      end // end of [if]
    ) : vartypset
    val () = begin
      !p := $Set.set_union (vtps, !p, compare_vartyp_vartyp)
    end
  in
    fold@ env
  end // end of [aux]
  val () =
    if vtps_flag = 0 then let
      val level0 = funentry_get_lev (entry0)
      val fls = funentry_get_labset_all (entry0)
(*
      val () = begin
        print "funentry_vtps_get_all: fls = "; print_funlabset fls; print_newline ()        
      end // end of [val]
*)
      val env = ENVcon (&vtps_all, level0)
      val () = begin
        funlabset_foreach_main {V} {VT} (view@ vtps_all | fls, aux, env)
      end
      val+ ~ENVcon (_, _) = env
      val () = funentry_set_vtps (entry0, vtps_all)
      val () = funentry_set_vtps_flag (entry0)
    in
      // empty
    end
(*
  val () = begin
    print "funentry_vtps_get_all: vtps_all = "; print_vartypset vtps_all; print_newline ()
  end // end of [val]
*)
in
  vtps_all
end // end of [funentry_vtps_get_all]

end // end of [local]

(* ****** ****** *)

local

viewtypedef varindmap = $Map.map_vt (d2var_t, int)

dataviewtype ENV (l:addr, i:addr) = ENVcon (l, i) of (ptr l, ptr i)

fn varindmap_nil ():<> varindmap = begin
  $Map.map_make {d2var_t, int} (compare_d2var_d2var)
end // end of [varindmap]

val the_varindmap = ref_make_elt<varindmap> (varindmap_nil ())

in

implement
varindmap_find (d2v) = let
  val (pfbox | p) = ref_get_view_ptr (the_varindmap)
  prval vbox pf = pfbox
in
  $Map.map_search (!p, d2v)
end // end of [varindmap_find]

implement
varindmap_find_some (d2v) = begin
  case+ varindmap_find d2v of
  | ~Some_vt ind => ind | ~None_vt () => begin
      prerr_interror ();
      prerr ": varindmap_find: d2v = "; prerr_d2var d2v; prerr_newline ();
      $Err.abort {int} ()
    end // end of [None_vt]
end // end of [varindmap_find_some]

implement
funentry_varindmap_reset () = let
  val (pfbox | p) = ref_get_view_ptr (the_varindmap)
  prval vbox pf = pfbox
  val () = $Map.map_free<d2var_t,int> (!p)
in
  !p := varindmap_nil ()
end // end of [funentry_varindmap_reset]

implement
funentry_varindmap_set (vtps) = let
  var i: int = 0
  val [l:addr] (pfbox | r) = ref_get_view_ptr (the_varindmap)
  viewdef V = (varindmap @ l, int @ i)
  viewdef VT = ENV (l, i)
  fn f (pf: !V | vtp: vartyp_t, env: !VT):<> void = let
    prval @(pf_map, pf_int) = pf
    val+ ENVcon (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val () = $Map.map_insert (!p_l, vartyp_get_var vtp, i)
  in
    pf := (pf_map, pf_int); fold@ env
  end
  prval vbox pf_map = pfbox
  prval pf = @(pf_map, view@ i)
  val env = ENVcon (r, &i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f, env)
  val+ ~ENVcon (_, _) = env
in
  pf_map := pf.0; view@ i := pf.1
end // end of [funentry_varindmap_set]

end // end of [local]

(* ****** ****** *)

local

val the_funlablst = begin
  ref_make_elt<funlablst_vt> (list_vt_nil ())
end // end of [the_funlablst]

in // in of [local]

implement
funentry_add_lablst (fl) = let
(*
  val () = begin
    print "funentry_add_lablst: fl = "; print fl; print_newline ()
  end // end of [val]
*)
  val (pfbox | p) = ref_get_view_ptr (the_funlablst)
  prval vbox pf = pfbox
in
  !p := list_vt_cons (fl, !p)
end // end of [funentry_lablst_add]

implement
funentry_get_lablst () = let
  val res = let
    val (pfbox | p) = ref_get_view_ptr (the_funlablst)
    prval vbox pf = pfbox
    val res = !p
  in
    !p := list_vt_nil (); res
  end // end of [val]
in
  $Lst.list_vt_reverse (res)
end // end of [funentry_lablst_get]

end // end of [local]

(* ****** ****** *)

local

dataviewtype loopexnlablst =
  | LOOPEXNLABLSTcons of (
      tmplab_t(*init*), tmplab_t(*fini*), tmplab_t(*cont*), loopexnlablst
    )
  | LOOPEXNLABLSTnil of ()
// end of [loopexnlablst]

val the_loopexnlablst =
  ref_make_elt<loopexnlablst> (LOOPEXNLABLSTnil ())
// end of [the_loopexnlablst]

in

implement
loopexnlablst_push
  (tl_init, tl_fini, tl_cont) = let
  val (pfbox | p) = ref_get_view_ptr (the_loopexnlablst)
  prval vbox pf = pfbox
in
  !p := LOOPEXNLABLSTcons (tl_init, tl_fini, tl_cont, !p)
end // end of [loopexnlablst_push]

implement
loopexnlablst_pop () = let
  var err: int = 0
  val () = let
    val (pfbox | p) = ref_get_view_ptr (the_loopexnlablst)
    prval vbox pf = pfbox
  in
    case+ !p of
    | ~LOOPEXNLABLSTcons (_, _, _, tls) => (!p := tls)
    | LOOPEXNLABLSTnil () => (fold@ (!p); err := 1)
  end // end of [val]
in
  if err > 0 then begin
    prerr_interror (); prerr ": loopexnlablst_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [loopexnlablst_pop]

implement
loopexnlablst_get (i) = let
  fn tmplab_gen (): tmplab_t = begin
    prerr_interror (); prerr ": loopexnlablst_get"; prerr_newline ();
    $Err.abort {tmplab_t} ()
  end // end of [tmplab_gen]
  val (pfbox | p) = ref_get_view_ptr (the_loopexnlablst)
  prval vbox pf = pfbox
in
  case+ !p of
  | LOOPEXNLABLSTcons
      (_(*init*), tl_fini, tl_cont, _) => begin
      fold@ (!p); if i = 0 then tl_fini else tl_cont
    end // end of [LOOPEXNLABLSTcons]
  | LOOPEXNLABLSTnil () =>
      (fold@ (!p); $effmask_all (tmplab_gen ()))
end // end of [loopexnlablst_get]

end // end of [local]

(* ****** ****** *)

local

val the_glocstlst =
  ref_make_elt<glocstlst> (GLOCSTLSTnil ())
// end of [val]

fn glocstlst_reverse
  (xs: glocstlst): glocstlst = let
  fun aux (xs: glocstlst, ys: glocstlst)
    : glocstlst = begin case+ xs of
    | GLOCSTLSTcons_clo (_(*d2c*), !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end // end of [GLOCSTLSTcons_clo]
    | GLOCSTLSTcons_fun (_(*d2c*), !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end // end of [GLOCSTLSTcons_fun]
    | GLOCSTLSTcons_val (_(*d2c*), _(*vp*), !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end // end of [GLOCSTLSTcons_val]
    | ~GLOCSTLSTnil () => ys
  end // end of [aux]
in
  aux (xs, GLOCSTLSTnil ())
end (* end of [glocstlst_reverse] *)

in // in of [local]

implement
the_glocstlst_get () = let
  val xs = let
    val (vbox pf | p) = ref_get_view_ptr (the_glocstlst)
    val xs = !p
  in
    !p := GLOCSTLSTnil (); xs
  end // end of [val]
in
  glocstlst_reverse (xs)
end // end of [the_glocstlst_get]

(* ****** ****** *)

implement
the_glocstlst_add_clo (d2c) = let
  val (vbox pf | p) = ref_get_view_ptr (the_glocstlst)
in
  !p := GLOCSTLSTcons_clo (d2c, !p)
end // end of [the_glocstlst_add_clo]

implement
the_glocstlst_add_fun (d2c) = let
  val (vbox pf | p) = ref_get_view_ptr (the_glocstlst)
in
  !p := GLOCSTLSTcons_fun (d2c, !p)
end // end of [the_glocstlst_add_fun]

implement
the_glocstlst_add_val (d2c, vp) = let
  val (vbox pf | p) = ref_get_view_ptr (the_glocstlst)
in
  !p := GLOCSTLSTcons_val (d2c, vp, !p)
end // end of [the_glocstlst_add_val]

end // end of [local]

(* ****** ****** *)

local

val the_partvalst =
  ref_make_elt<partvalst> (PARTVALSTnil ())
// end of [val]

fn partvalst_reverse
  (xs: partvalst): partvalst = let
  fun aux (xs: partvalst, ys: partvalst)
    : partvalst = begin case+ xs of
    | PARTVALSTcons (_(*name*), _(*vp*), !p_xs1) => let
        val xs1 = !p_xs1; val () = (!p_xs1 := ys; fold@ (xs))
      in
        aux (xs1, xs)
      end // end of [PARTVALSTcons]
    | ~PARTVALSTnil () => ys
  end // end of [aux]
in
  aux (xs, PARTVALSTnil ())
end (* end of [partvalst_reverse] *)

in // in of [local]

implement
the_partvalst_get () = let
  val xs = let
    val (vbox pf | p) = ref_get_view_ptr (the_partvalst)
    val xs = !p
  in
    !p := PARTVALSTnil (); xs
  end // end of [val]
in
  partvalst_reverse (xs)
end // end of [the_partvalst_get]

implement
the_partvalst_add (name, vp) = let
  val (vbox pf | p) = ref_get_view_ptr (the_partvalst)
in
  !p := PARTVALSTcons (name, vp, !p)
end // end of [the_partvalst_add]

end // end of [local]

(* ****** ****** *)

local

viewtypedef
cstctx = $Map.map_vt (d2cst_t, valprim)

fn cstctx_nil ()
  : cstctx = $Map.map_make (compare_d2cst_d2cst)
// end of [cstctx]

val the_topcstctx = ref_make_elt<cstctx> (cstctx_nil ())

in // in of [local]

implement
the_topcstctx_add (d2c, vp) = let
  val (pfbox | p) = ref_get_view_ptr (the_topcstctx)
  prval vbox pf = pfbox
in
  $Map.map_insert (!p, d2c, vp)
end // end of [the_topcstctx_add]

implement
the_topcstctx_find (d2c) = let
  val (pfbox | p) = ref_get_view_ptr (the_topcstctx)
  prval vbox pf = pfbox
in
  $Map.map_search (!p, d2c)
end // end of [the_topcstctx_find]

end // end of [local]

(* ****** ****** *)

local

val the_valprimlst_free =
  ref_make_elt<valprimlst_vt> (list_vt_nil ())
// end of [the_valprimlst_free]

in // in of [local]

implement
the_valprimlst_get_free () = let
  val (vbox pf | p) = ref_get_view_ptr (the_valprimlst_free)
  val vps = !p; val () = !p := list_vt_nil ()
in
  $Lst.list_vt_reverse (vps)
end // end of [the_valprimlst_free_get]

implement
the_valprimlst_add_free (vp) = let
  val (vbox pf | p) = ref_get_view_ptr (the_valprimlst_free)
in
  !p := list_vt_cons (vp, !p)
end // end of [the_valprimlst_free_add]

end // end of [local]

(* ****** ****** *)

%{$

ats_void_type
atsopt_funentry_set_vtps
  (ats_ptr_type entry, ats_ptr_type vtps) {
  ((funentry_t)entry)->atslab_funentry_vtps = vtps ; return ;
} // end of [atsopt_funentry_set_vtps]

ats_void_type
atsopt_funentry_set_vtps_flag
  (ats_ptr_type entry) {
  ((funentry_t)entry)->atslab_funentry_vtps_flag = 1 ; return ;
} // end of [atsopt_funentry_set_vtps_flag]

ats_void_type
atsopt_funentry_set_tailjoin
  (ats_ptr_type entry, ats_ptr_type tjs) {
  ((funentry_t)entry)->atslab_funentry_tailjoin = tjs ; return ;
} // end of [atsopt_funentry_set_tailjoin]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_ccomp_env.dats] *)
