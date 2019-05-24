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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December 2007

(* ****** ****** *)

(* Mainly for handling environments during the third translation *)

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Map = "ats_map_lin.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_patcst2.sats"
staload "ats_dynexp3.sats"

staload TR2 = "ats_trans2.sats"
staload SOL = "ats_staexp2_solve.sats"

(* ****** ****** *)

staload "ats_stadyncst2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_map_lin.dats"

(* ****** ****** *)

#define THISFILENAME "ats_trans3_env.dats"

(* ****** ****** *)

overload = with $Lab.eq_label_label
overload prerr with $Loc.prerr_location

(* ****** ****** *)

fn prerr_loc_error3 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(3)")
// end of [prerr_loc_error3]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans3_env)"

fn prerr_loc_interror (loc: loc_t) = begin
  $Loc.prerr_location loc; prerr ": INTERNAL ERROR (ats_trans3_env)"
end // end of [prerr_loc_interror]

(* ****** ****** *)

implement
c3str_prop (loc, s2e) = '{
  c3str_loc= loc
, c3str_kind= C3STRKINDmain
, c3str_node= C3STRprop (s2e)
} // end of [c3str_prop]

implement
c3str_itmlst
  (loc, knd, s3is) = '{
  c3str_loc= loc
, c3str_kind= knd
, c3str_node= C3STRitmlst (s3is)
} // end of [c3str_itmlst]

implement
c3str_metric_nat (loc, s2e) = '{
  c3str_loc= loc
, c3str_kind= C3STRKINDmetric_nat
, c3str_node= begin
    C3STRprop (s2exp_gte_int_int_bool (s2e, s2exp_int_0))
  end // end of [c3str_node]
}

implement
c3str_metric_dec (loc, met, met_bound) = '{
  c3str_loc= loc
, c3str_kind= C3STRKINDmetric_dec
, c3str_node= C3STRprop (s2exp_metlt (met, met_bound))
}

implement
c3str_pattern_match_exhaustiveness (loc, knd, p2tcs) = '{
  c3str_loc= loc
, c3str_kind= C3STRKINDpattern_match_exhaustiveness (knd, p2tcs)
, c3str_node= C3STRprop (s2exp_bool false)
} // end of [c3str_pattern_match_exhaustiveness]

//

implement
h3ypo_prop (loc, s2p) = '{
  h3ypo_loc= loc, h3ypo_node = H3YPOprop s2p
} // end of [h3ypo_prop]

implement
h3ypo_bind (loc, s2v1, s2e2) = '{
  h3ypo_loc= loc, h3ypo_node = H3YPObind (s2v1, s2e2)
} // end of [h3ypo_bind]

implement
h3ypo_eqeq (loc, s2e1, s2e2) = '{
  h3ypo_loc= loc, h3ypo_node = H3YPOeqeq (s2e1, s2e2)
} // end of [h3ypo_eqeq]

(* ****** ****** *)

local

viewtypedef
s2varbindmap = $Map.map_vt (stamp_t, s2exp)

val s2varbind_svs: ref (s2varlst) = ref_make_elt (list_nil ())
val s2varbind_svs_lst: ref (List s2varlst) = ref_make_elt (list_nil ())

val the_s2varbindmap = ref_make_elt<s2varbindmap> (
  $Map.map_make {stamp_t, s2exp}
    (lam (s1, s2) => $Stamp.compare_stamp_stamp (s1, s2))
) // end of [the_s2varbindmap]

in // in of [local]

implement
the_s2varbindmap_initize () = let
  val (vbox pf | p) = ref_get_view_ptr (the_s2varbindmap)
in
  $Map.map_cleanup<stamp_t, s2exp> (!p)
end // end of [the_s2varbindmap_initialize]

implement
fprint_the_s2varbindmap
  {m} (pfout | out) = let
  fun loop (
    out: &FILE m, kis: List_vt @(stamp_t, s2exp)
  ) : void =
    case+ kis of
    | ~list_vt_cons (ki, kis) => begin
         $Stamp.fprint_stamp (pfout | out, ki.0);
         fprint_string (pfout | out,  " -> ");
         fprint_s2exp (pfout | out, ki.1);
         fprint_string (pfout | out,  "\n");
         loop (out, kis)
       end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  // end of [loop]
  val kis = $Map.map_list_inf (!p) where {
    val (vbox pf | p) = ref_get_view_ptr (the_s2varbindmap)
  } // end of [val]
in
  loop (out, kis)
end // end of [fprint_the_s2varbindmap]

implement
print_the_s2varbindmap () = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
  val () = fprint_the_s2varbindmap (file_mode_lte_w_w | !ptr_stdout)
in
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_the_s2varbindmap]

implement
prerr_the_s2varbindmap () = let
  val (pf_stderr | ptr_stderr) = stderr_get ()
  val () = fprint_the_s2varbindmap (file_mode_lte_w_w | !ptr_stderr)
in
  stderr_view_set (pf_stderr | (*none*))
end // end of [prerr_the_s2varbindmap]

//

implement
the_s2varbindmap_add (s2v, s2e) = let
  val stamp = s2var_get_stamp (s2v)
(*
  val () = begin
    print "the_s2varbindmap_add: s2v = "; print s2v; print_newline ();
    print "the_s2varbindmap_add: s2e = "; print s2e; print_newline ();
    print "the_s2varbindmap_add: stamp = "; $Stamp.print_stamp stamp; print_newline ();
  end // end of [val]
*)
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_s2varbindmap)
(*
    val () = $effmask_ref (case+ $Map.map_search (!p, stamp) of
      | ~None_vt () => () | ~Some_vt s2e0 => begin
          prerr "the_s2varbindmap_add: a binding for the static variable [";
          prerr s2v; prerr "] already exists: "; prerr_newline ();
          prerr "the_s2varbindmap_add: s2e = "; prerr s2e; prerr_newline ();
          prerr "the_s2varbindmap_add: s2e0 = "; prerr s2e0; prerr_newline ();
          $Err.abort {void} ()
        end // end of [Some_vt]
    ) // end of [val]
*)
  in
    $Map.map_insert (!p, stamp, s2e)
  end // end of [val]
in
  !s2varbind_svs := list_cons (s2v, !s2varbind_svs)
end // end of [the_s2varbindmap_add]

implement
the_s2varbindmap_find (s2v) = let
(*
  val () = begin
    print "the_s2varbindmap_find: s2v = "; print s2v; print_newline ()
  end // end of [val]
*)
  val stamp = s2var_get_stamp (s2v)
  val (vbox pf | p) = ref_get_view_ptr (the_s2varbindmap)
in
  $Map.map_search (!p, stamp)
end // end of [the_s2varbindmap_find]

implement
the_s2varbindmap_pop () = let
(*
  val () = begin
    print "the_s2varbindmap_pop: the_s2varbindmap =\n"; print_the_s2varbindmap ()
  end // end of [val]
*)
  fun aux {n:nat} {l:addr} .<n>.
    (pf: !s2varbindmap @ l | p: ptr l, s2vs: list (s2var_t, n)):<> void =
    case+ s2vs of
    | list_cons (s2v, s2vs) => let
        val stamp = $effmask_all (s2var_get_stamp s2v)
        val ans = $Map.map_remove (!p, stamp)
        val () = case+ ans of ~None_vt () => () | ~Some_vt _ => ()
      in
        aux (pf | p, s2vs)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [aux]
in
  case+ !s2varbind_svs_lst of
  | list_cons (s2vs, s2vss) => let
      val () = let
        val (vbox pf | p) = ref_get_view_ptr (the_s2varbindmap)
      in
        aux (pf | p, $effmask_ref (!s2varbind_svs))
      end
      val () = begin
        !s2varbind_svs := s2vs; !s2varbind_svs_lst := s2vss
      end // end of [val]
    in
      // empty
    end // end of [list_cons]
  | list_nil () => begin
      prerr_interror ();
      prerr ": the_s2varbindmap_pop: [s2varbind_svs_lst] is empty.";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [list_nil]
end // end of [s2varbindmap_pop]

implement
the_s2varbindmap_push () = let
  val s2vs = !s2varbind_svs
in
  !s2varbind_svs := list_nil ();
  !s2varbind_svs_lst := list_cons (s2vs, !s2varbind_svs_lst)
end // end of [the_s2varbindmap_push]

end // end of [loca]

(* ****** ****** *)

local

viewtypedef s2Varsetlst = List_vt s2Varset_t

val the_s2Varset = ref_make_elt<s2Varset_t> (s2Varset_nil)
val the_s2Varsetlst = ref_make_elt<s2Varsetlst> (list_vt_nil ())

in

implement
the_s2Varset_env_add (s2V) = begin
  !the_s2Varset := s2Varset_add (!the_s2Varset, s2V)
end

implement
the_s2Varset_env_get () = !the_s2Varset

implement
the_s2Varset_env_get_prev () = let
  val (vbox pf | p) = ref_get_view_ptr (the_s2Varsetlst)
in
  case+ !p of
  | list_vt_cons (sVs, !sVss) => (fold@ (!p); sVs)
  | list_vt_nil () => (fold@ (!p); s2Varset_nil)
end // end of [the_s2Varset_env_get_prev]

implement
the_s2Varset_env_pop () = let
  var err: int = 0
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_s2Varsetlst)
  in
    case+ !p of
    | ~list_vt_cons (sVs, sVss) => begin
        $effmask_ref (!the_s2Varset := sVs); !p := (sVss: s2Varsetlst)
      end
    | list_vt_nil () => (fold@ (!p); err := 1)
  end
in
  if err > 0 then begin
    prerr_interror (); prerr ": the_s2Varset_env_pop"; prerr_newline ();
    $Err.abort {void} ()
  end // endof [if]
end // end of [the_s2Varset_env_pop]

implement
the_s2Varset_env_push () = let
  val (vbox pf | p) = ref_get_view_ptr the_s2Varsetlst
in
  !p := list_vt_cons ($effmask_ref (!the_s2Varset), !p)
end // end of [the_s2Varset_env_push]

end // end of [local]

(* ****** ****** *)

fun s2lablst_is_prefix
  (s2ls1: s2lablst, s2ls2: s2lablst): Option_vt s2lablst = begin
  case+ s2ls1 of
  | list_cons (s2l1, s2ls1) => begin case+ s2l1 of
    | S2LAB1lab (l1, s2e1) => begin case+ s2ls2 of
      | list_cons (s2l2, s2ls2) => begin case+ s2l2 of
        | S2LAB0lab l2 => begin
            if l1 = l2 then s2lablst_is_prefix (s2ls1, s2ls2) else None_vt ()
          end // end of [S2LAB0lab]
        | S2LAB1lab (l2, s2e2) => begin
            if l1 = l2 then
              if s2exp_syneq (s2e1, s2e2) then s2lablst_is_prefix (s2ls1, s2ls2)
              else None_vt ()
            else None_vt ()
          end // end of [S2LAB1lab]
        | _ => None_vt ()
        end // end of [list_cons]
      | list_nil () => None_vt ()
      end // end of [S2LAB1lab]
    | _ => None_vt () // raise an exception?
    end // end [list_cons]
  | list_nil () => Some_vt (s2ls2)
end // end of [s2lablst_is_prefix]

(* ****** ****** *)

fn d2var_fin_check
  (loc0: loc_t, d2v: d2var_t): void = let
(*
  val () = begin
    print "d2var_fin_check: d2v = "; print_d2var d2v; print_newline ()
  end // end of [val]
  val os2e = d2var_get_typ (d2v)
  val () = case+ os2e of
    | Some _ => (print "d2var_fin_check: os2e = Some _"; print_newline ())
    | None _ => (print "d2var_fin_check: os2e = None _"; print_newline ())
*)
in
  case+ d2var_get_typ (d2v) of 
  | Some s2e => begin
    case+ d2var_get_fin (d2v) of 
    | D2VARFINsome s2e0 => let
(*
        val () = begin
          print "d2var_fin_check: D2VARFINsome: d2v = "; print d2v; print_newline ();
          print "d2var_fin_check: D2VARFINsome: s2e = "; print s2e; print_newline ();
          print "d2var_fin_check: D2VARFINsome: s2e0 = "; print s2e0; print_newline ();
        end // end of [val]
*)
        val () = trans3_env_push_sta ()
        val () = $SOL.s2exp_tyleq_solve (loc0, s2e, s2e0)
        val knd = C3STRKINDvarfin (d2v, s2e, s2e0)
        val () = trans3_env_pop_sta_and_add (loc0, knd)
      in
        d2var_set_typ (d2v, Some s2e0)
      end // end of [D2VARFINsome]
    | D2VARFINvbox s2e0 => let
        val () = trans3_env_push_sta ()
        val () = $SOL.s2exp_tyleq_solve (loc0, s2e, s2e0)
        val knd = C3STRKINDvarfin (d2v, s2e, s2e0)
        val () = trans3_env_pop_sta_and_add (loc0, knd)
      in
        d2var_set_typ (d2v, Some s2e0)
      end // end of [D2VARFINvbox]
    | D2VARFINdone () => () // handled by [funarg_varfin_check]
    | D2VARFINnone () => let
        val () = if s2exp_is_linear s2e then begin
          prerr_loc_error3 loc0;
          prerr ": the linear dynamic variable [";
          prerr d2v;
          prerr "] needs to be consumed but it is preserved with the type [";
          prerr s2e;
          prerr "] instead.";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [if]
      in
        if d2var_get_lin d2v >= 0 then d2var_set_typ (d2v, None ())
      end (* end of [D2VARFINnone] *)
    end // end of [Some]
  | None () => begin case+ d2var_get_fin (d2v) of
    | D2VARFINdone () => () // handled by [funarg_varfin_check]
    | D2VARFINnone () => () | _ => begin
        prerr_loc_error3 loc0;
        prerr ": the linear dynamic variable ["; prerr d2v;
        prerr "] needs to be preserved but it is consumed instead.";
        prerr_newline ();
        $Err.abort {void} ()
      end (* end of [_] *)
    end // end of [None]
end (* end of [d2var_fin_check] *)

(* ****** ****** *)

local

assume d2varset_env_token = unit_v

datatype ld2vsitem = // local dynamic variables
  | LD2VSITEMlam // marker for nonlinear lambda
  | LD2VSITEMllam of ref (d2varlst) // marker for linear lambda
  | LD2VSITEMset of d2varset_t // local dynamic variable set
// end of [ld2vsitem]

typedef ld2vsitemlst = List ld2vsitem

val the_ld2vs = ref_make_elt<d2varset_t> (d2varset_nil)
val the_ld2vsitems = ref_make_elt<ld2vsitemlst> (list_nil ())

in // in of [local]

implement
the_d2varset_env_add (d2v) = begin
  !the_ld2vs := d2varset_add (!the_ld2vs, d2v)
end // end of [the_d2varset_env_add]

implement
the_d2varset_env_addlst (d2vs) = begin
  !the_ld2vs := d2varset_adds (!the_ld2vs, d2vs)
end // end of [the_d2varset_env_addlst]

implement
the_d2varset_env_add_p2at (p2t) = let
  val d2vs = d2varlst_of_d2varlstord (p2t.p2at_dvs)
in
  !the_ld2vs := d2varset_adds (!the_ld2vs, d2vs)
end // end of [the_d2varset_env_add_p2at]

implement
the_d2varset_env_add_p2atlst (p2ts) = case+ p2ts of
  | list_cons (p2t, p2ts) => begin
      the_d2varset_env_add_p2at p2t; the_d2varset_env_add_p2atlst p2ts
    end // end of [list_cons]
  | list_nil () => ()
// end of [the_d2varset_env_add_p2atlst]  

//

implement
the_d2varset_env_print_ld2vs () = print (!the_ld2vs)
implement
the_d2varset_env_prerr_ld2vs () = prerr (!the_ld2vs)

fn the_d2varset_env_get_llam_ld2vs
  (loc0: loc_t): d2varlst = begin case+ !the_ld2vsitems of
  | list_cons (LD2VSITEMllam r, _) => !r
  | _ => begin
      prerr_loc_interror loc0;
      prerr ": the_d2varset_env_get_llam_ld2vs"; prerr_newline ();
      $Err.abort {d2varlst} ()
    end // end of [_]
end // end of [the_d2varset_env_get_llam_ld2vs]

//

implement
the_d2varset_env_pop_lam
  (pf | (*none*)) = let
  prval unit_v () = pf; var err: int = 0
  var ld2vsitems_var: ld2vsitemlst = list_nil
  val () = case+ !the_ld2vsitems of
    | list_cons (ld2vsitem, ld2vsitems) => begin
      case+ ld2vsitem of
      | LD2VSITEMlam () => ld2vsitems_var := ld2vsitems
      | LD2VSITEMllam _ => ld2vsitems_var := ld2vsitems
      | _ => (err := 1)
      end
    | list_nil () => (err := 1)
  val () = case+ ld2vsitems_var of
    | list_cons (ld2vsitem, ld2vsitems) => begin
      case+ ld2vsitem of
      | LD2VSITEMset ld2vs => begin
          !the_ld2vs := ld2vs; !the_ld2vsitems := ld2vsitems
        end
      | _ => (err := 1)
      end
    | list_nil () => (err := 1)
in
  if err > 0 then begin
    prerr_interror ();
    prerr ": the_d2varset_env_pop_lam"; prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [the_d2varset_env_pop_lam]

implement
the_d2varset_env_push_lam (lin) = let
  val marker = (
    if lin > 0 then
      (LD2VSITEMllam (ref_make_elt<d2varlst> (list_nil)))
    else LD2VSITEMlam ()
  ) : ld2vsitem // end of [val]
  val () = !the_ld2vsitems :=
     list_cons (marker, list_cons (LD2VSITEMset !the_ld2vs, !the_ld2vsitems))
  val () = !the_ld2vs := d2varset_nil
in
  (unit_v () | ())
end // end of [the_d2varset_env_push_lam]

implement
the_d2varset_env_pop_let
  (pf | (*none*)) = let
  prval unit_v () = pf; var err: int = 0
  val () = (case+ !the_ld2vsitems of
    | list_cons (ld2vsitem, ld2vsitems) => begin
      case+ ld2vsitem of
      | LD2VSITEMset ld2vs => begin
          !the_ld2vs := ld2vs; !the_ld2vsitems := ld2vsitems
        end
      | _ => (err := 1)
      end // end of [list_cons]
    | list_nil () => (err := 1)
  ) : void // end of [val]
in
  if err > 0 then begin
    prerr_interror ();
    prerr ": the_d2varset_env_pop_let"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [the_d2varset_env_pop_let]

implement
the_d2varset_env_push_let () = let
  val () = !the_ld2vsitems :=
    list_cons (LD2VSITEMset (!the_ld2vs), !the_ld2vsitems)
  val () = !the_ld2vs := d2varset_nil // it is not a constructor
in
  (unit_v () | ())
end // end of [the_d2varset_env_push_let]

//

implement
the_d2varset_env_pop_try
  (pf | (*none*)) = begin
  the_d2varset_env_pop_lam (pf | (*none*))
end // end of [the_d2varset_env_pop_try]

implement
the_d2varset_env_push_try () = begin
  the_d2varset_env_push_lam (0(*lin*))
end // end of [the_d2varset_env_push_try]

//

implement
the_d2varset_env_d2var_is_lam_local
  (d2v) = let
//
  fun aux (
    itms: ld2vsitemlst, d2v: d2var_t
  ) : bool = begin
    case+ itms of
    | list_cons (itm, itms) => begin case+ itm of
      | LD2VSITEMlam () => false
      | LD2VSITEMllam _ => false
      | LD2VSITEMset dvs => begin
          if d2varset_ismem (dvs, d2v) then true else aux (itms, d2v)
        end // end of [LD2VSITEMset]
      end // end of [list_cons]
    | list_nil () => begin
        prerr_interror ();
        prerr ": d2var_is_lam_local: aux: d2v = "; prerr d2v; prerr_newline ();
        $Err.abort {bool} ()
      end // end of [list_nil]
  end // end of [aux]
//
  val ans: bool = d2varset_ismem (!the_ld2vs, d2v)
//
in
  if ans then true else aux (!the_ld2vsitems, d2v)
end // end of [the_d2varset_env_d2var_is_lam_local]

implement
the_d2varset_env_d2var_is_llam_local
  (d2v) = let
//
  fun aux (
    itms: ld2vsitemlst, d2v: d2var_t
  ) : bool = begin
    case+ itms of
    | list_cons (itm, itms) => begin case+ itm of
      | LD2VSITEMlam () => false
      | LD2VSITEMllam r => begin
          !r := list_cons (d2v, !r); aux (itms, d2v)
        end // end of [LD2VSITEMllam]
      | LD2VSITEMset dvs => begin
          if d2varset_ismem (dvs, d2v) then true else aux (itms, d2v)
        end // end of [LD2VSITEMset]
      end // end of [list_cons]
    | list_nil () => begin
        prerr_interror ();
        prerr ": d2var_is_llam_local: aux: d2v = "; prerr d2v; prerr_newline ();
        $Err.abort {bool} ()
      end // end of [list_nil]
  end // end of [aux]
//
  val ans: bool = d2varset_ismem (!the_ld2vs, d2v)
//
(*
  val () = begin
    print "d2var_is_llam_local: the_ld2vs = ";
    print (!the_ld2vs);
    print_newline ();
    print "d2var_is_llam_local: d2v = ";
    print (d2v);
    print_newline ();
    print "d2var_is_llam_local: ans = ";
    print (ans);
    print_newline ()
  end // end of [val]
*)
in
  if ans then true else aux (!the_ld2vsitems, d2v)
end // end of [the_d2varset_env_d2var_is_llam_local]

//

implement
the_d2varset_env_check (loc0) = let
(*
  val () = begin
    print "the_d2varset_env_check: enter"; print_newline ()
  end // end of [val]
*)
in
  d2varset_foreach_cloptr
    (!the_ld2vs, lam (d2v) => d2var_fin_check (loc0, d2v))
end // end of [the_d2varset_env_check]

implement
the_d2varset_env_check_llam (loc0) = let
  fn auxCK (d2v: d2var_t):<cloptr1> void = begin
    case+ d2var_get_typ (d2v) of
    | Some s2e => begin
        if s2exp_is_nonlin s2e then d2var_set_typ (d2v, None ())
        else let
          val () = prerr_loc_error3 loc0
          val () = prerr ": the linear dynamic variable ["
          val () = prerr d2v
          val () = prerr "] needs to be consumed but it is preserved with the type ["
          val () = prerr s2e
          val () = prerr "] instead."
          val () = prerr_newline ()
        in
          $Err.abort {void} ()
        end // end of [if]
      end // end of [Some]
    | None () => ()
  end // end of [auxCK]
  fun auxlst (d2vs: d2varlst):<cloptr1> void = begin case+ d2vs of
    | list_cons (d2v, d2vs) => (auxCK d2v; auxlst d2vs) | list_nil () => ()
  end // end of [auxlst]
in
  auxlst (the_d2varset_env_get_llam_ld2vs (loc0))
end // end of [the_d2varset_env_check_llam]

(* ****** ****** *)

implement
the_d2varset_env_find_view (s2e0) = let
  exception NotFound // local exception
  exception Found of d2var_t // local exception
  typedef env_t = s2exp; val env = s2e0 // closure environment
  fn f (pf: !unit_v | d2v: d2var_t, env: !env_t): void = begin
    case+ d2var_get_typ d2v of
    | Some s2e => begin
        if s2exp_syneq (env, s2e) then $raise Found (d2v) else ()
      end // end of [Some]
    | None => () // this happens if [d2v] is linear and consumed
  end // end of [f]
  fun loop (
      pf: !unit_v | ld2vsitems: ld2vsitemlst, env: !env_t
    ) : void = begin case+ ld2vsitems of
    | list_cons (ld2vsitem, ld2vsitems) => let
        val () = (case+ ld2vsitem of
          | LD2VSITEMlam () => $raise NotFound ()
          | LD2VSITEMllam _(*r_d2vs*) => () // continue search
          | LD2VSITEMset dvs => begin
              d2varset_foreach_main {unit_v} {env_t} (pf | dvs, f, env)
            end // end of [LD2VSITEMset]
        ) : void
      in
        loop (pf | ld2vsitems, env)
      end // end of [list_vt_cons]
    | list_nil () => ()
  end // end of [loop]
in
  try let
    prval pf = unit_v ()
    val () = begin
      d2varset_foreach_main {unit_v} {env_t} (pf | !the_ld2vs, f, env)
    end // end of [val]
    val () = loop (pf | !the_ld2vsitems, env)
    prval unit_v () = pf
  in
    None_vt ()
  end with
    | ~NotFound () => None_vt () | ~Found d2v => Some_vt d2v
  // end of [try]
end // end of [the_d2varset_env_find_view]

implement
the_d2varset_env_find_viewat
  (s2r0, s2ls0) = let
//
  exception NotFound // local exception
  exception Found of d2varset_env_find_viewat_t // local exception
  dataviewtype env_vt = ENVcon of (s2exp, s2lablst)
//
  fn f (
    pf: !unit_v | d2v: d2var_t, env: !env_vt
  ) : void = begin
    case+ d2var_get_typ d2v of
    | Some s2e => let val s2e = s2exp_whnf s2e in
        case+ un_s2exp_at_viewt0ype_addr_view s2e of
        | ~Some_vt (s2ts2a (*type/addr*)) => let
            val (s2r, s2ls_ft) = s2exp_addr_normalize s2ts2a.1
            val+ ENVcon (s2r0, s2ls0) = env
            val () = (case+ 0 of
              | _ when s2exp_syneq (s2r0, s2r) => begin
                case+ s2lablst_is_prefix (s2ls_ft, s2ls0) of
                | ~Some_vt (s2ls_bk) => begin
                    $raise Found @(d2v, s2ts2a.0, s2ts2a.1, s2ls_ft, s2ls_bk)
                  end
                | ~None_vt () => ()
                end // end of [_ when ...]
              | _ => ()
            ) : void
          in
            fold@ env
          end // end of [Some_vt]
        | ~None_vt () => ()
      end // end of [let]
    | None => () // this happens if [d2v] is linear and consumed
  end // end of [f]
//
  fun loop (
      pf: !unit_v
    | ld2vsitems: ld2vsitemlst, env: !env_vt
    ) : void = begin case+ ld2vsitems of
    | list_cons (ld2vsitem, ld2vsitems) => let
        val () = (case+ ld2vsitem of
          | LD2VSITEMlam () => $raise NotFound ()
          | LD2VSITEMllam _(*r_d2vs*) => () // continue search
          | LD2VSITEMset dvs => begin
              d2varset_foreach_main {unit_v} {env_vt} (pf | dvs, f, env)
            end // end of [LD2VSITEMset]
        ) : void
      in
        loop (pf | ld2vsitems, env)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [loop]
//
in
  try let
    prval pf = unit_v ()
    val env = ENVcon (s2r0, s2ls0) // cloenv
    val () = begin
      d2varset_foreach_main {unit_v} {env_vt} (pf | !the_ld2vs, f, env)
    end
    val () = loop (pf | !the_ld2vsitems, env)
    val+ ~ENVcon (_, _) = env
    prval unit_v () = pf
  in
    None_vt ()  
  end with
    | ~NotFound () => None_vt () | ~Found x => Some_vt x
  // end of [try]
end // end of [the_d2varset_env_find_viewat]

(* ****** ****** *)

implement
the_d2varset_env_stbefitemlst_save
  () = let
//
  var sbis: stbefitemlst = list_nil ()
//
  typedef sbisptr = ptr sbis
  viewdef V = stbefitemlst @ sbis
//
  fun f (
    pf: !V | d2v: d2var_t, sbis: !sbisptr
  ) : void = let
    val lin = d2var_get_lin d2v
(*
    val () = begin
      print "the_d2varset_env_stbefitemlst_save: f: d2v = "; print d2v; print_newline ();
      print "the_d2varset_env_stbefitemlst_save: f: lin = "; print lin; print_newline ();
    end // end of [val]
*)
  in
    if lin >= 0 then let val sbi =
      stbefitem_make (d2v, lin) in !sbis := list_cons (sbi, !sbis)
    end // end of [if]
  end (* end of [f] *)
//
  fun aux (
    pf: !V | xs: ld2vsitemlst, sbis: !sbisptr
  ) : void = begin
    case+ xs of
    | list_cons (x, xs) => begin case+ x of
      | LD2VSITEMlam () => ()
      | LD2VSITEMllam _ => aux (pf | xs, sbis)
      | LD2VSITEMset dvs => let
          val () = begin
            d2varset_foreach_main {V} {sbisptr} (pf | dvs, f, sbis)
          end
        in
          aux (pf | xs, sbis)
        end (* LD2VSITEMset *)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
//
  prval pf = view@ (sbis)
  val () = begin
    d2varset_foreach_main {V} {sbisptr} (pf | !the_ld2vs, f, &sbis)
  end // end of [val]
  val () = aux (pf | !the_ld2vsitems, &sbis)
//
in
  view@ sbis := pf; sbis
end // end of [the_d2varset_env_stbefitemlst_save]

end // end of [local]

(* ****** ****** *)

local

val the_s3itemlst = ref_make_elt<s3itemlst_vt> (list_vt_nil ())
val the_s3itemlstlst = ref_make_elt<s3itemlstlst_vt> (list_vt_nil ())

in

implement
trans3_env_s3itemlst_copy () = let
  val (vbox pf | p) = ref_get_view_ptr (the_s3itemlst)
in
  $Lst.list_vt_copy__boxed (!p)
end // end of [trans3_Env_s3itemlst_copy]

implement
trans3_env_s3itemlst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (the_s3itemlst)
  val s3is = !p; val () = !p := list_vt_nil ()
in
  s3is
end // end of [trans3_env_s3itemlst_get]

implement
trans3_env_s3itemlst_set (s3is) = let
  val (vbox pf | p) = ref_get_view_ptr (the_s3itemlst)
in
  case+ !p of
  | ~list_vt_nil () => (!p := s3is; None_vt ())
  | list_vt_cons _ => (fold@ (!p); Some_vt s3is)
end // end of [trans3_env_s3itemlst_set]

implement
trans3_env_add_svar (s2v) = let
  val (vbox pf | p) = ref_get_view_ptr (the_s3itemlst)
in
  !p := list_vt_cons (S3ITEMsvar s2v, !p)
end // end of [trans3_env_add_svar]

implement
trans3_env_add_svarlst (s2vs) = let
  fun aux {n:nat} .<n>.
    (s3is: s3itemlst_vt, s2vs: list (s2var_t, n)):<> s3itemlst_vt =
    case+ s2vs of
    | list_cons (s2v, s2vs) => aux (list_vt_cons (S3ITEMsvar s2v, s3is), s2vs)
    | list_nil () => s3is
  val (vbox pf | p) = ref_get_view_ptr (the_s3itemlst)
in
  !p := aux (!p, s2vs)
end // end of [trans3_env_add_svarlst]

(* ****** ****** *)

implement
trans3_env_add_sVar (s2V) = let
  val () = the_s2Varset_env_add (s2V)
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
 !p := list_vt_cons (S3ITEMsVar s2V, !p)
end // end of [trans3_env_add_sVar]

implement
trans3_env_add_sVarlst (s2Vs) = let
  fun aux {n:nat} .<n>.
    (s3is: s3itemlst_vt, s2Vs: list (s2Var_t, n))
    :<> s3itemlst_vt = begin case+ s2Vs of
    | list_cons (s2V, s2Vs) => begin
        $effmask_all (the_s2Varset_env_add s2V);
        aux (list_vt_cons (S3ITEMsVar s2V, s3is), s2Vs)
      end // end of [val]
    | list_nil () => s3is
  end // end of [aux]
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := aux (!p, s2Vs)
end // end of [trans3_env_add_sVarlst]

(* ****** ****** *)

implement
trans3_env_add_cstr (c3t) = let
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := list_vt_cons (S3ITEMcstr c3t, !p)
end // end of [trans3_env_add_cstr]

implement
trans3_env_add_cstr_ref (r) = let
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := list_vt_cons (S3ITEMcstr_ref r, !p)
end // end of [trans3_env_add_cstr_ref]

(* ****** ****** *)

implement
trans3_env_add_prop (loc, s2p) =
  case+ s2p.s2exp_node of
  | S2Etyleq (knd, s2e1, s2e2) when knd > 0 => let
      val () = trans3_env_push_sta ()
      val () = $SOL.s2exp_tyleq_solve (loc, s2e1, s2e2)
      val () = trans3_env_pop_sta_and_add_none (loc)
    in
      // empty
    end // end of [S2Etyleq when ...]
  | _ => begin
      trans3_env_add_cstr (c3str_prop (loc, s2p))
    end // end of [_]
// end of [trans3_env_add_prop]

implement
trans3_env_add_proplst (loc, s2ps) =
  case+ s2ps of
  | list_cons (s2p, s2ps) => let
      val () = trans3_env_add_prop (loc, s2p)
    in
      trans3_env_add_proplst (loc, s2ps)
    end // end of [list_cons]
  | list_nil () => ()
// end of [trans3_env_add_proplst]

implement
trans3_env_add_proplstlst (loc, s2pss) =
  case+ s2pss of
  | list_cons (s2ps, s2pss) => let
      val () = trans3_env_add_proplst (loc, s2ps)
    in
      trans3_env_add_proplstlst (loc, s2pss)
    end // end of [list_cons]
  | list_nil () => ()
// end of [trans3_env_add_proplstlst]

(* ****** ****** *)

implement
trans3_env_add_eqeq
  (loc, s2e1, s2e2) = let
(*
  val () = begin
    print "trans3_env_add_eqeq: s2e1 = "; print_s2exp s2e1; print_newline ();
    print "trans3_env_add_eqeq: s2e2 = "; print_s2exp s2e2; print_newline ();
  end // end of [val]
*)
  val s2p = s2exp_eqeq (s2e1, s2e2)
in
  trans3_env_add_prop (loc, s2p)
end // end of [trans3_env_add_eqeq]

implement
trans3_env_add_tyleq
  (loc, s2e1, s2e2) = let
  val s2p = s2exp_tyleq (0, s2e1, s2e2) // already tried
in
  trans3_env_add_prop (loc, s2p)
end // end of [trans3_env_add_tyleq]

(* ****** ****** *)

implement
trans3_env_hypo_add_prop (loc, s2p) = let
(*
  val () = begin
    print "trans3_env_hypo_add_prop: s2p = "; print s2p; print_newline ()
  end // end of [val]
*)
  val h3p = h3ypo_prop (loc, s2p)
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := list_vt_cons (S3ITEMhypo h3p, !p)
end // end of [trans3_env_hypo_add_prop]

implement
trans3_env_hypo_add_proplst (loc, s2ps) =
  case+ s2ps of
  | list_cons (s2p, s2ps) => begin
      trans3_env_hypo_add_prop (loc, s2p);
      trans3_env_hypo_add_proplst (loc, s2ps)
    end // end of [list_cons]
  | list_nil () => ()
// end of [trans3_env_hypo_add_proplst]

implement
trans3_env_hypo_add_bind
  (loc, s2v1, s2e2) = let
(*
  val () = begin
    print "trans3_env_hypo_add_bind: s2v1 = "; print s2v1; print_newline ();
    print "trans3_env_hypo_add_bind: s2e2 = "; print s2e2; print_newline ();
  end // end of [val]
*)
  val os2e1 = the_s2varbindmap_find (s2v1)
in
  case+ os2e1 of
  | ~Some_vt (s2e1) =>
      trans3_env_hypo_add_eqeq (loc, s2e1, s2e2)
    // end of [Some_vt]
  | ~None_vt () => let
      val () = the_s2varbindmap_add (s2v1, s2e2)
      val h3p = h3ypo_bind (loc, s2v1, s2e2)
      val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
    in
      !p := list_vt_cons (S3ITEMhypo h3p, !p)
    end // end of [None_vt]
end // end of [trans3_env_hypo_add_bind]

implement
trans3_env_hypo_add_eqeq
  (loc, s2e1, s2e2) = let
(*
  val () = begin
    print "trans3_env_hypo_add_eqeq: s2e1 = "; print s2e1; print_newline ();
    print "trans3_env_hypo_add_eqeq: s2e2 = "; print s2e2; print_newline ();
  end // end of [val]
*)
  val h3p = h3ypo_eqeq (loc, s2e1, s2e2)
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := list_vt_cons (S3ITEMhypo h3p, !p)
end // end of [trans3_env_hypo_add_eqeq]

implement
trans3_env_hypo_add_s2qualst
  (loc, s2vpss) = case+ s2vpss of
  | list_cons (s2vps, s2vpss) => begin
      trans3_env_add_svarlst s2vps.0;
      trans3_env_hypo_add_proplst (loc, s2vps.1);
      trans3_env_hypo_add_s2qualst (loc, s2vpss)
    end // end of [list_cons]
  | list_nil () => ()
// end of [trans3_env_hypo_add_s2qualst]

//
// HX: used in [trans3_env_hypo_add_p2atcstlstlst]
//
fn trans3_env_hypo_add_disj
  (s3iss: s3itemlstlst): void = let
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := list_vt_cons (S3ITEMdisj s3iss, !p)
end // end of [trans3_env_hypo_add_disj]

(* ****** ****** *)

extern
fun print_the_s3itemlst (): void
  = "atsopt_print_the_s3itemlst"
// end of [print_the_s3itemlst]

implement
print_the_s3itemlst () = let
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  $effmask_ref (print_s3itemlst_vt !p)
end // end of [print_the_s3itemlst]

extern
fun print_the_s3itemlstlst (): void
  = "atsopt_print_the_s3itemlstlst"
// end of [print_the_s3itemlstlst]
  
implement
print_the_s3itemlstlst () = let
  val (vbox pf | ps) = ref_get_view_ptr the_s3itemlstlst
in
  $effmask_ref (print_s3itemlstlst_vt !ps)
end // end of [print_the_s3itemlstlst]

(* ****** ****** *)

extern
fun free_the_s3itemlst (): void = "atsopt_free_the_s3itemlst"

implement
free_the_s3itemlst () = let
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
  val s3is = !p
in
  !p := list_vt_nil (); $Lst.list_vt_free__boxed (s3is)
end // end of [free_the_s3itemlst]

(* ****** ****** *)

implement
trans3_env_pop_sta () = let
(*
  val () = $effmask_ref begin
    print "trans3_env_pop_sta: the_s3itemlst = "; print_the_s3itemlst (); print_newline ();
    print "trans3_env_pop_sta: the_s3itemlstlst = "; print_the_s3itemlstlst (); print_newline ();
  end // end of [val]
*)
  val () = the_s2varbindmap_pop ()
  val () = the_s2Varset_env_pop ()
  var err: int = 0
  val s3is1 = (let
    val (vbox pf | ps) = ref_get_view_ptr the_s3itemlstlst
  in
    case+ !ps of
    | ~list_vt_cons (s3is, s3iss) => (!ps := (s3iss: s3itemlstlst_vt); s3is)
    | ~list_vt_nil () => begin
        !ps := list_vt_nil {s3itemlst_vt} (); err := 1; list_vt_nil {s3item} ()
      end // end of [list_vt_nil]
  end) : s3itemlst_vt
  val () = if err > 0 then begin
    prerr_interror ();
    prerr ": trans3_env_pop_sta: [the_s3itemlstlst] is empty."; prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
  val s3is0 = !p; val () = (!p := s3is1)
in
  s3is0
end // end of [trans3_env_pop_sta]

implement
trans3_env_pop_sta_and_add (loc, cstrknd) = let
  val s3is0 = trans3_env_pop_sta ()
  val c3t = c3str_itmlst (loc, cstrknd, $Lst.list_vt_reverse_list s3is0)
(*
  val () = begin
    print "trans3_env_pop_sta_and_add: c3t = "; print c3t; print_newline ()
  end // end of [val]
*)
  val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
in
  !p := list_vt_cons (S3ITEMcstr c3t, !p)
end // end of [trans3_env_pop_sta_and_add]

implement
trans3_env_pop_sta_and_add_none (loc) =
 trans3_env_pop_sta_and_add (loc, C3STRKINDmain ())
// end of ...

implement
trans3_env_pop_sta_and_free () = let
  val s3is = trans3_env_pop_sta () in $Lst.list_vt_free__boxed (s3is)
end // end of [trans3_env_pop_sta_and_free]

(* ****** ****** *)

implement
trans3_env_push_sta () = let
(*
  val () = begin
    print "trans3_env_push_sta: the_s3itemlst = "; print_the_s3itemlst (); print_newline ();
    print "trans3_env_push_sta: the_s3itemlstlst = "; print_the_s3itemlstlst (); print_newline ();
  end // end of [val]
*)
  var s3is0: s3itemlst_vt? // uninitialized
  val () = let
    val (vbox pf | p) = ref_get_view_ptr the_s3itemlst
  in
    s3is0 := !p; !p := list_vt_nil ()
  end
  val () = let
    val (vbox pf | ps) = ref_get_view_ptr the_s3itemlstlst
  in
    !ps := list_vt_cons (s3is0, !ps)
  end // end of [val]
in
  the_s2varbindmap_push (); the_s2Varset_env_push ()
end // end of [trans3_env_push_sta]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

implement
s2exp_Var_make_srt (loc, s2t) = let
  val s2V = s2Var_make_srt (loc, s2t)
  val () = s2Var_set_sVarset (s2V, the_s2Varset_env_get_prev ())
in
  trans3_env_add_sVar (s2V); s2exp_Var (s2V)
end // end of [s2exp_Var_make_srt]

implement
s2exp_Var_make_var (loc, s2v) = let
(*
  val () = begin
    print "s2exp_Var_make_var: s2v = "; print s2v; print_newline ()
  end // end of [val]
*)
  val s2V = s2Var_make_var (loc, s2v)
  val () = s2Var_set_sVarset (s2V, the_s2Varset_env_get_prev ())
(*
  val () = begin
    print "s2exp_Var_make_var: s2V = "; print s2V; print_newline ()
  end // end of [val]
*)
in
  trans3_env_add_sVar (s2V); s2exp_Var (s2V)
end // end of [s2exp_Var_make_var]

(* ****** ****** *)

implement
s2qua_instantiate_and_add
  (loc0, s2vs, s2ps) = let
(*
  val () = begin
    print "s2qua_instantiate_and_add: s2vs = "; print s2vs; print_newline ();
    print "s2qua_instantiate_and_add: s2ps = "; print s2ps; print_newline ();
  end // end of [val]
*)
  val sub = aux (loc0, s2vs) where {
    fun aux (loc0: loc_t, s2vs: s2varlst): stasub_t =
      case+ s2vs of
      | list_cons (s2v, s2vs) => let
(*
          val () = begin
            print "s2qua_instantiate_and_add: aux: s2v = "; print s2v; print_newline ()
          end
*)
          val s2e = s2exp_Var_make_var (loc0, s2v)
        in
          stasub_add (aux (loc0, s2vs), s2v, s2e)
        end // end of [list_cons]
      | list_nil () => stasub_nil
  } // end of [where]
  val s2ps_new = s2explst_subst (sub, s2ps)
(*
  val () = begin
    print "s2qua_instantiate_and_add: s2ps_new = "; print s2ps_new; print_newline ()
  end // end of [val]
*)
in
  trans3_env_add_proplst (loc0, s2ps_new); sub
end // end of [s2qua_instantiate_and_add]

implement
s2qua_instantiate_with_and_add
  (loc0, s2vs, s2ps, loc_arg, s2es) = let
  fun aux (s2vs: s2varlst, s2es: s2explst):<cloptr1> stasub_t =
    case+ (s2vs, s2es) of
    | (list_cons (s2v, s2vs), list_cons (s2e, s2es)) => let
        val s2t_s2v = s2var_get_srt s2v and s2t_s2e = s2e.s2exp_srt
        val () = // sort-checking
          if s2t_s2e <= s2t_s2v then () else begin
            prerr_loc_error3 loc_arg;
            prerr ": the static expression [";
            prerr s2e;
            prerr "] is of sort [";
            prerr s2t_s2e;
            prerr "] but is expected to be of sort [";
            prerr s2t_s2v;
            prerr "].";
            prerr_newline ();
            $Err.abort {void} ()
          end
      in
        stasub_add (aux (s2vs, s2es), s2v, s2e)
      end // end of [list_cons, list_cons]
    | (list_nil _, list_nil _) => stasub_nil
    | (list_cons _, list_nil _) => begin
        prerr_loc_error3 loc0;
        prerr ": the static application needs more arguments.";
        prerr_newline ();
        $Err.abort {stasub_t} ()
      end // end of [list_cons, list_nil]
    | (list_nil _, list_cons _) => begin
        prerr_loc_error3 loc0;
        prerr ": the static application needs fewer arguments.";
        prerr_newline ();
        $Err.abort {stasub_t} ()
      end // end of [list_nil, list_cons]
  val sub = aux (s2vs, s2es)
  val s2ps_new = s2explst_subst (sub, s2ps)
  val () = trans3_env_add_proplst (loc0, s2ps_new)
in
  sub
end // end of [s2qua_instantiate_with_and_add]

implement
s2qua_hypo_instantiate_and_add
  (loc0, s2vs, s2ps) = let
  val @(sub, s2vs_new) = stasub_extend_svarlst (stasub_nil, s2vs)
  val s2ps_new = s2explst_subst (sub, s2ps)
  val () = trans3_env_add_svarlst s2vs_new
  val () = trans3_env_hypo_add_proplst (loc0, s2ps_new)
in
  sub
end // end of [s2qua_hypo_instantiate_and_add]

(* ****** ****** *)

implement
s2exp_metric_instantiate
  (loc0, d2vopt, met) = begin
  case+ d2vopt of
  | Some d2v_stamp => let
      val met_bound = (case+ metric_env_get d2v_stamp of
        | Some s2es => s2es | None () => begin
            prerr_interror ();
            prerr ": s2exp_metric_instantiate: no metric bound";
            prerr_newline ();            
            $Err.abort {s2explst} ()
          end // end of [None]
      ) : s2explst
      val sgn = $Lst.list_length_compare (met, met_bound)
      val () = assert_errmsg_bool1 (sgn = 0,
        "INTERNAL ERROR: s2exp_metric_instantiate: metric length mismatch"
      ) // end of [assert_errmsg]
    in
      trans3_env_add_metric_dec (loc0, met, met_bound)
    end // end of [Some]
  | None () => ()
end // end of [s2exp_metric_instantiate]

(* ****** ****** *)

implement
s2exp_exi_instantiate_all (loc0, s2e0) = let
  val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
    | S2Eexi (s2vs, s2ps, s2e) => let
        val sub = s2qua_instantiate_and_add (loc0, s2vs, s2ps)
        val s2e = s2exp_subst (sub, s2e)
      in
        s2exp_exi_instantiate_all (loc0, s2e)
      end // end of [S2Eexi]
    | _ => s2e0
end // end of [s2exp_exi_instantiate_all]

implement
s2exp_exi_instantiate_one (loc0, s2e0) = let
  val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
    | S2Eexi (s2vs, s2ps, s2e) => let
        val sub = s2qua_instantiate_and_add (loc0, s2vs, s2ps)
      in
        s2exp_subst (sub, s2e)
      end // end of [S2Eexi]
    | _ => begin
        prerr_loc_error3 loc0;
        prerr ": the type ["; prerr s2e0;
        prerr "] is expected to be existentially quantified.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end // end of [_]
end // end of [s2exp_exi_instantiate_one]

implement
s2exp_exi_instantiate_seq (
  loc0, s2e0, loc_arg, s2es0
) = let
  val s2e0 = s2exp_whnf s2e0 in
  case+ s2e0.s2exp_node of
  | S2Eexi (s2vs, s2ps, s2e) => let
      val sub = begin
        s2qua_instantiate_with_and_add (loc0, s2vs, s2ps, loc_arg, s2es0)
      end
    in
      s2exp_subst (sub, s2e)
    end // end of [S2Eexi]
  | _ => let
      val () = prerr_loc_error3 loc0
      val () = prerr ": the type ["
      val () = prerr_s2exp (s2e0)
      val () = prerr "] is expected to be existentially quantified."
      val () = prerr_newline ()
    in
      $Err.abort {s2exp} ()
    end // end of [_]
end // end of [s2exp_exi_instantiate_seq]

implement
s2exp_exi_instantiate_sexparg
  (loc0, s2e0, s2a) = begin
  case+ s2a.s2exparg_node of
  | S2EXPARGall () => s2exp_exi_instantiate_all (loc0, s2e0)
  | S2EXPARGone () => s2exp_exi_instantiate_one (loc0, s2e0)
  | S2EXPARGseq s2es => begin
      s2exp_exi_instantiate_seq (loc0, s2e0, s2a.s2exparg_loc, s2es)
    end // end of [S2EXPARGseq]
end // end of [s2exp_exi_instantiate_sexparg]

(* ****** ****** *)

implement
funarg_varfin_check (loc0) = let
(*
  val () = begin
    $Loc.print_location loc0; print ": funarg_varfin_check"; print_newline ()
  end // end of [val]
*)
  fn auxvar
    (loc0: loc_t, d2v: d2var_t): void = let
(*
    val () = begin
      print "funarg_varfin_check: auxvar: d2v (bef) = "; print_d2var d2v; print_newline ()
    end // end of [val]
*)
    val d2v = (case+ d2var_get_view d2v of
      | D2VAROPTsome d2v => d2v | D2VAROPTnone () => d2v
    ) : d2var_t
(*
    val () = begin
      print "funarg_varfin_check: auxvar: d2v (aft) = "; print_d2var d2v; print_newline ()
    end // end of [val]
*)
    val () = d2var_fin_check (loc0, d2v)
  in
    d2var_set_fin (d2v, D2VARFINdone ()) // done!
  end // end of [auxvar]

  fun auxpatlst
    (loc0: loc_t, p3ts: p3atlst): void = begin
    case+ p3ts of
    | list_cons (p3t, p3ts) => let
        val () = (case+ p3t.p3at_node of
          | P3Tvar (_(*refknd*), d2v) => auxvar (loc0, d2v)
          | P3Tas (_(*refknd*), d2v, _(*p3at*)) => auxvar (loc0, d2v)
          | _ => ()
        ) : void // end of [val]
      in
        auxpatlst (loc0, p3ts)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [auxpatlst]
  val opt = the_lamloop_env_arg_get ()
in
  case+ opt of
  | ~Some_vt p3ts => auxpatlst (loc0, p3ts)
  | ~None_vt () => begin
      prerr_loc_interror loc0;
      prerr ": funarg_varfin_check: no argument(s)."; prerr_newline ();
      $Err.abort {void} ()
    end // end of [None_vt]
end (* end of [funarg_varfin_check] *)

(* ****** ****** *)

implement
s2exp_wth_instantiate (loc0, s2e0) = let
(*
  val () = begin
    print "s2exp_wth_instantiate: s2e0 = "; print s2e0; print_newline ()
  end // end of [val]
*)
  fn aux (
      loc0: loc_t
    , refval: int
    , p3t: p3at
    , s2e: s2exp
    ) : void = let
    val d2v = (case+ p3t.p3at_node of
      | P3Tvar (_(*refknd*), d2v) => d2v
      | P3Tas (_(*refknd*), d2v, _(*p2at*)) => d2v
      | _ => begin
          prerr_loc_interror loc0;
          prerr ": s2exp_wth_instantiate: aux: p3t = "; prerr p3t;
          prerr_newline ();
          $Err.abort {d2var_t} ()
        end // end of [_]
    ) : d2var_t // end of [val]
(*
    val () = begin
      print "s2exp_wth_instantiate: aux: refval = "; print refval; print_newline ();
      print "s2exp_wth_instantiate: aux: d2v = "; print d2v; print_newline ();
      print "s2exp_wth_instantiate: aux: s2e = "; print s2e; print_newline ();
    end // end of [val]
*)
  in
    case+ refval of
    | _ when refval = 0 => d2var_set_fin (d2v, D2VARFINsome s2e)
    | _ (* refval = 1 *) => let
        val d2v_view = d2var_get_view_some (loc0, d2v)
        val s2e_addr = d2var_get_addr_some (loc0, d2v)
        val s2e_at = s2exp_at_viewt0ype_addr_view (s2e, s2e_addr)
      in
        d2var_set_fin (d2v_view, D2VARFINsome s2e_at)
      end // end of [_]
  end // end of [aux]
  fun auxlst (loc0: loc_t, p3ts: p3atlst, wths2es: wths2explst): void =
    case+ wths2es of
    | WTHS2EXPLSTcons_some (refval, s2e, wths2es) => let
        val () = assert_errmsg_bool1 (
          $Lst.list_is_cons p3ts, "INTERNAL ERROR: s2exp_wth_instantiate"
        ) // end of [assert_errmsg]
        val+ list_cons (p3t, p3ts) = p3ts
        val () = aux (loc0, refval, p3t, s2e)
      in
        auxlst (loc0, p3ts, wths2es)     
      end // end of [WTHS2EXPLSTcons_some]
    | WTHS2EXPLSTcons_none (wths2es) => let
(*
        val () = assert_errmsg_bool1 (
          $Lst.list_is_cons p3ts, "INTERNAL ERROR: s2exp_wth_instantiate"
        ) // end of [assert_errmsg]
*)
        val- list_cons (p3t, p3ts) = p3ts
      in
        auxlst (loc0, p3ts, wths2es)
      end // end of [WTHS2EXPLSTcons_none]
    | WTHS2EXPLSTnil () => ()
  val s2e0 = s2exp_exi_instantiate_all (loc0, s2e0)
in
  case+ s2e0.s2exp_node of
  | S2Ewth (s2e, wths2es) => let
      val opt = the_lamloop_env_arg_get () 
      val p3ts = (
        case+ opt of
        | ~Some_vt p3ts => p3ts
        | ~None_vt () => begin
            prerr_loc_interror loc0;
            prerr ": s2exp_wth_instantiate"; prerr_newline ();
            $Err.abort {p3atlst} ()
          end // end of [None_vt]
      ) : p3atlst
    in
      auxlst (loc0, p3ts, wths2es); s2e
    end // end of [S2Ewth]
  | _ => s2e0
end // end of [s2exp_wth_instantiate]

(* ****** ****** *)

implement
s2exp_uni_instantiate_all (loc0, s2e0) = let
  val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
    | S2Euni (s2vs, s2ps, s2e) => let
        val sub = s2qua_instantiate_and_add (loc0, s2vs, s2ps)
        val s2e = s2exp_subst (sub, s2e)
      in
        s2exp_uni_instantiate_all (loc0, s2e)
      end // end of [S2Euni]
    | S2Emetfn (d2vopt, s2es_met, s2e) => let
        val () = s2exp_metric_instantiate (loc0, d2vopt, s2es_met)
      in
        s2exp_uni_instantiate_all (loc0, s2e)
      end // end of [S2Emetfn]
    | _ => s2e0
end // end [s2exp_uni_instantiate_all]

implement
s2exp_uni_instantiate_one
  (loc0, s2e0) = let
  val s2e0 = s2exp_whnf s2e0
in
  case+ s2e0.s2exp_node of
  | S2Euni (s2vs, s2ps, s2e) => let
      val sub = s2qua_instantiate_and_add (loc0, s2vs, s2ps)
    in
      s2exp_subst (sub, s2e)
    end // end of [S2Euni]
  | _ => let
      val () = prerr_loc_error3 loc0
      val () = prerr ": the type ["
      val () = prerr_s2exp (s2e0)
      val () = prerr "] is expected to be universally quantified."
      val () = prerr_newline ()
    in
      $Err.abort {s2exp} ()
    end // end of [_]
end // end of [s2exp_uni_instantiate_one]

implement
s2exp_uni_instantiate_seq
  (loc0, s2e0, loc_arg, s2es0) = let
  val s2e0 = s2exp_whnf s2e0 in case+ s2e0.s2exp_node of
    | S2Euni (s2vs, s2ps, s2e) => let
        val sub = begin
          s2qua_instantiate_with_and_add (loc0, s2vs, s2ps, loc_arg, s2es0)
        end // end of [val]
      in
        s2exp_subst (sub, s2e)
      end // end of [S2Euni]
    | _ => begin
        prerr_loc_error3 loc0;
        prerr ": the type ["; prerr s2e0;
        prerr "] is expected to be universally quantified.";
        prerr_newline ();
        $Err.abort {s2exp} ()
      end // end of [_]
end // end of [s2exp_uni_instantiate_seq]

implement
s2exp_uni_instantiate_sexparg
  (loc0, s2e0, s2a) = begin
  case+ s2a.s2exparg_node of
  | S2EXPARGone () => s2exp_uni_instantiate_one (loc0, s2e0)
  | S2EXPARGall () => s2exp_uni_instantiate_all (loc0, s2e0)
  | S2EXPARGseq s2es => begin
      s2exp_uni_instantiate_seq (loc0, s2e0, s2a.s2exparg_loc, s2es)
    end // end of [S2EXPARGseq]
end // end of [s2exp_uni_instantiate_sexparg]

implement
s2exp_uni_instantiate_sexparglst
  (loc0, s2e0, s2as) = begin
  case+ s2as of
  | list_cons (s2a, s2as) => let
      val s2e0 = s2exp_uni_instantiate_sexparg (loc0, s2e0, s2a)
    in
      s2exp_uni_instantiate_sexparglst (loc0, s2e0, s2as)
    end
  | list_nil () => s2e0
end // end of [s2exp_uni_instantiate_sexparglst]

(* ****** ****** *)

implement
s2exp_template_instantiate
  (loc0, s2vpss, ts2ess, s2e) = let
  fun aux0 (sub: stasub_t, s2vpss: s2qualst): s2qualst = begin
    case+ s2vpss of
    | list_cons (s2vps, s2vpss) => begin
        list_cons (@(s2vps.0, s2explst_subst (sub, s2vps.1)), aux0 (sub, s2vpss))
      end // end of [list_cons]
    | list_nil () => list_nil ()
  end // end of [aux0]
  fun aux1 (loc0: loc_t, subs: List stasub_t, s2vpss: s2qualst, s2e: s2exp)
    : @(List stasub_t, s2exp) = begin case+ s2vpss of
    | list_cons (s2vps, s2vpss) => let
        val sub = s2qua_instantiate_and_add (loc0, s2vps.0, s2vps.1)
        val s2vpss = aux0 (sub, s2vpss)
        val s2e = s2exp_subst (sub, s2e)
      in
        aux1 (loc0, list_cons (sub, subs), s2vpss, s2e)
      end // end of [list_cons]
    | list_nil () => ($Lst.list_reverse subs, s2e)
  end // end of [aux1]
  fun aux2 (
    loc0: loc_t
  , subs: List stasub_t
  , s2vpss: s2qualst
  , ts2ess: tmps2explstlst
  , s2e: s2exp
  ) : @(List stasub_t, s2exp) = begin
    case+ ts2ess of
    | TMPS2EXPLSTLSTcons (loc, s2es, ts2ess) => begin case+ s2vpss of
      | list_cons (s2vps, s2vpss) => let
          val sub = begin
            s2qua_instantiate_with_and_add (loc0, s2vps.0, s2vps.1,loc, s2es)
          end
          val s2vpss = aux0 (sub, s2vpss)
          val s2e = s2exp_subst (sub, s2e)
        in
          aux2 (loc0, list_cons (sub, subs), s2vpss, ts2ess, s2e)
        end // end of [list_cons]
      | list_nil () => begin
          prerr_loc_error3 loc0;
          $Deb.debug_prerrf (": %s: s2exp_template_instantiate", @(THISFILENAME));
          prerr ": too many template arguments are given.";
          prerr_newline ();
          $Err.abort ()
        end // end of [list_nil]
      end // end of [TMPS2EMPLSTLSTcons]
    | TMPS2EXPLSTLSTnil () => aux1 (loc0, subs, s2vpss, s2e)
  end // end of [aux2]
in
  aux2 (loc0, list_nil (), s2vpss, ts2ess, s2e)
end // end of [s2exp_template_instantiate]

(* ****** ****** *)

implement
s2exp_absuni_and_add (loc0, s2e0) = let
(*
  val () = begin
    print "s2exp_absuni_and_add: before: s2e0 = "; print s2e0; print_newline ()
  end // end of [val]
*)
  val s2vss2pss2e = s2exp_absuni s2e0
(*
  val () = begin
    print "s2exp_absuni_and_add: after: s2vs = "; print s2vss2pss2e.0;
    print_newline ()
  end // end of [val]
  val () = begin
    print "s2exp_absuni_and_add: before: s2e = "; print s2vss2pss2e.2;
    print_newline ()
  end // end of [val]
*)
//
  val s2vs: s2varlst = s2vss2pss2e.0
  val () = s2varlst_set_sVarset (s2vs, the_s2Varset_env_get ())
//
  val () = trans3_env_add_svarlst (s2vss2pss2e.0)
  val () = trans3_env_hypo_add_proplst (loc0, s2vss2pss2e.1)
in
  s2vss2pss2e.2
end // end of [s2exp_absuni_and_add]

implement
s2exp_opnexi_and_add (loc0, s2e0) = let
(*
  val () = begin
    print "s2exp_opnexi_and_add: before: s2e0 = "; print s2e0;
    print_newline ()
  end // end of [val]
*)
  val s2vss2pss2e = s2exp_opnexi s2e0
(*
  val () = begin
    print "s2exp_opnexi_and_add: after: s2vs = "; print s2vss2pss2e.0;
    print_newline ()
  end // end of [val]
  val () = begin
    print "s2exp_opnexi_and_add: after: s2e = "; print s2vss2pss2e.2;
    print_newline ()
  end // end of [val]
*)
//
  val s2vs: s2varlst = s2vss2pss2e.0
  val () = s2varlst_set_sVarset (s2vs, the_s2Varset_env_get ())
//
  val () = trans3_env_add_svarlst (s2vs)
  val () = trans3_env_hypo_add_proplst (loc0, s2vss2pss2e.1)
in
  s2vss2pss2e.2
end // end of [s2exp_opnexi_and_add]

implement
s2explst_opnexi_and_add
  (loc0, s2es0) = let
  val s2vss2pss2es = s2explst_opnexi s2es0
//
  val s2vs: s2varlst = s2vss2pss2es.0
  val () = s2varlst_set_sVarset (s2vs, the_s2Varset_env_get ())
//
  val () = trans3_env_add_svarlst (s2vs)
  val () = trans3_env_hypo_add_proplst (loc0, s2vss2pss2es.1)
in
  s2vss2pss2es.2
end // end of [s2exp_opnexi_and_add]

implement
s2expopt_opnexi_and_add
  (loc0, os2e0) = begin
  case+ os2e0 of
  | Some s2e0 => Some (s2exp_opnexi_and_add (loc0, s2e0))
  | None () => None ()
end // end of [s2expopt_opnexi_and_add]

(* ****** ****** *)

implement
trans3_env_hypo_add_p2atcst
  (loc0, p2tc, s2e0) = let
  val s2e0 = s2exp_opnexi_and_add (loc0, s2e0)
in
  case+ p2tc of
  | P2TCany () => ()
  | P2TCbool b => begin
    case+ un_s2exp_bool_bool_t0ype s2e0 of
    | ~Some_vt (s2e_arg) => begin
        $SOL.s2exp_hypo_equal_solve (loc0, s2e_arg, s2exp_bool b)
      end // end of [Some_vt]
    | ~None_vt () => () // end of [None_vt]
    end // end of [P2TCbool]
  | P2TCchar c => begin
      case+ un_s2exp_char_char_t0ype s2e0 of
      | ~Some_vt (s2e_arg) => begin
          $SOL.s2exp_hypo_equal_solve (loc0, s2e_arg, s2exp_char c)
        end // end of [Some_vt]
      | ~None_vt () => ()
    end // end of [P2TCchar]
  | P2TCcon (d2c, p2tcs) => begin case+ s2e0.s2exp_node of
    | S2Edatcontyp (d2c1, _) => begin
        if (d2c <> d2c1) then trans3_env_hypo_add_prop (loc0, s2exp_bool false)
      end // end of [S2Edatcontyp]
    | _ => let
        val @(s2vpss_d2c, s2e_d2c) = $TR2.p1at_con_instantiate (loc0, d2c)
        val (s2es_fun_arg, s2e_fun_res) = (
          case+ s2e_d2c.s2exp_node of
          | S2Efun (_, _, _, _, s2es, s2e) => @(s2es, s2e)
          | _ => begin
              prerr_interror ();
              prerr ": tran3_env_hypo_add_p2atcst: P2TCcon"; prerr_newline ();
              $Err.abort {@(s2explst, s2exp)} ()
            end // end of [_]
        ) : @(s2explst, s2exp)
(*
        val () = begin
          print "trans3_env_hypo_add_p2atcst: s2vpss_d2c = "; print_s2qualst s2vpss_d2c; print_newline ()
        end // end of [val]
        val () = begin
          print "trans3_env_hypo_add_p2atcst: s2es_fun_arg = "; print_s2explst s2es_fun_arg; print_newline ()
        end // end of [val]
        val () = begin
          print "trans3_env_hypo_add_p2atcst: s2e_fun_res = "; print_s2exp s2e_fun_res; print_newline ()
        end // end of [val]
*)
        val () = aux (loc0, s2vpss_d2c) where {
          fun aux (loc0: loc_t, s2vpss: s2qualst): void =
            case+ s2vpss of
            | list_cons (s2vps, s2vpss) => begin
                trans3_env_add_svarlst s2vps.0;
                trans3_env_hypo_add_proplst (loc0, s2vps.1);
                aux (loc0, s2vpss)
              end
            | list_nil () => ()
        } // end of [where]
        val () = $SOL.s2exp_hypo_equal_solve (loc0, s2e_fun_res, s2e0)
      in
        trans3_env_hypo_add_p2atcstlst (loc0, p2tcs, s2es_fun_arg)
      end // end of [_]
    end // end of [P2TCcon]
  | P2TCempty _ => ()
  | P2TCfloat _ => ()
  | P2TCint i => begin
      case+ un_s2exp_int_int_t0ype s2e0 of
      | ~Some_vt s2e_arg => begin
          $SOL.s2exp_hypo_equal_solve (loc0, s2e_arg, s2exp_intinf i)
        end // end of [Some_vt]
      | ~None_vt () => ()
    end // end of [P2TCint]
  | P2TCintc xs => begin case+ un_s2exp_int_int_t0ype s2e0 of
    | ~Some_vt s2e_arg => aux (intinflst_of_intinfset xs) where {
        fun aux (xs: List intinf_t):<cloptr1> void = case+ xs of
          | list_cons (x, xs) => let
              val s2p = s2exp_neq_int_int_bool (s2e_arg, s2exp_intinf x)
            in
              trans3_env_hypo_add_prop (loc0, s2p); aux xs
            end
          | list_nil () => ()
      } // end of [Some_vt]
    | ~None_vt () => ()
    end // end of [P2TCintc]
  | P2TCrec (_, lp2tcs) => begin case+ s2e0.s2exp_node of
      | S2Etyrec (_, _, ls2es) => begin
          trans3_env_hypo_add_labp2atcstlst (loc0, lp2tcs, ls2es)
        end
      | _ => ()
    end // end of [P2TCrec]
  | P2TCstring _ => ()
end // end of [trans3_env_hypo_add_p2atcst]

implement
trans3_env_hypo_add_p2atcstlst
  (loc0, p2tcs, s2es) = let
  fun aux (loc0: loc_t, p2tcs: p2atcstlst, s2es: s2explst)
    : int = begin case+ p2tcs of
    | list_cons (p2tc, p2tcs) => begin case+ s2es of
      | list_cons (s2e, s2es) => begin
          trans3_env_hypo_add_p2atcst (loc0, p2tc, s2e);
          aux (loc0, p2tcs, s2es)
        end
      | list_nil () => 1
      end // end of [list_cons]
    | list_nil () => begin
        case+ s2es of list_cons _ => 1 | list_nil () => 0
      end // end of [list_nil]
  end // end of [aux]
  val err = aux (loc0, p2tcs, s2es)
in
  if err > 0 then begin
    prerr_loc_interror loc0;
    prerr ": trans3_env_hypo_add_p2atcstlst"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [trans3_env_hypo_add_p2atcstlst]

implement
trans3_env_hypo_add_labp2atcstlst
  (loc0, lp2tcs, ls2es) = let
  fun aux (
    loc0: loc_t, lp2tcs: labp2atcstlst, ls2es: labs2explst
  ) : int = begin case+ lp2tcs of
    | LABP2ATCSTLSTcons (_, p2tc, lp2tcs) => begin case+ ls2es of
      | LABS2EXPLSTcons (_, s2e, ls2es) => begin
          trans3_env_hypo_add_p2atcst (loc0, p2tc, s2e);
          aux (loc0, lp2tcs, ls2es)
        end // end of [LABS2EXPLSTcons]
      | LABS2EXPLSTnil () => 1
      end // end of [LABP2ATCSTLSTcons]
    | LABP2ATCSTLSTnil () => begin
        case+ ls2es of LABS2EXPLSTcons _ => 1 | LABS2EXPLSTnil _ => 0
      end // end of [LABP2ATCSTLSTnil]
  end // end of [aux]
  val err = aux (loc0, lp2tcs, ls2es)
in
  if err > 0 then begin
    prerr_loc_interror loc0;
    prerr ": trans3_env_hypo_add_labp2atcstlst"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
end // end of [trans3_env_hypo_add_labp2atcstlst]

//
// HX: for adding sequentiality assumption
//
implement
trans3_env_hypo_add_p2atcstlstlst
  (loc0, p2tcss, s2es) = let
  fun aux (
    p2tcss: p2atcstlstlst, s3iss: List_vt (s3itemlst)
  ) :<cloptr1> s3itemlstlst = begin case+ p2tcss of
    | list_cons (p2tcs, p2tcss) => let
        val () = trans3_env_push_sta ()
        val () = trans3_env_hypo_add_p2atcstlst (loc0, p2tcs, s2es)
        val s3is = trans3_env_pop_sta ()
        val s3is = $Lst.list_vt_reverse_list s3is
      in
        aux (p2tcss, list_vt_cons (s3is, s3iss))
      end
    | list_nil () => $Lst.list_vt_reverse_list (s3iss)
  end // end of [aux]
in
  trans3_env_hypo_add_disj (aux (p2tcss, list_vt_nil ()))
end // end of [trans3_env_hypo_add_p2atcstlstlst]

//
// HX: for checking termination metric being decreasing
//
implement
trans3_env_add_metric_dec
  (loc, met, met_bound) = let
  val c3t = c3str_metric_dec (loc, met, met_bound)
in
  trans3_env_add_cstr c3t
end // end of [trans3_env_add_metric]

//
// HX: for checking pattern matching exhaustiveness
//
implement
trans3_env_add_p2atcstlstlst_false
  (loc0, casknd, p2tcss, s2es) = let
  fun aux (p2tcss: p2atcstlstlst):<cloptr1> void = begin
    case+ p2tcss of
    | list_cons (p2tcs, p2tcss) => let
        val () = trans3_env_push_sta ()
        val () = trans3_env_hypo_add_p2atcstlst (loc0, p2tcs, s2es)
        val c3t = begin
          c3str_pattern_match_exhaustiveness (loc0, casknd, p2tcs)
        end // end of [val]
        val () = trans3_env_add_cstr (c3t)
        val () = trans3_env_pop_sta_and_add_none (loc0)
      in
        aux p2tcss
      end // end of [list_cons]
    | list_nil () => () // end of [list_nil]
  end // end of [aux]
in
  aux (p2tcss)
end // end of [trans3_env_add_p2atcstlstlst_false]

(* ****** ****** *)

implement
trans3_env_initize
  ((*void*)) = () where {
//
  val () = the_s2varbindmap_initize ()
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Bool_t0ype)
    val s2c1 = s2cstref_get_cst (Bool_bool_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Char_t0ype)
    val s2c1 = s2cstref_get_cst (Char_char_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Int_t0ype)
    val s2c1 = s2cstref_get_cst (Int_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Uint_t0ype)
    val s2c1 = s2cstref_get_cst (Uint_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Lint_t0ype)
    val s2c1 = s2cstref_get_cst (Lint_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Ulint_t0ype)
    val s2c1 = s2cstref_get_cst (Ulint_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Size_t0ype)
    val s2c1 = s2cstref_get_cst (Size_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Ssize_t0ype)
    val s2c1 = s2cstref_get_cst (Ssize_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Ptr_type)
    val s2c1 = s2cstref_get_cst (Ptr_addr_type)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (Strbuf_t0ype)
    val s2c1 = s2cstref_get_cst (Strbuf_int_int_t0ype)
  } // end of [where]
//
  val () = s2cst_add_sup (s2c1, s2c0) where {
    val s2c0 = s2cstref_get_cst (String_type)
    val s2c1 = s2cstref_get_cst (String_int_type)
  } // end of [where]
//
  val () = clo_viewt0ype_viewt0ype_assume ()
  val () = cloptr_viewt0ype_viewtype_assume ()
  val () = cloref_t0ype_type_assume ()
//
  val () = crypt_viewt0ype_viewt0ype_assume ()
//
  val () = sizeof_viewt0ype_int_assume ()
//
} // end of [trans3_env_initilize]

(* ****** ****** *)

(* end of [ats_trans3_env.dats] *)
