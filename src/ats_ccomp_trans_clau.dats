(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
// Time: May 2008
//
(* ****** ****** *)

%{^
#include "ats_intinf.cats"
%} // end of [%{^]

(* ****** ****** *)

staload
IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

viewtypedef branchlst_vt = List_vt branch

fn branch_make
(
  tl: tmplab_t, inss: instrlst
) : branch = '{
  branch_lab= tl, branch_inss= inss
} // end of [branch_make]

(* ****** ****** *)

datatype
tmpmovlst =
  | TMPMOVLSTcons of (tmpvar_t, tmpvar_t, tmpmovlst)
  | TMPMOVLSTnil
// end of [tmpmovlst]

typedef
matpnt = '{
  matpnt_kont= kont, matpnt_tmpmovlst= tmpmovlst
} // end of [matpnt]

(* ****** ****** *)

extern fun kont_matpnt (mpt: matpnt_t): kont
extern fun matpnt_make (k: kont, xs: tmpmovlst): matpnt_t

extern fun matpnt_get_tmpmovlst (mpt: matpnt_t): tmpmovlst
extern fun matpnt_tmpmovlst_set
  (mpt: matpnt_t, _: tmpmovlst): void = "atsopt_matpnt_set_tmpmovlst"
// end of [matpnt_set_tmpmovlst]

(* ****** ****** *)

local

fn _matpnt_make (
  k: kont, xs: tmpmovlst
) : matpnt = '{
  matpnt_kont= k, matpnt_tmpmovlst= xs
} // end of [matpnt_make]

assume matpnt_t = matpnt

in // in of [local]

extern typedef "matpnt_t" = matpnt

implement kont_matpnt (mpt) = KONTmatpnt (mpt)

implement matpnt_make (k, xs) = _matpnt_make (k, xs)
implement matpnt_get_kont (mpt) = mpt.matpnt_kont
implement matpnt_get_tmpmovlst (mpt) = mpt.matpnt_tmpmovlst

implement
emit_matpnt {m}
  (pf | out, mpt) = let
  val tmpmovlst =
    matpnt_get_tmpmovlst (mpt)
  // end of [val]
  val () = aux (out, tmpmovlst) where {
    fun aux (
      out: &FILE m, xs: tmpmovlst
    ) : void = begin case+ xs of
      | TMPMOVLSTcons (
          tmp1, tmp2, xs
        ) => aux (out, xs)  where {
          val () = emit_tmpvar (pf | out, tmp2)
          val () = fprint1_string (pf | out, " = ")
          val () = emit_tmpvar (pf | out, tmp1)
          val () = fprint1_string (pf | out, " ; ")
        } // end of [where]
      | TMPMOVLSTnil () => () // end of [TMPMOVLSTnil]
    end // end of [aux]
  } // end of [where]
  val () = emit_kont (pf | out, matpnt_get_kont mpt)
in
  // empty
end // end of [emit_matpnt]

end // end of [local]

(* ****** ****** *)

extern
fun ccomp_hiclau
(
  loc0: loc_t
, level: int
, branchlst: &branchlst_vt
, tl: tmplab_t
, vps: valprimlst
, hicl: hiclau
, tmp_res: tmpvar_t
) : @(matpntlst, matpntopt)

implement
ccomp_hiclau
(
  loc0, level, branchlst, tl, vps, hicl, tmp_res
) = let
//
  fun aux_pat
  (
    res: &instrlst_vt
  , tl: tmplab_t, i: &int >> int
  , vps: valprimlst, hips: hipatlst
  ) : matpntlst =
  (
    case+ (vps, hips) of
    | (list_cons (vp, vps),
       list_cons (hip, hips)) => let
        val loc = hip.hipat_loc
        val () = instr_add_tmplabint (res, loc, tl, i)
        val mpt = matpnt_make (KONTnone (), TMPMOVLSTnil ())
        val () = ccomp_patck (res, vp, hip, kont_matpnt mpt)
        val () = i := i + 1
        val mpts = aux_pat (res, tl, i, vps, hips)
      in
        list_cons (mpt, mpts)
      end // end of [list_cons]
    | (_, _) => list_nil ()
  ) (* end of [aux_pat] *)
//
  fun aux_mat
  (
    res: &instrlst_vt
  , level: int, vps: valprimlst, hips: hipatlst
  ) : void =
  (
    case+ (vps, hips) of
    | (list_cons (vp, vps),
       list_cons (hip, hips)) => let
        val () = ccomp_match (res, level, vp, hip)
      in
        aux_mat (res, level, vps, hips)
      end // end of [list_cons _, list_cons _]
    | (_, _) => ()
  ) (* end of [aux_mat] *)
//
  fun aux_gua (
      res: &instrlst_vt
    , level: int
    , himats: himatlst
    , fail: kont
    ) : void = begin case+ himats of
    | list_cons (himat, himats) => let
        val hip = (
          case+ himat.himat_pat of
          | None () => hipat_bool (himat.himat_loc, hityp_bool, true)
          | Some hip => hip
        ) : hipat
        val vp = ccomp_exp (res, himat.himat_exp)
        val () = ccomp_patck (res, vp, hip, fail)
        val () = ccomp_match (res, level, vp, hip)
      in
        aux_gua (res, level, himats, fail)
      end // end of [list_cons]
    | list_nil () => ()
  end (* end of [aux_gua] *)
//
  var i: int = 0
  var res: instrlst_vt = list_vt_nil ()
  val hips = hicl.hiclau_pat
  val mpts = aux_pat (res, tl, i, vps, hips)
  val () = begin
    instr_add_tmplabint (res, loc0, tl, i) // [i] = the length of [hicls]
  end // end of [val]
//
  val () = aux_mat (res, level, vps, hips)
//
  var ompt: matpntopt = None ()
  val () = let
    val himats = hicl.hiclau_gua
  in
    case+ himats of
    | list_cons _ => let
        val mpt = matpnt_make (KONTnone (), TMPMOVLSTnil ())
        val () = aux_gua (res, level, himats, kont_matpnt mpt)
      in
        ompt := Some mpt
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [val]
//
  val () = instr_add_valprimlst_free (res, hicl.hiclau_loc)
//
  val () = ccomp_exp_tmpvar (res, hicl.hiclau_exp, tmp_res)
  val res = $Lst.list_vt_reverse_list res
  val () = branchlst := list_vt_cons (branch_make (tl, res), branchlst)
in
  (mpts, ompt)
end // end of [ccomp_hiclau]

(* ****** ****** *)

extern fun hipat_test_int (hip1: hipat, hip2: hipat): bool
extern fun hipatlst_test_int (hips1: hipatlst, hips2: hipatlst): bool

extern fun labhipatlst_test_int
  (lhips1: labhipatlst, lhips2: labhipatlst): bool
// end of [labhipatlst_test_int]

(* ****** ****** *)

implement
hipat_test_int (hip1, hip2) = let
(*
  val () = begin
    print "hipat_test_int: hip1 = "; print hip1; print_newline ();
    print "hipat_test_int: hip2 = "; print hip2; print_newline ();
  end // end of [val]
*)
in
  case+ (hip1.hipat_node, hip2.hipat_node) of
  | (HIPann (hip1, _), _) => hipat_test_int (hip1, hip2)
  | (_, HIPann (hip2, _)) => hipat_test_int (hip1, hip2)
  | (HIPany _, _) => true
  | (_, HIPany _) => true
  | (HIPas (_(*knd*), _(*d2v*), hip1), _) => hipat_test_int (hip1, hip2)
  | (_, HIPas (_(*knd*), _(*d2v*), hip2)) => hipat_test_int (hip1, hip2)
  | (HIPvar _, _) => true
  | (_, HIPvar _) => true
  | (HIPbool b1, HIPbool b2) => (b1 = b2)
  | (HIPchar c1, HIPchar c2) => (c1 = c2)
  | (HIPcon (_, d2c1, hips1, _), HIPcon (_, d2c2, hips2, _)) =>
      if d2c1 = d2c2 then hipatlst_test_int (hips1, hips2) else false
  | (HIPcon (_, d2c1, _, _), HIPcon_any (_, d2c2)) => d2c1 = d2c2
  | (HIPcon_any (_, d2c1), HIPcon (_, d2c2, _, _)) => d2c1 = d2c2
  | (HIPcon_any (_, d2c1), HIPcon_any (_, d2c2)) => d2c1 = d2c2
  | (HIPempty _, HIPempty _) => true
  | (HIPfloat f1, HIPfloat f2) => (f1 = f2)
  | (HIPint (_, i1), HIPint (_, i2)) =>
      $IntInf.eq_intinf_intinf (i1, i2)
  | (HIPlst (_, hips1), HIPlst (_, hips2)) =>
      hipatlst_test_int (hips1, hips2)
  | (HIPrec (_, lhips1, _), HIPrec (_, lhips2, _)) =>
      labhipatlst_test_int (lhips1, lhips2)
  | (HIPstring s1, HIPstring s2) => (s1 = s2)
  | (_, _) => false
end // end of [hipat_test_int]

(* [hips1] and [hips2] are of the same length *)
implement
hipatlst_test_int (hips1, hips2) = begin
  case+ hips1 of
  | list_cons (hip1, hips1) => begin case+ hips2 of
    | list_cons (hip2, hips2) => begin
        if hipat_test_int (hip1, hip2) then hipatlst_test_int (hips1, hips2)
        else false
      end
    | list_nil () => false
    end // end of [list_cons]
  | list_nil () => begin case+ hips2 of
    | list_cons _ => false | list_nil _ => true
    end // end of [list_nil]
end (* end of [hipatlst_test_int] *)

implement
labhipatlst_test_int
  (lhips1, lhips2) = begin
  case+ lhips1 of
  | LABHIPATLSTcons (l1, hip1, hips1) => begin
    case+ lhips2 of
    | LABHIPATLSTcons (l2, hip2, hips2) => begin
      case+ 0 of
      | _ when $Lab.eq_label_label (l1, l2) =>
          if hipat_test_int (hip1, hip2) then
            labhipatlst_test_int (lhips1, lhips2)
          else false
      | _ => false // end of [_]
      end (* end of [LABHIPATLSTcons] *)
    | _ => true
    end (* end of [LABHIPATLSTcons] *)
  | _ => begin case+ lhips2 of
    | LABHIPATLSTcons _ => false | _ => true
    end // end of [_]
end // end of [labhipatlst_test_int]

(* ****** ****** *)

extern fun hipat_test_sub (hip1: hipat, hip2: hipat): bool
extern fun hipatlst_test_sub (hips1: hipatlst, hips2: hipatlst): bool
extern fun labhipatlst_test_sub
  (lhips1: labhipatlst, lhips2: labhipatlst): bool
// end of [labhipatlst_test_sub]

(* ****** ****** *)

fun hipat_is_any
  (hip0: hipat): bool =
  case+ hip0.hipat_node of
  | HIPann (hip, _) => hipat_is_any hip
  | HIPany _ => true
  | HIPas (_, _, hip) => hipat_is_any hip
  | HIPvar _ => true
  | _ => false
// end of [hipat_is_any]

fun hipatlst_is_any
  (hips: hipatlst): bool =
  case+ hips of
  | list_cons (hip, hips) => begin
      if hipat_is_any hip then hipatlst_is_any hips else false
    end
  | list_nil () => false
// end of [hipatlst_is_any]

implement
hipat_test_sub (hip1, hip2) = let
(*
  val () = begin
    print "hipat_test_sub: hip1 = "; print hip1; print_newline ();
    print "hipat_test_sub: hip2 = "; print hip2; print_newline ();
  end // end of [val]
*)
in
  case+ (hip1.hipat_node, hip2.hipat_node) of
  | (_, HIPany _) => true
  | (_, HIPvar _) => true
  | (_, HIPann (hip2, _)) => hipat_test_sub (hip1, hip2)
  | (_, HIPas (_(*knd*), _(*d2v*), hip2)) => hipat_test_sub (hip1, hip2)
  | (HIPann (hip1, _), _) => hipat_test_sub (hip1, hip2)
  | (HIPas (_(*knd*), _(*d2v*), hip1), _) => hipat_test_sub (hip1, hip2)
  | (HIPbool b1, HIPbool b2) => (b1 = b2)
  | (HIPchar c1, HIPchar c2) => (c1 = c2)
  | (HIPcon (_, d2c1, hips1, _), HIPcon (_, d2c2, hips2, _)) =>
      if d2c1 = d2c2 then hipatlst_test_sub (hips1, hips2) else false
  | (HIPcon (_, d2c1, hips1, _), HIPcon_any (_, d2c2)) => d2c1 = d2c2
  | (HIPcon_any (_, d2c1), HIPcon (_, d2c2, hips2, _)) =>
      if d2c1 = d2c2 then hipatlst_is_any hips2 else false
  | (HIPcon_any (_, d2c1), HIPcon_any (_, d2c2)) => d2c1 = d2c2
  | (HIPempty _, HIPempty _) => true
  | (HIPfloat f1, HIPfloat f2) => (f1 = f2)
  | (HIPint (_, i1), HIPint (_, i2)) =>
      $IntInf.eq_intinf_intinf (i1, i2)
  | (HIPlst (_, hips1), HIPlst (_, hips2)) =>
      hipatlst_test_sub (hips1, hips2)
  | (HIPrec (_, lhips1, _), HIPrec (_, lhips2, _)) =>
      labhipatlst_test_sub (lhips1, lhips2)
  | (HIPstring s1, HIPstring s2) => (s1 = s2)
  | (_, _) => false
end // end of [hipat_test_sub]

(*
** HX: [hips1] and [hips2] are of the same length
*)
implement
hipatlst_test_sub
  (hips1, hips2) = case+ hips1 of
  | list_cons (hip1, hips1) => begin case+ hips2 of
    | list_cons (hip2, hips2) => begin
        if hipat_test_sub (hip1, hip2) then hipatlst_test_sub (hips1, hips2)
        else false
      end
    | list_nil () => false
    end // end of [list_cons]
  | list_nil () => begin case+ hips2 of
    | list_cons _ => false | list_nil _ => true
    end // end of [list_nil]
(* end of [hipatlst_test_sub] *)

implement
labhipatlst_test_sub
  (lhips1, lhips2) = case+ lhips1 of
  | LABHIPATLSTcons (l1, hip1, hips1) => begin
    case+ lhips2 of
    | LABHIPATLSTcons (l2, hip2, hips2) => begin
      case+ 0 of
      | _ when $Lab.eq_label_label (l1, l2) =>
          if hipat_test_sub (hip1, hip2) then
            labhipatlst_test_sub (lhips1, lhips2)
          else false
      | _ => false
      end // end of [LABHIPATLSTcons]
    | _ => true
    end // end of [LABHIPATLSTcons]
  | _ => begin case+ lhips2 of
    | LABHIPATLSTcons _ => false | _ => true
    end // end of [_]
(* end of [labhipatlst_test_sub] *)

(* ****** ****** *)

local

datatype l0st =
  | L0STcons of (tmplab_t, hiclau, matpntlst, matpntopt, l0st)
  | L0STnil
// end of [l0st]

fun hipatlst_prefix_test_int (
  i: int, hips1: hipatlst, hips2: hipatlst
) : bool = begin
  if i > 0 then begin case+ hips1 of
   | list_cons (hip1, hips1) => begin case+ hips2 of
      | list_cons (hip2, hips2) => begin
          if hipat_test_int (hip1, hip2) then
            hipatlst_prefix_test_int (i-1, hips1, hips2)
          else false
        end // end of [list_cons]
      | list_nil () => true
      end // end of [list_cons]
    // this clause should never be chosen:
    | list_nil () => begin case+ hips2 of
      | list_cons _ => false | list_nil () => true
      end // end of [list_nil]
  end else begin
    true // return value
  end // end of [if]
end (* end of [hipatlst_test_int] *)

fun aux_major (
  i: int, hips0: hipatlst, xs: l0st
) : Option_vt @(tmplab_t, hiclau) = begin
  case+ xs of
  | L0STcons (tl, hicl, _, _, xs) => let
      val isint = hipatlst_prefix_test_int (i, hips0, hicl.hiclau_pat)
    in
      if isint then Some_vt @(tl, hicl) else aux_major (i, hips0, xs)
    end // end of [L0STcons]
  | L0STnil () => None_vt ()
end (* end [aux_major] *)

fun aux_minor (
  i0: int, hips0: hipatlst, hicl: hiclau
) : int = let
  fun f (i: int, hips1: hipatlst, hips2: hipatlst)
    :<cloptr1> int = begin case+ i of
    | _ when i < i0 => begin case+ (hips1, hips2) of
      | (list_cons (hip1, hips1), list_cons (hip2, hips2)) =>
          if hipat_test_sub (hip1, hip2) then f (i+1, hips1, hips2) else i
      | (_, _) => i // this clause should never be taken
      end // end of [_ when ...]
    | _ => i
  end (* end of [f] *)
in
  f (0, hips0, hicl.hiclau_pat)
end // end of [aux_minor]

fun aux_tmpmov (
  i: int, hips0: hipatlst, hicl: hiclau
) : tmpmovlst = let
//
  fun auxpat (
      hip1: hipat
    , hip2: hipat
    , res: &tmpmovlst
    ) : void = begin
    case+ (hip1.hipat_node, hip2.hipat_node) of
    | (HIPann (hip1, _), _) => auxpat (hip1, hip2, res)
    | (_, HIPann (hip2, _)) => auxpat (hip1, hip2, res)
    | (HIPcon (_, d2c1, hips1, _), HIPcon (_, d2c2, hips2, _)) => begin
        if d2c1 = d2c2 then let
          val od2v1 = hip1.hipat_asvar; val od2v2 = hip2.hipat_asvar
          val () = case+ (od2v1, od2v2) of
            | (D2VAROPTsome d2v1, D2VAROPTsome d2v2) => let
                val vp1 = the_dynctx_find d2v1 in case+ vp1.valprim_node of
                | VPtmp tmp1 => let
                    val vp2 = the_dynctx_find d2v2 in
                    case+ vp2.valprim_node of
                    | VPtmp tmp2 => (res := TMPMOVLSTcons (tmp1, tmp2, res))
                    | _ => () // deadcode!
                  end // end of [VPtmp]
                | _ => ()
              end (* end of [D2VAROPTsome, D2VAROPTsome] *)
            | (_, _) => ()
        in
          auxpatlst (hips1, hips2, res)
        end // end of [if]
      end (* end of [HIPcon, HIPcon] *)
    | (HIPrec (_, lhips1, _), HIPrec (_, lhips2, _)) =>
        auxlabpatlst (lhips1, lhips2, res)
    | (_, _) => ()
  end // end of [auxpat]
//
  and auxpatlst (
      hips1: hipatlst
    , hips2: hipatlst
    , res: &tmpmovlst
    ) : void = begin case+ (hips1, hips2) of
    | (list_cons (hip1, hips1), list_cons (hip2, hips2)) =>
        (auxpat (hip1, hip2, res); auxpatlst (hips1, hips2, res))
    | (_, _) => ()
  end // end of [auxpatlst]
//
  and auxlabpatlst (
      lhips1: labhipatlst
    , lhips2: labhipatlst
    , res: &tmpmovlst
    ) : void = begin case+ (lhips1, lhips2) of
    | (LABHIPATLSTcons (_(*l1*), hip1, lhips1),
       LABHIPATLSTcons (_(*l2*), hip2, lhips2)) => begin
        auxpat (hip1, hip2, res); auxlabpatlst (lhips1, lhips2, res)
      end // end of [LABHIPATLSTcons, LABHIPATLSTcons]
    | (_, _) => ()       
  end // end of [auxlabpatlst]
//
  fun auxpatlst_prefix (
      i: int
    , hips1: hipatlst
    , hips2: hipatlst
    , res: &tmpmovlst
    ) : void = begin case+ 0 of
    | _ when i > 0 => begin case+ (hips1, hips2) of
      | (list_cons (hip1, hips1),
         list_cons (hip2, hips2)) => let
          val () = auxpat (hip1, hip2, res)
        in
          auxpatlst_prefix (i-1, hips1, hips2, res)
        end // end of [list_cons, list_cons]
      | (_, _) => ()
      end // end of [_ when i > 0]
    | _ => ()
  end (* end of [auxpatlst_prefix] *)
//
  var res: tmpmovlst = TMPMOVLSTnil ()
  val () = auxpatlst_prefix (i, hips0, hicl.hiclau_pat, res)
  val res = auxrev (res, TMPMOVLSTnil ()) where {
    fun auxrev (
      xs: tmpmovlst, ys: tmpmovlst
    ) : tmpmovlst = case+ xs of
      | TMPMOVLSTcons (tmp1, tmp2, xs) => begin
          auxrev (xs, TMPMOVLSTcons (tmp1, tmp2, ys))
        end // end of [TMPMOVLSTcons]
      | TMPMOVLSTnil () => ys // end of [TMPMOVLSTnil]
    // end of [auxrev]
  } // end [where]
//
in
  res
end // end of [aux_tmpmov]

fun matpnt_set_kont_all
  (xs: l0st, fail_default: kont): void = begin case+ xs of
  | L0STcons (tl, hicl, mpts, ompt, xs) => let
//
      fn aux (
          i: int
        , hips0: hipatlst
        , mpt: matpnt_t
        ) :<cloptr1> void = begin
        case+ aux_major (i, hips0, xs) of
        | ~Some_vt (tl_hicl) => let
            val tl = tl_hicl.0 and hicl = tl_hicl.1
            val j = aux_minor (i, hips0, hicl)
            val () = matpnt_set_kont (mpt, kont) where {
              val kont = KONTtmplabint (tl, j)
            } // end of [where]
            val () = matpnt_tmpmovlst_set (mpt, tmpmovlst) where {
              val tmpmovlst = aux_tmpmov (j, hips0, hicl)
            } // end of [where]
          in
            // empty
          end // end of [Some_vt]
        | ~None_vt () => matpnt_set_kont (mpt, fail_default)
      end // end of [aux]
//
      fun auxlst (
          i: int
        , hips0: hipatlst
        , mpts: matpntlst
        ) :<cloptr1> int = begin case+ mpts of
        | list_cons (mpt, mpts) => begin
            aux (i, hips0, mpt); auxlst (i+1, hips0, mpts)
          end // end of [list_cons]
        | list_nil () => i
      end // end of [auxlst]
//
      fn auxopt (
          i: int
        , hips0: hipatlst
        , ompt: matpntopt
        ) :<cloptr1> void = begin case+ ompt of
        | Some mpt => aux (i, hips0, mpt) | None () => ()
      end // end of [auxopt]
//
      val () = auxopt (i, hips0, ompt) where {
        val hips0 = hicl.hiclau_pat; val i = auxlst (0, hips0, mpts)
      } // end of [where]
//
    in
      matpnt_set_kont_all (xs, fail_default)
    end // end ofl[L0STcons]
  | L0STnil () => () // end of [L0STnil]
end // end of [matpnt_set_kont_all]

in // in of [local]

implement
ccomp_hiclaulst (
  level, vps, hicls, tmp_res, fail_default
) = let
//
  fun auxlst (
      branchlst: &branchlst_vt
    , hicls: hiclaulst
    ) :<cloptr1> l0st = begin case+ hicls of
    | list_cons (hicl, hicls) => let
//
        val tl = tmplab_make ()
        val xy = ccomp_hiclau
          (hicl.hiclau_loc, level, branchlst, tl, vps, hicl, tmp_res)
//
        val xys = auxlst (branchlst, hicls)
//
      in
        L0STcons (tl, hicl, xy.0, xy.1, xys)
      end // end of [list_cons]
    | list_nil () => L0STnil ()
  end // end of [auxlst]
//
  var branchlst: branchlst_vt = list_vt_nil ()
  val xs(*l0st*) = auxlst (branchlst, hicls)
  val () = matpnt_set_kont_all (xs, fail_default)
//
in
  $Lst.list_vt_reverse_list (branchlst)
end // end of [ccomp_hiclaulst]

end // end of [local]

(* ****** ****** *)

%{$

ats_void_type
atsopt_matpnt_set_kont
  (ats_ptr_type mpt, ats_ptr_type kont) {
  ((matpnt_t)mpt)->atslab_matpnt_kont = kont ;
  return ;
} // end of [atsopt_matpnt_set_kont]

ats_void_type
atsopt_matpnt_set_tmpmovlst
  (ats_ptr_type mpt, ats_ptr_type tmpmovlst) {
  ((matpnt_t)mpt)->atslab_matpnt_tmpmovlst = tmpmovlst ;
  return ;
} // end of [atsopt_matpnt_set_tmpmovlst]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_ccomp_trans_clau.dats] *)
