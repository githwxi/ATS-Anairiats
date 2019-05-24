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
// Time: January 2008
//
(* ****** ****** *)

(* Mainly for tracking states during the third translation *)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload SOL = "ats_staexp2_solve.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

typedef stbefitem = '{
  stbefitem_var= d2var_t, stbefitem_lin= int, stbefitem_typ= s2expopt
} // end of [stbefitem]

assume stbefitem_t = stbefitem

(* ****** ****** *)

fn prerr_interror
  () = prerr "INTERNAL ERROR (ats_trans3_env_state)"
// end of [prerr_interror]

(* ****** ****** *)

implement
stbefitem_make (d2v, lin) = let
  val os2e = d2var_get_typ d2v in '{
  stbefitem_var= d2v, stbefitem_lin= lin, stbefitem_typ= os2e
} end // end of [stbefitem_make]

implement
stbefitemlst_restore_typ (sbis) = let
  fun loop (sbis: stbefitemlst): void = case+ sbis of
    | list_cons (sbi, sbis) => let
        val d2v = sbi.stbefitem_var
        val () = d2var_set_typ (d2v, sbi.stbefitem_typ)
      in
        loop (sbis)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (sbis)
end // end of [stbefitemlst_restore_typ]

implement
stbefitemlst_restore_lin_typ (sbis) = let
  fun loop (
    sbis: stbefitemlst
  ) : void = case+ sbis of
    | list_cons (sbi, sbis) => let
        val d2v = sbi.stbefitem_var
        val () = d2var_set_lin (d2v, sbi.stbefitem_lin)
        val () = d2var_set_typ (d2v, sbi.stbefitem_typ)
      in
        loop (sbis)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (sbis)
end // end of [stbefitemlst_restore_lin_typ]

(* ****** ****** *)

datatype saityp =
  | SAITYPsome of (loc_t, s2exp) | SAITYPnone of loc_t
typedef saityplst = List saityp

fn saityp_get_loc (x: saityp): loc_t = case+ x of
  | SAITYPsome (loc, _) => loc | SAITYPnone loc => loc
// end of [saityp_get_loc]

fun print_saityp (x: saityp): void =
  case+ x of
  | SAITYPsome (_, s2e) =>
      (print "SAITYPsome("; print_s2exp s2e; print ")")
  | SAITYPnone _ => print "SAITYPnone()"
// end of [print_saityp]
fun print_saityplst
  (xs: saityplst): void = loop (xs, 0) where {
  fun loop (xs: saityplst, i: int): void =
    case+ xs of
    | list_cons (x, xs) => (
        if (i > 0) then print ", "; print_saityp x; loop (xs, i+1)
      ) // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [print_saityp]

(* ****** ****** *)

(*
//
// HX-2012-06-01: the function is not used anywhere
//
fn saityplst_check
  (d2v: d2var_t, xs: saityplst): int = let
  fn errmsg (d2v: d2var_t, x: saityp): void = case+ x of
    | SAITYPsome (loc, _) => begin
        $Loc.prerr_location loc;
        prerr ": the dynamic variable ["; prerr d2v;
        prerr "] is not consumed in this branch.";
        prerr_newline ()
      end // end of [SAITYPsome]
    | SAITYPnone (loc) => begin
        $Loc.prerr_location loc;
        prerr ": the dynamic variable ["; prerr d2v;
        prerr "] is consumed in this branch.";
        prerr_newline ()
      end // end of [SAITYPnone]
  fun aux (xs: saityplst, xs_some: &saityplst, xs_none: &saityplst): void =
    case+ xs of
    | list_cons (x, xs) => begin case+ x of
      | SAITYPsome _ => begin
          xs_some := list_cons (x, xs_some)
        end // end of [SAITYPsome]
      | SAITYPnone _ => begin
          xs_none := list_cons (x, xs_none)
        end // end of [SAITYPnone]
      end (* end of [list_cons] *)
    | list_nil () => ()
  var xs_some: saityplst = list_nil ()
  and xs_none: saityplst = list_nil ()
  val () = aux (xs, xs_some, xs_none)
in
  case+ (xs_some, xs_none) of
  | (list_nil _, _) => 0
  | (_, list_nil _) => 1
  | (list_cons (x1, _), list_cons (x2, _)) => let
      val loc1 = saityp_get_loc x1 and loc2 = saityp_get_loc x2
    in
      if $Loc.lte_location_location (loc1, loc2) then begin
        errmsg (d2v, x1); errmsg (d2v, x2); $Err.abort {int} ()
      end else begin
        errmsg (d2v, x2); errmsg (d2v, x1); $Err.abort {int} ()
      end // end of [if]
    end (* end of [list_cons, list_cons] *)
end // end of [saityplst_check]
*)

(* ****** ****** *)

typedef staftitem = '{
  staftitem_var= d2var_t, staftitem_lin= int, staftitem_typ= saityplst
} // end of [staftitem]

assume staftitem_t = staftitem

extern fun staftitem_set_lin
  (sai: staftitem, lin: int): void = "atsopt_state_staftitem_set_lin"
// end of [staftitem_set_lin]

extern fun staftitem_set_typ
  (sai: staftitem, typ: saityplst): void = "atsopt_state_staftitem_set_typ"
// end of [staftitem_set_typ]

(* ****** ****** *)

typedef
sascstr = '{
  sascstr_loc= loc_t
, sascstr_met= s2explstopt
, sascstr_sub= stasub_t
, sascstr_ref= ref (c3stropt)
} // end of [sascstr]

typedef sascstrlst = List sascstr

fn sascstr_make (
  loc: loc_t, met: s2explstopt, sub: stasub_t, ref: ref c3stropt
) : sascstr = '{
  sascstr_loc= loc, sascstr_met= met, sascstr_sub= sub, sascstr_ref= ref
} // end of [sascstr_make]

typedef
staftscstr (n:int) = '{
  staftscstr_met= s2explstopt
, staftscstr_res= i2nvresstate
, staftscstr_sais= staftitemlst n
, staftscstr_cstr= sascstrlst
} // end of [staftscstr]

assume staftscstr_t (n:int) = staftscstr (n)

extern
fun staftscstr_cstr_set {n:nat} (
  sac: staftscstr n, cstr: sascstrlst
) : void = "atsopt_state_staftscstr_cstr_set"
// end of [staftscstr_cstr_set]

(* ****** ****** *)

implement
staftscstr_initize
  (res, sbis) = let
  val sais =
  aux(sbis) where
  {
    fun aux {n:nat}
      (sbis: stbefitemlst n): staftitemlst n = case+ sbis of
      | list_cons (sbi, sbis) => let
          val d2v = sbi.stbefitem_var; val lin = d2var_get_lin d2v
(*
          val () = begin
            print "staftscstr_initialize: aux: d2v = "; print d2v; print_newline ();
            print "staftscstr_initialize: aux: lin = "; print lin; print_newline ();
          end // end of [val]
*)
          val sai = '{
            staftitem_var= d2v, staftitem_lin= lin, staftitem_typ= list_nil ()
          } // end of [val]
        in
          list_cons (sai, aux sbis)
        end // end of [list_cons]
      | list_nil () => list_nil ()
    // end of [aux]
  } (* end of [where] *)
in '{
  staftscstr_met= None ()
, staftscstr_res= res
, staftscstr_sais= sais
, staftscstr_cstr= list_nil ()
} end // end of [staftscstr_initialize]

//
// HX: [loc0] is the location of the branch
//
fun
staftscstr_stbefitemlst_merge_ifmetck
  {n:nat} (
  loc0: loc_t, sac: staftscstr_t n, sbis: stbefitemlst n, metck: bool
) : void = let
  fn aux (loc0: loc_t, sai: staftitem, sbi: stbefitem): void = let
    val linbef = sbi.stbefitem_lin
    val d2v = sbi.stbefitem_var
    val lincur = d2var_get_lin d2v
    val linaft = sai.staftitem_lin
(*
    val () = begin
      print "staftscstr_stbefitemlst_merge: aux: sbi.stbefitem_lin = ";
      print linbef; print_newline ();
      print "staftscstr_stbefitemlst_merge: aux: d2v = ";
      print d2v; print_newline ();
      print "staftscstr_stbefitemlst_merge: aux: d2v.d2var_lin = ";
      print lincur; print_newline ();
      print "staftscstr_stbefitemlst_merge: aux: sai.staftitem_lin = ";
      print linaft; print_newline ();

    end // end of [val]
*)
    val saityp = case+ d2var_get_typ d2v of
      | Some s2e => SAITYPsome (loc0, s2e) | None () => SAITYPnone loc0
    // end of [val]
(*
    val () = begin
      print "staftscstr_stbefitemlst_merge: aux: saityp = ";
      print_saityp saityp; print_newline ()
    end // end of [val]
*)
    val () = if lincur > linbef then begin
      staftitem_set_lin (sai, linaft + lincur - linbef)
    end // end of [val]
    val saityps = sai.staftitem_typ
(*
    val () = begin
      print "staftscstr_stbefitemlst_merge: aux: saityps = ";
      print_saityplst saityps; print_newline ()
    end // end of [val]
*)
    val () = case+ saityps of // consistency check
      | list_cons (saityp1, _) => begin case+ (saityp, saityp1) of
        | (SAITYPsome (loc, _), SAITYPnone _) => begin
            $Loc.prerr_location loc; prerr ": error(3)";
            prerr ": the dynamic variable ["; prerr d2v;
            prerr "] is expected to be consumed but it is preserved instead.";
            prerr_newline (); $Err.abort {void} ()
          end // end of [SAITYPsome, SAITYPnone]
        | (SAITYPnone loc, SAITYPsome (_, _)) => begin
            $Loc.prerr_location loc; prerr ": error(3)";
            prerr ": the dynamic variable ["; prerr d2v;
            prerr "] is expected to be preserved but it is consumed instead.";
            prerr_newline (); $Err.abort {void} ()
          end // end of [SAITYPnone, SAITYPsome]
        | (_, _) => ()
        end // end of [list_cons]
      | list_nil () => ()
    val () = staftitem_set_typ (sai, list_cons (saityp, saityps))
  in
    // empty
  end // end of [aux]
  fun auxlst {n:nat}
    (loc0: loc_t, sais: staftitemlst n, sbis: stbefitemlst n): void =
    case+ sais of
    | list_cons (sai, sais) => let
        val+ list_cons (sbi, sbis) = sbis
      in
        aux (loc0, sai, sbi); auxlst (loc0, sais, sbis)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [auxlst]
  val res = sac.staftscstr_res
  val sub = s2qua_instantiate_and_add
    (loc0, res.i2nvresstate_svs, res.i2nvresstate_gua)
  // end of [val]
  val met = (
    if metck then
      case+ res.i2nvresstate_met of
      | Some s2es => Some (s2explst_subst (sub, s2es)) | None () => None ()
    else None () // end of [if]
  ) : s2explstopt
  val r = ref_make_elt<c3stropt> (None ())
  val sascstr = sascstr_make (loc0, met, sub, r)
in
  trans3_env_add_cstr_ref (r);
  staftscstr_cstr_set (sac, list_cons (sascstr, sac.staftscstr_cstr));
  auxlst (loc0, sac.staftscstr_sais, sbis)
end // end of [staftscstr_stbefitemlst_merge_ifmetck]

implement staftscstr_stbefitemlst_merge
  (loc0, sac, sbis) = staftscstr_stbefitemlst_merge_ifmetck (loc0, sac, sbis, true)
// end of [staftscstr_stbefitemlst_merge]

implement staftscstr_stbefitemlst_merge_skipmetck
  (loc0, sac, sbis) = staftscstr_stbefitemlst_merge_ifmetck (loc0, sac, sbis, false)
// end of [staftscstr_stbefitemlst_merge_skipmetck]

(* ****** ****** *)

fun i2nvarglst_find_d2var
  (args: i2nvarglst, d2v: d2var_t): Option_vt i2nvarg = let
(*
  val () = begin
    print "i2nvarglst_find_d2var: d2v = "; print d2v; print_newline ()
  end // end of [val]
*)
in
  case+ args of
  | list_cons (arg, args) => begin
      if eq_d2var_d2var (arg.i2nvarg_var, d2v) then Some_vt arg
      else i2nvarglst_find_d2var (args, d2v)
    end // end of [list_cons]
  | list_nil () => None_vt ()
end // end [i2nvarlst_find_d2var]

(* ****** ****** *)

local

fn d2var_is_done (d2v: d2var_t): bool = begin
  case+ d2var_get_fin d2v of D2VARFINdone () => true | _ => false
end // end of [d2var_is_done]

fn aux_find (
    sub: stasub_t
  , args: i2nvarglst
  , d2v: d2var_t
  ) : Option_vt (s2expopt) = let
  val ans = i2nvarglst_find_d2var (args, d2v)
in
  case+ ans of
  | ~Some_vt arg => let
      val os2e = (case+ arg.i2nvarg_typ of
        | Some s2e => Some (s2exp_subst (sub, s2e)) | None () => None ()
      ) : s2expopt
    in
      Some_vt (os2e)
    end // end of [Some_vt]
  | ~None_vt () => None_vt ()
end // end of [aux_find]

fn aux_item_errmsg1 (loc: loc_t, d2v: d2var_t): s2exp = begin
  $Loc.prerr_location loc;
  prerr ": error(3)";
  prerr ": the dynamic variable ["; prerr d2v;
  prerr "] is expected to be consumed but it is not.";
  prerr_newline ();
  $Err.abort {s2exp} ()
end // end of [aux_item_errmsg1]

fn aux_item_errmsg2 (loc: loc_t, d2v: d2var_t): void = begin
  $Loc.prerr_location loc;
  prerr ": error(3)";
  prerr ": the dynamic variable ["; prerr d2v;
  prerr "] is expected to be preserved but it is not.";
  prerr_newline ();
  $Err.abort {void} ()
end // end of [aux_item_errmsg2]

fn aux_saityp (
  used: int // [d2v] is used
, sub: stasub_t, args: i2nvarglst, d2v: d2var_t, x: saityp
) : void = begin case+ x of
  | SAITYPsome (loc, s2e) => let
      var used1: int = used
(*
      val () = begin
        print "staftscstr_stbefitemlst_check: aux_saityp: used1 = ";      
        print used1; print_newline ();
        print "staftscstr_stbefitemlst_check: aux_saityp: d2v = ";
        print d2v; print_newline ();
        print "staftscstr_stbefitemlst_check: aux_saityp: s2e = ";
        print s2e; print_newline ()
      end // end of [val]
*)
      val s2e_check = (case+ aux_find (sub, args, d2v) of
        | ~Some_vt os2e => let
            val () = used1 := used1 + 1 in case+ os2e of
            | Some s2e => s2e | None () => aux_item_errmsg1 (loc, d2v)
          end // end of [Some_vt]
        | ~None_vt () => begin case+ d2var_get_mastyp d2v of
            | Some s2e => s2e | None () => aux_item_errmsg1 (loc, d2v)
          end // end of [None_vt]
      ) : s2exp
(*
      val () = begin
        print "staftscstr_stbefitemlst_check: aux_saityp: used1 = ";      
        print used1; print_newline ();
        print "staftscstr_stbefitemlst_check: aux_saityp: s2e_check = ";
        print s2e_check; print_newline ();
      end // end of [val]
*)
      val () = if (used1 > 0) then let
        val () = trans3_env_push_sta ()
        val () = $SOL.s2exp_tyleq_solve (loc, s2e, s2e_check)
        val knd = C3STRKINDvarfin (d2v, s2e, s2e_check)
        val () = trans3_env_pop_sta_and_add (loc, knd)
      in
        // empty
      end // end of [val]
    in
      // empty
    end // end of [SAITYPsome]
  | SAITYPnone (loc) => begin
    case+ aux_find (sub, args, d2v) of
    | ~Some_vt (os2e) => begin case+ os2e of
      | Some _ => aux_item_errmsg2 (loc, d2v) | None () => ()
      end // end of [Some_vt]
    | ~None_vt () => ()
    end // end of [SAITYPnone]
end // end of [aux_saityp]

fn aux_item_one (
    used: int // [d2v] is used
  , sub: stasub_t, res: i2nvresstate, sai: staftitem, d2v: d2var_t
  ) : void = let
(*
  val () = begin
    print "aux_item_one: d2v = "; print d2v; print_newline ()
  end // end of [val]
*)
  val xs = sai.staftitem_typ
in
  case+ xs of
  | list_cons (x, xs) => let
      val args = res.i2nvresstate_arg
      val () = staftitem_set_typ (sai, xs)
    in
      aux_saityp (used, sub, res.i2nvresstate_arg, d2v, x)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [aux_item_one]

fun
aux_item_all
  {n:nat} (
  sub: stasub_t
, res: i2nvresstate
, sais: staftitemlst n
, sbis: stbefitemlst n
) : void = begin case+ sais of
  | list_cons (sai, sais) => let
      val+ list_cons (sbi, sbis) = sbis
      val d2v = sbi.stbefitem_var
(*
      val () = begin
        print "aux_item_all: d2v = "; print d2v; print_newline ()
      end // end of [aux_item_all]
*)
      val linaft = sai.staftitem_lin
      and linbef = sbi.stbefitem_lin
      val () = begin case+ 0 of // type check
        | _ when d2var_is_done d2v => begin
            // already handled by [funarg_fin_check]
          end // end of [_ when ...]
        | _ => aux_item_one (linaft - linbef, sub, res, sai, d2v)
      end // end of [case]
    in
      aux_item_all (sub, res, sais, sbis)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [aux_item_all]

fn aux_term_check (
  met_bound: s2explstopt, x: sascstr
) : void = begin
  case+ met_bound of
  | Some s2es_bound => begin case+ x.sascstr_met of
    | Some s2es => let
        val [n:int] sgn = $Lst.list_length_compare (s2es, s2es_bound)
        val () = (
          if (sgn <> 0) then begin
            prerr_interror ();
            prerr ": aux_term_check: Some: Some"; prerr_newline ();
            $Err.abort {void} ();
            assert (sgn = 0)
          end else begin
            // [sgn==n] holds
          end // end of [if]
        ) : [n==0] void
      in
        trans3_env_add_metric_dec (x.sascstr_loc, s2es, s2es_bound)
      end // end of [Some]
    | None () => () // this means that termination checking is skipped
    end (* end of [Some] *)
  | None () => ()
end // end of [aux_term_check]

fun
aux_itemlst_all
  {n:nat} (
  met_bound: s2explstopt
, res: i2nvresstate
, sais: staftitemlst n
, sbis: stbefitemlst n
, xs: sascstrlst
) : void = begin case+ xs of
  | list_cons (x, xs) => let
      val () = trans3_env_push_sta ()
      val () = aux_term_check (met_bound, x)
      val () = aux_item_all (x.sascstr_sub, res, sais, sbis)
      val s3is = trans3_env_pop_sta ()
      val s3is = $Lst.list_vt_reverse_list s3is
      val c3t = c3str_itmlst (x.sascstr_loc, C3STRKINDmain, s3is)
      val () = !(x.sascstr_ref) := Some (c3t)
    in
      aux_itemlst_all (met_bound, res, sais, sbis, xs)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [aux_itemlst_all]

in // in of [local]

implement
staftscstr_stbefitemlst_check
  (loc0, sac, sbis) = let
(*
  val () = begin
    $Loc.print_location loc0;
    print ": staftscstr_stbefitemlst_check: res = ";
    print sac.staftscstr_res (* : i2nvresstate *);
    print_newline ();
  end // end of [val]
*)
  val met = sac.staftscstr_met
  val res = sac.staftscstr_res
  val sais = sac.staftscstr_sais
in
  aux_itemlst_all (met, res, sais, sbis, sac.staftscstr_cstr)
end // end of [staftscstr_stbefitemlst_check]

end // end of [local]

(* ****** ****** *)

local

fun aux_find (
   args: i2nvarglst, d2v: d2var_t
 ) : Option_vt (s2expopt) = let
  val ans = i2nvarglst_find_d2var (args, d2v)
in
  case+ ans of
  | ~Some_vt arg => Some_vt (arg.i2nvarg_typ)
  | ~None_vt () => None_vt ()
end // end of [aux_find]

fun
aux_iter
  {n:nat} (
  loc0: loc_t
, args: i2nvarglst
, sais: staftitemlst n
, sbis: stbefitemlst n
) : void = begin case+ sais of
  | list_cons (sai, sais) => let
      val+ list_cons (sbi, sbis) = sbis
      val d2v = sbi.stbefitem_var
      val linaft = sai.staftitem_lin and linbef = sbi.stbefitem_lin
(*
      val () = begin
        print "staftscstr_stbefitemlst_update: aux_iter: d2v = ";
        print d2v; print_newline ();
        printf (
          "staftscstr_stbefitemlst_update: aux_iter: linaft = %i and linbef = %i"
        , @(linaft, linbef)
        );
        print_newline ();
      end // end of [val]
*)
      val () = begin
        if linaft > linbef then d2var_set_lin (d2v, linaft)
      end // end of [val]
      val () = let
        val ans = aux_find (args, d2v) in
        case+ ans of
        | ~Some_vt os2e => let
            val os2e = s2expopt_opnexi_and_add (loc0, os2e)
          in
            d2var_set_typ (d2v, os2e)
          end // end of [Some_vt]
        | ~None_vt () => begin case+ 0 of
          | _ when linaft > linbef => begin
            case+ d2var_get_typ d2v of
            | Some _ => let
                val os2e = d2var_get_mastyp d2v
                val os2e = s2expopt_opnexi_and_add (loc0, os2e)
              in
                d2var_set_typ (d2v, os2e)
              end // end of [Some]
            | None _ => () // nothing to update
            end // end of [_ when ...]
          | _ => () // [d2v] is unused and no update is needed
          end // end of [None_vt]
      end // end of [val]
    in
      aux_iter (loc0, args, sais, sbis)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [aux_iter]

in // in of [local]

implement
staftscstr_stbefitemlst_update
  (loc0, sac, sbis) = let
  val res = sac.staftscstr_res and sais = sac.staftscstr_sais
  val () = trans3_env_add_svarlst res.i2nvresstate_svs
  val () = trans3_env_hypo_add_proplst (loc0, res.i2nvresstate_gua)
in
  aux_iter (loc0, res.i2nvresstate_arg, sais, sbis)
end // end of [staftscstr_stbefitemlst_update]

end // end of [local]

(* ****** ****** *)

extern typedef "staftitem_t" = staftitem

%{$

ats_void_type
atsopt_state_staftitem_set_lin
  (ats_ptr_type sai, ats_int_type lin) {
  ((staftitem_t)sai)->atslab_staftitem_lin = lin; return ;
} // end of [atsopt_state_staftitem_set_lin]

ats_void_type
atsopt_state_staftitem_set_typ
  (ats_ptr_type sai, ats_ptr_type os2es) {
  ((staftitem_t)sai)->atslab_staftitem_typ = os2es; return ;
} // end of [atsopt_state_staftitem_set_typ]

%} // end of [%{$]

extern typedef "staftscstr_t" = [n:int] staftscstr (n)

%{$

ats_void_type
atsopt_state_staftscstr_met_set
  (ats_ptr_type sac, ats_ptr_type met) {
  ((staftscstr_t)sac)->atslab_staftscstr_met = met ; return ;
} // end of [atsopt_state_staftscstr_met_set]

ats_void_type
atsopt_state_staftscstr_cstr_set
  (ats_ptr_type sac, ats_ptr_type cstr) {
  ((staftscstr_t)sac)->atslab_staftscstr_cstr = cstr ; return ;
} // end of [atsopt_state_staftscstr_cstr_set]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_trans3_env_state.dats] *)
