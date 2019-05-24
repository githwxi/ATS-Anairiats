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
// Time: June 2008
//
(* ****** ****** *)

staload CS = "ats_charlst.sats"
staload Err = "ats_error.sats"
staload IntInf = "ats_intinf.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_ccomp_trans_tailcal)"

(* ****** ****** *)

fn tailjoin_name_make
  (f0: funentry_t, fs: funentrylst): string = let
  viewtypedef T = $CS.Charlst_vt
  fun aux_char (cs: &T, c: char): void = (cs := $CS.CHARLSTcons (c, cs))

  fun aux_string {n,i:nat | i <= n}
    (cs: &T, i: size_t i, s: string n): void = begin
    if string_is_atend (s, i) then () else begin
      cs := $CS.CHARLSTcons (s[i], cs); aux_string (cs, i+1, s)
    end // end of [if]
  end // end of [aux_string]

  fun aux_entry (
    cs: &T, f: funentry_t
  ) : void = let
    val name = funlab_get_name (funentry_get_lab (f))
  in
    aux_string (cs, 0, string1_of_string name)
  end // end of [aux_entry]

  fun aux_entrylst
    (cs: &T, fs: funentrylst): void = case+ fs of
    | list_cons (f, fs) => begin
        aux_char (cs, '$'); aux_entry (cs, f); aux_entrylst (cs, fs)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [aux_entrylst]

  var cs: T = $CS.CHARLSTnil ()
  val () = aux_entry (cs, f0); val () = aux_entrylst (cs, fs)
in
  $CS.string_make_charlst_rev (cs)
end // end of [tailjoin_name_make]

fn tailjoin_retyp_check // retyp: return type
  (hit0: hityp_t, fs: funentrylst): void = let
  fun aux (
      name0: string
    , fs: funentrylst
    ) : void = begin case+ fs of
    | list_cons (f, fs) => let
        val hit = tmpvar_get_typ (funentry_get_ret f)
        val HITNAM (knd, name) = hityp_t_get_name (hit)
      in
        case+ 0 of
        | _ when name0 = name => aux (name0, fs)
        | _ => begin
            $Loc.prerr_location (funentry_get_loc f);
            prerr ": error(ccomp)";
            prerr ": the return type of this function is inconsistent.";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [_]
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
  val HITNAM (knd0, name0) = hityp_t_get_name (hit0)
in
  aux (name0, fs)
end // end of [tailjoin_retyp_check]

(* ****** ****** *)

fn tailjoin_funentry_update (
    loc_all: loc_t
  , fl_all: funlab_t
  , hit_fun_all: hityp_t
  , tmp_ret_all: tmpvar_t
  , f: funentry_t
  , tag: int
  ) : @(int, funlab_t, tmpvarlst, instr) = let
//
  val fl = funentry_get_lab (f)
  val hits_arg = funlab_get_typ_arg (fl)
  val tmps_arg = funlab_get_tailjoined (fl)
  val tmp_ret = funentry_get_ret (f)
  val ins_fun = let
    val vps = $Lst.list_map_fun (tmps_arg, valprim_tmp)
    val body = funentry_get_body (f)
  in
    instr_function (loc_all, tmp_ret_all, vps, body, tmp_ret)
  end // end of [val]
//
  val vp_tag = valprim_int ($IntInf.intinf_make_int tag)
  val vps_arg = aux
    (0, hityplst_decode hits_arg) where {
    fun aux (i: int, hits: hityplst): valprimlst =
      case+ hits of
      | list_cons (hit, hits) => let
          val hit_arg = (
            case+ hit.hityp_node of
            | HITrefarg _ => hityp_ptr | _ => hit
          ) : hityp
          val vp_arg = valprim_arg (i, hityp_encode hit_arg)
        in
          list_cons (vp_arg, aux (i+1, hits))
        end // end of [list_cons]
      | list_nil () => list_nil ()
  } // end of [where]
//
  val loc_f = funentry_get_loc (f)
  val vp_fun = valprim_funclo_make (fl_all)
  val tmp_ret_new = tmpvar_make_ret (tmpvar_get_typ tmp_ret)
  val ins_call = instr_call
    (loc_f, tmp_ret_new, hit_fun_all, vp_fun, list_cons (vp_tag, vps_arg))
//
  val f_new = let
    val level = funentry_get_lev (f)
    val vtps = begin // empty
      let val () = the_vartypset_push () in the_vartypset_pop () end
    end // end of [val]
    val fls = the_funlabset_pop () where { // singleton
      val () = the_funlabset_push (); val () = the_funlabset_add (fl_all)
    } // end of [where]
    val body = '[ins_call]
  in
    funentry_make (loc_f, fl, level, fls, vtps, tmp_ret_new, body)
  end // end of [val]
(*
  val () = funentry_lablst_add (fl) // already added
*)
  val () = funentry_associate (f_new) // the previous association is discarded
in
  @(tag, fl, tmps_arg, ins_fun)
end // end of [tailjoin_funentry_update]

(* ****** ****** *)

fun tailjoin_funentrylst_update (
    loc_all: loc_t
  , fl_all: funlab_t
  , hit_fun_all: hityp_t
  , tmp_ret_all: tmpvar_t
  , inss_fun: &instrlst_vt
  , fs: funentrylst
  , tag: int
  ) : tailjoinlst = begin case+ fs of
  | list_cons (f, fs) => let
      val x = tailjoin_funentry_update
        (loc_all, fl_all, hit_fun_all, tmp_ret_all, f, tag)
      val () = inss_fun := list_vt_cons (x.3, inss_fun)
      val tjs = tailjoin_funentrylst_update
        (loc_all, fl_all, hit_fun_all, tmp_ret_all, inss_fun, fs, tag+1)
    in
      TAILJOINLSTcons (x.0, x.1, x.2, tjs)
    end // end of [list_cons]
  | list_nil () => TAILJOINLSTnil ()
end // end of [tailjoin_funentrylst_update]

(* ****** ****** *)

implement
ccomp_tailjoin_funentrylst (loc_all, fs0) = let
//
  val @(f0, fs) = (case+ fs0 of
    | list_cons (f0, fs) => @(f0, fs) | list_nil () => begin
        prerr_interror ();
        prerr ": tailjoin_funentrylst: empty funentrylst"; prerr_newline ();
        $Err.abort ()
      end // end of [list_nil]
  ) : @(funentry_t, funentrylst)
//
  val name_all = tailjoin_name_make (f0, fs)
//
  val hit0_ret = tmpvar_get_typ (funentry_get_ret (f0))
  val () = tailjoin_retyp_check (hit0_ret, fs)
//
  val tmp_ret_all = tmpvar_make_ret (hit0_ret)
//
  val fl_all = let
    val fc0 = funlab_get_funclo (funentry_get_lab f0)
    val hits_arg = '[hityp_int, hityp_vararg]
    val hit_fun = hityp_fun (fc0, hits_arg, hityp_decode hit0_ret)
  in
    funlab_make_nam_typ (name_all, hityp_encode hit_fun)
  end : funlab_t // end of [val]
//
  val vtps_all =
    aux_vtps (vtps0, fs) where {
    val vtps0 = funentry_get_vtps_all (f0)
    fun aux_vtps
      (vtps0: vartypset, fs: funentrylst): vartypset = begin
      case+ fs of
      | list_cons (f, fs) => let
          val vtps0 = vartypset_union (vtps0, funentry_get_vtps_all f)
        in
          aux_vtps (vtps0, fs)
        end // end of [list_cons]
      | list_nil () => vtps0
    end // end of [aux_vtps]
  } // end of [where]
  val () = funentry_set_vtps (f0, vtps_all)
  val () = funentry_set_vtps_flag (f0)
//
  val hit_fun_all = funlab_get_typ (fl_all)
  var inss_fun: instrlst_vt = list_vt_nil ()
  val tjs = tailjoin_funentrylst_update
    (loc_all, fl_all, hit_fun_all, tmp_ret_all, inss_fun, fs0, 0)
  val inss_fun = $Lst.list_vt_reverse_list inss_fun
  val f_all = let
    val level = funentry_get_lev (f0)
    // [fls] is set aribitrarily as [vtps_all] is already final
    val () = the_funlabset_push (); val fls(*empty*) = the_funlabset_pop ()
  in
    funentry_make (
      loc_all, fl_all, level, fls, vtps_all, tmp_ret_all, inss_fun
    ) // end of [funentry_make]
  end // end of [val]
  val () = funentry_set_vtps_flag (f_all)
  val () = funentry_set_tailjoin (f_all, tjs)
  val () = funentry_add_lablst (fl_all)
  val () = funentry_associate (f_all) // [fl_all] -> [f_all]
in
  // empty
end // end of [ccomp_tailjoin_funentrylst]

(* ****** ****** *)

local

assume tailcalist_token = unit_v

val the_tailcalist = ref_make_elt<tailcalist> (TAILCALLSTnil ())

in // in of [local]

implement
the_tailcalist_add (fl, tmps) = let
(*
  val () = begin
    print "the_tailcalist_add: fl = "; print_funlab fl; prerr_newline ()
  end // end of [val]
*)
  val (vbox pf | p) = ref_get_view_ptr (the_tailcalist)
in
  !p := TAILCALLSTcons (fl, tmps, !p)
end // end of [the_tailcalist_add]

implement
the_tailcalist_find (fl0) = let
  fun aux (fl0: funlab_t, tcs: !tailcalist)
    : Option_vt (tmpvarlst) = begin case+ tcs of
    | TAILCALLSTcons (fl, tmps, !tcs1) => let
        val ans = (
          if fl0 = fl then Some_vt (tmps) else aux (fl0, !tcs1)
        ) : Option_vt tmpvarlst
      in
        fold@ tcs; ans
      end // end of [TAILCALLSTcons]
    | TAILCALLSTmark _ => (fold@ tcs; None_vt ())
    | TAILCALLSTnil () => (fold@ tcs; None_vt ())
  end // end of [aux]
  val (vbox pf | p) = ref_get_view_ptr (the_tailcalist)
in
  $effmask_ref (aux (fl0, !p))
end // end of [the_tailcalist_find]

implement
the_tailcalist_mark () = let
  val (vbox pf | p) = ref_get_view_ptr (the_tailcalist)
in
  !p := TAILCALLSTmark (!p); (unit_v () | ())
end // end of [the_tailcalist_mark]

implement
the_tailcalist_unmark
  (pf_token | (*none*)): void = let
  prval unit_v () = pf_token
  fun aux (tcs: tailcalist): tailcalist = begin
    case+ tcs of
    | ~TAILCALLSTcons (_, _, tcs) => aux (tcs)
    | ~TAILCALLSTmark (tcs) => tcs
    | ~TAILCALLSTnil () => TAILCALLSTnil ()
  end // end of [aux]
  val (vbox pf | p) = ref_get_view_ptr (the_tailcalist)
in
  !p := $effmask_ref (aux (!p))
end // end of [the_tailcalist_unmark]

end // end of [local]

(* ****** ****** *)

#define FUNTAGNAME "arg0" // the first argument

fn emit_tailjoin_case {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m
  , tag: int
  , fl: funlab_t
  , tmps: tmpvarlst
  ) : void = let
  val () = fprintf1_exn (pf | out, "case %i:\n", @(tag))
  val () = begin
    fprint1_string (pf | out, "va_start(funarg, ");
    fprint1_string (pf | out, FUNTAGNAME);
    fprint1_string (pf | out, ") ;\n")
  end
  val () = aux (out, tmps) where {
    fun aux (out: &FILE m, tmps: tmpvarlst)
      : void = begin case+ tmps of
      | list_cons (tmp, tmps) => let
          val () = emit_valprim_tmpvar (pf | out, tmp)
          val () = fprint1_string (pf | out, " = va_arg(funarg, ")
          val () = emit_hityp (pf | out, tmpvar_get_typ tmp)
          val () = fprint1_string (pf | out, ") ;\n")
        in
          aux (out, tmps)
        end // end of [list_cons]
      | list_nil () => ()
    end // end of [aux]
  }
  val () = fprint1_string (pf | out, "va_end(funarg) ;\n")
  val () = begin
    fprint1_string (pf | out, "goto __ats_lab_");
    emit_funlab (pf | out, fl);
    fprint1_string (pf | out, " ;\n\n")
  end // end of [val]
in
  // empty
end // end of [emit_tailjoin_case]

implement
emit_tailjoinlst {m} (pf | out, tjs) = let
  val () = fprint1_string (pf | out, "va_list funarg ;\n\n")
  val () = begin
    fprint1_string (pf | out, "switch (");
    fprint1_string (pf | out, FUNTAGNAME);
    fprint1_string (pf | out, ") {\n")
  end // end of [val]
  val () = aux (out, tjs) where {
    fun aux (out: &FILE m, tjs: tailjoinlst): void = case+ tjs of
      | TAILJOINLSTcons (tag, fl, tmps, tjs) => begin
          emit_tailjoin_case (pf | out, tag, fl, tmps); aux (out, tjs)
        end // end of [TAILJOINLSTcons]
      | TAILJOINLSTnil () => ()
    // end of [aux]
  } // end of [val]
  val () = fprint1_string (
    pf | out, "default: exit(1) ; /* deadcode */\n} /* end of switch */\n\n"
  ) // end of [fprint1_string]
in
  // empty
end // end of [emit_tailjoinlst]

(* ****** ****** *)

(* end of [ats_ccomp_trans_tailcal.dats] *)
