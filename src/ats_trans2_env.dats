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
// Time: October 2007

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload HT = "ats_hashtbl.sats"
staload Lst = "ats_list.sats"
staload NS = "ats_namespace.sats"
staload Sym = "ats_symbol.sats"
staload SymEnv = "ats_symenv.sats"

(* ****** ****** *)

staload "ats_reference.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_hashtbl.dats"
staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_symenv.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

fn prerr_loc_error2 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(2)")
// end of [prerr_loc_error2]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_trans2_env)"

(* ****** ****** *)

viewtypedef
s2rtextmap = $SymEnv.symmap_t (s2rtext)
typedef s2rtextmapref = ref s2rtextmap
typedef s2rtextmaptbl = $HT.hashtbl_t (sym_t, s2rtextmapref)

val the_s2rtextmaptbl: s2rtextmaptbl =
  $HT.hashtbl_make_hint {sym_t, s2rtextmapref} (
    lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
  )
// end of [the_s2rtextmaptbl]

(* ****** ****** *)

viewtypedef s2itemmap = $SymEnv.symmap_t (s2item)
typedef s2itemmapref = ref s2itemmap
typedef s2itemmaptbl = $HT.hashtbl_t (sym_t, s2itemmapref)

val the_s2itemmaptbl: s2itemmaptbl =
  $HT.hashtbl_make_hint {sym_t, s2itemmapref} (
    lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
  )

(* ****** ****** *)

viewtypedef
d2itemmap = $SymEnv.symmap_t (d2item)
typedef d2itemmapref = ref d2itemmap
typedef d2itemmaptbl = $HT.hashtbl_t (sym_t, d2itemmapref)

val the_d2itemmaptbl: d2itemmaptbl =
  $HT.hashtbl_make_hint {sym_t, d2itemmapref} (
  lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
) // end of [the_d2itemmaptbl]

(* ****** ****** *)

typedef d2eclsttbl = $HT.hashtbl_t (sym_t, d2eclst)

val the_d2eclsttbl: d2eclsttbl =
  $HT.hashtbl_make_hint {sym_t, d2eclst} (
  lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
) // end of [the_d2eclsttbl]

implement
d2eclst_namespace_add (id, d2cs) = let
  val ans = $HT.hashtbl_insert (the_d2eclsttbl, id, d2cs)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr_interror ();
      prerr ": d2eclst_namespace_add: id = "; $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [Some_vt]
  | ~None_vt _ => ()
end // end of [d2eclst_namespace_add]

implement
d2eclst_namespace_find (id) = 
  $HT.hashtbl_search (the_d2eclsttbl, id)
// end of [d2eclst_namespace_find]

(* ****** ****** *)

typedef s2rtenv = $SymEnv.symenv_t (s2rtext)

local

assume s2rtenv_token = unit_v
val the_s2rtenv: s2rtenv = $SymEnv.symenv_make ()

in // in of [local]

implement the_s2rtenv_add (id, s2te) = let
  val ans = $SymEnv.symenv_remove_fst (the_s2rtenv, id)
  val () = begin
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert_fst (the_s2rtenv, id, s2te)
end // end of [the_s2rtenv_add]

fn the_s2rtenv_namespace_find
  (id: sym_t): s2rtextopt_vt = let
  fn f (name: sym_t):<cloptr1> s2rtextopt_vt = let
    val r_m: s2rtextmapref =
      case+ $HT.hashtbl_search (the_s2rtextmaptbl, name) of
      | ~Some_vt m => m | ~None_vt _ => begin
          prerr_interror ();
          prerr ": s2rtenv_namespace_find: name = "; $Sym.prerr_symbol name;
          prerr_newline ();
          $Err.abort {s2rtextmapref} ()
        end // end of [None_vt]
  in
    $SymEnv.symmap_ref_search (r_m, id)
  end // end of [f]
in
//
// HX: a linear closure is created and then freed after its use:
//
  $NS.the_namespace_search (f)
end // end of [the_s2rtenv_namespace_find]

implement
the_s2rtenv_find (id) = let
  val ans =
    $SymEnv.symenv_search_all (the_s2rtenv, id)
  // end of [ans]
in
  case+ ans of
  | Some_vt _ => (fold@ ans; ans)
  | ~None_vt () => let
      val ans = the_s2rtenv_namespace_find id
    in
      case+ ans of
      | Some_vt _ => begin fold@ ans; ans end
      | ~None_vt () => begin
          $SymEnv.symenv_pervasive_search (the_s2rtenv, id)
        end // end of [None_vt]
    end // end of [None_vt]
end // end of [the_s2rtenv_find]

implement
the_s2rtenv_find_qua (q, id) = begin
  case+ q.s0rtq_node of
  | $Syn.S0RTQnone () => the_s2rtenv_find id
  | $Syn.S0RTQsym q_id => let
      val fil = case+ the_s2expenv_find q_id of
        | ~Some_vt (S2ITEMfil fil) => fil
        | ~Some_vt _ => begin
            prerr_loc_error2 q.s0rtq_loc;
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] should refer to a filename but it does not.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [Some_vt]
        | ~None_vt _ => begin
            prerr_loc_error2 q.s0rtq_loc;
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] is unrecognized.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
      val fil_sym = $Fil.filename_full_sym fil
    in
      case+ $HT.hashtbl_search (the_s2rtextmaptbl, fil_sym) of
      | ~Some_vt r_m => $SymEnv.symmap_ref_search (r_m, id)
      | ~None_vt () => begin
          prerr_interror ();
          prerr ": the loaded file [";
          $Sym.prerr_symbol fil_sym;
          prerr "] cannot be located.";
          prerr_newline ();
          $Err.abort {s2rtextopt_vt} ()
        end // end of [None_vt]
    end (* end of [S0RTQsym] *)
  | $Syn.S0RTQstr name => let
      // this feature should probably be deprecated!!!
    in
      None_vt ()
    end // end of [S0RTQstr]
end // end [the_s2rtenv_find_qua]

implement
the_s2rtenv_pop (pf | (*none*)) = begin
  let prval unit_v () = pf in $SymEnv.symenv_pop (the_s2rtenv) end
end // end of [the_s2rtenv_pop]

implement
the_s2rtenv_push () = let
  val () = $SymEnv.symenv_push (the_s2rtenv) in (unit_v | ())
end // end of [the_s2rtenv_push]

implement
the_s2rtenv_localjoin
  (pf1, pf2 | (*none*)) = let
  prval unit_v () = pf1 and unit_v () = pf2
in
  $SymEnv.symenv_localjoin (the_s2rtenv)
end // end of [the_s2rtenv_localjoin]

fn the_s2rtenv_pervasive_add_topenv (): void = let
  val m = $SymEnv.symenv_top_get (the_s2rtenv)
in
  $SymEnv.symenv_pervasive_add (the_s2rtenv, m)
end // end of [the_s2rtenv_pervasive_add_topenv]

fn the_s2rtenv_namespace_add_topenv (id: sym_t): void = let
  val m = $SymEnv.symenv_top_get the_s2rtenv
  val r_m = ref_make_elt<s2rtextmap> (m)
  val ans = $HT.hashtbl_insert (the_s2rtextmaptbl, id, r_m)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr_interror ();
      prerr ": s2rtenv_namespace_add_topenv: id = "; $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [Some_vt]
  | ~None_vt _ => ()  
end // end of [the_s2rtenv_namespace_add_topenv]

fn the_s2rtenv_save () = $SymEnv.symenv_save (the_s2rtenv)
fn the_s2rtenv_restore () = $SymEnv.symenv_restore (the_s2rtenv)

end // end of [local]

(* ****** ****** *)

typedef s2expenv = $SymEnv.symenv_t (s2item)

local

assume s2expenv_token = unit_v
val the_s2expenv: s2expenv = $SymEnv.symenv_make ()

in // in of [local]

implement
the_s2expenv_add (id, s2i) = let
  val ans = $SymEnv.symenv_remove_fst (the_s2expenv, id)
  val () = begin
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert_fst (the_s2expenv, id, s2i)
end // end of [the_s2expenv_add]

implement
the_s2expenv_add_scst (s2c) = let
(*
  val () = begin
    print "s2expenv_add_scst: s2c = "; print s2c; print_newline ()
  end
  val () = begin
    print "s2expenv_add_scst: s2c_s2t = "; print (s2cst_get_srt s2c);
    print_newline ()
  end // end of [val]
*)
  val id = s2cst_get_sym s2c
  val s2cs = (
    case+ the_s2expenv_find (id) of
    | ~Some_vt s2i => begin case+ s2i of
      | S2ITEMcst s2cs => s2cs | _ => S2CSTLSTnil ()
      end // end of [Some_vt]
    | ~None_vt () => S2CSTLSTnil ()
  ) : s2cstlst
  val ans = $SymEnv.symenv_remove_fst (the_s2expenv, id)
  val () = begin
    case+ ans of ~Some_vt s2i => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert_fst (
    the_s2expenv, id, S2ITEMcst (S2CSTLSTcons (s2c, s2cs))
  ) // end of [$SymEnv.symenv_insert_fst]
end // end of [the_s2expenv_add_scst]

implement
the_s2expenv_add_svar (s2v) = let
  val id = s2var_get_sym s2v in the_s2expenv_add (id, S2ITEMvar s2v)
end // end of [the_s2expenv_add_svar]

implement
the_s2expenv_add_svarlst (s2vs) = begin
  case+ s2vs of
  | cons (s2v, s2vs) => begin
      the_s2expenv_add_svar s2v; the_s2expenv_add_svarlst s2vs
    end // end of [cons]
  | nil () => ()
end // end of [the_s2expenv_add_svarlst]

(* ****** ****** *)

implement
the_s2expenv_add_datconptr (d2c) = let
  val sym = d2con_get_sym d2c
  val name = $Sym.symbol_name sym
  val id = $Sym.symbol_make_string (name + "_unfold")
  val () = the_s2expenv_add (id, S2ITEMdatconptr d2c)
in
  // empty
end // end of [the_s2expenv_add_datconptr]

implement
the_s2expenv_add_datcontyp (d2c) = let
  val sym = d2con_get_sym d2c
  val name = $Sym.symbol_name sym
  val id = $Sym.symbol_make_string (name + "_pstruct")
  val () = the_s2expenv_add (id, S2ITEMdatcontyp d2c)
in
  // empty
end // end of [the_s2expenv_add_datcontyp]

(* ****** ****** *)

fn the_s2expenv_namespace_find
  (id: sym_t): s2itemopt_vt = let
  fn f (name: sym_t):<cloptr1> s2itemopt_vt = let
    val r_m: s2itemmapref = begin
      case+ $HT.hashtbl_search (the_s2itemmaptbl, name) of
      | ~Some_vt m => m | ~None_vt _ => begin
          prerr_interror ();
          prerr ": the_s2expenv_namespace_find: name = "; $Sym.prerr_symbol name;
          prerr_newline ();
          $Err.abort {s2itemmapref} ()
        end // end of [None_vt]
    end // end of [val]
  in
    $SymEnv.symmap_ref_search (r_m, id)
  end // end of [f]
in
  $NS.the_namespace_search (f)
end // end of [the_s2expenv_namespace_find]

implement
the_s2expenv_find (id) = let
  val ans =
    $SymEnv.symenv_search_all (the_s2expenv, id) 
  // end of [val]
in
  case+ ans of
  | Some_vt _ => begin
      let val () = fold@ ans in ans end
    end // end of [Some]
  | ~None_vt () => let
      val ans = the_s2expenv_namespace_find id in
      case+ ans of
      | Some_vt _ => begin
          let val () = fold@ ans in ans end
        end // end of [Some_vt]
      | ~None_vt () => begin
          $SymEnv.symenv_pervasive_search (the_s2expenv, id)
        end // end of [None_vt]
    end // end of [None_vt]
end // end of [the_s2expenv_find]

implement
the_s2expenv_pervasive_find (id) = begin
  $SymEnv.symenv_pervasive_search (the_s2expenv, id)
end // end of [the_s2expenv_pervasive_find]

implement
the_s2expenv_find_qua (q, id) = begin
  case+ q.s0taq_node of
  | $Syn.S0TAQnone () => the_s2expenv_find id
  | $Syn.S0TAQsymdot (q_id) => let
      val ans = the_s2expenv_find q_id
      val fil = case+ ans of
        | ~Some_vt (S2ITEMfil fil) => fil
        | ~Some_vt _ => begin
            prerr_loc_error2 q.s0taq_loc;
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] should refer to a filename but it does not.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [Some_vt]
        | ~None_vt _ => begin
            prerr_loc_error2 q.s0taq_loc;
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] is unrecognized.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
      // end of [val]
      val fil_sym = $Fil.filename_full_sym fil
      val ans = $HT.hashtbl_search (the_s2itemmaptbl, fil_sym)
    in
      case+ ans of
      | ~Some_vt r_m => $SymEnv.symmap_ref_search (r_m, id)
      | ~None_vt () => None_vt ()
    end // end of [$Syn.S0TAQsymdot]
  | _ => None_vt ()
end // end of [the_s2expenv_find_qua]

implement
the_s2expenv_pop (pf | (*none*)) = begin
  let prval unit_v () = pf in $SymEnv.symenv_pop (the_s2expenv) end
end // end of [the_s2expenv_pop]

implement
the_s2expenv_push () = let
  val () = $SymEnv.symenv_push (the_s2expenv) in (unit_v | ())
end // end of [the_s2expenv_push]

implement
the_s2expenv_localjoin (pf1, pf2 | (*none*)) = let
  prval unit_v () = pf1 and unit_v () = pf2
in
  $SymEnv.symenv_localjoin (the_s2expenv)
end // end of [the_s2expenv_localjoin]

fn the_s2expenv_pervasive_add_topenv (): void = let
  val m = $SymEnv.symenv_top_get (the_s2expenv)
in
  $SymEnv.symenv_pervasive_add (the_s2expenv, m)
end // end of [the_s2expenv_pervasive_add_topenv]

fn the_s2expenv_namespace_add_topenv (id: sym_t): void = let
  val m = $SymEnv.symenv_top_get the_s2expenv
  val r_m = ref_make_elt<s2itemmap> (m)
  val ans = $HT.hashtbl_insert (the_s2itemmaptbl, id, r_m)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr_interror ();
      prerr ": the_s2expenv_namespace_add_topenv: id = "; $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [Some_vt]
  | ~None_vt _ => ()  
end // end of [the_s2expenv_namespace_add_topenv]

fn the_s2expenv_save () = $SymEnv.symenv_save (the_s2expenv)
fn the_s2expenv_restore () = $SymEnv.symenv_restore (the_s2expenv)

end // end of [local]

(* ****** ****** *)

local

val the_macdef: ref int = ref_make_elt<int> (0)

in // in of [local]

implement macdef_get () = !the_macdef
implement macdef_inc () = let
  val x = !the_macdef in !the_macdef := x + 1
end // end of [macdef_inc]
implement macdef_dec () = let
  val x = !the_macdef in !the_macdef := x - 1
end // end of [macdef_dec]

end // end of [local]

(* ****** ****** *)

local

val the_macro_level: ref int = ref_make_elt<int> (1)

in // in of [local]

implement
macro_level_get () = !the_macro_level

implement
macro_level_inc (loc) = let
  val level = !the_macro_level
(*
  val () = if level > 0 then begin
    print_loc_error2 loc;
    print ": the syntax `(...) is used incorrectly at this location.";
    print_newline ();
    $Err.abort {void} ()
  end // end of [val]
*)
in
  !the_macro_level := level + 1
end // end of [macro_level_inc]

implement
macro_level_dec (loc) = let
  val level = !the_macro_level
  val () = if level = 0 then begin
    prerr_loc_error2 loc;
    prerr ": the syntax ,(...) or %(...) is used incorrectly at this location.";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
in
  !the_macro_level := level - 1
end // end of [macro_level_dec]

end // end of [local]

(* ****** ****** *)

local

val the_template_level = ref_make_elt<int> (0)

in

implement
template_level_get () = !the_template_level

implement
template_level_inc () =
  !the_template_level := !the_template_level + 1
// end of [template_level_inc]

implement template_level_dec () =
  !the_template_level := !the_template_level - 1
// end of [template_level_dec]

end // end of [local]

implement
s2var_check_tmplev (loc, s2v) = let
  val s2v_tmplev = s2var_get_tmplev (s2v)
in
  case+ 0 of
  | _ when s2v_tmplev > 0 => let
      val tmplev = template_level_get ()
    in
      if s2v_tmplev < tmplev then begin
        prerr_loc_error2 loc;
        prerr ": the static variable ["; prerr s2v; prerr "] is out of scope.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [if]
    end // end of [_ when s2v_tmplev > 0]
  | _ => () // not a template variable
end // end of [s2var_tmplev_check]

implement
s2qualst_set_tmplev
  (s2vpss, tmplev) = let
  fun aux_s2vs (
    s2vs: s2varlst, tmplev: int
  ) : void = case+ s2vs of
    | cons (s2v, s2vs) => begin
        s2var_set_tmplev (s2v, tmplev); aux_s2vs (s2vs, tmplev)
      end // end of [cons]
    | nil () => ()
  fun aux_s2qualst (s2vpss: s2qualst, tmplev: int): void =
    case+ s2vpss of
    | cons (s2vps, s2vpss) => begin
        aux_s2vs (s2vps.0, tmplev); aux_s2qualst (s2vpss, tmplev)
      end // end of [cons]
    | nil () => ()
in
  aux_s2qualst (s2vpss, tmplev)
end // end of s2qualst_tmplev_set]

(* ****** ****** *)

local

assume d2var_current_level_v = unit_v
val the_d2var_current_level = ref_make_elt<int> (0)

in // in of [local]

implement
d2var_current_level_get () = !the_d2var_current_level
implement
d2var_current_level_set (n) = (!the_d2var_current_level := n)

implement
d2var_current_level_inc () = let
  val n = !the_d2var_current_level
  val () = !the_d2var_current_level := n + 1
in
  (unit_v () | ())
end // end of [d2var_current_level_inc]

implement
d2var_current_level_dec (pf | (*none*)) = let
  prval unit_v () = pf; val n = !the_d2var_current_level
in
  !the_d2var_current_level := n - 1
end // end of [d2var_current_level_dec]

end // end of [local]

(* ****** ****** *)

typedef d2expenv = $SymEnv.symenv_t (d2item)

(* ****** ****** *)

local

assume d2expenv_token = unit_v
val the_d2expenv: d2expenv = $SymEnv.symenv_make ()

in // in of [local]

implement
the_d2expenv_add (id, d2i) = let
  val ans = $SymEnv.symenv_remove_fst (the_d2expenv, id)
  val () = begin
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert_fst (the_d2expenv, id, d2i)
end // end of [the_d2expenv_add]

implement
the_d2expenv_add_dcon (d2c) = let
  val id = d2con_get_sym d2c
  val d2cs = (
    case+ the_d2expenv_find (id) of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMcon d2cs => d2cs | _ => D2CONLSTnil ()
      end // end of [Some_vt]
    | ~None_vt () => D2CONLSTnil ()
  ) : d2conlst
  val ans = $SymEnv.symenv_remove_fst (the_d2expenv, id)
  val () = begin
    case+ ans of ~Some_vt _ => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert_fst (
    the_d2expenv, id, D2ITEMcon (D2CONLSTcons (d2c, d2cs))
  ) // end of [$SymEnv.symenv_insert_fst]
end // end of [the_d2expenv_add_dcon]

implement
the_d2expenv_add_dcst (d2c) = begin
  let val id = d2cst_get_sym d2c in the_d2expenv_add (id, D2ITEMcst d2c) end
end // end of [the_d2expenv_add_dcst]

implement
the_d2expenv_add_dmac_def (d2m) = let
  val id = d2mac_get_sym d2m in the_d2expenv_add (id, D2ITEMmacdef d2m)
end // end of [the_d2expenv_add_dmac_def]

implement
the_d2expenv_add_dmac_var (d2v) = let
  val id = d2var_get_sym d2v in the_d2expenv_add (id, D2ITEMmacvar d2v)
end // end of [the_d2expenv_add_dmac_var]

implement
the_d2expenv_add_dmac_varlst (d2vs) = begin
  $Lst.list_foreach_fun (d2vs, the_d2expenv_add_dmac_var)
end // end of [the_d2expenv_add_dmac_varlst]

implement
the_d2expenv_add_dvar (d2v) = let
  val id = d2var_get_sym d2v in the_d2expenv_add (id, D2ITEMvar d2v)
end // end of [the_d2expenv_add_dvar]

implement
the_d2expenv_add_dvarlst (d2vs) = begin
  $Lst.list_foreach_fun (d2vs, the_d2expenv_add_dvar)
end // end of [the_d2expenv_add_dvarlst]

(* ****** ****** *)

fn the_d2expenv_namespace_find
  (id: sym_t): d2itemopt_vt = let
  fn f (name: sym_t):<cloptr1> d2itemopt_vt = let
    val ans = $HT.hashtbl_search (the_d2itemmaptbl, name)
    val r_m = (case+ ans of
      | ~Some_vt m => m | ~None_vt _ => begin
          prerr_interror ();
          prerr ": d2expenv_namespace_find: name = "; $Sym.prerr_symbol name;
          prerr_newline ();
          $Err.abort {d2itemmapref} ()
        end // end of [None_vt]
    ) : d2itemmapref
  in
    $SymEnv.symmap_ref_search (r_m, id)
  end // end of [f]
in
  $NS.the_namespace_search (f)
end // end of [the_d2expenv_namespace_find]

implement
the_d2expenv_find (id) = let
(*
  val () = let
    val ptr = __cast (the_d2expenv)
      where { extern castfn __cast (x: d2expenv): ptr }
    // end of [val]
  in
    print "the_d2expenv_find: ptr = "; print ptr; print_newline ()
  end // end of [val]
  val () = begin
    print "the_d2expenv_find: id = "; $Sym.print_symbol id; print_newline ()
  end // end of [val]
*)
  val ans =
    $SymEnv.symenv_search_all (the_d2expenv, id)
  // end of [val]
in
  case+ ans of
  | Some_vt _ => let
      prval () = fold@ ans in ans
    end // end of [Some_vt]
  | ~None_vt _ => let
      val ans = the_d2expenv_namespace_find id
    in
      case+ ans of
      | Some_vt _ => let
          prval () = fold@ ans in ans
        end // end of [Some]
      | ~None_vt _ => begin
          $SymEnv.symenv_pervasive_search (the_d2expenv, id)
        end // end of [None_vt]
    end // end of [None_vt]
end // end of [the_d2expenv_find]

(* ****** ****** *)

implement
the_d2expenv_current_find (id) =
  $SymEnv.symenv_search_all (the_d2expenv, id)
// end of [the_d2expenv_current_find]

implement
the_d2expenv_pervasive_find (id) = begin
  $SymEnv.symenv_pervasive_search (the_d2expenv, id)
end // end of [the_d2expenv_pervasive_find]

(* ****** ****** *)

implement
the_d2expenv_find_qua (q, id) = begin
  case+ q.d0ynq_node of
  | $Syn.D0YNQnone () => the_d2expenv_find id
  | $Syn.D0YNQsymdot (q_id) => let
      val fil = case+ the_s2expenv_find q_id of
        | ~Some_vt (S2ITEMfil fil) => fil
        | ~Some_vt _ => begin
            prerr_loc_error2 q.d0ynq_loc;
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] should refer to a filename but it does not.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [Some_vt]
        | ~None_vt _ => begin
            prerr_loc_error2 q.d0ynq_loc;
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] is unrecognized.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
      val fil_sym = $Fil.filename_full_sym fil
    in
      case+ $HT.hashtbl_search (the_d2itemmaptbl, fil_sym) of
      | ~Some_vt r_m => $SymEnv.symmap_ref_search (r_m, id)
      | ~None_vt () => None_vt ()
    end // end of [D0YNQsymdoc]
  | _ => None_vt ()
end // end of [the_d2expenv_find_qua]

(* ****** ****** *)

implement
the_d2expenv_pop (pf | (*none*)) = begin
  let prval unit_v () = pf in $SymEnv.symenv_pop (the_d2expenv) end
end // end of [the_d2expenv_pop]

implement
the_d2expenv_push () = let
  val () = $SymEnv.symenv_push (the_d2expenv) in (unit_v | ())
end // end of [the_d2expenv_push]

implement
the_d2expenv_swap (r_map) =
  $SymEnv.symenv_swap (the_d2expenv, r_map)
// end of [the_d2expenv_swap]

(* ****** ****** *)

implement
the_d2expenv_localjoin
  (pf1, pf2 | (*none*)) = let
  prval unit_v () = pf1 and unit_v () = pf2 in
  $SymEnv.symenv_localjoin (the_d2expenv)
end // end of [the_d2expenv_localjoin]

(* ****** ****** *)

fn the_d2expenv_pervasive_add_topenv (): void = let
  val m = $SymEnv.symenv_top_get (the_d2expenv) in
  $SymEnv.symenv_pervasive_add (the_d2expenv, m)
end // end of [the_d2expenv_pervasive_add_topenv]

fn the_d2expenv_namespace_add_topenv (id: sym_t): void = let
  val m = $SymEnv.symenv_top_get the_d2expenv
  val r_m = ref_make_elt<d2itemmap> (m)
  val ans = $HT.hashtbl_insert (the_d2itemmaptbl, id, r_m)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr_interror ();
      prerr ": d2expenv_namespace_add_topenv: id = "; $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [Some_vt]
  | ~None_vt _ => ()  
end // end of [the_d2expenv_namespace_add_topenv]

(* ****** ****** *)

fn the_d2expenv_save () = $SymEnv.symenv_save (the_d2expenv)
fn the_d2expenv_restore () = $SymEnv.symenv_restore (the_d2expenv)

end // end of [local]

(* ****** ****** *)

local

assume staload_level_token = unit_v
val the_staload_level = ref_make_elt<int> (0)

in // in of [local]

implement
staload_level_get_level () = !the_staload_level

implement
staload_level_push () = let
  val (vbox pf | p) = ref_get_view_ptr (the_staload_level)
  val () = !p := !p + 1
in
  (unit_v () | ())
end // end of [staload_level_inc]

implement
staload_level_pop (pf | (*none*)) = let
  prval unit_v () = pf
  val (vbox pf | p) = ref_get_view_ptr (the_staload_level)
in
  !p := !p - 1
end // end of [staload_level_dec]

end // end of [local]

(* ****** ****** *)

local

assume trans2_env_token = @(
  s2rtenv_token, s2expenv_token, d2expenv_token
) // end of [trans2_env_token]

in // in of [local]

implement
trans2_env_pop (pf | (*none*)) = let
  val () = $NS.the_namespace_pop ()
  val () = the_s2rtenv_pop (pf.0 | (*none*))
  val () = the_s2expenv_pop (pf.1 | (*none*))
  val () = the_d2expenv_pop (pf.2 | (*none*))
in
  // empty
end // end of [trans2_env_pop]

implement
trans2_env_push () = let
  val () = $NS.the_namespace_push ()
  val (pf0 | ()) = the_s2rtenv_push ()
  val (pf1 | ()) = the_s2expenv_push ()
  val (pf2 | ()) = the_d2expenv_push ()
in
  (@(pf0, pf1, pf2) | ())
end // end of [trans2_env_push]

implement
trans2_env_localjoin (pf1, pf2 | (*none*)) = let
  val () = $NS.the_namespace_localjoin ()
  val () = the_s2rtenv_localjoin (pf1.0, pf2.0 | (*none*))
  val () = the_s2expenv_localjoin (pf1.1, pf2.1 | (*none*))
  val () = the_d2expenv_localjoin (pf1.2, pf2.2 | (*none*))
in
  // empty
end // end of [trans2_env_localjoin]

end // end of [local]

(* ****** ****** *)

implement
trans2_env_save
  () = () where {
  val () = $NS.the_namespace_save ()
  val () = the_s2rtenv_save ()
  val () = the_s2expenv_save ()
  val () = the_d2expenv_save ()
} // end of [trans2_env_save]

implement
trans2_env_restore
  () = () where {
  val () = $NS.the_namespace_restore ()
  val () = the_s2rtenv_restore ()
  val () = the_s2expenv_restore ()
  val () = the_d2expenv_restore ()
} // end of [trans2_env_restore]

implement
trans2_env_pervasive_add_topenv
  () = () where {
  val () = the_s2rtenv_pervasive_add_topenv ()
  val () = the_s2expenv_pervasive_add_topenv ()
  val () = the_d2expenv_pervasive_add_topenv ()
} // end of [trans2_env_pervasive_add_topenv]

implement
trans2_env_namespace_add_topenv
  (id) = () where {
  val () = the_s2rtenv_namespace_add_topenv (id)
  val () = the_s2expenv_namespace_add_topenv (id)
  val () = the_d2expenv_namespace_add_topenv (id)
} // end of [trans2_env_namespace_add_topenv]

implement
trans2_env_initize
(
// argumentless
) = begin
  // sort environment
  the_s2rtenv_add ($Sym.symbol_ADDR, S2TEsrt s2rt_addr);
  the_s2rtenv_add ($Sym.symbol_BOOL, S2TEsrt s2rt_bool);
  the_s2rtenv_add ($Sym.symbol_CHAR, S2TEsrt s2rt_char);
  the_s2rtenv_add ($Sym.symbol_CLS, S2TEsrt s2rt_cls);
  the_s2rtenv_add ($Sym.symbol_EFF, S2TEsrt s2rt_eff);
  the_s2rtenv_add ($Sym.symbol_INT, S2TEsrt s2rt_int);
  the_s2rtenv_add ($Sym.symbol_PROP, S2TEsrt s2rt_prop);
  the_s2rtenv_add ($Sym.symbol_TYPE, S2TEsrt s2rt_type);
  the_s2rtenv_add ($Sym.symbol_T0YPE, S2TEsrt s2rt_t0ype);
  the_s2rtenv_add ($Sym.symbol_VIEW, S2TEsrt s2rt_view);
  the_s2rtenv_add ($Sym.symbol_VIEWTYPE, S2TEsrt s2rt_viewtype);
  the_s2rtenv_add ($Sym.symbol_VIEWT0YPE, S2TEsrt s2rt_viewt0ype);
  the_s2rtenv_add ($Sym.symbol_TYPES, S2TEsrt s2rt_types);
  the_s2rtenv_pervasive_add_topenv ();
  // dynamic environment
  the_d2expenv_add ($Sym.symbol_LRBRACKETS, D2ITEMsymdef nil);
  the_d2expenv_pervasive_add_topenv ()
end // end of [trans2_env_initialize]

(* ****** ****** *)

(* end of [ats_trans2_env.dats] *)
