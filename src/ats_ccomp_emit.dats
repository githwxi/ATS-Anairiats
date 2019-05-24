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
// Time: March 2008
//
(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Glo = "ats_global.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
typedef lab_t = $Lab.label_t
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

sortdef fmode = file_mode
propdef fmlte (fm1:fmode, fm2:fmode) = file_mode_lte (fm1, fm2)

(* ****** ****** *)

fn prerr_interror () =
  prerr "INTERNAL ERROR (ats_ccomp_emit)"
// end of [prerr_interror]

fn prerr_loc_errorccomp (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(ccomp)")
// end of [prerr_loc_errorccomp]

(* ****** ****** *)

%{$

ats_void_type
atsopt_emit_identifier (
  ats_ptr_type out, ats_ptr_type name
) {
  char c ;
  char *s = name ;
  while ((c = *s++)) {
    if (isalnum (c)) {
      fputc (c, (FILE*)out) ; continue ;
    }
    if (c == '_') {
/*
    fputs ("_0", (FILE*)out); continue ;
*/
      fputc ('_', (FILE*)out); continue ;
    }
    if (c == '$') {
      fputs ("_0", (FILE*)out); continue ;
    } // end of [if]
    if (c == '\'') {
      fputs ("_1", (FILE*)out); continue ;
    } // end of [if]
    if (c == '/') {
      fputs ("_2", (FILE*)out); continue ;
    } // end of [if]
    if (c == '\\') {
      fputs ("_3", (FILE*)out); continue ;
    } // end of [if]
    fputc ('_', (FILE*)out);
    fprintf ((FILE*)out, "%.2x", (unsigned char)c);
  } /* end of [while] */
  return ;
} /* atsopt_emit_identifier */

%} // end of [%{$]

(* ****** ****** *)

implement
emit_label (pf | out, l) = $Lab.fprint_label (pf | out, l)

implement
emit_labelext
  (pf | out, isext, l) = let
  val () = (
    if isext then () else fprint1_string (pf | out, "atslab_")
  ) : void // end of [val]
in
  $Lab.fprint_label (pf | out, l)
end // end of [emit_labelext]

(* ****** ****** *)

(*
//
// HX: not working properly on special chars
//
implement emit_filename (pf | out, fil) =
  emit_identifier (pf | out, $Fil.filename_full fil)
// end of [emit_filename]
*)

%{$

extern char *atsopt_ATSHOME ;
extern int atsopt_ATSHOME_length ;
extern char *atsopt_ATSHOMERELOC ;
extern ats_ptr_type atsopt_filename_full (ats_ptr_type) ;

ats_void_type
atsopt_emit_filename (ats_ptr_type out, ats_ptr_type fil) {
  int sgn ; char *name ;
  name = atsopt_filename_full (fil) ;
//
  if (!atsopt_ATSHOMERELOC) {
    atsopt_emit_identifier (out, name) ; return ;
  }
//
  sgn = strncmp
    (atsopt_ATSHOME, name, atsopt_ATSHOME_length) ;
  if (sgn) {
    atsopt_emit_identifier (out, name) ;
  } else {
    atsopt_emit_identifier (out, atsopt_ATSHOMERELOC) ;
    atsopt_emit_identifier (out, (char*)name + atsopt_ATSHOME_length) ;
  } // end of [if]
//
  return ;
} /* end of atsopt_emit_filename */

%} // end of [%{$]

(* ****** ****** *)

implement
emit_d2con
  (pf | out, d2c) = let
  val fil = d2con_get_fil (d2c)
  val sym = d2con_get_sym (d2c)
  val name = $Sym.symbol_name sym
  val () = emit_filename (pf | out, fil)
  val () = fprint1_string (pf | out, "__")
  val () = emit_identifier (pf | out, name)
  val tag = d2con_get_tag (d2c)
  val () = if
    tag >= 0 then let // HX: no exncon
    val () = fprintf1_exn (pf | out, "_%i", @(tag))
  in
    // nothing
  end // end of [val]
in
  // nothing
end // end of [emit_d2con]

implement
emit_d2cst (pf | out, d2c) = let
  val extdef = d2cst_get_extdef (d2c)
in
  case+ extdef of
  | $Syn.DCSTEXTDEFnone () => let
      val fil = d2cst_get_fil (d2c)
      val name = d2cst_get_name (d2c)
      val () = emit_filename (pf | out, fil)
      val () = fprint1_string (pf | out, "__")
      val () = emit_identifier (pf | out, name)
    in
      // nothing
    end // end of [DCSTEXTDEFnone]
  | $Syn.DCSTEXTDEFsome_ext (name) => let
      var name: string = name
      val () = if string_is_empty (name) then name := d2cst_get_name (d2c)
    in
      emit_identifier (pf | out, name)
    end // end of [DCSTEXTDEFsome_ext]
  | $Syn.DCSTEXTDEFsome_mac (name) => let
      var name: string = name
      val () = if string_is_empty (name) then name := d2cst_get_name (d2c)
    in
      emit_identifier (pf | out, name)
    end // end of [DCSTEXTDEFsome_sta]
  | $Syn.DCSTEXTDEFsome_sta (name) => let
      var name: string = name
      val () = if string_is_empty (name) then name := d2cst_get_name (d2c)
    in
      emit_identifier (pf | out, name)
    end // end of [DCSTEXTDEFsome_sta]
end // end of [emit_d2cst]

(* ****** ****** *)

fn emit_funlab_prefix{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m
) : void = let
  val prfx = $Glo.atsopt_namespace_get ()
in
  if stropt_is_some prfx then let
    val prfx = stropt_unsome prfx in fprint1_string (pf | out, prfx)
  end else begin
    // the default is the empty string
  end // end of [if]
end // end of [emit_funlab_prefix]

implement
emit_funlab (pf | out, fl) = let
  val () = (case+ funlab_get_qua fl of
    | D2CSTOPTsome d2c => let // global function
        val () = emit_d2cst (pf | out, d2c) in (*empty*)
      end // end of [D2CSTOPTsome]
    | D2CSTOPTnone () => let // local function
        val () = emit_funlab_prefix (pf | out)
        val () = emit_identifier (pf | out, funlab_get_name fl)
      in
        // empty
      end // end of [D2CSTOPTnone]
  ) : void // end of [val]
in
  if funlab_get_prfck fl > 0 then fprint1_string (pf | out, "_prfck")
end // end of [emit_funlab]

(* ****** ****** *)

implement
emit_tmplab
  (pf | out, tl) = let
  val () = fprint1_string (pf | out, "__ats_lab_")
in
  $Stamp.fprint_stamp (pf | out, tmplab_get_stamp tl)
end // end of [emit_tmplab]

implement
emit_tmplabint
  (pf | out, tl, i) = () where {
  val () = emit_tmplab (pf | out, tl)
  val () = fprintf1_exn (pf | out, "_%i", @(i))
} // end of [emit_tmplabint]

(* ****** ****** *)

implement
emit_tmpvar
  (pf | out, tmp) = let
  val knd = tmpvar_get_top (tmp)
  val () = (case+ 0 of
    | _ when knd = 1(*top(static)*) => let
        val prfx = $Glo.atsopt_namespace_get ()
        val () = if stropt_is_some prfx then let
          val prfx = stropt_unsome prfx in fprint1_string (pf | out, prfx)
        end else begin
          // there is no prefix
        end // end of [val]
      in
         fprint1_string (pf | out, "statmp") // static temporary
      end // end of [knd = 1]
    | _ => begin
        fprint1_string (pf | out, "tmp") // local temporary variable
      end // end of [_]
  ) : void // end of [val]
in
  $Stamp.fprint_stamp (pf | out, tmpvar_get_stamp tmp)
end // end of [emit_tmpvar]

(* ****** ****** *)

#define PTR_TYPE_NAME "ats_ptr_type"

(* ****** ****** *)

fn _emit_hityp{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, hit: hityp
) : void = let
  val HITNAM (knd, name) = hit.hityp_name
(*
  val () = (
    print "_emit_hityp: knd = "; print knd; print_newline ()
  ) // end of [val]
  val () = (
    print "_emit_hityp: name = "; print name; print_newline ()
  ) // end of [val]
*)
in
  case+ 0 of
  | _ when knd <= 0 => (* flt_ext: ~1; flt: 0 *)
      fprint1_string (pf | out, name)
  | _ => (* boxed: knd > 0 *)
      fprint1_string (pf | out, PTR_TYPE_NAME)
  // end of [case]
end // end of [_emit_hityp]

fn _emit_hityp_ptr{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, hit: hityp
) : void = let
  val HITNAM (knd, name) = hit.hityp_name
  val () = fprint_string (pf | out, name)
  val () = if knd = 0 then fprint1_char (pf | out, '&') // an error!
in
  // empty
end // end of [emit_hityp_ptr]

fn _emit_hityplst_sep{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, hits: hityplst, sep: string
) : void = let
  fun aux (
    out: &FILE m, i: int, hits: hityplst, sep: string
  ) : void = begin case+ hits of
    | list_cons (hit, hits) => let
        val () = if i > 0 then fprint1_string (pf | out, sep)
        val () = _emit_hityp (pf | out, hit)
      in
        aux (out, i+1, hits, sep)
      end (* end of [list_cons] *)
    | list_nil () => () // end of [list_nil]
  end // end of [aux]
in
  aux (out, 0, hits, sep)
end // end of [_emit_hityplst_sep]

(* ****** ****** *)

implement
emit_hityp (
  pf | out, hit
) = let
  val hit = hityp_decode (hit)
in
  case+ hit.hityp_node of
  | HITcltype (fl) => () where {
      val () = emit_funlab (pf | out, fl)
      val () = fprint1_string (pf | out, "_closure_type")
    } // end of [HITcltype]  
  | _ => _emit_hityp (pf | out, hit)
end // end of [emit_hityp]

implement
emit_hityp_ptr (pf | out, hit) =
  _emit_hityp_ptr (pf | out, hityp_decode (hit))
// end of [emit_hityp_ptr]

implement
emit_hityplst_sep (
  pf | out, _arg, sep
) = _emit_hityplst_sep (pf | out, hityplst_decode (_arg), sep)
// end of [emit_hityplst_sep]

(* ****** ****** *)

extern
fun emit_hityp_fun{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, _arg: hityplst_t, _res: hityp_t
) : void // end of [emit_hityp_fun]
implement
emit_hityp_fun (
  pf | out, _arg, _res
) = () where {
  val () = emit_hityp (pf | out, _res)
  val () = fprint1_string (pf | out, "(*)(")
  val () = emit_hityplst_sep (pf | out, _arg, ", ")
  val () = fprint1_string (pf | out, ")")
} // end of [emit_hityp_fun]

extern
fun emit_hityp_clofun{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, _arg: hityplst_t, _res: hityp_t
) : void // end of [emit_hityp_clofun]
implement
emit_hityp_clofun (
  pf | out, _arg, _res
) = let
  val () = emit_hityp (pf | out, _res)
  val () = fprint1_string (pf | out, "(*)(ats_clo_ptr_type")
  val () = case+ 0 of
    | _ when hityplst_is_cons _arg => let
        val () = fprint1_string (pf | out, ", ") in
        emit_hityplst_sep (pf | out, _arg, ", ")
      end // end of [_ when ...]
    | _ => () // end of [_]
  // end of [_]
  val () = fprint1_string (pf | out, ")")
in
  // empty
end // end of [emit_hityp_fun]

(* ****** ****** *)

extern
fun emit_cloenv{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, map: envmap_t, vtps: vartypset, i0: int
) : int // i0 = 0: without leading comma; i0 = 1: with leading comma

(* ****** ****** *)

local

viewtypedef valprimlstlst_vt = List_vt (valprimlst)

val the_level = ref_make_elt<int> (0)
val the_funarglst = ref_make_elt<valprimlst> (list_nil ())
val the_funarglstlst = ref_make_elt<valprimlstlst_vt> (list_vt_nil ())

in

fn funarglst_find (i: int): Option_vt (valprim) = let
  fun loop (vps: valprimlst, i: int): valprim = case+ vps of
    | list_cons (vp, vps) => if i > 0 then loop (vps, i-1) else vp
    | list_nil () => valprim_void () // deadcode
  // end of [loop]
in
  if !the_level > 0 then Some_vt (loop (!the_funarglst, i)) else None_vt ()
end // end of [funarglst_find]

fn funarglst_pop (): void = let
  val n = !the_level
  // run-time checking
  val () = if n > 0 then (!the_level := n-1) else begin
    prerr_interror (); prerr ": funarglst_pop: n = 0"; prerr_newline ();
    $Err.abort {void} ()
  end // end of [if]
  var vps0: valprimlst = list_nil ()
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_funarglstlst)
  in
    case+ !p of
    | ~list_vt_cons (vps, vpss) => begin
        !p := (vpss: valprimlstlst_vt); vps0 := vps
      end // end of [list_vt_cons]
    | list_vt_nil () => fold@ (!p)
  end // end of [val]
in
  !the_funarglst := vps0
end // end of [funarglst_pop]

fn funarglst_push (vps: valprimlst): void = let
  val n = !the_level; val () = !the_level := n + 1
in
  if n > 0 then let
    val vps0 = !the_funarglst
    val () = (!the_funarglst := vps)
    val (vbox pf | p) = ref_get_view_ptr (the_funarglstlst)
  in
    !p := list_vt_cons (vps0, !p)
  end else begin
    !the_funarglst := vps
  end // end of [if]
end // end of [funarglst_push]

end // end of [local]

(* ****** ****** *)

fn emit_valprim_arg{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, ind: int
) : void = begin
  case+ funarglst_find ind of
  | ~Some_vt vp => emit_valprim (pf | out, vp)
  | ~None_vt () => fprintf1_exn (pf | out, "arg%i", @(ind))
end (* end of [emit_valprim_arg] *)

fn emit_valprim_argref{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, ind: int, hit: hityp_t
) : void = let
  val () = fprint1_string (pf | out, "ats_ptrget_mac(");
  val () = emit_hityp (pf | out, hit)
  val () = fprint1_string (pf | out, ", ");
  val () = emit_valprim_arg (pf | out, ind)
  val () = fprint1_string (pf | out, ")")
in
  // nothing
end (* end of [emit_valprim_argref] *)

(* ****** ****** *)

fn emit_valprim_bool{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, b: bool
) : void = begin
  if b then begin
    fprint1_string (pf | out, "ats_true_bool")
  end else begin
    fprint1_string (pf | out, "ats_false_bool")
  end // end of [if]
end (* end of [emit_valprim_bool] *)

(* ****** ****** *)

fn emit_valprim_char{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, c: char
) : void = let
in
//
case+ c of
| '\'' => fprint1_string (pf | out, "'\\''")
| '\n' => fprint1_string (pf | out, "'\\n'")
| '\t' => fprint1_string (pf | out, "'\\t'")
| '\\' => fprint1_string (pf | out, "'\\\\'")
| _ when char_isprint c => fprintf1_exn (pf | out, "'%c'", @(c))
| _ => fprintf1_exn (pf | out, "'\\%.3o'", @(uint_of_char c))
//
end (* end of [emit_valprim_char] *)

(* ****** ****** *)

fn emit_tmpvar_cloptr_init{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, knd: int
, tmp_ptr: tmpvar_t, fl: funlab_t, map: envmap_t
) : void = let
  val entry = funlab_get_entry_some (fl)
  val vtps = funentry_get_vtps_all (entry)
  val () = emit_funlab (pf | out, fl)
  val () = fprint1_string (pf | out, "_closure_init (")
  val () = emit_tmpvar (pf | out, tmp_ptr)
  val _(*int*) = emit_cloenv (pf | out, map, vtps, 1)
  val () = fprint1_string (pf | out, ")")
in
  // empty
end // end of [emit_valprim_clo_init]

fn emit_valprim_clo_make{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, knd: int, fl: funlab_t, map: envmap_t
) : void = let
  val entry = funlab_get_entry_some (fl)
  val vtps = funentry_get_vtps_all (entry)
  val () = emit_funlab (pf | out, fl)
in
  case+ 0 of
  | _ when knd <> 0 => let
      val () = fprint1_string (pf | out, "_closure_make (")
      val _(*int*) = emit_cloenv (pf | out, map, vtps, 0)
      val () = fprint1_string (pf | out, ")")
    in
      // empty
    end  // end of [knd <> 0]
  | _ => let (* knd = 0: a flat closure *)
      val () = fprint1_string (pf | out, "_closure_error ()")
    in
      // empty
    end // end of [_]
end // end of [emit_valprim_clo_make]

(* ****** ****** *)

%{^
ats_void_type
atsopt_emit_valprim_float
  (ats_ptr_type out, ats_ptr_type str) {
  char *s = str ;
  if (*s == '~') { fputc ('-', (FILE*)out) ; s += 1 ; }
  fputs (s, (FILE*)out) ;
  return ;
} /* atsopt_emit_valprim_float */
%} // end of [%{^]
extern
fun emit_valprim_float{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, f: string): void
  = "atsopt_emit_valprim_float"
// end of [emit_valprim_float]

(* ****** ****** *)

fn emit_valprim_int{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, int: intinf_t
) : void = let
in
  $IntInf.fprint_intinf (pf | out, int)
end // end of [emit_valprim_int]

(* ****** ****** *)

%{^
ats_void_type
atsopt_emit_valprim_intsp
  (ats_ptr_type out, ats_ptr_type str) {
  char *s = str ;
  if (*s == '~') { fputc ('-', (FILE*)out) ; s += 1 ; }
  fputs (s, (FILE*)out) ;
  return ;
} /* atsopt_emit_valprim_intsp */
%} // end of [%{^]
extern
fun emit_valprim_intsp{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, f: string): void
  = "atsopt_emit_valprim_intsp"
// end of [emit_valprim_intsp]

(* ****** ****** *)

fn emit_valprim_ptrof{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, vp: valprim)
  : void = begin case+ vp.valprim_node of
(*
//
// HX-2011-04-12: this is embarrassingly wrong!
//
  | VParg ind => begin
      fprint1_string (pf | out, "(&");
      emit_valprim_arg (pf | out, ind);
      fprint1_string (pf | out, ")")
    end
*)
  | VPargref ind => emit_valprim_arg (pf | out, ind)
  | VPargtmpref ind => begin
      fprint1_string (pf | out, "(&");
      emit_valprim_arg (pf | out, ind);
      fprint1_string (pf | out, ")")
    end
  | VPenv vtp => let
      val ind = varindmap_find_some (vartyp_get_var vtp)
    in
      fprint1_string (pf | out, "env"); fprint1_int (pf | out, ind)
    end // end of [VPenv]
  | VPext nam => () where {
      val () = fprintf1_exn (pf | out, "(&%s)", @(nam))
    } // end of [VPextval]
  | VPtmpref tmp => let
      val () = fprint1_string (pf | out, "(&")
      val () = emit_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, ")")
    in
      // empty
    end // end of [VPtmpref]
  | _ => let
(*
      val () = prerr_interror ()
      val () = (prerr ": emit_valprim_ptrof: vp = "; prerr_valprim vp; prerr_newline ())
      val () = $Err.abort {void} ()
*)
      val () = fprint1_string (pf | out, "ptrof_error(")
      val () = emit_valprim (pf | out, vp)
      val () = fprint1_string (pf | out, ")")
    in
      // empty
    end // end of [_]
end // end of [emit_valprim_ptrof]

(* ****** ****** *)

fn emit_array_index{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, vpss: valprimlstlst
) : void = let
  fun aux (
      out: &FILE m, vpss: valprimlstlst
    ) : void = begin case+ vpss of
    | list_cons (vps, vpss) => let
        val () = fprint1_string (pf | out, "[")
        val () = emit_valprimlst (pf | out, vps)
        val () = fprint1_string (pf | out, "]")
      in
        aux (out, vpss)
      end // end of [list_cons]
    | list_nil () => () // end of [list_nil]
  end // end of [aux]
in
  aux (out, vpss)
end // end of [emit_array_index]

(* ****** ****** *)
//
// HX: this function calls another one of
// the same name defined in [ats_hiexp_util.dats]
//
fn label_is_tyarr
  (hit_rec: hityp_t, lab: lab_t) : bool = let
  val hit_rec = hityp_decode (hit_rec) in label_is_tyarr (hit_rec, lab)
end // end of [label_is_tyarr]

(* ****** ****** *)

fn emit_select_clo{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, offs: offsetlst, froot: !(&FILE m) -<cloptr1> void
) : void = let
  fun aux (
    out: &FILE m, offs: List_vt (offset), froot: !(&FILE m) -<cloptr1> void
  ) : void = case+ offs of
  | ~list_vt_cons (off, offs) => (
    case+ off of
    | OFFSETind (
        vpss_dim, hit_elt
      ) => let
        val () = fprint1_string
          (pf | out, "ats_caselind_mac(")
        val () = emit_hityp (pf | out, hit_elt)
        val () = fprint1_string (pf | out, ", ")
        val () = aux (out, offs, froot)
        val () = fprint1_string (pf | out, ", ")
        val () = emit_array_index (pf | out, vpss_dim)
        val () = fprint1_string (pf | out, ")")
      in
        // nothing
      end // end of [OFFSETind]
    | OFFSETlab (
        lab, hit_rec
      ) => let
        var isext: bool = false
        var istyarr: bool = false
//
        val () = (case+ 0 of
        | _ when hityp_t_is_tyrecbox hit_rec => let
            val istyarr = label_is_tyarr (hit_rec, lab)
            val () = fprint1_string (pf | out, "ats_selbox_mac(")
          in
            // nothing
          end // end of [_ when ...]
        | _ when hityp_t_is_tyrecsin hit_rec => let
            val () = fprint1_string (pf | out, "ats_selsin_mac(")
          in
            // nothing
          end // end of [_ when ...]
        | _ => let
            val istyarr = label_is_tyarr (hit_rec, lab)
            val () = isext := hityp_t_is_tyrecext hit_rec
            val () = fprint1_string (pf | out, "ats_select_mac(")
          in
            // nothing
          end // end of [_]
        ) : void // end of [val]
//
        val hit_rec = hityp_decode (hit_rec)
        var iscast: int = 0
        val HITNAM (knd, name) = hit_rec.hityp_name
        val () = (case+ 0 of
          | _ when knd > 0 (*ptr*) => let
              val () = iscast := 1
              val () = fprint1_string (pf | out, "ats_castptr_mac(")
              val () = fprint1_string (pf | out, name)
              val () = fprint1_string (pf | out, ", ")
            in
              // nothing
            end // end of [_ when knd > 0]
          | _ (*nonptr*) => ()  
        ) : void // end of [val]
//
        val () = aux (out, offs, froot)
//
        val () = if iscast > 0 then fprint1_string (pf | out, ")")
//
        val () = fprint1_string (pf | out, ", ")
        val () = emit_labelext (pf | out, isext, lab)
        val () = if istyarr then
          fprint1_string (pf | out, "[0]") // HX: label for flat array
        val () = fprint1_string (pf | out, ")")
      in
        // nothing
      end // end of [OFFSETlab]
    ) // end of [list_vt_cons]
    | ~list_vt_nil () => froot (out)
  val offs = $Lst.list_reverse_list_vt (offs)
in
  aux (out, offs, froot)
end // end of [emit_select_clo]

(* ****** ****** *)

fn emit_valprim_select{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, vp: valprim, offs: offsetlst
) : void = emit_select_clo {m}
  (pf | out, offs, lam (out) => emit_valprim (pf | out, vp))
// end of [emit_valprim_select]

(* ****** ****** *)

(* knd=0/1: var/ptr *)
fn emit_valprim_select_varptr{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m
, knd: int, vp_root: valprim, offs: offsetlst
) : void = let
  fn aux_fst (
    out: &FILE m, knd: int, vp_root: valprim, off: offset
  ) : void = begin case+ off of
    | OFFSETind (vpss, hit_elt) => let
        val () = fprint1_string
          (pf | out, "ats_caselptrind_mac(")
        val () = emit_hityp (pf | out, hit_elt)
        val () = fprint1_string (pf | out, ", ")
//
        val () = if knd > 0 then begin
          emit_valprim (pf | out, vp_root); // ptr
        end else begin
          emit_valprim_ptrof (pf | out, vp_root); // var
        end // end of [if]
//
        val () = fprint1_string (pf | out, ", ")
        val () = emit_array_index (pf | out, vpss)
        val () = fprint1_string (pf | out, ")")
      in
        // nothing
      end // end of [OFFSETind]
    | OFFSETlab (lab, hit_rec) => begin
      case+ 0 of
      | _ when hityp_t_is_tyrecbox (hit_rec) => let
          val isext = false
          val istyarr = label_is_tyarr (hit_rec, lab)
          val () = fprint1_string
            (pf | out, "ats_caselptrlab_mac(")
          val () = emit_hityp_ptr (pf | out, hit_rec)
          val () = fprint1_string (pf | out, ", ")
          val () = emit_valprim (pf | out, vp_root)
          val () = fprint1_string (pf | out, ", ")
          val () = emit_labelext (pf | out, isext, lab)
          val () = if istyarr then
            fprint1_string (pf | out, "[0]") // HX: label for flat array
          val () = fprint1_string (pf | out, ")")
        in
          // nothing
        end // end of [_ when ...]
      | _ when hityp_t_is_tyrecsin (hit_rec) => let
          val () = if knd > 0 then
            fprint1_string (pf | out, "ats_ptrget_mac(")
          else
            fprint1_string (pf | out, "ats_varget_mac(")
          // end of [if]
          val () = emit_hityp (pf | out, hit_rec)
          val () = fprint1_string (pf | out, ", ")
          val () = emit_valprim (pf | out, vp_root)
          val () = fprint1_string (pf | out, ")")
        in
          // nothing
        end // end of [_ when ...]
      | _ => let // HX: [hit_rec] is flat!
          val isext = hityp_t_is_tyrecext hit_rec
          val istyarr = label_is_tyarr (hit_rec, lab)
          val () = if knd > 0 then
            fprint1_string (pf | out, "ats_selptr_mac(")
          else
            fprint1_string (pf | out, "ats_select_mac(")
          // end of [if]
          val () = if knd > 0 then let
            val () = fprint1_string (pf | out, "ats_castptr_mac(")
            val () = emit_hityp (pf | out, hit_rec)
            val () = fprint1_string (pf | out, ", ")
            val () = emit_valprim (pf | out, vp_root)
            val () = fprint1_string (pf | out, ")")
          in
            // nothing
          end else let
            val () = emit_valprim (pf | out, vp_root)
          in
            // nothing
          end // end of [if]
          val () = fprint1_string (pf | out, ", ")
          val () = emit_labelext (pf | out, isext, lab)
          val () = if istyarr then
            fprint1_string (pf | out, "[0]") // HX: label for flat array
          val () = fprint1_string (pf | out, ")")
        in
          // nothing
        end // end of [_]
    end // end [OFFSETlab]
  end // end of [aux_fst]
in
  case+ offs of
  | list_cons (off_fst, offs_rst) => let
      val () = emit_select_clo {m}
        (pf | out, offs_rst, lam (out) => aux_fst (out, knd, vp_root, off_fst))
      // end of [val]
    in
      // empty
    end // end of [list_cons]
  | list_nil () => let
      val () = prerr_interror ()
      val () = (
        prerr ": emit_valprim_select_varptr: vp_root = "; prerr vp_root; prerr_newline ()
      ) // end of [val]
    in
      $Err.abort {void} ()
    end // end of [list_nil]
end // end of [emit_valprim_select_varptr]

(* ****** ****** *)

fn emit_valprim_select_var{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, vp_root: valprim, offs: offsetlst
) : void = begin
  emit_valprim_select_varptr (pf | out, 0(*var*), vp_root, offs)
end // end of [emit_valprim_select_var]

fn emit_valprim_select_ptr{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, vp_root: valprim, offs: offsetlst
) : void = begin
  emit_valprim_select_varptr (pf | out, 1(*ptr*), vp_root, offs)
end // end of [emit_valprim_select_ptr]

(* ****** ****** *)

%{$

ats_void_type
atsopt_emit_valprim_string (
  ats_ptr_type out, ats_ptr_type str, ats_size_type len
) {
  char *s = str; int i; char c;
//
  fputs ("ATSstrcst(\"", (FILE*)out);
//
  for (i = 0; i < len; i += 1, s += 1) {
    c = *s;
    switch (c) {
    case '"': fprintf ((FILE*)out, "\\\""); break;
    case '\n': fprintf ((FILE*)out, "\\n"); break;
    case '\t': fprintf ((FILE*)out, "\\t"); break;
    case '\\': fprintf ((FILE*)out, "\\\\"); break;
    default:
      if (isprint(c)) {
        fputc (c, (FILE*)out) ;
      } else {
        fprintf ((FILE*)out, "\\%.3o", (unsigned char)c);
      }
    } // end of [switch]
  } // end of [for]
//
  fputs ("\")", (FILE*)out);
//
  return ;
} // end of [atsopt_emit_valprim_string]

%} // end of [%{$]

extern
fun emit_valprim_string{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, str: string, len: size_t): void
  = "atsopt_emit_valprim_string"
// end of [emit_valprim_string]

(* ****** ****** *)

implement
emit_valprim_tmpvar
  (pf | out, tmp) = emit_tmpvar (pf | out, tmp)
// end of [emit_valprim_tmpvar]

(* ****** ****** *)

implement
emit_valprim
  {m} (pf | out, vp0) = begin
  case+ vp0.valprim_node of
  | VParg ind => emit_valprim_arg (pf | out, ind)
  | VPargref ind => begin
      emit_valprim_argref (pf | out, ind, vp0.valprim_typ)
    end // end of [VPargref]
  | VPargtmpref ind => emit_valprim_arg (pf | out, ind)
  | VPbool b => emit_valprim_bool (pf | out, b)
  | VPcastfn (_d2c, vp_arg) => let
      val () = fprint1_string
        (pf | out, "ats_castfn_mac(")
      val () = emit_hityp (pf | out, vp0.valprim_typ)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_arg)
      val () = fprint1_string (pf | out, ")")
    in
      // nothing
    end // end of [VPcast]
  | VPchar c => emit_valprim_char (pf | out, c)
  | VPclo (knd, fl, env) =>
      emit_valprim_clo_make (pf | out, knd, fl, env)
  | VPcst d2c => begin case+ 0 of
    | _ when d2cst_is_fun d2c => let
        val () = fprint1_char (pf | out, '&')
      in
        emit_d2cst (pf | out, d2c) // HX: is '&' mandatory?
      end // end of [_ when ...]
    | _ => emit_d2cst (pf | out, d2c)
    end // end of [VPcst]
  | VPcstsp (loc, cst) => begin case+ cst of
    | $Syn.CSTSPfilename () => let
        val fil = $Loc.location_get_filename (loc)
        val name = $Fil.filename_full fil; val len = string_length (name)
      in
        emit_valprim_string (pf | out, name, len)
      end (* end of [CSTSPfilename] *)
    | $Syn.CSTSPlocation () => let
        val () = fprint1_string (pf | out, "\"")
        val () = $Loc.fprint_location (pf | out, loc) 
        val () = fprint1_string (pf | out, "\"")
      in
        // nothing
      end (* end of [CSTSPlocation] *)
    end // end of [VPcstsp]
  | VPenv vtp => let
      val d2v = vartyp_get_var vtp
      val ind = varindmap_find_some (d2v)
    in
      case+ 0 of
      | _ when d2var_is_mutable d2v => let
          val () = fprint1_string
            (pf | out, "ats_ptrget_mac(")
          val () = emit_hityp (pf | out, vartyp_get_typ vtp)
          val () = fprint1_string (pf | out, ", ")
          val () = fprintf1_exn (pf | out, "env%i", @(ind))
          val () = fprint1_string (pf | out, ")")
        in
          // nothing
        end // end of [_ when ...]
      | _ => fprintf1_exn (pf | out, "env%i", @(ind))
    end // end of [VPenv]
  | VPext code => fprint1_string (pf | out, code)
  | VPfix (vpr) => emit_valprim (pf | out, !vpr)
  | VPfloat str => emit_valprim_float (pf | out, str)
  | VPfloatsp str => emit_valprim_float (pf | out, str)
  | VPfun fl => begin
      fprint1_string (pf | out, "&"); emit_funlab (pf | out, fl)
    end // end of [VPfun]
  | VPint (int) =>
      $IntInf.fprint_intinf (pf | out, int)
  | VPintsp (str, _(*int*)) => emit_valprim_intsp (pf | out, str)
  | VPptrof vp => emit_valprim_ptrof (pf | out, vp)
  | VPptrof_ptr_offs (vp, offs) => begin
      fprint1_char (pf | out, '&');
      emit_valprim_select_ptr (pf | out, vp, offs)
    end // end of [VPptrof_ptr_offs]
  | VPptrof_var_offs (vp, offs) => begin
      fprint1_char (pf | out, '&');
      emit_valprim_select_var (pf | out, vp, offs)
    end // end of [VPptrof_var_offs]
  | VPsizeof hit => let
      val () = fprint1_string (pf | out, "sizeof(")
      val () = emit_hityp (pf | out, hit)
      val () = fprint1_string (pf | out, ")")
    in
      // empty
    end // end of [VPsizeof]
  | VPstring (str, len) => let
      val len = int1_of_int len; val () = assert (len >= 0)
    in
      emit_valprim_string (pf | out, str, size1_of_int1 len)
    end // end of [VPstring]
  | VPtmp tmp => emit_valprim_tmpvar (pf | out, tmp)
  | VPtmpref tmp => emit_valprim_tmpvar (pf | out, tmp)
  | VPtop () => fprint1_string (pf | out, "?top") // for debugging
  | VPvoid () => fprint1_string (pf | out, "?void") // for debugging
(*
  | _ => begin
      prerr_interror ();
      prerr ": emit_valprim: vp0 = "; prerr vp0; prerr_newline ();
      $Err.abort {void} ()
    end // end of [_]
*)
end // end of [emit_valprim]

implement
emit_valprimlst {m} (pf | out, vps) = let
  fun aux
    (out: &FILE m, i: int, vps: valprimlst): void = begin
    case+ vps of
    | list_cons (vp, vps) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        emit_valprim (pf | out, vp); aux (out, i+1, vps)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
in
  aux (out, 0, vps)
end // end of [emit_valprimlst]    

(* ****** ****** *)

implement
emit_kont
  (pf | out, kont) = case+ kont of
  | KONTtmplab tl => begin
      fprint1_string (pf | out, "goto "); emit_tmplab (pf | out, tl)
    end // end of [KONTtmplab]
  | KONTtmplabint (tl, i) => begin
      fprint1_string (pf | out, "goto "); emit_tmplabint (pf | out, tl, i)
    end // end of [KONTtmplabint]
  | KONTcaseof_fail (loc) => () where {
      val () = fprint1_string (pf | out, "ats_caseof_failure_handle (\"")
      val () = $Loc.fprint_location (pf | out, loc)
      val () = fprint1_string (pf | out, "\")")
    } // end of [KONTcaseof_fail]
  | KONTfunarg_fail (loc, fl) => () where {
      val () = fprint1_string (pf | out, "ats_funarg_failure_handle (\"")
      val () = $Loc.fprint_location (pf | out, loc)
      val () = fprint1_string (pf | out, "\")")
    } // end of [KONTfunarg_fail]
  | KONTraise vp_exn => () where {
      val () = fprint1_string (pf | out, "ats_raise_exn (")
      val () = emit_valprim (pf | out, vp_exn)
      val () = fprint1_string (pf | out, ")")
    } // end of [KONTraise]
  | KONTmatpnt mpt => emit_matpnt (pf | out, mpt)
  | KONTnone () => begin
      fprint1_string (pf | out, "ats_deadcode_failure_handle ()")
    end // end of [KONTnone]
(* end of [emit_kont] *)

(* ****** ****** *)

extern
fun emit_patck{m:fmode}
(
  pf: fmlte (m, w) | out: &FILE m, vp: valprim, patck: patck, fail: kont
) : void // end of [emit_patck]

implement
emit_patck (
  pf | out, vp, patck, fail
) = begin
  case+ patck of
  | PATCKbool b => begin
      fprint1_string (pf | out, "if (");
      if b then fprint1_char (pf | out, '!');
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint1_string (pf | out, " ; }")
    end // end of [PATCKbool]
  | PATCKchar c => begin
      fprint1_string (pf | out, "if (");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " != ");
      emit_valprim_char (pf | out, c);
      fprint1_string (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint1_string (pf | out, " ; }")
    end // end of [PATCKchar]
  | PATCKcon d2c => let
      val s2c = d2con_get_scst (d2c)
    in
      case+ s2c of
      | _ when s2cst_is_singular (s2c) => ()
      | _ when s2cst_is_listlike (s2c) => let
          val isnil = (
            case+ s2cst_get_islst (s2c) of
            | Some x(*nil,cons*) => eq_d2con_d2con (d2c, x.0)
            | None () => false (* deadcode *)
          ) : bool
          val iscons = not (isnil)
        in
          fprint1_string (pf | out, "if (");
          emit_valprim (pf | out, vp);
          if isnil then fprint1_string (pf | out, " != ");
          if iscons then fprint1_string (pf | out, " == ");
          fprint1_string (pf | out, "(ats_sum_ptr_type)0) { ");
          emit_kont (pf | out, fail);
          fprint1_string (pf | out, " ; }")
        end // end of [s2cst_is_listlike]
      | _ => begin
          fprint1_string (pf | out, "if (((ats_sum_ptr_type)");
          emit_valprim (pf | out, vp);
          fprint1_string (pf | out, ")->tag != ");
          fprint1_int (pf | out, d2con_get_tag d2c);
          fprint1_string (pf | out, ") { ");
          emit_kont (pf | out, fail);
          fprint1_string (pf | out, " ; }")
        end
    end // end of [PATCKcon]
  | PATCKexn d2c => let
      val arity = d2con_get_arity_real (d2c)
    in
      case+ arity of
      | _ when arity = 0 => begin
          fprint1_string (pf | out, "if (");
          emit_valprim (pf | out, vp);
          fprint1_string (pf | out, " != &");
          emit_d2con (pf | out, d2c);
          fprint1_string (pf | out, ") { ");
          emit_kont (pf | out, fail);
          fprint1_string (pf | out, " ; }")
        end
      | _ => begin
          fprint1_string (pf | out, "if (((ats_exn_ptr_type)");
          emit_valprim (pf | out, vp);
          fprint1_string (pf | out, ")->tag != ");
          emit_d2con (pf | out, d2c);
          fprint1_string (pf | out, ".tag) { ");
          emit_kont (pf | out, fail);
          fprint1_string (pf | out, " ; }")
        end
    end // end of [PATCKexn]
  | PATCKfloat (f) => begin
      fprint1_string (pf | out, "if (");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " != ");
      emit_valprim_float (pf | out, f);
      fprint1_string (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint1_string (pf | out, " ; }")
    end // end of [PATCKfloat]
  | PATCKint int => begin
      fprint1_string (pf | out, "if (");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " != ");
      emit_valprim_int (pf | out, int);
      fprint1_string (pf | out, ") { ");
      emit_kont (pf | out, fail);
      fprint1_string (pf | out, " ; }")
    end // end of [PATCKint]
  | PATCKstring str => begin
      fprint1_string (pf | out, "if (__strcmpats(");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, ", ");
      emit_valprim_string (pf | out, str, string0_length str);
      fprint1_string (pf | out, ")) { ");
      emit_kont (pf | out, fail);
      fprint1_string (pf | out, " ; }")
    end // end of [PATCKstr]
(*
  | _ => begin
      prerr_interror ();
      prerr ": emit_patck: not implemented yet"; prerr_newline ();
      $Err.abort {void} ()
    end // end of [_]
*)
end (* end of [emit_patck] *)

(* ****** ****** *)

extern
fun emit_branch{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, br: branch): void
// end of [emit_branch]

implement
emit_branch
  (pf | out, br) = let
  val inss = br.branch_inss
  val () = fprint1_string (pf | out, "/* branch: ")
  val () = emit_tmplab (pf | out, br.branch_lab)
  val () = fprint1_string (pf | out, " */")
  val () = begin case+ inss of
    | list_cons _ => fprint1_char (pf | out, '\n') | list_nil () => ()
  end // end of [val]
in
  emit_instrlst (pf | out, inss); fprint1_string (pf | out, "\nbreak ;\n")
end // end of [emit_branch]

extern
fun emit_branchlst{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, brs: branchlst): void
implement
emit_branchlst {m} (pf | out, brs) = let
  fun aux (
    out: &FILE m, i: int, brs: branchlst
  ) : void =
    case+ brs of
    | list_cons (br, brs) => let
        val () = if i > 0 then fprint1_char (pf | out, '\n')
      in
        emit_branch (pf | out, br); aux (out, i+1, brs)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [aux]
in
  aux (out, 0, brs)
end // end of [emit_branchlst]

(* ****** ****** *)

implement
emit_cloenv {m} (
  pf | out, map, vtps, i0
) : int = let
//
  fn aux_envmap (
      out: &FILE m
    , map: envmap_t, d2v: d2var_t
    ) : void = begin
    case+ envmap_find (map, d2v) of
    | ~Some_vt vp => begin case+ 0 of
       | _ when d2var_is_mutable d2v =>
           emit_valprim_ptrof (pf | out, vp)
         // end of [_ when ...]
       | _ => emit_valprim (pf | out, vp)
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr_interror ();
        prerr ": emit_cloenv: None_vt: d2v = "; prerr d2v; prerr_newline ();
        $Err.abort {void} ()
      end // end of [None_vt]
  end // end of [envmap]
//
  fun aux_main (
      out: &FILE m
    , map: envmap_t
    , i: int
    , d2vs: d2varlst_vt
    , err: &int
    ) :<cloptr1> int = begin
    case+ d2vs of
    | ~list_vt_cons (d2v, d2vs) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = case+ varindmap_find (d2v) of
          | ~Some_vt ind => fprintf1_exn (pf | out, "env%i", @(ind))
          | ~None_vt () => aux_envmap (out, map, d2v)
        // end of [val]
      in
        aux_main (out, map, i+1, d2vs, err)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => i
  end // end of [aux_main]
//
  val d2vs = vartypset_d2varlst_make (vtps)
  var err: int = 0
  val n = aux_main (out, map, i0, d2vs, err)
  val () = if err > 0 then $Err.abort {void} ()
//
in
  n - i0 // the number of variables in the closure environment
end // end of [emit_cloenv]

(* ****** ****** *)

fun
emit_move_con
  {m:fmode} (
  pf: fmlte (m, w)
| out: &FILE m
, tmp: tmpvar_t
, hit_sum: hityp_t
, d2c: d2con_t
, vps: valprimlst
) : void = let
in
//
case+ vps of
| list_cons _ => let
    val () = emit_valprim_tmpvar (pf | out, tmp)
    val () = fprint1_string (pf | out, " = ATS_MALLOC(sizeof(")
    val () = emit_hityp_ptr (pf | out, hit_sum)
    val () = fprint1_string (pf | out, ")) ;")
    val () = (
      case+ 0 of
      | _ when d2con_is_exn (d2c) => begin
          fprint1_char (pf | out, '\n');
          fprint1_string (pf | out, "((ats_exn_ptr_type)");
          emit_valprim_tmpvar (pf | out, tmp);
          fprint1_string (pf | out, ")->tag = ");
          emit_d2con (pf | out, d2c);
          fprint1_string (pf | out, ".tag ;\n");
          fprint1_string (pf | out, "((ats_exn_ptr_type)");
          emit_valprim_tmpvar (pf | out, tmp);
          fprint1_string (pf | out, ")->name = ");
          emit_d2con (pf | out, d2c);
          fprint1_string (pf | out, ".name ;")
        end // end of [_ when ...]
      | _ => let
          val s2c = d2con_get_scst (d2c)
        in
          case+ 0 of
          | _ when s2cst_is_singular s2c => ()
          | _ when s2cst_is_listlike s2c => ()
          | _ => begin
              fprint1_char (pf | out, '\n');
              fprint1_string (pf | out, "((ats_sum_ptr_type)");
              emit_valprim_tmpvar (pf | out, tmp);
              fprint1_string (pf | out, ")->tag = ");
              fprint1_int (pf | out, d2con_get_tag d2c);
              fprint1_string (pf | out, " ;")
            end
        end // end of [_]
    ) : void // end of [val]
    val () = aux_arg (out, 0, vps) where {
      fun aux_arg (
        out: &FILE m
      , i: int, vps: valprimlst
      ) :<cloptr1> void = begin case+ vps of
        | list_cons (vp, vps) => let
            val () = (
              case+ vp.valprim_node of
              | VPtop () => ()
              | _ => () where {
//
                  val () = fprint1_char (pf | out, '\n')
//
                  val () = fprint1_string
                    (pf | out, "ats_selptrset_mac(")
                  val () = emit_hityp_ptr (pf | out, hit_sum)
                  val () = fprint1_string (pf | out, ", ")
                  val () = emit_valprim_tmpvar (pf | out, tmp)
                  val () = fprint1_string (pf | out, ", ")
                  val () = fprintf1_exn (pf | out, "atslab_%i", @(i))
                  val () = fprint1_string (pf | out, ", ")
                  val () = emit_valprim (pf | out, vp)
                  val () = fprint1_string (pf | out, ") ;")
                } // end of [_]
            ) : void // end of [val]
          in
            aux_arg (out, i+1, vps)
          end // end of [list_cons]
        | list_nil () => ()
      end // end of [aux_arg]
    } // end of [where]
  in
    // empty
  end // end of [list_cons]
| list_nil () => let
    val s2c = d2con_get_scst (d2c) in
    case+ 0 of
    | _ when s2cst_is_listlike s2c => begin
        emit_valprim_tmpvar (pf | out, tmp);
        fprint1_string (pf | out, " = (ats_sum_ptr_type)0 ;");
      end // end of [_ when ...]
    | _ => begin
        emit_valprim_tmpvar (pf | out, tmp);
        fprint1_string (pf | out, " = (ats_sum_ptr_type)(&");
        emit_d2con (pf | out, d2c);
        fprint1_string (pf | out, ") ;")
      end // end of [_]
  end // end of [list_nil]
//
end // end of [emit_move_con]

(* ****** ****** *)

fn emit_instr_assgn_arr{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, tmp_arr: tmpvar_t
, vp_asz: valprim, tmp_elt: tmpvar_t, vp_tsz: valprim
) : void = let
  val () = fprint1_string
    (pf | out, "/* array initialization */\n")
  val () = fprint1_string
    (pf | out, "atspre_array_ptr_initialize_elt_tsz (")
  val () = emit_tmpvar (pf | out, tmp_arr)
  val () = fprint1_string (pf | out, ", ")
  val () = emit_valprim (pf | out, vp_asz)
  val () = fprint1_string (pf | out, ", ")
  val () = fprint1_string (pf | out, "&")
  val () = emit_tmpvar (pf | out, tmp_elt)
  val () = fprint1_string (pf | out, ", ")
  val () = emit_valprim (pf | out, vp_tsz)
  val () = fprint1_string (pf | out, ") ;")
in
  // empty
end // end of [emit_instr_assgn_arr]

(* ****** ****** *)

(*
//
// HX: This definition should not be changed!!!
//
viewtypedef
arrayptrsize_viewt0ype_int_viewt0ype (a: viewt@ype, n:int) =
  [l:addr | l <> null] (free_gc_v (a, n, l), @[a][n] @ l | ptr l, int n)
// end of [arrayptrsize_viewt0ype_int_viewt0ype]
*)

fn emit_instr_arr_heap{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, tmp: tmpvar_t, asz: int, hit_elt: hityp_t
) : void = let
  val () = fprint1_string
    (pf | out, "/* array allocation on heap */\n")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = fprint1_string
    (pf | out, ".atslab_2 = atspre_array_ptr_alloc_tsz (")
  val () = fprint1_int (pf | out, asz)
  val () = fprint1_string (pf | out, ", sizeof(")
  val () = emit_hityp (pf | out, hit_elt)
  val () = fprint1_string (pf | out, ")) ;\n")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = fprint1_string (pf | out, ".atslab_3 = ")
  val () = fprint1_int (pf | out, asz)
  val () = fprint1_string (pf | out, " ;\n")
in
  // empty
end // end of [emit_instr_arr_heap]

(* ****** ****** *)

fn emit_instr_arr_stack{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, tmp: tmpvar_t
, level: int, vp_asz: valprim, hit_elt: hityp_t
) : void = let
  val () = fprint1_string
    (pf | out, "/* array allocation on stack */\n")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = case+ 0 of
    | _ when level > 0 => fprint1_string (pf | out, " = ATS_ALLOCA2(")
    | _ (* level = 0 *) => fprint1_string (pf | out, " = ATS_MALLOC2(")
  // end of [val]
  val () = emit_valprim (pf | out, vp_asz)
  val () = fprint1_string (pf | out, ", sizeof(")
  val () = emit_hityp (pf | out, hit_elt)
  val () = fprint1_string (pf | out, ")) ;")
in
  // empty
end // end of [emit_instr_arr_stack]

(* ****** ****** *)

fn d2cst_fun_is_void
  (d2c: d2cst_t): bool = begin
  hityp_t_fun_is_void (d2cst_get_hityp_some d2c)
end // end of [d2cst_fun_is_void]

fn funlab_fun_is_void
  (fl: funlab_t): bool = begin
  hityp_t_is_void (funlab_get_typ_res fl)
end // end of [funlab_fun_is_void]

fun emit_instr_call{m:fmode}
(
  pf: fmlte (m, w)
| out: &FILE m, tmp: tmpvar_t
, hit_fun: hityp_t, vp_fun: valprim, vps_arg: valprimlst
) : void = let
(*
  val () = (
    print "emit_instr_call: vp_fun = "; print_valprim vp_fun; print_newline ()
  ) // end of [val]
*)
  val noret = (
    case+ vp_fun.valprim_node of
    | VPcst d2c => d2cst_fun_is_void (d2c)
    | VPclo (_(*knd*), fl, _(*env*)) => funlab_fun_is_void (fl)
    | VPfun fl => funlab_fun_is_void (fl)
    | _ => hityp_t_fun_is_void hit_fun
  ) : bool
  val () = if noret then fprint1_string (pf | out, "/* ")
  val () = emit_valprim_tmpvar (pf | out, tmp)
  val () = fprint1_string (pf | out, " = ");
  val () = if noret then fprint1_string (pf | out, "*/ ")
in
//
case+ vp_fun.valprim_node of
//
| VPcst (d2c)
    when d2cst_is_fun (d2c) => let
    val () = emit_d2cst (pf | out, d2c)
    val () = fprint1_string (pf | out, " (")
    val () = emit_valprimlst (pf | out, vps_arg)
    val () = fprint1_string (pf | out, ") ;")
  in
    // empty
  end // end of [VPcst]
//
| VPclo (knd, fl, envmap) => let
    val entry = funlab_get_entry_some (fl)
    val vtps = funentry_get_vtps_all (entry)
    val () = emit_funlab (pf | out, fl)
    val () = fprint1_string (pf | out, " (")
    val n = emit_cloenv (pf | out, envmap, vtps, 0)
    val () = if n > 0 then begin case+ vps_arg of
      | list_cons _ => fprint1_string (pf | out, ", ") | _ => ()
    end // end of [val]
    val () = emit_valprimlst (pf | out, vps_arg)
    val () = fprint1_string (pf | out, ") ;")
  in
    // empty
  end // end of [VPclo]
//
| VPfun fl => let
    val () = emit_funlab (pf | out, fl)
    val () = fprint1_string (pf | out, " (")
    val () = emit_valprimlst (pf | out, vps_arg)
    val () = fprint1_string (pf | out, ") ;")
  in
    // empty
  end // end of [VPfun]
//
| VPfix (vpr) => emit_instr_call (
    pf | out, tmp, hit_fun, !vpr, vps_arg
  ) // end of [VPfix]
//
| _ (*function variable*) => let
    val hit_fun = hityp_decode (hit_fun)
  in
    case+ hit_fun.hityp_node of
    | HITfun (fc, hits_arg, hit_res) => begin
      case+ fc of
      | $Syn.FUNCLOclo _(*knd*) => let
          val hits_arg = hityplst_encode hits_arg
          val hit_res = hityp_encode hit_res
          val () = fprint1_string (pf | out, "((")
          val () = emit_hityp_clofun (pf | out, hits_arg, hit_res)
          val () = fprint1_string (pf | out, ")(ats_closure_fun(")
          val () = emit_valprim (pf | out, vp_fun)
          val () = fprint1_string (pf | out, "))) (")
          val () = emit_valprim (pf | out, vp_fun)
          val () = if $Lst.list_is_cons (vps_arg) then fprint1_string (pf | out, ", ")
          val () = emit_valprimlst (pf | out, vps_arg)
          val () = fprint1_string (pf | out, ") ;")
        in
          // nothing
        end // end of [FUNCLOclo]
      | $Syn.FUNCLOfun () => let
          val hits_arg = hityplst_encode hits_arg
          val hit_res = hityp_encode hit_res
          val () = fprint1_string (pf | out, "((")
          val () = emit_hityp_fun (pf | out, hits_arg, hit_res)
          val () = fprint1_string (pf | out, ")")
          val () = emit_valprim (pf | out, vp_fun)
          val () = fprint1_string (pf | out, ") (")
          val () = emit_valprimlst (pf | out, vps_arg)
          val () = fprint1_string (pf | out, ") ;")
        in
          // nothing
        end // end of [FUNCLOfun]
      end // end of [HITfun]
    | _ => begin
        prerr_interror ();
        prerr ": emit_instr_call: hit_fun = "; prerr_hityp hit_fun; prerr_newline ();
        $Err.abort {void} ()
      end // end of [_]
    // end of [case]
  end (* end of [_(*function variable*)] *)
// end of [case]
end // end of [emit_instr_call]

(* ****** ****** *)

implement
emit_instr {m}
  (pf | out, ins) = let
//
// generating #line progma for debugging
//
  val gline = $Deb.gline_flag_get ()
  val () = if gline > 0 then (
    $Loc.fprint_line_pragma (pf | out, ins.instr_loc)
  ) // end of [if]
  // end of [val]
//
  val ndeb = $Deb.debug_flag_get ()
  val () = // generating informaion for debugging
    if ndeb > 0 then let
      val () = fprint1_string (pf | out, "/* ")
      val () = fprint_instr (pf | out, ins)
      val () = fprint1_string (pf | out, " */")
      val () = fprint1_char (pf | out, '\n')
    in
      // empty
    end // end of [if]
  // end of [val]
in
  case+ ins.instr_node of
  | INSTRarr_heap (tmp, asz, hit_elt) => begin
      emit_instr_arr_heap (pf | out, tmp, asz, hit_elt)
    end // end of [INSTRarr_heap]
  | INSTRarr_stack (tmp, level, vp_asz, hit_elt) => begin
      emit_instr_arr_stack (pf | out, tmp, level, vp_asz, hit_elt)
    end // end of [INSTRarr_heap]
  | INSTRassgn_arr (vp_arr, vp_asz, tmp_elt, vp_tsz) => begin
      emit_instr_assgn_arr (pf | out, vp_arr, vp_asz, tmp_elt, vp_tsz)
    end // end of [INSTRassgn_arr]
  | INSTRassgn_clo (
      tmp_ptr, tmp_clo, fl, env
    ) => () where {
//
      val () = emit_tmpvar (pf | out, tmp_ptr)
      val () = fprint1_string (pf | out, " = &(")
      val () = emit_tmpvar (pf | out, tmp_clo)
      val () = fprint1_string (pf | out, ") ;\n")
//
      val () = emit_tmpvar_cloptr_init
        (pf | out, 0(*unboxed*), tmp_ptr, fl, env) 
      val () = fprint1_string (pf | out, " ; // closure initialization")
//
    } // end of [INSTRassgn_clo]
  | INSTRcall (tmp, hit_fun, vp_fun, vps_arg) => begin
      emit_instr_call (pf | out, tmp, hit_fun, vp_fun, vps_arg)
    end // end of [INSTRcall]
  | INSTRcall_tail fl => begin
      fprint1_string (pf | out, "goto ");
      fprint1_string (pf | out, "__ats_lab_");
      emit_funlab (pf | out, fl);
      fprint1_string (pf | out, " ; // tail call")      
    end // end of [INSTRcall_tail]
  | INSTRcond (vp_cond, inss_then, inss_else) => begin
      fprint1_string (pf | out, "if (");
      emit_valprim (pf | out, vp_cond);
      fprint1_string (pf | out, ") {\n");
      emit_instrlst (pf | out, inss_then);
      fprint1_string (pf | out, "\n} else {\n");
      emit_instrlst (pf | out, inss_else);
      fprint1_string (pf | out, "\n} /* end of [if] */")
    end // end of [INSTRcond]
//
  | INSTRdefine_clo (d2c, fl) => begin
      fprint1_string (pf | out, "ATS_GC_MARKROOT(&");
      emit_d2cst (pf | out, d2c);
      fprint1_string (pf | out, ", sizeof(ats_ptr_type)) ;\n");
      emit_d2cst (pf | out, d2c);
      fprint1_string (pf | out, " = ");
      emit_funlab (pf | out, fl);
      fprint1_string (pf | out, "_closure_make () ;")
    end // end of [INSTRdefine_clo]
  | INSTRdefine_fun (d2c, fl) => begin
      emit_d2cst (pf | out, d2c);
      fprint1_string (pf | out, " = &");
      emit_funlab (pf | out, fl);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRdefine_fun]
  | INSTRdefine_val (d2c, vp) => begin
      fprint1_string (pf | out, "ATS_GC_MARKROOT(&");
      emit_d2cst (pf | out, d2c);
      fprint1_string (pf | out, ", sizeof(");
      emit_hityp (pf | out, vp.valprim_typ);
      fprint1_string (pf | out, ")) ;\n");
      emit_d2cst (pf | out, d2c);
      fprint1_string (pf | out, " = ");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRdefine_val]
//
// HX-2011-01-15: partial value template
//
  | INSTRdefine_partval (name, vp) => begin
(*
//
// HX-2011-01-15: is this really needed?
//  
      fprint1_string (pf | out, "ATS_GC_MARKROOT(&");
      fprint1_string (pf | out, name);
      fprint1_string (pf | out, ", sizeof(");
      emit_hityp (pf | out, vp.valprim_typ);
      fprint1_string (pf | out, ")) ;\n");
*)
      fprint1_string (pf | out, "/*\n");
//
      fprint1_string (pf | out, name);
      fprint1_string (pf | out, " = ");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " ;");
//
      fprint1_string (pf | out, "\n*/")
    end // end of [INSTRdefine_partval]
//
  | INSTRextval (name, vp) => begin
      fprint1_string (pf | out, "ATS_GC_MARKROOT(&");
      fprint1_string (pf | out, name);
      fprint1_string (pf | out, ", sizeof(");
      emit_hityp (pf | out, vp.valprim_typ);
      fprint1_string (pf | out, ")) ;\n");
      fprint1_string (pf | out, name);
      fprint1_string (pf | out, " = ");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRextval]
  | INSTRfreeptr vp => begin
      fprint1_string (pf | out, "ATS_FREE(");
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, ") ;")
    end // end of [INSTRfreeptr]
  | INSTRfunction
      (tmp_ret_all, vps_arg, inss_body, tmp_ret) => let
      val () = funarglst_push (vps_arg)
      val () = emit_instrlst (pf | out, inss_body)
      val () = funarglst_pop ()
      val () = fprint1_char (pf | out, '\n')
    in
      case+ 0 of
      | _ when tmpvar_is_void tmp_ret => begin
          fprint1_string (pf | out, "return /* ");
          emit_valprim_tmpvar (pf | out, tmp_ret);
          fprint1_string (pf | out, " */ ;\n")
        end // end of [_ when ...]
      | _ => begin
          fprint1_string (pf | out, "return ");
          emit_valprim_tmpvar (pf | out, tmp_ret);
          fprint1_string (pf | out, " ;\n")
        end // end of [_]
    end // end of [INSTRfunction]
  | INSTRfunlab fl => begin
      fprint1_string (pf | out, "__ats_lab_");
      emit_funlab (pf | out, fl); fprint1_char (pf | out, ':')
    end // end of [INSTRfunlab]
  | INSTRdynload_file fil => let
      val () = emit_filename (pf | out, fil)
      val () = fprint1_string (pf | out, "__dynload () ;")
    in
      // empty
    end // end of [INSTRdynload_file]
  | INSTRload_ptr (tmp, vp_ptr) => let
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = ")
      val () = fprint1_string (pf | out, "ats_ptrget_mac(")
      val () = emit_hityp (pf | out, tmpvar_get_typ tmp)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_ptr)
      val () = fprint1_string (pf | out, ") ;")
    in
      // empty
    end // end of [INSTRload_ptr]
  | INSTRload_ptr_offs (tmp, vp_ptr, offs) => begin
      emit_valprim_tmpvar (pf | out, tmp);
      fprint1_string (pf | out, " = ");
      emit_valprim_select_ptr (pf | out, vp_ptr, offs);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRload_ptr_offs]
  | INSTRload_var_offs (tmp, vp_var, offs) => begin
      emit_valprim_tmpvar (pf | out, tmp);
      fprint1_string (pf | out, " = ");
      emit_valprim_select_var (pf | out, vp_var, offs);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRload_var_offs]
//
  | INSTRloop (
      tl_init, tl_fini, tl_cont
    , inss_init
    , vp_test, inss_test
    , inss_post
    , inss_body
    ) => let
      val () = fprint1_string (pf | out, "/* loop initialization */\n")
      val () = emit_instrlst (pf | out, inss_init)
      val () = fprint1_string (pf | out, "\n")
      val ispost = $Lst.list_is_cons inss_post // this is a for loop
      val () = fprint1_string (pf | out, "ats_loop_beg_mac(")
      val () = emit_tmplab (pf | out, tl_init)
      val () = fprint1_string (pf | out, ")\n")
      val () = emit_instrlst (pf | out, inss_test)
      val () = fprint1_char (pf | out, '\n')
      val () = fprint1_string (pf | out, "if (!")
      val () = emit_valprim (pf | out, vp_test)
      val () = fprint1_string (pf | out, ") break ;\n")
      val () = emit_instrlst (pf | out, inss_body)
      val () = fprint1_char (pf | out, '\n')
      val () = if ispost then let
        val () = fprint1_string (pf | out, "/* post update before continue */\n")
        val () = emit_tmplab (pf | out, tl_cont)
        val () = fprint1_string (pf | out, ":\n")
        val () = emit_instrlst (pf | out, inss_post)
        val () = fprint1_string (pf | out, "\n")
      in
        // empty
      end // end of [if]
      val () = fprint1_string (pf | out, "ats_loop_end_mac(")
      val () = emit_tmplab (pf | out, tl_init)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_tmplab (pf | out, tl_fini)
      val () = fprint1_string (pf | out, ")")
    in
      // empty
    end // end of [INSTRloop]
  | INSTRloopexn (_(*knd*), tl) => begin
      fprint1_string (pf | out, "goto ");
      emit_tmplab (pf | out, tl);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRloopexn]
//
  | INSTRmove_arg (arg, vp) => begin
      fprintf1_exn (pf | out, "arg%i = ", @(arg));
      emit_valprim (pf | out, vp);
      fprint1_string (pf | out, " ;")
    end // end of [INSTRmove_arg]
  | INSTRmove_con (tmp, hit_sum, d2c, vps) => begin
      emit_move_con (pf | out, tmp, hit_sum, d2c, vps)
    end // end of [INSTRmove_con]
//
  | INSTRmove_lazy_delay
      (tmp, lin, hit_body, vp_clo) => let
      val () = if lin = 0 then begin
        fprint1_string (pf | out, "ats_instr_move_lazy_delay_mac (")
      end else begin
        fprint1_string (pf | out, "ats_instr_move_lazy_ldelay_mac (")
      end // end of [val]
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_hityp (pf | out, hit_body)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_clo)
      val () = fprint1_string (pf | out, ") ;")
    in
      // empty
    end // end of [INSTRmove_lazy_delay]
  | INSTRmove_lazy_force
      (tmp, lin, hit_val, vp_lazy) => let
      val () = if lin = 0 then begin
        fprint1_string (pf | out, "ats_instr_move_lazy_force_mac (")
      end else begin
        fprint1_string (pf | out, "ats_instr_move_lazy_lforce_mac (")        
      end // end of [val]
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_hityp (pf | out, hit_val)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_lazy)
      val () = fprint1_string (pf | out, ") ;")
    in
      // empty
    end // end of [INSTRmove_lazy_delay]
//
  | INSTRmove_rec_box
      (tmp, hit_rec, lvps) => let
      val isext =
        hityp_t_is_tyrecext hit_rec
      // end of [val]
      fun aux (
        out: &FILE m
      , tmp: tmpvar_t, lvps: labvalprimlst
      ) :<cloptr1> void = (case+ lvps of
        | LABVALPRIMLSTcons
            (l, vp, lvps) => let
            val () = fprint1_string
              (pf | out, "ats_selptrset_mac(")
            val () = emit_hityp_ptr (pf | out, hit_rec)
            val () = fprint1_string (pf | out, ", ")
            val () = emit_valprim_tmpvar (pf | out, tmp)
            val () = fprint1_string (pf | out, ", ")
            val () = emit_labelext (pf | out, isext, l)
            val () = fprint1_string (pf | out, ", ")
            val () = emit_valprim (pf | out, vp)
            val () = fprint1_string (pf | out, ") ;\n")
          in
            aux (out, tmp, lvps)
          end
        | LABVALPRIMLSTnil () => ()
      ) // end of [aux]
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = ATS_MALLOC(sizeof(")
      val () = emit_hityp_ptr (pf | out, hit_rec)
      val () = fprint1_string (pf | out, ")) ;\n")
    in
      aux (out, tmp, lvps)
    end // end of [INSTRmove_rec_box]
  | INSTRmove_rec_flt
      (tmp, hit_rec, lvps) => let
      val isext = hityp_t_is_tyrecext hit_rec
      fun aux (
          out: &FILE m, tmp: tmpvar_t, lvps: labvalprimlst
        ) :<cloptr1> void = begin case+ lvps of
        | LABVALPRIMLSTcons (l, v, lvps) => let
            val () = emit_valprim_tmpvar (pf | out, tmp)
            val () = if isext then
              fprint1_string (pf | out, ".")
            else
              fprint1_string (pf | out, ".atslab_")
            // end of [if]
            val () = emit_label (pf | out, l)
            val () = fprint1_string (pf | out, " = ")
            val () = emit_valprim (pf | out, v)
            val () = fprint1_string (pf | out, " ;\n")
          in
            aux (out, tmp, lvps)
          end
        | LABVALPRIMLSTnil () => ()
      end // end of [aux]
    in
      aux (out, tmp, lvps)
    end // end of [INSTRmove_rec_flt]
//
  | INSTRmove_ref (tmp, vp) => let
      val () = fprint1_string
        (pf | out, "ats_instr_move_ref_mac (")
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_hityp (pf | out, vp.valprim_typ)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp)
      val () = fprint1_string (pf | out, ") ;")
    in
      // nothing
    end // end of [INSTRmove_ref]
  | INSTRmove_val (tmp, vp) => let
      val isvoid = valprim_is_void vp
      val () = if isvoid then
        fprint1_string (pf | out, "/* ")
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = ")
      val () = emit_valprim (pf | out, vp)
      val () = if isvoid then
        fprint1_string (pf | out, " */")
      val () = fprint1_string (pf | out, " ;")
    in
      // nothing
    end // end of [INSTRmove_val]
//
  | INSTRpatck (vp, patck, fail) => let
      val fail1 = case+ fail of
        | KONTmatpnt mpt => matpnt_get_kont (mpt) | _ => fail
      // end of [val]
      val () = case+ fail1 of
        | KONTnone () => fprint1_string (pf | out, "// ") | _ => ()
      // end of [val]
    in
      emit_patck (pf | out, vp, patck, fail)
    end // end of [INSTRpatck]
//
  | INSTRraise (tmp, vp_exn) => () where {
      val () = fprint1_string (pf | out, "/* ")
      val () = emit_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = */ ats_raise_exn (")
      val () = emit_valprim (pf | out, vp_exn)
      val () = fprint1_string (pf | out, ") ;")
    } // end of [INSTRraise]
//
  | INSTRselect (tmp, vp_root, offs) => let
      val is_void = tmpvar_is_void tmp
      val () = if is_void then fprint1_string (pf | out, "/* ")
      val () = emit_valprim_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = ")
      val () = emit_valprim_select (pf | out, vp_root, offs)
      val () = if is_void then fprint1_string (pf | out, " */")
      val () = fprint1_string (pf | out, " ;")
    in
      // empty
    end // end of [INSTRselect]
//
  | INSTRselcon (
      tmp, vp_sum, hit_sum, ind
    ) => let
      val () = emit_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = ")
      val () = fprint1_string (pf | out, "ats_caselptrlab_mac(")
      val () = emit_hityp_ptr (pf | out, hit_sum)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_sum)
      val () = fprint1_string (pf | out, ", ")
      val () = fprintf1_exn (pf | out, "atslab_%i", @(ind))
      val () = fprint1_string (pf | out, ") ;")
    in
      // nothing
    end // end of [INSTRselcon]
  | INSTRselcon_ptr (
      tmp, vp_sum, hit_sum, ind
    ) => let
      val () = emit_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " = ")
      val () = fprint1_string (pf | out, "&ats_caselptrlab_mac(")
      val () = emit_hityp_ptr (pf | out, hit_sum)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_sum)
      val () = fprint1_string (pf | out, ", ")
      val () = fprintf1_exn (pf | out, "atslab_%i", @(ind))
      val () = fprint1_string (pf | out, ") ;")
    in
      // nothing
    end // end of [INSTRselcon_ptr]
//
  | INSTRstore_ptr (vp_ptr, vp_val) => let
      val () = fprint1_string
        (pf | out, "ats_ptrget_mac(")
      val () = emit_hityp (pf | out, vp_val.valprim_typ)
      val () = fprint1_string (pf | out, ", ")
      val () = emit_valprim (pf | out, vp_ptr)
      val () = fprint1_string (pf | out, ")")
      val () = fprint1_string (pf | out, " = ")
      val () = emit_valprim (pf | out, vp_val)
      val () = fprint1_string (pf | out, " ;")
    in
      // nothing
    end // end of [INSTRstore_ptr]
  | INSTRstore_ptr_offs
      (vp_ptr, offs, vp_val) => let
      val () = emit_valprim_select_ptr (pf | out, vp_ptr, offs)
      val () = fprint1_string (pf | out, " = ")
      val () = emit_valprim (pf | out, vp_val)
      val () = fprint1_string (pf | out, " ;")
    in
      // nothing
    end // end of [INSTRstore_ptr_offs]
//
  | INSTRstore_var
      (vp_mut, vp_val) => let
      val () = emit_valprim (pf | out, vp_mut)
      val () = fprint1_string (pf | out, " = ")
      val () = emit_valprim (pf | out, vp_val)
      val () = fprint1_string (pf | out, " ;")
    in
      // nothing
    end // end of [INSTRstore_var]
  | INSTRstore_var_offs
      (vp_var, offs, vp_val) => let
      val () = emit_valprim_select_var (pf | out, vp_var, offs)
      val () = fprint1_string (pf | out, " = ")
      val () = emit_valprim (pf | out, vp_val)
      val () = fprint1_string (pf | out, " ;")
    in
      // nothing
    end // end of [INSTRstore_ptr]
//
  | INSTRswitch branchlst => begin
      fprint1_string (pf | out, "do {\n");
      emit_branchlst (pf | out, branchlst);
      fprint1_string (pf | out, "} while (0) ;")
    end // end of [INSTRswitch]
//
  | INSTRtmplabint (tl, i) => begin
      emit_tmplabint (pf | out, tl, i); fprint1_char (pf | out, ':')
    end // end of [INSTRtmplabint]
//
  | INSTRprfck_beg (d2c) => let
      val () = fprint1_string (pf | out, "ats_proofcheck_beg_mac(")
      val () = emit_d2cst (pf | out, d2c)
      val () = fprint1_string (pf | out, ") ;")
    in
      // empty
    end // end of [INSTRprfck_beg]
  | INSTRprfck_end (d2c) => let
      val () = fprint1_string (pf | out, "ats_proofcheck_end_mac(")
      val () = emit_d2cst (pf | out, d2c)
      val () = fprint1_string (pf | out, ") ;")
    in
      // empty
    end // end of [INSTRprfck_end]
  | INSTRprfck_tst (d2c) => begin
      emit_d2cst (pf | out, d2c); fprint1_string (pf | out, "_prfck () ;")
    end // end of [INSTRprfck_end]
//
  | INSTRtrywith (res_try, tmp_exn, brs) => let
      val () = fprint1_string (pf | out, "ATS_TRYWITH_TRY(")
      val () = emit_valprim_tmpvar (pf | out, tmp_exn)
      val () = fprint1_string (pf | out, ")\n")
      val () = emit_instrlst (pf | out, res_try)
      val () = fprint1_char (pf | out, '\n')
      val () = fprint1_string (pf | out, "ATS_TRYWITH_WITH(")
      val () = emit_valprim_tmpvar (pf | out, tmp_exn)
      val () = fprint1_string (pf | out, ")\n")
      val () = fprint1_string (pf | out, "do {\n")
      val () = emit_branchlst (pf | out, brs)
      val () = fprint1_string (pf | out, "} while (0) ;\n")
      val () = fprint1_string (pf | out, "ATS_TRYWITH_END() ;\n")
    in
      // empty
    end // end of [INSTRtrywith]
  | INSTRvardec tmp => let
      val () = fprint1_string (pf | out, "/* ")
      val () = emit_hityp (pf | out, tmpvar_get_typ tmp)
      val () = fprint1_char (pf | out, ' ')
      val () = emit_tmpvar (pf | out, tmp)
      val () = fprint1_string (pf | out, " ; */")
    in
      // nothing
    end // end of [INSTRvardec]
  | _ => begin
      prerr_interror ();
      prerr ": emit_instr: ins = "; prerr ins; prerr_newline ();
      $Err.abort {void} ()
    end // end of [_]
end // end of [emit_instr]

implement
emit_instrlst {m} (pf | out, inss) = let
  fun aux (out: &FILE m, i: int, inss: instrlst)
    : void = begin case+ inss of
    | list_cons (ins, inss) => begin
        if i > 0 then fprint1_char (pf | out, '\n');
        emit_instr (pf | out, ins); aux (out, i+1, inss)
      end
    | list_nil () => begin
        if i > 0 then () else fprint1_string (pf | out, "/* empty */")
      end
  end // end of [aux]
in
  aux (out, 0, inss)
end // end of [emit_instrlst]    

(* ****** ****** *)

extern
fun emit_funarg{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, hits: hityplst_t): void
// end of [emit_funarg]

implement
emit_funarg {m}
  (pf | out, hits) = let
  fun loop (
    out: &FILE m, i: int, hits: hityplst
  ) : void =
    case+ hits of
    | list_cons (hit, hits) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = _emit_hityp (pf | out, hit)
        val () = // variadacity needs to be properly handled
          if hityp_is_vararg hit then () else begin
            fprint1_string (pf | out, " arg"); fprint1_int (pf | out, i)
          end // end of [if]
      in
        loop (out, i + 1, hits)
      end (* end of [list_cons] *)
    | list_nil () => ()
  // end of [loop]
in
  loop (out, 0, hityplst_decode hits)
end // end of [emit_funarg]

(* ****** ****** *)

extern
fun emit_funenvarg{m:fmode}
  (pf: fmlte (m, w) | out: &FILE m, vtps: vartypset): int
// end of [emit_funenvarg]

local

dataviewtype ENV
  (l:addr, i:addr) = ENVcon (l, i) of (ptr l, ptr i)
// end of [ENV]

fn _emit_funenvarg
  {m:fmode}{l:addr}
(
  pf_mod: fmlte (m, w)
, pf_fil: !FILE m @ l
| p_l: ptr l, vtps: vartypset
) : int = let
  var i: int = 0
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_arg (
    pf: !V | vtp: vartyp_t, env: !VT
  ) : void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon (p_l, p_i)= env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_get_var (vtp)
    val hit = (
      if d2var_is_mutable (d2v)
        then hityp_encode hityp_ptr else vartyp_get_typ (vtp)
      // end of [if]
    ) : hityp_t
    val () = if i > 0 then fprint1_string (pf_mod | !p_l, ", ")
    val () = emit_hityp (pf_mod | !p_l, hit) // type specifier
    val () = fprintf1_exn (pf_mod | !p_l, " env%i", @(i)) // arg
  in
    pf := @(pf_fil, pf_int); fold@ env
  end
  val env = ENVcon (p_l, &i)
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_arg, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val+ ~ENVcon (_, _) = env
in
  i // the number of environment variables
end // end of [_emit_funenvarg]

in // in of [local]

implement
emit_funenvarg (pf | out, vtps) =
  _emit_funenvarg (pf, view@ out | &out, vtps)
// end of [emit_funenvarg]

end // end of [local]

(* ****** ****** *)

fn funentry_env_err
  (loc: loc_t, fl: funlab_t, vtps: vartypset)
  : void = let
  val d2vs = vartypset_d2varlst_make (vtps)
  val n = $Lst.list_vt_length__boxed (d2vs)
  val () =
    if n > 0 then prerr_loc_errorccomp loc else ()
  // end of [val]
  val () = if n > 1 then begin
    prerr ": the dynamic variables ["
  end else begin
    if n > 0 then begin
      prerr ": the dynamic variable ["
    end
  end // end of [if]
  fun aux (d2vs: d2varlst_vt, i: int): void = begin
    case+ d2vs of
    | ~list_vt_cons (d2v, d2vs) => begin
        if i > 0 then prerr ", "; prerr d2v; aux (d2vs, i+1)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  end // end of [aux]
  val () = aux (d2vs, 0)
  val () = if n > 1 then begin
    prerr "] are not function arguments."
  end else begin
    if n > 0 then begin
      prerr "] is not a function argument."
    end
  end // end of [if]
  val () = (if n > 0 then prerr_newline ())
in
  if n > 0 then $Err.abort {void} ()
end // end of [funentry_env_err]

(* ****** ****** *)

extern
fun emit_closure_type {m:fmode}
(
  pf_mod: fmlte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void // end of [emit_closure_type]

extern
fun emit_closure_init {m:fmode}
(
  pf_mod: fmlte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void // end of [emit_closure_init]

extern
fun emit_closure_make {m:fmode}
(
  pf_mod: fmlte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void // end of [emit_closure_make]

extern
fun emit_closure_clofun {m:fmode}
(
  pf_mod: fmlte (m, w) | out: &FILE m, fl: funlab_t, vtps: vartypset
) : void // end of [emit_closure_clofun]

(* ****** ****** *)

local

fn _emit_closure_type{m:fmode}{l:addr}
(
  pf_mod: fmlte (m, w), pf_fil: !FILE m @ l
| p_l: ptr l, fl: funlab_t, vtps: vartypset
) : void = let
  dataviewtype ENV (l:addr, i:addr) = ENVcon2 (l, i) of (ptr l, ptr i)
  var i: int = 0
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_fld (
    pf: !V | vtp: vartyp_t, env: !VT
  ) : void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i)= env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_get_var (vtp)
    val hit = (
      if d2var_is_mutable (d2v) then hityp_encode hityp_ptr
      else vartyp_get_typ (vtp)
    ) : hityp_t
    val () = emit_hityp (pf_mod | !p_l, hit)
    val () = fprintf1_exn (pf_mod | !p_l, " closure_env_%i ;\n", @(i))
  in
    pf := @(pf_fil, pf_int); fold@ env
  end

  val () = fprint1_string (pf_mod | !p_l, "typedef struct {\n")
  val () = fprint1_string (pf_mod | !p_l, "ats_fun_ptr_type closure_fun ;\n")

  val env = ENVcon2 (p_l, &i)
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_fld, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val+ ~ENVcon2 (_, _) = env

  val () = fprint1_string (pf_mod | !p_l, "} ")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_closure_type ;")
in
  // empty
end // end of [_emit_closure_type]

(* ****** ****** *)

fn _emit_closure_init{m:fmode}{l:addr}
(
  pf_mod: fmlte (m, w), pf_fil: !FILE m @ l
| p_l: ptr l, fl: funlab_t, vtps: vartypset
) : void = let
//
  dataviewtype ENV (l:addr, i:addr) = ENVcon2 (l, i) of (ptr l, ptr i)
  var i: int // uninitialized
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_arg (
    pf: !V | vtp: vartyp_t, env: !VT
  ) : void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_get_var (vtp)
    val hit = (
      if d2var_is_mutable (d2v) then hityp_encode hityp_ptr
      else vartyp_get_typ (vtp)
    ) : hityp_t
    val () = fprint1_string (pf_mod | !p_l, ", "); val () = begin
      emit_hityp (pf_mod | !p_l, hit); fprintf1_exn (pf_mod | !p_l, " env%i", @(i))
    end // end of [val]
  in
    pf := @(pf_fil, pf_int); fold@ env
  end // end of [f_arg]
//
  fn f_body (
    pf: !V | vtp: vartyp_t, env: !VT
  ) : void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val () = fprintf1_exn
      (pf_mod | !p_l, "p_clo->closure_env_%i = env%i ;\n", @(i, i))
  in
    pf := @(pf_fil, pf_int); fold@ env
  end // end of [f_body]
//
  val () = fprint1_string (pf_mod | !p_l, "ATSinline()\n")
  val () = fprint1_string (pf_mod | !p_l, "ats_void_type\n")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_closure_init (")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_closure_type *p_clo")
//  
  val env = ENVcon2 (p_l, &i)
//
  val () = i := 0
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_arg, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
//
  val () = fprint1_string (pf_mod | !p_l, ") {\n")
//
  val () = fprint1_string (pf_mod | !p_l, "p_clo->closure_fun = (ats_fun_ptr_type)&")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_clofun ;\n")
//
  val () = i := 0
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_body, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
//
  val+ ~ENVcon2 (_, _) = env
//
  val () = fprint1_string (pf_mod | !p_l, "return ;\n")
  val () = fprint1_string (pf_mod | !p_l, "} /* end of function */")
//
in
  // empty
end // end of [_emit_closure_init]

(* ****** ****** *)

fn _emit_closure_make{m:fmode}{l:addr}
(
  pf_mod: fmlte (m, w), pf_fil: !FILE m @ l
| p_l: ptr l, fl: funlab_t, vtps: vartypset
) : void = let
//
  dataviewtype ENV (l:addr, i:addr) = ENVcon2 (l, i) of (ptr l, ptr i)
  var i: int // uninitialized
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
//
  fn f_arg (
    pf: !V | vtp: vartyp_t, env: !VT
  ) : void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon2 (p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val d2v = vartyp_get_var (vtp)
    val hit = (
      if d2var_is_mutable (d2v)
        then hityp_encode hityp_ptr else vartyp_get_typ (vtp)
      // end of [if]
    ) : hityp_t
    val () = if i > 0 then fprint1_string (pf_mod | !p_l, ", ")
    val () = begin
      emit_hityp (pf_mod | !p_l, hit); fprintf1_exn (pf_mod | !p_l, " env%i", @(i))
    end // end of [val]
  in
    pf := @(pf_fil, pf_int); fold@ env
  end // end of [f_arg]
//
  val () = fprint1_string (pf_mod | !p_l, "ats_clo_ptr_type\n")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_closure_make (")
//
  val env = ENVcon2 (p_l, &i)
//
  val () = i := 0
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_arg, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val narg = i
//
  val () = fprint1_string (pf_mod | !p_l, ") {\n")
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = begin
    fprint1_string (pf_mod | !p_l, "_closure_type *p_clo = ATS_MALLOC(sizeof(")
  end // end of [val]
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_closure_type)) ;\n")
//
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_closure_init (p_clo")
  val () = loop (!p_l, narg, 0) where {
    fun loop (out: &FILE m, n: int, i: int): void =
      if i < n then begin
        fprintf1_exn (pf_mod | out, ", env%i", @(i)); loop (out, n, i+1)
      end // end of [if]
    // end of [loop]
  } // end of [val]
  val () = fprint1_string (pf_mod | !p_l, ") ;\n")
//
  val+ ~ENVcon2 (_, _) = env
//
  val () = fprint1_string (pf_mod | !p_l, "return (ats_clo_ptr_type)p_clo ;\n")
  val () = fprint1_string (pf_mod | !p_l, "} /* end of function */")
in
  // empty
end // end of [_emit_closure_make]

(* ****** ****** *)

fn _emit_closure_clofun{m:fmode}{l:addr}
(
  pf_mod: fmlte (m, w), pf_fil: !FILE m @ l
| p_l: ptr l, fl: funlab_t, vtps: vartypset
) : void = let
//
  dataviewtype ENV (l:addr, i:addr) = ENVcon3 (l, i) of (funlab_t, ptr l, ptr i)
// function header
  val hit_res = funlab_get_typ_res (fl)
  val () = emit_hityp (pf_mod | !p_l, hit_res)
  val () = fprint1_char (pf_mod | !p_l, '\n')
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, "_clofun (ats_clo_ptr_type cloptr")
  val hits_arg = funlab_get_typ_arg (fl)
  val () = begin case+ 0 of
    | _ when hityplst_is_cons hits_arg => fprint1_string (pf_mod | !p_l, ", ")
    | _ => ()
  end
  val () = emit_funarg (pf_mod | !p_l, hits_arg)
  val () = fprint1_string (pf_mod | !p_l, ") {\n")
//
  var i: int = 0
  viewdef V = (FILE m @ l, int @ i)
  viewtypedef VT = ENV (l, i)
  fn f_env (
    pf: !V | vtp: vartyp_t, env: !VT
  ) : void = let
    prval @(pf_fil, pf_int) = pf
    val+ ENVcon3 (fl, p_l, p_i) = env
    val i = !p_i; val () = (!p_i := i + 1)
    val () = if i > 0 then fprint1_string (pf_mod | !p_l, ", ")
    val () = fprint1_string (pf_mod | !p_l, "((")
    val () = emit_funlab (pf_mod | !p_l, fl)
    val () = fprintf1_exn
      (pf_mod | !p_l, "_closure_type*)cloptr)->closure_env_%i", @(i))
  in
    pf := @(pf_fil, pf_int); fold@ env
  end // end of [f_end]
//
  val is_void = hityp_t_is_void (hit_res) // function body
//
  val () = begin
    if is_void then () else fprint1_string (pf_mod | !p_l, "return ")
  end // end of [val]
//
  val () = emit_funlab (pf_mod | !p_l, fl)
  val () = fprint1_string (pf_mod | !p_l, " (")
//
  val env = ENVcon3 (fl, p_l, &i)
  prval pf = @(pf_fil, view@ i)
  val () = vartypset_foreach_main {V} {VT} (pf | vtps, f_env, env)
  prval () = (pf_fil := pf.0; view@ i := pf.1)
  val+ ~ENVcon3 (_, _, _) = env
//
  val () = if i > 0 then begin
    case+ 0 of // print a comma for separation if needed
    | _ when hityplst_is_cons hits_arg => fprint1_string (pf_mod | !p_l, ", ")
    | _ => ()
  end // end of [if] // end of [val]
//
  val hits_arg = hityplst_decode (hits_arg)
  val () = emit_arglst (!p_l, 0, hits_arg) where {
    fun emit_arglst // tailrec
      (out: &FILE m, i: int, hits: hityplst)
      : void = begin case+ hits of
      | list_cons (hit, hits) => let
          val () = begin
            if i > 0 then fprint1_string (pf_mod | out, ", ")
          end // end of [val]
          val () = fprintf1_exn (pf_mod | out, "arg%i", @(i))
        in
          emit_arglst (out, i+1, hits)
        end // end of [list_cons]
      | list_nil () => ()
    end // end of [emit_arglst]
  } // end of [where]
  val () = fprint1_string (pf_mod | !p_l, ") ;")
//
  val () = begin
    if is_void then fprint1_string (pf_mod | !p_l, " return ;") else ()
  end // end of [val]
//
  val () = fprint1_string (pf_mod | !p_l, "\n} /* end of function */")
//
in
  // empty
end // end of [_emit_clofun]

in // in of [local]

(* ****** ****** *)

implement
emit_closure_type (pf | out, fl, vtps) =
  _emit_closure_type (pf, view@ out | &out, fl, vtps)
// end of [emit_closure_type]

implement
emit_closure_init (pf | out, fl, vtps) =
  _emit_closure_init (pf, view@ out | &out, fl, vtps)
// end of [emit_closure_init]

implement
emit_closure_make (pf | out, fl, vtps) =
  _emit_closure_make (pf, view@ out | &out, fl, vtps)
// end of [emit_closure_make]

implement
emit_closure_clofun (pf | out, fl, vtps) =
  _emit_closure_clofun (pf, view@ out | &out, fl, vtps)
// end of [emit_closure_clofun]

end // end of [local]

(* ****** ****** *)

fn hityplst_get_nvararg
  (hits: hityplst_t): int = let
  val hits = hityplst_decode hits in
  case+ hits of
  | list_cons (hit, hits) => loop (0, hit, hits) where {
      fun loop (n: int, hit: hityp, hits: hityplst): int =
        case+ hits of
        | list_cons (hit, hits) => loop (n+1, hit, hits)
        | list_nil () => if hityp_is_vararg hit then n else ~1
      // end of [loop]
    } // end of [list_cons]
  | list_nil () => ~1
end // end of [hityplst_get_nvararg]

implement
emit_funentry
  (pf | out, entry) = let
  val fl = funentry_get_lab (entry)
(*
  val () = begin
    print "emit_funentry: fl = "; print_funlab fl; print_newline ()
  end // end of [val]
*)
  val fc = funlab_get_funclo (fl)
  val hits_arg = funlab_get_typ_arg (fl)
  val nvararg = hityplst_get_nvararg (hits_arg)
  val hit_res = funlab_get_typ_res (fl)
  val vtps_all = funentry_get_vtps_all (entry)
(*
  val () = begin
    print "emit_funentry: vtps_all = "; print_vartypset vtps_all; print_newline ()
  end // end of [val]
*)
  val loc_entry = funentry_get_loc (entry)
  val () = (case+ fc of
    | $Syn.FUNCLOfun () => begin
        funentry_env_err (loc_entry, fl, vtps_all)
      end // end of [FUNCLOfun]
    | $Syn.FUNCLOclo _ => ()
  ) : void // end of [val]
(*
  val () = begin
    print "emit_funentry: after [funentry_env_err]"; print_newline ()
  end // end of [val]
*)
  val tmp_ret = funentry_get_ret (entry)
  val () = funentry_varindmap_set (vtps_all)
//
#if (ATS_CC_VERBOSE_LEVEL >= 1) #then
//
// this location information is mostly for the purpose of debugging
//
  val () = fprint1_string (pf | out, "/*\n")
  val () = fprint1_string (pf | out, "// ")
  val () = $Loc.fprint_location (pf | out, loc_entry)
  val () = fprint1_string (pf | out, "\n*/\n")
#endif // end of ...
//
  val ndeb = $Deb.debug_flag_get ()
  val () = if ndeb >= 1 then (
    $Loc.fprint_line_pragma (pf | out, loc_entry) // #line pragma
  ) // end of [val]
//
// function header
//
  val () = let
    val qua = funlab_get_qua (fl)
  in
    case+ qua of
    | D2CSTOPTsome _ => fprint1_string (pf | out, "ATSglobaldec()\n")
    | D2CSTOPTnone _ => fprint1_string (pf | out, "ATSstaticdec()\n")
  end // end of [val]
  val () = begin
     emit_hityp (pf | out, hit_res); fprint1_char (pf | out, '\n')
  end // end of [val]
  val () = begin
    emit_funlab (pf | out, fl); fprint1_string (pf | out, " (")
  end // end of [val]
  val n = emit_funenvarg (pf | out, vtps_all)
  val () = // comma separation if needed
    if n > 0 then begin case+ 0 of
      | _ when hityplst_is_cons hits_arg => fprint1_string (pf | out, ", ")
      | _ => ()
    end (* end of [if] *)
  val () = begin
    emit_funarg (pf | out, hits_arg); fprint1_string (pf | out, ") {\n")
  end // end of [val]
//
// tailjoinlst
//
  val tjs = funentry_get_tailjoin (entry)
//
// local variable declaration
//
  val () = let
    val () = fprint1_string (pf | out, "/* local vardec */\n")
    var tmps_local: tmpvarmap_vt = tmpvarmap_nil ()
    val () =
      tailjoinlst_tmpvarmap_add (tmps_local, tjs)
    // end of [val]
    val () = funentry_tmpvarmap_add (tmps_local, entry)
    val n = emit_tmpvarmap_dec_local (pf | out, tmps_local)
    val () = if n > 0 then fprint1_char (pf | out, '\n')
  in
    tmpvarmap_free (tmps_local)
  end (* end of [val] *)
//
// mutual tail-recursion
//
  val istailjoin = (case+ tjs of
    | TAILJOINLSTcons _ => true | TAILJOINLSTnil () => false
  ) : bool // end of [val]
  val () = begin
    if istailjoin then emit_tailjoinlst (pf | out, tjs)
  end // end of [val]
//
  val () = if nvararg >= 0 then let
    val () = if nvararg = 0 then begin
      prerr_loc_errorccomp loc_entry;
      prerr ": a variadic function must have at least one argument (in front of ...)";
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [val]
(*
    // this check needs to be done earlier!!!
    val () = if istailjoin then begin
      prerr_loc_errorccomp loc_entry;
      prerr ": variadic functions cannot be joined."; prerr_newline ();
      $Err.abort {void} ()
    end // end of [val]
*)
    val () = fprintf1_exn
      (pf | out, "ATSlocal (va_list, arg%i) ;\n", @(nvararg))
    // end of [val]
    val () = fprintf1_exn
      (pf | out, "va_start(arg%i, arg%i) ;\n\n", @(nvararg, nvararg-1))
    // end of [val]
  in
    // nothing
  end // end of [val]
//
// function body
//
  val () = emit_instrlst (pf | out, funentry_get_body entry)
//
// varindmap needs to be reset
//
  val () = funentry_varindmap_reset ()
//
// return
//
  val () = fprint1_string (pf | out, "\nreturn ")
  val () = let
    val is_void = tmpvar_is_void (tmp_ret)
    val () = if is_void then fprint1_string (pf | out, "/* ")
    val () = fprint1_string (pf | out, "(")
    val () = emit_tmpvar (pf | out, tmp_ret)
    val () = fprint1_string (pf | out, ")")
    val () = if is_void then fprint1_string (pf | out, " */")
  in
    // empty
  end
  val () = fprint1_string (pf | out, " ;\n} /* end of [")
  val () = begin
    emit_funlab (pf | out, fl); fprint1_string (pf | out, "] */")
  end // end of [val]
//
// closure_type and closure_make and clofun
//
  val () = (case+ 0 of
    | _ when istailjoin => ()
    | _ => begin case+ fc of
      | $Syn.FUNCLOclo knd => let
          val () = fprint1_string (pf | out, "\n\n")
          val () = emit_closure_type (pf | out, fl, vtps_all)
          val () = fprint1_string (pf | out, "\n\n")
          val () = emit_closure_clofun (pf | out, fl, vtps_all)
          val () = fprint1_string (pf | out, "\n\n")
          val () = emit_closure_init (pf | out, fl, vtps_all)
          val () = if (knd <> 0) then let // boxed closure
            val () = fprint1_string (pf | out, "\n\n")
            val () = emit_closure_make (pf | out, fl, vtps_all)
          in
            // empty
          end // end of [val]
        in
          // empty
        end // end of [FUNCLOclo]
      | $Syn.FUNCLOfun _ => ()
      end // end of [_]
   ) : void // end of [val]
//
in
  // empty
end // end of [emit_funentry]

(* ****** ****** *)

implement
emit_funentry_prototype
  {m} (pf | out, entry) = let
  val fl = funentry_get_lab (entry)
  val fc = funlab_get_funclo (fl)
  val hits_arg = funlab_get_typ_arg (fl)
  val hit_res = funlab_get_typ_res (fl)
  val vtps_all = funentry_get_vtps_all (entry)
//
  fn aux_function
    (out: &FILE m):<cloptr1> void = let
    val () = fprint1_string (pf | out, "static\n")
    val () = emit_hityp (pf | out, hit_res)
    val () = fprint1_char (pf | out, ' ')
    val () = emit_funlab (pf | out, fl)
    val () = fprint1_string (pf | out, " (")
    val n = emit_funenvarg (pf | out, vtps_all)
    val () = if n > 0 then begin case+ 0 of // comma separation if needed
      | _ when hityplst_is_cons hits_arg => fprint1_string (pf | out, ", ")
      | _ => ()
    end // end of [val]
    val () = emit_funarg (pf | out, hits_arg)
    val () = fprint1_string (pf | out, ") ;\n")
  in
    // empty
  end // end of [aux_function]
//
  fn aux_closure_make
    (out: &FILE m):<cloptr1> void = let
    val () = fprint1_string (pf | out, "static\n")
    val () = fprint1_string (pf | out, "ats_clo_ptr_type ")
    val () = emit_funlab (pf | out, fl)
    val () = fprint1_string (pf | out, "_closure_make (")
    val _(*int*) = emit_funenvarg (pf | out, vtps_all)
    val () = fprint1_string (pf | out, ") ;\n")
  in
    // empty
  end // end of [aux_closure_make]
//
  fn aux_closure_clofun
    (out: &FILE m):<cloptr1> void = let
    val () = fprint1_string (pf | out, "static\n")
    val () = emit_hityp (pf | out, hit_res)
    val () = fprint1_char (pf | out, ' ')
    val () = emit_funlab (pf | out, fl)
    val () = fprint1_string (pf | out, "_clofun (ats_clo_ptr_type cloptr")
    val () = begin case+ 0 of
      | _ when hityplst_is_cons hits_arg => fprint1_string (pf | out, ", ")
      | _ => ()
    end
    val () = emit_funarg (pf | out, hits_arg)
    val () = fprint1_string (pf | out, ") ;\n")
  in
    // empty
  end // end of [aux_closure_clofun]
//
in
  case+ funlab_get_qua (fl) of
  | D2CSTOPTsome _(*d2c*) => begin case+ fc of
    | $Syn.FUNCLOclo knd =>
        if knd <> 0 then let
          val () = aux_closure_make (out)
          val () = aux_closure_clofun (out)
        in
          // empty
        end // end of [if]
      // end of [FUNCLOclo]
    | $Syn.FUNCLOfun () => ()
    end // end of [D2CSTOPTsome]
  | D2CSTOPTnone () => begin case+ fc of
    | $Syn.FUNCLOclo _(*knd*) => let
        val () = aux_function (out)
        val () = aux_closure_make (out)
        val () = aux_closure_clofun (out)
      in
        // empty
      end // end of [FUNCLOclo]
    | $Syn.FUNCLOfun () => let
        val () = aux_function (out)
      in
        // empty
      end // end of [FUNCLOfun]
    end // end of [D2CSTOPTnone]
end // end of [emit_funentry_prototype]

(* ****** ****** *)

implement
emit_mainfun
  (pf | out, fil) = () where {
  val () = fprint1_string
    (pf | out, "int main (int argc, char *argv[]) {\n")
//
  val () = fprint1_string (pf | out, "ATS_GC_INIT() ;\n")
//
  val () = fprint1_string (pf | out, "mainats_prelude() ;\n")
  val () = emit_filename (pf | out, fil)
  val () = fprint1_string (pf | out, "__dynload() ;\n")
  val () = fprint1_string
    (pf | out, "mainats((ats_int_type)argc, (ats_ptr_type)argv) ;\n")
//
  val () = fprint1_string (pf | out, "return (0) ;\n")
//
  val () = fprint1_string (pf | out, "} /* end of main */\n")
} // end of [emit_mainfun]

(* ****** ****** *)

(* end of [ats_ccomp_emit.dats] *)
