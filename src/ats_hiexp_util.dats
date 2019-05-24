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
// Start Time: March 2008
//
(* ****** ****** *)

(* high-level intermediate representation *)

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Map = "ats_map_lin.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_map_lin.dats"

(* ****** ****** *)

#define THISFILENAME "ats_hiexp_util.dats"

(* ****** ****** *)

#define nil list_nil; #define cons list_cons; #define :: list_cons

(* ****** ****** *)

#define ABS_TYPE_NAME "ats_abs_type"
#define VAR_TYPE_NAME "ats_var_type"
#define VOID_TYPE_NAME "ats_void_type"

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_hiexp_util)"

(* ****** ****** *)

implement
hityp_is_void (hit0) = begin
  case+ hit0.hityp_node of
  | HITextype (name, _(*arglst*)) => begin
    case+ 0 of
    | _ when name = ABS_TYPE_NAME => true
    | _ when name = VAR_TYPE_NAME => true
    | _ when name = VOID_TYPE_NAME => true
    | _ => false
    end (* end of [HITextype] *)
  | HITs2var s2v when s2var_is_unboxed s2v => true // problematic?
  | HITtyrecsin hit => hityp_is_void hit
  | _ => false
end // end of [hityp_is_void]

implement
hityp_fun_is_void (hit_fun) = let
(*
  val () = begin
    print "hityp_fun_is_void: hit_fun = "; print hit_fun; print_newline ()
  end // end of [val]
*)
in
  case+ hit_fun.hityp_node of
  | HITfun (_(*fc*), _(*arg*), hit_res) => hityp_is_void (hit_res)
  | _ => begin
      prerr_interror ();
      prerr ": hityp_fun_is_void: hit_fun = "; prerr_hityp hit_fun; prerr_newline ();
      $Err.abort {bool} ()
    end // end of [_]
end // end of [hityp_fun_is_void]

implement
hityp_is_vararg (hit) = begin
  case+ hit.hityp_node of HITvararg _ => true | _ => false
end // end of [hityp_is_vararg]

implement
hityp_fun_is_vararg (hit_fun) = let
  fun aux (hit: hityp, hits: hityplst): bool = case+ hits of
    | cons (hit, hits) => aux (hit, hits) | nil () => hityp_is_vararg hit
  // end of [aux]
in
  case+ hit_fun.hityp_node of
  | HITfun (_(*fc*), arg, _(*res*)) => begin
      case+ arg of cons (hit, hits) => aux (hit, hits) | nil () => false
    end // end of [HITfun]
  | _ => let
      val () = prerr_interror ()
      val () = prerr ": hityp_fun_is_vararg: hit_fun = "
      val () = prerr_hityp (hit_fun)
      val () = print_newline ()
    in
      $Err.abort {bool} ()
    end // end of [_]
  // end of [case]
end // end of [hityp_fun_is_vararg]

(* ****** ****** *)

implement
hityp_is_tyarr (hit_rec) = begin
  case+ hit_rec.hityp_node of HITtyarr _ => true | _ => false
end // end of [hityp_is_tyarr]

implement
hityp_is_tyrecbox (hit_rec) = begin
  case+ hit_rec.hityp_node of HITtyrec (knd, _) => knd > 0 | _ => false
end // end of [hityp_is_tyrecbox]

implement
hityp_is_tyrecext (hit_rec) = begin
  case+ hit_rec.hityp_node of HITtyrec (knd, _) => knd < 0 | _ => false
end // end of [hityp_is_tyrecext]

implement
hityp_is_tyrecsin (hit_rec) = begin
  case+ hit_rec.hityp_node of HITtyrecsin _ => true | _ => false
end // end of [hityp_is_tyrecsim]

(* ****** ****** *)

implement
label_is_tyarr
  (hit_rec, lab) = let
  fun istyarr (
    lhits: labhityplst, lab: lab_t
  ) : bool =
    case+ lhits of
    | LABHITYPLSTcons (l, hit, lhits) =>
        if $Lab.eq_label_label (lab, l)
          then hityp_is_tyarr(hit) else istyarr (lhits, lab)
      // end of [if]
    | LABHITYPLSTnil () => false
  // end of [istyarr]
in
  case+ hit_rec.hityp_node of
  | HITtyrec (_(*knd*), lhits) => istyarr (lhits, lab)
  | _ => false
end // end of [label_is_tyarr]

(* ****** ****** *)  

implement
hipatlst_is_unused
  (hips) = begin case+ hips of
  | list_cons (hip, hips) => begin
    case+ hip.hipat_node of
    | HIPany () => hipatlst_is_unused hips | _ => false
    end // end of [list_cons]
  | list_nil () => true
end // end of [hipatlst_is_unused]

(* ****** ****** *)

viewtypedef hiexplst_vt = List_vt hiexp

implement
hiexp_is_empty (hie0) =
  case+ hie0.hiexp_node of
  | HIEempty () => true
  | HIErec (
      knd, _(*hit_rec*), lhies
    ) when knd = 0 (*flt*) => begin case+ lhies of
    | LABHIEXPLSTcons (_(*lab*), hie, LABHIEXPLSTnil ()) =>
        hiexp_is_empty hie
    | _ => false
    end
  | _ => false
// end of [hiexp_is_empty]

implement
hiexp_seq_simplify (
  loc0: loc_t, hit0: hityp, hies: hiexplst
) : hiexp = let
  fun aux (
    res: &hiexplst_vt, hies: hiexplst
  ) : void = begin
    case+ hies of
    | cons (hie, hies) => let
        val () = begin
          if not (hiexp_is_empty hie) then res := list_vt_cons (hie, res)
        end // end of [val]
      in
        aux (res, hies)
      end (* end of [cons] *)
    | nil () => ()
  end // end of [aux]
  var res: hiexplst_vt = list_vt_nil ()
  val () = aux (res, hies)
  val hies_new = $Lst.list_vt_reverse_list (res)
in
  case+ hies_new of
  | list_cons (hie1, hies1_new) => begin
    case+ hies1_new of
    | list_cons _ => hiexp_seq (loc0, hit0, hies_new)
    | list_nil () => hie1
    end // end of [list_cons]
  | list_nil () => hiexp_empty (loc0, hit0)
end // end of [hiexp_seq_simplify]

(* ****** ****** *)

fun hiexplst_is_value
  (hies: hiexplst): bool = begin
  case+ hies of
  | cons (hie, hies) => begin
      if hiexp_is_value hie then hiexplst_is_value hies else false
    end (* end of [cons] *)
  | nil () => true
end // end of [hiexplst_is_value]

fun labhiexplst_is_value
  (lhies: labhiexplst): bool = begin
  case+ lhies of
  | LABHIEXPLSTcons (_, hie, lhies) => begin
      if hiexp_is_value hie then labhiexplst_is_value lhies else false
    end (* end of [LABHIEXPLSTcons] *)
  | LABHIEXPLSTnil () => true
end // end of [labhiexplst_is_value]

implement
hiexp_is_value
  (hie0) = case+ hie0.hiexp_node of
  | HIEbool _ => true
  | HIEchar _ => true
  | HIEcon (_, _, hies) => hiexplst_is_value hies
  | HIEcst _ => true
  | HIEempty _ => true
  | HIEfix (_, _, hie) => hiexp_is_value hie
  | HIEfloat _ => true
  | HIElam _ => true
  | HIElaminit _ => true
  | HIElst (_, _, hies) => hiexplst_is_value hies
  | HIEint _ => true
  | HIErec (_, _, lhies) => labhiexplst_is_value lhies
  | HIEseq hies => hiexplst_is_value hies
  | HIEstring _ => true
  | HIEtmpcst _ => true
  | HIEtmpvar _ => true
  | HIEvar d2v => begin
      if d2var_get_isfix d2v then false else true
    end // end of [HIEvar]
  | _ => false
// end of [hiexp_is_value]

(* ****** ****** *)

fn hiclau_is_bool_fst
  (hicl: hiclau): Option_vt @(bool, hiexp) = begin
  case+ hicl.hiclau_pat of
  | cons (hip, nil ()) => begin case+ hip.hipat_node of
    | HIPbool b => begin case+ hicl.hiclau_gua of
      | cons _ => None_vt () | nil _ => Some_vt @(b, hicl.hiclau_exp)
      end (* end of [HIPbool] *)
    | _ => None_vt ()
    end (* end of [cons (_, nil)] *)
  | _ => None_vt () // end of [_]
end // end of [hiclau_is_bool_fst]

fn hiclau_is_bool_snd
  (hicl: hiclau): Option_vt hiexp = begin
  case+ hicl.hiclau_pat of
  | cons (hip, nil ()) => begin case+ hicl.hiclau_gua of
    | cons _ => None_vt () | nil _ => Some_vt (hicl.hiclau_exp)
    end (* end of [cons] *)
  | _ => None_vt ()
end // end of [hiclau_is_bool_snd]

implement
hiexp_caseof_if
  (loc0, hit0, knd, hies, hicls) = let
  macdef hiexp_caseof_mac () =
    hiexp_caseof (loc0, hit0, knd, hies, hicls)
  // end of [macdef]
in
  case+ hies of
  | cons (hie, nil ()) => begin case+ hicls of
    | cons (hicl1, cons (hicl2, nil ())) => begin
      case+ hiclau_is_bool_fst hicl1 of
      | ~Some_vt bhie1 => begin
        case+ hiclau_is_bool_snd hicl2 of
        | ~Some_vt hie2 =>
            if bhie1.0 then begin
              hiexp_if (loc0, hit0, hie, bhie1.1, hie2)
            end else begin
              hiexp_if (loc0, hit0, hie, hie2, bhie1.1)
            end
        | ~None_vt () => hiexp_caseof_mac ()
        end
      | ~None_vt () => hiexp_caseof_mac ()
      end // end of [cons (_, cons (_, nil _))]
    | _ => hiexp_caseof_mac ()
    end // end of [cons (_, nil)]
  | _ => hiexp_caseof_mac () 
end // end of [hiexp_case_if]

(* ****** ****** *)

datatype hibind =
  | HIBINDnone
  | HIBINDsome_any of hiexp
  | HIBINDsome_emp of hiexp
  | HIBINDsome_var of (d2var_t, hiexp)

fn hidec_valdecs_is_singular (hid: hidec): hibind = let
(*
  val () = begin
    print "hidec_is_singular_var: entering"; print_newline ()
  end
*)
  fun aux (hie_def: hiexp, hip: hipat): hibind = let
(*
    val () = begin
      print "hidec_is_singular_var: hip = "; print hip; print_newline ()
    end
*)
  in
    case+ hip.hipat_node of
    | HIPany () => HIBINDsome_any hie_def
    | HIPempty () => HIBINDsome_emp (hie_def)
    | HIPvar (_(*refknd=0*), d2v) => HIBINDsome_var (d2v, hie_def)
    | HIPrec (knd, lhips, _(*hit_rec*)) when knd = 0 (*flt*) => begin
      case+ lhips of
      | LABHIPATLSTcons (_(*lab*), hip, LABHIPATLSTnil ()) =>
          aux (hie_def, hip)
      | _ => HIBINDnone ()
      end // end of [HIPrec]
    | _ => HIBINDnone ()
  end // end of [aux]
in
  case+ hid.hidec_node of
  | HIDvaldecs (_, valdecs) => begin case+ valdecs of
    | cons (valdec, nil ()) => aux (valdec.hivaldec_def, valdec.hivaldec_pat)
    | _ => HIBINDnone ()
    end
  | _ => HIBINDnone ()
end // end of [hidec_valdecs_is_singular]

(* ****** ****** *)

datatype hiempvar =
  | HIEMPVARnone | HIEMPVARsome_emp | HIEMPVARsome_var of d2var_t
// end of [hiempvar]

fun hiexp_is_empvar
  (hie: hiexp): hiempvar =
  case+ hie.hiexp_node of
  | HIEempty () => HIEMPVARsome_emp
  | HIEvar d2v => HIEMPVARsome_var d2v
  | HIErec (knd, hit_rec, lhies) when knd = 0 (* flat *) => begin
    case+ lhies of
    | LABHIEXPLSTcons (_, hie, LABHIEXPLSTnil ()) => hiexp_is_empvar hie
    | _ => HIEMPVARnone ()
    end // end of [HIErec]
  | _ => HIEMPVARnone ()
// end of [hiexp_is_empvar]

implement
hiexp_let_simplify
  (loc0, hit0, hids0, hie0) = let
  macdef hie0_let () = hiexp_let (loc0, hit0, hids0, hie0)
  fun aux_simplify
    (hid0: hidec, hids: hideclst, hie0: hiexp)
    :<cloptr1> hiexp = let
//
    fun aux_init_main
      (hid0: hidec, hids: hideclst, res: &hideclst? >> hideclst)
      : void = begin case+ hids of
      | cons (hid, hids) => let
          val () = (res := cons {hidec} {0} (hid0, ?))
          val+ cons (_, !res_nxt) = res
        in
          aux_init_main (hid, hids, !res_nxt); fold@ res
        end
      | nil () => (res := nil ())
    end // end of [aux_init_main]
//
    fun aux_init (
      hid0: hidec, hids: hideclst
    ) : hideclst = res where {
      var res: hideclst // uninitialized
      val () = aux_init_main (hid0, hids, res)
    } // end of [aux_init]
//
    fun aux_last (hid0: hidec, hids: hideclst): hidec = begin
      case+ hids of
      | cons (hid, hids) => aux_last (hid, hids) | nil () => hid0
    end // end of [aux_last]
//
  in
    case+ hiexp_is_empvar hie0 of
    | HIEMPVARsome_emp () => let
        val hid_last = aux_last (hid0, hids)
        val bind = hidec_valdecs_is_singular hid_last
      in
        case+ bind of
        | HIBINDsome_any hie1 => begin case+ 0 of
          | _ when hityp_is_void (hie1.hiexp_typ) => let
              val init = aux_init (hid0, hids)
            in
              hiexp_let (loc0, hit0, init, hie1)
            end
          | _ => hie0_let ()
          end // end of [HIBINDsome_any]
        | HIBINDsome_emp hie1 => let
            val init = aux_init (hid0, hids)
          in
            hiexp_let (loc0, hit0, init, hie1)
          end // end of [HIBINDsome_emp]
        | HIBINDsome_var (_, hie1) => begin case+ 0 of
          | _ when hityp_is_void (hie1.hiexp_typ) => let
              val init = aux_init (hid0, hids)
            in
              hiexp_let (loc0, hit0, init, hie1)
            end
          | _ => hie0_let ()
          end // end of [HIBINDsome_var]
        | HIBINDnone => hie0_let ()
      end // end of [HIEMPVARsome_emp]
    | HIEMPVARsome_var d2v2 => let
        val hid_last = aux_last (hid0, hids)
        val bind = hidec_valdecs_is_singular hid_last
      in
        case+ bind of
        | HIBINDsome_var (d2v1, hie1)
            when (eq_d2var_d2var (d2v1, d2v2)) => let
            val init = aux_init (hid0, hids)
          in
            hiexp_let (loc0, hit0, init, hie1)
          end
        | _ => hie0_let ()
      end // end of [HIEMPVARsome_var]
    | HIEMPVARnone () => hie0_let ()
  end // end of [aux_simplify]
in
  case+ hids0 of
  | cons (hid0, hids) => aux_simplify (hid0, hids, hie0)
  | nil () => hie0
end // end of [hiexp_let_simplify]

(* ****** ****** *)

local

assume hityp_t = hityp
assume hityplst_t = hityplst
assume hityplstlst_t = hityplstlst

in // in of [local]

implement hityp_encode (hit) = hit
implement hityp_decode (hit) = hit

implement hityplst_encode (hits) = hits
implement hityplst_decode (hits) = hits

implement hityplstlst_encode (hitss) = hitss
implement hityplstlst_decode (hitss) = hitss

(* ****** ****** *)

implement print_hityp_t (hit)=  print_hityp (hit)
implement prerr_hityp_t (hit)=  prerr_hityp (hit)

(* ****** ****** *)

implement
hityplst_is_nil (hits) = begin
  case+ hits of list_cons _ => false | list_nil () => true
end // end of [hityplst_is_nil]

implement
hityplst_is_cons (hits) = begin
  case+ hits of list_cons _ => true | list_nil () => false
end // end of [hityplst_is_cons]

implement
hityplstlst_is_nil (hitss) = begin
  case+ hitss of list_cons _ => false | list_nil () => true
end // end of [hityplstlst_is_nil]

implement
hityplstlst_is_cons (hitss) = begin
  case+ hitss of list_cons _ => true | list_nil () => false
end // end of [hityplstlst_is_cons]

(* ****** ****** *)

(*
// HX: this file must be loaded after [hityp_void] is defined
*)
implement hityp_t_ptr = hityp_ptr
implement hityp_t_void = hityp_void // so this file must be loaded
//
implement hityp_t_s2var (s2v) = hityp_s2var (s2v)
implement hityp_t_get_name (hit) = hit.hityp_name
//
implement hityp_t_is_void (hit) = hityp_is_void (hit)
implement hityp_t_fun_is_void (hit_fun) = hityp_fun_is_void (hit_fun) 
implement hityp_t_is_tyrecbox (hit_rec) = hityp_is_tyrecbox (hit_rec)
implement hityp_t_is_tyrecext (hit_rec) = hityp_is_tyrecext (hit_rec)
implement hityp_t_is_tyrecsin (hit_rec) = hityp_is_tyrecsin (hit_rec)

(* ****** ****** *)

fn hityp_name_get (hit: hityp) = let
  val HITNAM (knd, name) = hit.hityp_name
in
  case+ 0 of
  | _ when knd <= 0 => name (* flt_ext: ~1; flt: 0 *)
  | _ => name where {
      val HITNAM (_, name) = hityp_ptr.hityp_name
    } // end of [where]
  // end of [case]
end // end of [hityp_name_get]

implement
hityp_tyrec_make
  (recknd, lhits) = let
  val lnames = aux lhits where {
    fun aux (lhits: labhityplst): labstrlst = case+ lhits of
      | LABHITYPLSTcons (l, hit, lhits) => begin
          LABSTRLSTcons (l, hityp_name_get hit, aux lhits)
        end // end of [LABHITYPLSTcons]
      | LABHITYPLSTnil () => LABSTRLSTnil ()
  } // end of [where]
  val name_rec = typdefmap_find (TYPKEYrec lnames)
  val fltboxknd = (if recknd > 0 then 1 else 0): int
  val hit_rec = hityp_tyrec (fltboxknd, name_rec, lhits)
in
  hityp_encode (hit_rec)
end // end of [hityp_tyrec_make]

implement
hityp_tysum_make
  (d2c, hits_arg) = begin
  case+ hits_arg of
  | list_cons _ => let
(*
      val () = begin
        print "hityp_tysum_make: d2c = "; print d2c; print_newline ();
        print "hityp_tysum_make: hits_arg = "; print hits_arg; print_newline ()
      end // end of [val]
*)
      val names_arg = $Lst.list_map_fun (hits_arg, hityp_name_get)
      val s2c = d2con_get_scst (d2c)
      val tag = (case+ d2c of
        | _ when s2cst_is_singular s2c => 0
        | _ when s2cst_is_listlike s2c => 0
        | _ when d2con_is_exn d2c => ~1
        | _ => 1
      ) : int // end of [val]
      val name_sum = typdefmap_find (TYPKEYsum (tag, names_arg))
      val hit_sum = hityp_tysum (name_sum, d2c, hits_arg)
    in
      hityp_encode (hit_sum)
    end // end of [list_cons]
  | list_nil () => begin
      hityp_encode (hityp_tysum_ptr)
    end // end of [list_nil]
end // end of [hityp_tysum_make]

(* ****** ****** *)

fun hityp_normalize_flag
  (hit0: hityp, flag: &int): hityp = let
(*
  val () = begin
    print "hityp_normalize_flag: hit0 = "; print_hityp hit0; print_newline ()
  end // end of [val]
*)
  val hit0_new = case+ hit0.hityp_node of
  | HITfun (fc, hits_arg, hit_res) => let
      val flag0 = flag
      val hits_arg = hityplst_normalize_flag (hits_arg, flag)
      val hit_res = hityp_normalize_flag (hit_res, flag)
    in
      if flag > flag0 then hityp_fun (fc, hits_arg, hit_res) else hit0
    end // end of [HITfun]
  | HITtyrectemp (fltboxknd, lhits) => let
      val lhits = labhityplst_normalize_flag (lhits, flag)
    in
      flag := flag + 1; hityp_tyrec_make (fltboxknd, lhits)
    end // end of [HITtyrectemp]
  | HITtysumtemp (d2c, hits_arg) => let
      val hits_arg = hityplst_normalize_flag (hits_arg, flag)
    in
      flag := flag + 1; hityp_tysum_make (d2c, hits_arg)
    end // end of [HITtysumtemp]
  | HITtyrecsin hit => let
      val flag0 = flag
      val hit = hityp_normalize_flag (hit, flag)
    in
      if flag > flag0 then hityp_tyrecsin hit else hit0
    end // end of [HITtyrecsin]
  | HITrefarg (refval, hit_arg) =>
      if refval = 0 then let // call-by-value
        val flag0 = flag
        val hit_arg = hityp_normalize_flag (hit_arg, flag)
      in
        if flag > flag0 then hityp_refarg (0, hit_arg) else hit0
      end else hit0
    // end of [HITrefarg]
  | HITs2var s2v => hit0_new where {
      val hit0_new = (
        case+ hityp_s2var_normalize (s2v) of
        | ~Some_vt hit => (flag := flag + 1; hit) | ~None_vt () => hit0
      ) : hityp
    } // end of [HITs2var]
  | _ => hit0 // end of [_]
(*
  val () = begin
    print "hityp_normalize: hit0_new = "; print_hityp hit0_new; print_newline ()
  end // end of [val]
*)
in
  hit0_new
end // end of [hityp_normalize_flag]

and hityplst_normalize_flag (
  hits0: hityplst, flag: &int
) : hityplst = begin case+ hits0 of
  | list_cons (hit, hits) => let
      val flag0 = flag
      val hit = hityp_normalize_flag (hit, flag)
      val hits = hityplst_normalize_flag (hits, flag)
    in
      if flag > flag0 then list_cons (hit, hits) else hits0
    end
  | list_nil () => list_nil ()
end // end of [hityplst_normalize_flag]
  
and labhityplst_normalize_flag (
  lhits0: labhityplst, flag: &int
) : labhityplst = begin case+ lhits0 of
  | LABHITYPLSTcons (l, hit, lhits) => let
      val flag0 = flag
      val hit = hityp_normalize_flag (hit, flag)
      val lhits = labhityplst_normalize_flag (lhits, flag)
    in
      if flag > flag0 then LABHITYPLSTcons (l, hit, lhits) else lhits0
    end // end of [LABHITYPLSTcons]
  | LABHITYPLSTnil () => LABHITYPLSTnil ()
end // end of [labhityplst_normalize_flag]

(* ****** ****** *)

implement
hityp_normalize (hit) = let
  var flag: int = 0 in hityp_normalize_flag (hit, flag)
end // end of [hityp_normalize]

implement
hityplst_normalize (hits) =
  $Lst.list_map_fun (hits, hityp_normalize)
// end of [hityplst_normalize]

implement
hityplstlst_normalize (hitss) =
  $Lst.list_map_fun (hitss, hityplst_normalize)
// end of [hityplstlst_normalize]

end // end of [local]

(* ****** ****** *)

implement
d2cst_get_hityp_some
  (d2c) = let
  val hitopt = d2cst_get_hityp (d2c)
in
  case+ hitopt of
  | Some hit => hit
  | None () => let
      val () = prerr_interror ()
      val () = prerr ": d2cst_hityp_get_some: d2c = "
      val () = prerr_d2cst (d2c)
      val () = prerr_newline ()
    in
      $Err.abort {hityp_t} ()
    end // end of [None]
end // end of [d2cst_hityp_get_some]

(* ****** ****** *)

local

typedef tmpdef = '{
  tmpdef_arg= s2qualst, tmpdef_exp= hiexp
} // end of [tmpdef]

assume tmpdef_t = tmpdef

fn _tmpdef_make
  (arg: s2qualst, hie: hiexp)
: tmpdef = '{
  tmpdef_arg= arg, tmpdef_exp= hie
} // end of [tmpdef_make]

in // in of [local]

implement tmpdef_make
  (arg, hie) = _tmpdef_make (arg, hie)
// end of [tmpdef_make]

implement tmpdef_get_arg (def) = def.tmpdef_arg
implement tmpdef_get_exp (def) = def.tmpdef_exp

end // end of [local]

(* ****** ****** *)

local

viewtypedef
tmpcstmap = $Map.map_vt (d2cst_t, tmpdef_t)

fn tmpcstmap_nil ()
  : tmpcstmap = $Map.map_make (compare_d2cst_d2cst)
// end of [tmpcstmap_nil]

val the_tmpcstmap =
  ref_make_elt<tmpcstmap> (tmpcstmap_nil ())
// end of [val]

in // in of [local]

implement
tmpcstmap_add
  (d2c, decarg, hie_def) = let
  val tmpdef = tmpdef_make (decarg, hie_def)
  val (vbox pf | p) = ref_get_view_ptr (the_tmpcstmap)
in
  $Map.map_insert (!p, d2c, tmpdef)
end // end of [tmpcstmap_add]

implement
tmpcstmap_find (d2c) = let
  val (vbox pf | p) = ref_get_view_ptr (the_tmpcstmap)
in
  $Map.map_search (!p, d2c)
end // end of [tmpcstmap_find]

end // end of [local]

(* ****** ****** *)

local

viewtypedef
tmpvarmap = $Map.map_vt (d2var_t, tmpdef_t)

fn tmpvarmap_nil ()
  : tmpvarmap = $Map.map_make (compare_d2var_d2var)
// end of [tmpvarmap_nil]

val the_tmpvarmap =
  ref_make_elt<tmpvarmap> (tmpvarmap_nil ())
// end of [val]

in // in of [local]

implement
tmpvarmap_add (
  d2v, decarg, hie_def
) = let
  val tmpdef = tmpdef_make (decarg, hie_def)
  val (vbox pf | p) = ref_get_view_ptr (the_tmpvarmap)
in
  $Map.map_insert (!p, d2v, tmpdef)
end // end of [tmpvarmap_add]

implement
tmpvarmap_find (d2v) = let
  val (vbox pf | p) = ref_get_view_ptr (the_tmpvarmap)
in
  $Map.map_search (!p, d2v)
end // end of [tmpvarmap_find]

end // end of [local]

(* ****** ****** *)

(* end of [ats_hiexp_util.dats] *)
