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

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Lst = "ats_list.sats"
staload Stamp = "ats_stamp.sats"
macdef print_stamp = $Stamp.print_stamp

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

typedef
s2cst_struct = @{ (* builtin or abstract *)
  s2cst_sym= sym_t // the name
(*
// HX: abstract type is associated with a filename
*)
, s2cst_fil= Option (fil_t)
, s2cst_loc= loc_t // the location of introduction
, s2cst_srt= s2rt // the sort
, s2cst_isabs= Option (s2expopt) // is abstract?
, s2cst_iscon= bool // is constructive?
, s2cst_isrec= bool // is recursive?
, s2cst_isasp= bool // already assumed?
, s2cst_iscpy= s2cstopt // is a copy?
  // is list-like?
, s2cst_islst= Option @(d2con_t (*nil*), d2con_t (*cons*))
, s2cst_arilst= List int // arity list
  // variance: -1: contravarint; 0: invariant; 1: covarint
, s2cst_argvar= Option (List @(symopt_t, s2rt, int))
  // the associated dynamic constructors
, s2cst_conlst= Option (d2conlst)
, s2cst_def= s2expopt // definition
, s2cst_sup= s2cstlst // parents if any
, s2cst_supcls= s2explst // superclasses if any
, s2cst_sVarset= s2Varset_t // for occurrence checks
, s2cst_stamp= stamp_t // unique stamp
, s2cst_tag= int // tag >= 0 if associated with a datasort
} // end of [s2cst_struct]

(* ****** ****** *)

fun s2rt_arity_list
  (s2t: s2rt): List int = case+ s2t of
  | S2RTfun (s2ts, s2t) => begin
      list_cons ($Lst.list_length s2ts, s2rt_arity_list s2t)
    end // end of [S2RTfun]
  | _ => list_nil () // end of [_]
// end of [s2rt_arity_list]

(* ****** ****** *)

// implementing [s2cst_t]

local

assume s2cst_t = [l:addr] (vbox (s2cst_struct @ l) | ptr l)

in // in of [local]

implement s2cst_make (
  id, loc, s2t, isabs, iscon, isrec, isasp, islst, argvar, def
) = let

val stamp = $Stamp.s2cst_stamp_make ()
val (pf_gc, pf | p) = ptr_alloc_tsz {s2cst_struct} (sizeof<s2cst_struct>)
prval () = free_gc_elim {s2cst_struct?} (pf_gc)

val () = begin
p->s2cst_sym := id;
p->s2cst_fil := None ();
p->s2cst_loc := loc;
p->s2cst_srt := s2t;
p->s2cst_isabs := isabs;
p->s2cst_iscon := iscon;
p->s2cst_isrec := isrec;
p->s2cst_isasp := isasp;
p->s2cst_iscpy := S2CSTOPTnone ();
p->s2cst_islst := islst;
p->s2cst_arilst := s2rt_arity_list s2t;
p->s2cst_argvar := argvar;
p->s2cst_conlst := None ();
p->s2cst_def := def;
p->s2cst_sup := S2CSTLSTnil ();
p->s2cst_supcls := list_nil ();
p->s2cst_sVarset := s2Varset_nil;
p->s2cst_stamp := stamp;
p->s2cst_tag := (~1);
end // end of [val]

val (pfbox | ()) = vbox_make_view_ptr (pf | p)

in // in of [let]

(pfbox | p)

end // end of [s2cst_make]

(* ****** ****** *)

implement s2cst_get_sym (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_sym end

implement s2cst_get_fil (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_fil end
implement s2cst_set_fil (s2c, opt) =
  let val (vbox pf | p) = s2c in p->s2cst_fil := opt end

implement s2cst_get_loc (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_loc end

implement s2cst_get_srt (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_srt end

implement s2cst_get_isabs (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_isabs end

implement s2cst_get_iscon (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_iscon end

implement s2cst_get_isrec (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_isrec end

implement s2cst_get_isasp (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_isasp end

implement s2cst_set_isasp (s2c, isasp) =
  let val (vbox pf | p) = s2c in p->s2cst_isasp := isasp end

implement s2cst_get_iscpy (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_iscpy end

implement s2cst_set_iscpy (s2c, iscpy) =
  let val (vbox pf | p) = s2c in p->s2cst_iscpy := iscpy end

implement s2cst_get_islst (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_islst end

implement s2cst_set_islst (s2c, islst) =
  let val (vbox pf | p) = s2c in p->s2cst_islst := islst end

implement s2cst_get_arilst (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_arilst end

implement s2cst_get_argvar (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_argvar end

implement s2cst_get_conlst (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_conlst end

implement s2cst_set_conlst (s2c, od2cs) =
  let val (vbox pf | p) = s2c in p->s2cst_conlst := od2cs end

(* ****** ****** *)

implement s2cst_get_def (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_def end

implement s2cst_set_def (s2c, def) =
  let val (vbox pf | p) = s2c in p->s2cst_def := def end

(* ****** ****** *)

implement s2cst_get_sup (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_sup end
// end of [s2cst_sup_get]

implement s2cst_add_sup (s2c, sup) = let
  val (vbox pf | p) = s2c; val sups = p->s2cst_sup
in
  p->s2cst_sup := S2CSTLSTcons (sup, sups)
end // end of [s2cst_sup_add]

implement s2cst_get_supcls (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_supcls end

implement
s2cst_add_supcls (s2c, sup) = let
  val (vbox pf | p) = s2c; val sups = p->s2cst_supcls
in
  p->s2cst_supcls := list_cons (sup, sups)
end // end of [s2cst_supcls_add]

(* ****** ****** *)

implement s2cst_get_sVarset (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_sVarset end

implement s2cst_set_sVarset (s2c, sVs) =
  let val (vbox pf | p) = s2c in p->s2cst_sVarset := sVs end

implement s2cst_get_stamp (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_stamp end

implement s2cst_set_stamp (s2c, stamp) =
  let val (vbox pf | p) = s2c in p->s2cst_stamp := stamp end

implement s2cst_get_tag (s2c) =
  let val (vbox pf | p) = s2c in p->s2cst_tag end

implement s2cst_set_tag (s2c, tag) =
  let val (vbox pf | p) = s2c in p->s2cst_tag := tag end

(* ****** ****** *)

implement lt_s2cst_s2cst
  (s2c1, s2c2) = compare_s2cst_s2cst (s2c1, s2c2) < 0
implement lte_s2cst_s2cst
  (s2c1, s2c2) = compare_s2cst_s2cst (s2c1, s2c2) <= 0

implement eq_s2cst_s2cst
  (s2c1, s2c2) = compare_s2cst_s2cst (s2c1, s2c2) = 0
implement neq_s2cst_s2cst
  (s2c1, s2c2) = compare_s2cst_s2cst (s2c1, s2c2) <> 0

fn _compare_s2cst_s2cst
  (s2c1: s2cst_t, s2c2: s2cst_t): Sgn = let
  val stamp1 =
    let val (vbox pf1 | p1) = s2c1 in p1->s2cst_stamp end
  // end of [val]
  val stamp2 =
    let val (vbox pf2 | p2) = s2c2 in p2->s2cst_stamp end
  // end of [val]
in
  $Stamp.compare_stamp_stamp (stamp1, stamp2)
end // end of [_compare_s2cst_s2cst]

implement
compare_s2cst_s2cst (s2c1, s2c2) =
  $effmask_all ( _compare_s2cst_s2cst (s2c1, s2c2) )
// end of [compare_s2cst_s2cst]

(* ****** ****** *)

implement
s2cst_is_abstract (s2c) = let
  val (vbox pf | p) = s2c in
  case+ p->s2cst_isabs of Some _ => true | None _ => false
end // end of [s2cst_is_abstract]

implement
s2cst_is_data (s2c) = let
  val (vbox pf | p) = s2c in
  case+ p->s2cst_isabs of Some _ => false | None _ => p->s2cst_iscon
end // end of [s2cst_is_data]

implement
s2cst_is_eqsup (s2c1, s2c2) = let
  fun aux (s2c1: s2cst_t, stamp2: stamp_t): bool = let
    val stamp1 = begin
      let val (vbox pf1 | p1) = s2c1 in p1->s2cst_stamp end
    end // end of [val]
  in
    if $Stamp.eq_stamp_stamp (stamp1, stamp2) then true
    else let
      val sup = let val (vbox pf1 | p1) = s2c1 in p1->s2cst_sup end
    in
      case+ sup of
      | S2CSTLSTcons (s2c1, _) => aux (s2c1, stamp2) | S2CSTLSTnil () => false
    end // end of [if]
  end (* end of [aux] *)
  val stamp2 = begin
    let val (vbox pf2 | p2) = s2c2 in p2->s2cst_stamp end
  end (* end of [val] *)
in
  aux (s2c1, stamp2)
end // end of [s2cst_is_eqsup]

implement
s2cst_is_listlike (s2c) = let
  val islst = let val (vbox pf | p) = s2c in p->s2cst_islst end
in
  case+ islst of Some _ => true | None () => false
end // end of [s2cst_is_listlike]

implement
s2cst_is_singular (s2c) = let
  val od2cs = let val (vbox pf | p) = s2c in p->s2cst_conlst end
in
  case+ od2cs of
  | Some d2cs => begin case+ d2cs of
    | D2CONLSTcons (_, D2CONLSTnil ()) => true | _ => false
    end // end of [Some]
  | None () => false // end of [None]
end // end of [s2cst_is_singular]

end // end of [local] (for assuming s2cst_t)

(* ****** ****** *)

implement
s2cst_make_dat (
  id, loc, os2ts_arg, s2t_res, argvar
) = let
  val s2t = (
    case+ os2ts_arg of
    | Some s2ts_arg => s2rt_fun (s2ts_arg, s2t_res)
    | None () => s2t_res
  ) : s2rt // end of [val]
in
  s2cst_make (
    id // name
  , loc // the location of declaration
  , s2t // sort
  , None () // isabs
  , true // iscon
  , false // isrec
  , false // isasp
  , None () // islst
  , argvar // argumnet variance
  , None () // definition
  ) // end of [s2cst_make]
end // end of [s2cst_make_dat]

(* ****** ****** *)

implement
s2cst_make_cls
  (id, loc, s2vss) = let
  val s2t = aux (s2vss, s2rt_cls) where {
    fun aux (
        s2vss: s2varlstlst, res: s2rt
      ) : s2rt = begin case+ s2vss of
      | list_cons (s2vs, s2vss) => let
          val res = aux (s2vss, res)
          val s2ts_arg = $Lst.list_map_fun (s2vs, s2var_get_srt)
        in
          s2rt_fun (s2ts_arg, res)
        end // end of [list_cons]
       | list_nil () => res
    end // end of [aux]
  } // end of [val]
in
  s2cst_make (
    id // name
  , loc // the location of declaration
  , s2t // sort
  , None () // isabs
  , true // iscon
  , false // isrec
  , false // isasp
  , None () // islst
  , None () // argumnet variance
  , None () // definition
  ) // end of [s2cst_make]
end // end of [s2cst_make_cls]

(* ****** ****** *)

implement
fprint_s2cst (pf_out | out, s2c) =
  $Sym.fprint_symbol (pf_out | out, s2cst_get_sym s2c)
// end of [fprint_s2cst]

implement print_s2cst (s2c) = print_mac (fprint_s2cst, s2c)
implement prerr_s2cst (s2c) = prerr_mac (fprint_s2cst, s2c)

(* ****** ****** *)

implement
fprint_s2cstlst
  {m} (pf | out, s2cs) = let
  fun aux (
    out: &FILE m, s2cs: s2cstlst, i: int
  ) : void =
    case+ s2cs of
    | S2CSTLSTcons (s2c, s2cs) => let
        val () = if i > 0 then
          fprint1_string (pf | out, ", ")
        // end of [val]
        val () = fprint_s2cst (pf | out, s2c)
      in
        aux (out, s2cs, i+1)
      end // end of [S2CSTLSTcons]
    | S2CSTLSTnil () => () // end of [S2CSTLSTnil]
  // end of [aux]
in
  aux (out, s2cs, 0)
end // end of [fprint_s2cstlst]

implement print_s2cstlst (s2cs) = print_mac (fprint_s2cstlst, s2cs)
implement prerr_s2cstlst (s2cs) = prerr_mac (fprint_s2cstlst, s2cs)

(* ****** ****** *)

(* end of [ats_staexp2_scst.dats] *)
