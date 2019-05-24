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
// Time: August 2007

(* ****** ****** *)

(* ats_effect: for handing effects *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_effect.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

typedef t0kn = $Syn.t0kn
typedef funclo = $Syn.funclo
typedef funcloopt = $Syn.funcloopt
typedef loc_t = $Loc.location_t

(* ****** ****** *)

overload prerr with $Loc.prerr_location

(* ****** ****** *)

typedef effect = int
assume $Syn.effect_t = effect
extern typedef "atsopt_effect_t" = effect
//
// HX the maximal effect number
//
#define MAX_EFFECT_NUMBER 4
// #assert (MAX_EFFECT_NUMBER < __WORDSIZE)

macdef EFFexn = 1 // exception
macdef EFFntm = 2 // nontermination
macdef EFFref = 3 // reference
macdef EFFwrt = 4 // write // not supported

implement effect_exn = EFFexn
implement effect_ntm = EFFntm
implement effect_ref = EFFref
(*
implement effect_wrt = EFFwrt // not supported
*)
implement effectlst_all = '[ EFFexn, EFFntm, EFFref ]

implement eq_effect_effect
  (eff1, eff2) = eq_int_int (eff1, eff2)
// end of [eq_effect_effect]

implement
fprint_effect
  (pf | out, eff) = begin
  if eq_int_int (eff, EFFexn) then
    fprint1_string (pf | out, "exn")
  else if eq_int_int (eff, EFFntm) then
    fprint1_string (pf | out, "ntm")
  else if eq_int_int (eff, EFFref) then
    fprint1_string (pf | out, "ref")
  else begin
    fprint1_string (pf | out, "eff(");
    fprint1_int (pf | out, eff);
    fprint1_string (pf | out, ")")
  end (* end of [if] *)
end // end of [fprint_effect]

implement
fprint_effectlst
  {m} (pf | out, effs) = let
  fun aux (i: int, out: &FILE m, effs: effectlst): void =
    case+ effs of
    | list_cons (eff, effs) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_effect (pf | out, eff); aux (i+1, out, effs)
      end // end of [list_cons]
    | list_nil () => () // end of [list_nil]
  // end of [aux]
in
  aux (0, out, effs)
end // end of [fprint_effectlst]

(* ****** ****** *)

implement print_effect (eff) = print_mac (fprint_effect, eff)
implement prerr_effect (eff) = prerr_mac (fprint_effect, eff)

(* ****** ****** *)

typedef effset = uint

assume effset_t = effset
extern typedef "atsopt_effset_t" = effset

macdef effset_exn = 0x1 // exception
macdef effset_ntm = 0x2 // nontermination
macdef effset_ref = 0x4 // reference
macdef effset_wrt = 0x8 // write effect (* program *)

implement effset_all = uint_of ((1 << MAX_EFFECT_NUMBER) - 1)
implement effset_nil = uint_of_int 0 // 0U

implement eq_effset_effset (efs1, efs2) = eq_uint_uint (efs1, efs2)

%{

#define MAX_EFFECT_NUMBER 4

#ifdef __WORDSIZE

#if (MAX_EFFECT_NUMBER > __WORDSIZE)
#error "MAX_EFFECT_NUMBER is too large!"
#endif

#endif

ats_void_type
atsopt_fprint_effset (
  ats_ptr_type out, atsopt_effset_t effs
) {
  int i, n ;
  i = 1 ; n = 0 ;
  while (i <= MAX_EFFECT_NUMBER) {
    if (effs & 0x1) {
      if (n > 0) fprintf ((FILE *)out, ",");
      atsopt_fprint_effect (out, i) ; ++n ;
    }
    ++i ; effs >>= 1 ;
  }
  return ;
} /* end of [atsopt_fprint_effset] */

%} // end of [%{]

(* ****** ****** *)

%{

atsopt_effset_t
atsopt_effset_add (
  atsopt_effset_t efs, atsopt_effect_t eff
) {
  unsigned int i = 1 ;
  while (eff > 1) { i <<= 1; --eff ; }
  return (efs | i) ;
} // end of [atsopt_effset_add]

atsopt_effset_t
atsopt_effset_del (
  atsopt_effset_t efs, atsopt_effect_t eff
) {
  unsigned int i = 1 ;
  while (eff > 1) { i <<= 1; --eff ; }
  return (efs & ~i) ;
} // end of [atsopt_effset_del]

ats_bool_type
atsopt_effset_contain (
  atsopt_effset_t efs, atsopt_effect_t eff
) {
  unsigned int i = 1 ;
  while (eff > 1) { i <<= 1; --eff ; }
  return (efs & i ? ats_true_bool : ats_false_bool) ;
} // end of [atsopt_effset_contain]

atsopt_effset_t
atsopt_effset_union (
  atsopt_effset_t efs1, atsopt_effset_t efs2
) {
  return (efs1 | efs2) ;
} // end of [atsopt_effset_union]

ats_bool_type
atsopt_effset_subset (
  atsopt_effset_t efs1, atsopt_effset_t efs2
) {
  return (efs1 & ~efs2 ? ats_false_bool : ats_true_bool) ;
} // end of [atsopt_effset_subset]

%} // end of [%{]

(* ****** ****** *)

implement
$Syn.d0exp_effmask_all (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask effectlst_all
} // end of [d0exp_effmask_all]

implement
$Syn.d0exp_effmask_exn (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask '[effect_exn]
} // end of [d0exp_effmask_exn]

implement
$Syn.d0exp_effmask_ntm (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask '[effect_ntm]
} // end of [d0exp_effmask_ntm]

implement
$Syn.d0exp_effmask_ref (t: t0kn) = '{
  d0exp_loc= t.t0kn_loc, d0exp_node= $Syn.D0Eeffmask '[effect_ref]
} // end of [d0exp_effmask_ref]

(* ****** ****** *)

val effvars_nil: effvarlst = nil ()

fun fprint_effvarlst
  {m:file_mode} (
    pf: file_mode_lte (m,w)
  | out: &FILE m
  , evs: effvarlst
  ) : void = let
  fun aux (out: &FILE m, i: int, evs: effvarlst): void =
    case+ evs of
    | cons (ev, evs) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        $Syn.fprint_i0de (pf | out, ev); aux (out, i+1, evs)
      end // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, 0, evs)
end // end of [fprint_effvarlst]

implement
fprint_effcst
  (pf | out, efc) = begin case+ efc of
  | EFFCSTall () => fprint1_string (pf | out, "all")
  | EFFCSTnil () => fprint1_string (pf | out, "nil")
  | EFFCSTset (es, evs) => begin
      fprint1_string (pf | out, "set(");
      fprint_effset (pf | out, es);
      fprint1_string (pf | out, "; ");
      fprint_effvarlst (pf | out, evs);
      fprint1_string (pf | out, ")")
    end // end of [EFFCSTset]
end // end of [fprint_effcst]

(* ****** ****** *)

implement
print_effcst (efc) = print_mac (fprint_effcst, efc)
implement
prerr_effcst (efc) = prerr_mac (fprint_effcst, efc)

(* ****** ****** *)

implement effcst_contain (efc, eff) = begin
  case+ efc of
  | EFFCSTall () => true
  | EFFCSTnil () => false
  | EFFCSTset (efs, evs)  => effset_contain (efs, eff)
end // end of [effcst_contain]

implement effcst_contain_ntm efc = effcst_contain (efc, EFFntm)

(* ****** ****** *)

fn name_is_emp (name: string): bool = name = "0"

fn name_is_all (name: string): bool = name = "1"

fn name_is_exn (name: string): bool =
  if name = "exn" then true else name = "exception"

fn name_is_exnref (name: string): bool = name = "exnref"

fn name_is_ntm (name: string): bool =
  if name = "ntm" then true else name = "nonterm"

fn name_is_ref (name:string): bool =
  if name = "ref" then true else name = "reference"

fn name_is_term (name: string): bool = name = "term"

(*
fn name_is_wrt (name: string): bool =
  if name = "wrt" then true else name = "write"
*)

//
// HX-2010-07-31: !laz = 1,~ref
//
fn name_is_lazy (name: string): bool = name = "laz"

(* ****** ****** *)

local

fn loop_err (loc: loc_t, name: string): void = begin
  $Loc.prerr_location loc; prerr ": error(1)";
  prerr ": unrecognized effect constant: ["; prerr name; prerr "]";
  prerr_newline ();
  $Err.abort ()
end // end of [loop_err]

fun loop (
    ofc: &funcloopt
  , lin: &int
  , prf: &int
  , efs: &effset
  , evs: &effvarlst
  , tags: $Syn.e0fftaglst
  ) : void = begin case+ tags of
  | cons (tag, tags) => let
      val () = case+ tag.e0fftag_node of
      | $Syn.E0FFTAGvar ev => evs := cons (ev, evs)
//
      | $Syn.E0FFTAGcst (isneg, name)
          when name_is_all name => begin
          evs := effvars_nil;
          if isneg > 0 then efs := effset_nil else efs := effset_all
        end // end of [E0FFTAGcst when ...]
      | $Syn.E0FFTAGcst (isneg, name)
          when name_is_emp name => begin
          evs := effvars_nil;
          if isneg > 0 then efs := effset_all else efs := effset_nil
        end // end of [E0FFTAGcst when ...]
      | $Syn.E0FFTAGcst (isneg, name)
          when name_is_lazy name => begin
          evs := effvars_nil;
          if isneg > 0 then
            efs := effset_add (effset_nil, EFFref) // HX: a pathological case
          else
            efs := effset_del (effset_all, EFFref) // HX: !laz = 1,~ref
          // end of [if]
        end // end of [E0FFTAGcst when ...]
//
      | $Syn.E0FFTAGcst (isneg, name) => begin case+ name of
        | _ when name_is_exn name => begin
            if isneg > 0 then
              efs := effset_del (efs, EFFexn)
            else
              efs := effset_add (efs, EFFexn)
            // end of [if]
          end // end of [_ when ...]
        | _ when name_is_exnref name => begin
            if isneg > 0 then
              efs := effset_del (effset_del (efs, EFFexn), EFFref)
            else
              efs := effset_add (effset_add (efs, EFFexn), EFFref)
            // end of [if]
          end // end of [_ when ...]
        | _ when name_is_ntm name => begin
            if isneg > 0 then
              efs := effset_del (efs, EFFntm)
            else
              efs := effset_add (efs, EFFntm)
            // end of [if]
          end // end of [_ when ...]
        | _ when name_is_term name => begin
            if isneg > 0 then
              efs := effset_add (efs, EFFntm)
            else
              efs := effset_del (efs, EFFntm)
            // end of [if]
          end // end of [_ when ...]
        | _ when name_is_ref name => begin
            if isneg > 0 then
              efs := effset_del (efs, EFFref)
            else
              efs := effset_add (efs, EFFref)
            // end of [if]
          end // end of [_ when ...]
        | _ => loop_err (tag.e0fftag_loc, name)
        end // end of [E0FFTAGcst]
//
      | $Syn.E0FFTAGprf () => prf := 1
//
      | $Syn.E0FFTAGlin
          (i(*nil/all*)) => let
          val () = lin := 1 // linearity
        in
          if i > 0 then (efs := effset_all; evs := effvars_nil)
        end // end of [E0FFTAGlin]
//
      | $Syn.E0FFTAGfun
          (uln, i(*nil/all*)) => let
          val () = if (uln >= 0) then lin := uln
          val () = ofc := Some ($Syn.FUNCLOfun ())
        in
          if i > 0 then (efs := effset_all; evs := effvars_nil)
        end // end of [E0FFTAGfun]
//
      | $Syn.E0FFTAGclo
          (uln, knd, i) => let
          // knd : 1/~1:ptr/ref; i : nil/all
          val () = if (uln >= 0) then lin := uln
          val () = ofc := Some ($Syn.FUNCLOclo (knd))
        in
          if i > 0 then (efs := effset_all; evs := effvars_nil)
        end // end of [E0FFTAGclo]
//
    in
      loop (ofc, lin, prf, efs, evs, tags)
    end // end of [let] // end of [cons]
  | nil () => () // end of [nil]
end // end of [loop]

in // in of [local]

implement
e0fftaglst_tr (tags) = let
  var ofc: funcloopt = None()
  var lin: int = 0 and prf: int = 0
  var efs: effset = effset_nil and evs: effvarlst = effvars_nil
  val () = loop (ofc, lin, prf, efs, evs, tags)
  val efc = (case+ 0 of
    | _ when eq_effset_effset (efs, effset_all) => EFFCSTall ()
    | _ when eq_effset_effset (efs, effset_nil) => begin
        case+ evs of nil () => EFFCSTnil () | _ => EFFCSTset (efs, evs)
      end // end of [_ when ...]
    | _ => EFFCSTset (efs, evs)
  ) : effcst
in
  @(ofc, lin, prf, efc)
end // end of [e0fftaglst_tr]

end // end of [local]

(* ****** ****** *)

(* end of [ats_effect.dats] *)
