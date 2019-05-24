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
// Time: November 2007
//
(* ****** ****** *)

(* The second translation resolves binding as well as sort assignment *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

#define nil list_nil; #define cons list_cons; #define :: list_cons

(* ****** ****** *)

overload < with $Sym.lt_symbol_symbol
overload <= with $Sym.lte_symbol_symbol

(* ****** ****** *)

fn prerr_interror () = prerr "INTERNAL ERROR (ats_dynexp2)"

(* ****** ****** *)

implement
d2sym_make (loc, q, id, d2is) = '{
  d2sym_loc= loc, d2sym_qua= q, d2sym_sym= id, d2sym_itm= d2is
} // end of [d2sym_make]

(* ****** ****** *)

extern val s2varlstord_nil: s2varlstord_t
extern val d2varlstord_nil: d2varlstord_t

extern fun s2varlstord_sing (s2v: s2var_t): s2varlstord_t
extern fun d2varlstord_sing (d2v: d2var_t): d2varlstord_t

extern fun s2varlstord_add
  (s2vs0: s2varlstord_t, s2v: s2var_t): s2varlstord_t

extern fun s2varlstord_addlst
  (s2vs0: s2varlstord_t, s2vs: s2varlst): s2varlstord_t

extern fun d2varlstord_add
  (d2vs0: d2varlstord_t, d2v: d2var_t): d2varlstord_t

extern fun s2varlstord_union
  (s2vs1: s2varlstord_t, s2vs2: s2varlstord_t): s2varlstord_t

extern fun d2varlstord_union
  (d2vs1: d2varlstord_t, d2vs2: d2varlstord_t): d2varlstord_t

(* ****** ****** *)

local

assume s2varlstord_t = s2varlst
assume d2varlstord_t = d2varlst

(* ****** ****** *)

fn s2var_sym_lt
  (s2v1: s2var_t, s2v2: s2var_t): bool =
  s2var_get_sym s2v1 < s2var_get_sym s2v2

fn s2var_sym_lte
  (s2v1: s2var_t, s2v2: s2var_t): bool =
  s2var_get_sym s2v1 <= s2var_get_sym s2v2

fn d2var_sym_lt
  (d2v1: d2var_t, d2v2: d2var_t): bool =
  d2var_get_sym d2v1 < d2var_get_sym d2v2

fn d2var_sym_lte
  (d2v1: d2var_t, d2v2: d2var_t): bool =
  d2var_get_sym d2v1 <= d2var_get_sym d2v2

(* ****** ****** *)

fn s2var_errmsg (loc: loc_t, s2v: s2var_t): void = begin
  $Loc.prerr_location loc; prerr ": error(2)";
  prerr ": the pattern contains repeated occurrences of the static variable [";
  prerr s2v;
  prerr "].";
  prerr_newline ();
end // end of [s2var_errmsg]

fn d2var_errmsg (loc: loc_t, d2v: d2var_t): void = begin
  $Loc.prerr_location loc; prerr ": error(2)";
  prerr ": the pattern contains repeated occurrences of the dynamic variable [";
  prerr d2v;
  prerr "].";
  prerr_newline ();
end // end of [d2var_errmsg]

in // in of [local]

implement s2varlstord_nil = nil ()
implement d2varlstord_nil = nil ()

implement s2varlstord_sing (s2v) = cons (s2v, nil ())
implement d2varlstord_sing (d2v) = cons (d2v, nil ())

implement s2varlst_of_s2varlstord (s2vs) = s2vs
implement d2varlst_of_d2varlstord (d2vs) = d2vs

implement
s2varlstord_add (s2vs0, s2v0) = begin
  case+ s2vs0 of
  | cons (s2v, s2vs) => begin
      if s2var_sym_lte (s2v0, s2v) then begin
        cons (s2v0, s2vs0)
      end else begin
        cons (s2v, s2varlstord_add (s2vs, s2v0))
      end // end of [if]
    end (* end of [cons] *)
  | nil () => cons (s2v0, nil ()) 
end (* end of [s2varlstord_add] *)

implement
s2varlstord_addlst (s2vs0, s2vs) = begin
  case+ s2vs of
  | cons (s2v, s2vs) => begin
      s2varlstord_addlst (s2varlstord_add (s2vs0, s2v), s2vs)
    end // end of [cons]
  | nil () => s2vs0
end (* end of [s2varlstord_addlst] *)

implement
d2varlstord_add (d2vs0, d2v0) = begin
  case+ d2vs0 of
  | cons (d2v, d2vs) => begin
      if d2var_sym_lte (d2v0, d2v) then begin
        cons (d2v0, d2vs0)
      end else begin
        cons (d2v, d2varlstord_add (d2vs, d2v0))
      end // end of [if]
    end (* end of [cons] *)
  | nil () => cons (d2v0, nil ())
end (* end of [d2varlstord_add] *)

implement
s2varlstord_union (s2vs10, s2vs20) = begin
  case+ s2vs10 of
  | s2v1 :: s2vs1 => begin case+ s2vs20 of
    | s2v2 :: s2vs2 => begin
        if s2var_sym_lte (s2v1, s2v2) then begin
          cons (s2v1, s2varlstord_union (s2vs1, s2vs20))
        end else begin
          cons (s2v2, s2varlstord_union (s2vs10, s2vs2))
        end // end of [if]
      end (* end of [::] *)
    | nil () => s2vs10
    end (* end of [::] *)
  | nil () => s2vs20 // end of [nil]
end // end of [s2varlstord_union]

implement
d2varlstord_union (d2vs10, d2vs20) = begin
  case+ d2vs10 of
  | d2v1 :: d2vs1 => begin case+ d2vs20 of
    | d2v2 :: d2vs2 => begin
        if d2var_sym_lte (d2v1, d2v2) then begin
          cons (d2v1, d2varlstord_union (d2vs1, d2vs20))
        end else begin
          cons (d2v2, d2varlstord_union (d2vs10, d2vs2))
        end // end of [if]
      end (* end of [::] *)
    | nil () => d2vs10 // end of [nil]
    end (* end of [::] *)
  | nil () => d2vs20
end // end of [d2varlstord_union]

(* ****** ****** *)

implement
s2varlstord_linearity_test (loc, s2vs) = let
  fun aux (
      loc: loc_t, s2v0: s2var_t, s2vs: s2varlst, err: int
    ) : int =
    case+ s2vs of
    | cons (s2v, s2vs) => begin
        if s2var_sym_lt (s2v0, s2v) then begin
          aux (loc, s2v, s2vs, err)
        end else begin
          s2var_errmsg (loc, s2v0); aux (loc, s2v, s2vs, err+1)
        end // end of [if]
      end (* end of [cons] *)
    | nil () => err // end of [nil]
  // end of [aux]
in
  case+ s2vs of
  | cons (s2v, s2vs) => begin
      if aux (loc, s2v, s2vs, 0) > 0 then $Err.abort {void} ()
    end // end of [cons]
  | nil () => () // end of [nil]
end (* end of [s2varlstord_linearity_test] *)

implement
d2varlstord_linearity_test (loc, d2vs) = let
  fun aux
    (loc: loc_t, d2v0: d2var_t, d2vs: d2varlst, err: int): int =
    case+ d2vs of
    | cons (d2v, d2vs) => begin
        if d2var_sym_lt (d2v0, d2v) then begin
          aux (loc, d2v, d2vs, err)
        end else begin
          d2var_errmsg (loc, d2v0); aux (loc, d2v, d2vs, err+1)
        end // end of [if]
      end (* end of [cons] *)
    | nil () => err // end of [nil]
  // end of [aux]
in
  case+ d2vs of
  | cons (d2v, d2vs) => begin
      if aux (loc, d2v, d2vs, 0) > 0 then $Err.abort {void} ()
    end // end of [cons]
  | nil () => () // end of [nil]
end (* end of [d2varlstord_linearity_test] *)

end // end of [local]

(* ****** ****** *)

implement
p2atlst_svs_union (p2ts) = let
  fun loop (p2ts: p2atlst, ans: s2varlstord_t): s2varlstord_t =
    case+ p2ts of
    | cons (p2t, p2ts) => begin
        loop (p2ts, s2varlstord_union (ans, p2t.p2at_svs))
      end // end of [cons]
    | nil () => ans
  // end of [loop]
in
  loop (p2ts, s2varlstord_nil)
end // end of [p2atlst_svs_union]

implement
p2atlst_dvs_union (p2ts) = let
  fun loop (p2ts: p2atlst, ans: d2varlstord_t): d2varlstord_t =
    case+ p2ts of
    | cons (p2t, p2ts) => begin
        loop (p2ts, d2varlstord_union (ans, p2t.p2at_dvs))
      end // end of [cons]
    | nil () => ans // end of [nil]
  // end of [loop]
in
  loop (p2ts, d2varlstord_nil)
end // end of [p2atlst_dvs_union]

(* ****** ****** *)

implement
labp2atlst_svs_union (lp2ts) = let
  fun loop (lp2ts: labp2atlst, ans: s2varlstord_t): s2varlstord_t =
    case+ lp2ts of
    | LABP2ATLSTcons (l, p2t, lp2ts) => begin
        loop (lp2ts, s2varlstord_union (ans, p2t.p2at_svs))
      end // end of [LABP2ATLSTcons]
    | _ => ans // end of [_]
  // end of [loop]
in
  loop (lp2ts, s2varlstord_nil)
end // end of [labp2atlst_svs_union]

implement
labp2atlst_dvs_union (lp2ts) = let
  fun loop (lp2ts: labp2atlst, ans: d2varlstord_t): d2varlstord_t =
    case+ lp2ts of
    | LABP2ATLSTcons (l, p2t, lp2ts) => begin
        loop (lp2ts, d2varlstord_union (ans, p2t.p2at_dvs))
      end // end of [LABP2ATLSTcons]
    | _ => ans // end of [_]
  // end of [loop]
in
  loop (lp2ts, d2varlstord_nil)
end // end of [labp2atlst_dvs_union]

(* ****** ****** *)

implement
p2at_ann (loc, p2t, s2e) = '{
  p2at_loc= loc
, p2at_svs= p2t.p2at_svs, p2at_dvs= p2t.p2at_dvs, p2at_typ= None ()
, p2at_node= P2Tann (p2t, s2e)
}

implement
p2at_any (loc) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tany ()
}

implement
p2at_as (loc, refknd, d2v, p2t) = let
  val dvs = d2varlstord_add (p2t.p2at_dvs, d2v)
in '{
  p2at_loc= loc
, p2at_svs= p2t.p2at_svs
, p2at_dvs= dvs
, p2at_typ= None ()
, p2at_node= P2Tas (refknd, d2v, p2t)
} end // end of [p2at_as]

implement
p2at_bool (loc, b) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tbool (b)
}

implement
p2at_char (loc, chr) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tchar (chr)
}

implement
p2at_con (
  loc
, refknd
, d2c, qua, res, npf, p2ts_arg
) = let
  val svs = p2atlst_svs_union (p2ts_arg)
  val svs = loop (qua, svs) where {
    fun loop
      (s2vpss: s2qualst, svs: s2varlstord_t): s2varlstord_t =
      case+ s2vpss of
      | cons (s2vps, s2vpss) => begin
          loop (s2vpss, s2varlstord_addlst (svs, s2vps.0))
        end // end of [cons]
      | nil () => svs // end of [nil]
  } // end of [where]
  val dvs = p2atlst_dvs_union (p2ts_arg)
in '{
  p2at_loc= loc
, p2at_svs= svs
, p2at_dvs= dvs
, p2at_typ= None ()
, p2at_node= P2Tcon (refknd, d2c, qua, res, npf, p2ts_arg)
} end // end of [p2at_con]

implement
p2at_exist (loc, s2vs, p2t) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_addlst (p2t.p2at_svs, s2vs)
, p2at_dvs= p2t.p2at_dvs
, p2at_typ= None ()
, p2at_node= P2Texist (s2vs, p2t)
}

implement
p2at_empty (loc) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tempty ()
}

implement
p2at_float (loc, str) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tfloat (str)
}

implement
p2at_int (loc, s, i) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tint (s, i)
}

implement
p2at_list (loc, npf, p2ts) = let
  val svs = p2atlst_svs_union (p2ts)
  val dvs = p2atlst_dvs_union (p2ts)
in '{
  p2at_loc= loc
, p2at_svs= svs
, p2at_dvs= dvs
, p2at_typ= None ()
, p2at_node= P2Tlist (npf, p2ts)
} end // end of [p2at_list]

implement
p2at_lst (loc, p2ts) = let
  val svs = p2atlst_svs_union (p2ts)
  val dvs = p2atlst_dvs_union (p2ts)
in '{
  p2at_loc= loc
, p2at_svs= svs
, p2at_dvs= dvs
, p2at_typ= None ()
, p2at_node= P2Tlst p2ts
} end

implement
p2at_rec (loc, recknd, npf, lp2ts) = let
  val svs = labp2atlst_svs_union (lp2ts)
  val dvs = labp2atlst_dvs_union (lp2ts)
in '{
  p2at_loc= loc
, p2at_svs= svs
, p2at_dvs= dvs
, p2at_typ= None ()
, p2at_node= P2Trec (recknd, npf, lp2ts)
} end // end of [p2at_rec]

implement
p2at_string (loc, str) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_nil
, p2at_typ= None ()
, p2at_node= P2Tstring (str)
}

implement
p2at_tup (loc, tupknd, npf, p2ts) = let
  val svs = p2atlst_svs_union (p2ts)
  val dvs = p2atlst_dvs_union (p2ts)
  val lp2ts = aux (0, p2ts) where {
    fun aux (i: int, p2ts: p2atlst): labp2atlst =
      case+ p2ts of
      | p2t :: p2ts => let
          val l = $Lab.label_make_int i
        in
          LABP2ATLSTcons (l, p2t, aux (i+1, p2ts))
        end // end of [::]
      | nil () => LABP2ATLSTnil ()    
  } // end of [where]
in '{
  p2at_loc= loc
, p2at_svs= svs
, p2at_dvs= dvs
, p2at_typ= None ()
, p2at_node= P2Trec (tupknd, npf, lp2ts)
} end // end of [p2at_tup]

implement
p2at_var (loc, refknd, d2v) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_sing (d2v)
, p2at_typ= None ()
, p2at_node= P2Tvar (refknd, d2v)
}

implement
p2at_vbox (loc, d2v) = '{
  p2at_loc= loc
, p2at_svs= s2varlstord_nil
, p2at_dvs= d2varlstord_sing (d2v)
, p2at_typ= None ()
, p2at_node= P2Tvbox (d2v)
}

(* ****** ****** *)

implement
d2exp_ann_type
  (loc, d2e, s2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Eann_type (d2e, s2e)
, d2exp_typ= None ()
}

implement
d2exp_ann_seff
  (loc, d2e, s2fe) = '{
  d2exp_loc= loc
, d2exp_node= D2Eann_seff (d2e, s2fe)
, d2exp_typ= None ()
}

implement
d2exp_ann_funclo
  (loc, d2e, fc) = '{
  d2exp_loc= loc
, d2exp_node= D2Eann_funclo (d2e, fc)
, d2exp_typ= None ()
}

implement
d2exp_apps (
  loc, d2e_fun, d2as_arg
) = '{
  d2exp_loc= loc
, d2exp_node= D2Eapps (d2e_fun, d2as_arg)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_app_sta (
  loc0, d2e_fun, s2as
) = begin
  case+ s2as of
  | cons _ => let
      val node = (case+ d2e_fun.d2exp_node of
        | D2Eapps (d2e_fun, d2as) => let
            val d2as = $Lst.list_extend (d2as, D2EXPARGsta s2as)
          in
            D2Eapps (d2e_fun, d2as)
          end
        | _ => D2Eapps (d2e_fun, cons (D2EXPARGsta s2as, nil ()))
      ) : d2exp_node
    in
      '{ d2exp_loc= loc0, d2exp_node= node, d2exp_typ= None () }
    end // end of [cons]
  | nil _ => d2e_fun // end of [nil]
end (* end of [d2exp_app_sta] *)

implement
d2exp_app_dyn (
  loc0
, d2e_fun, loc_arg, npf, darg
) = let
  val d2a =
    D2EXPARGdyn (loc_arg, npf, darg)
  // end of [val]
  val node = (
    case+ d2e_fun.d2exp_node of
    | D2Eapps (d2e_fun, d2as) => let
        val d2as = $Lst.list_extend (d2as, d2a) in
        D2Eapps (d2e_fun, d2as)
      end
    | _ => D2Eapps (d2e_fun, cons (d2a, nil ()))
  ) // end of [val]
in
  '{ d2exp_loc= loc0, d2exp_node= node, d2exp_typ= None () }
end // end of [d2exp_app_dyn]

implement
d2exp_app_sta_dyn (
  loc0, loc1
, d2e_fun, sarg, loc_arg, npf, darg
) = let
  val d2e_fun = d2exp_app_sta (loc1, d2e_fun, sarg)
in
  d2exp_app_dyn (loc0, d2e_fun, loc_arg, npf, darg)
end // end of [d2exp_app_sta_dyn]

(* ****** ****** *)

implement
d2exp_arrinit
  (loc, s2e_elt, od2e_asz, d2es_elt) = '{
  d2exp_loc= loc
, d2exp_node= D2Earrinit (s2e_elt, od2e_asz, d2es_elt)
, d2exp_typ= None ()
}

implement
d2exp_arrpsz
  (loc, os2e_elt, d2es_elt) = '{
  d2exp_loc= loc
, d2exp_node= D2Earrpsz (os2e_elt, d2es_elt)
, d2exp_typ= None ()
}

implement
d2exp_arrsub
  (loc, d2s, d2e_arr, loc_ind, d2ess_ind) = '{
  d2exp_loc= loc
, d2exp_node= D2Earrsub (d2s, d2e_arr, loc_ind, d2ess_ind)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_assgn (loc, d2e_lval, d2e_val) = '{
  d2exp_loc= loc
, d2exp_node= D2Eassgn (d2e_lval, d2e_val)
, d2exp_typ= None ()
}

implement
d2exp_bool (loc, b(*bool*)) = '{
  d2exp_loc= loc, d2exp_node= D2Ebool b, d2exp_typ= None ()
}

implement
d2exp_caseof
  (loc, casknd, inv, n, d2es, c2ls) = '{
  d2exp_loc= loc
, d2exp_node= D2Ecaseof (casknd, inv, n, d2es, c2ls)
, d2exp_typ= None ()
} // end of [d2exp_caseof]

implement
d2exp_char (loc, chr) = '{
  d2exp_loc= loc, d2exp_node= D2Echar chr, d2exp_typ= None ()
}

implement
d2exp_con (loc, d2c, s2as_arg, npf, d2es_arg) = '{
  d2exp_loc= loc
, d2exp_node= D2Econ (d2c, s2as_arg, npf, d2es_arg)
, d2exp_typ= None ()
}

implement
d2exp_cst (loc, d2c) = '{
  d2exp_loc= loc, d2exp_node= D2Ecst (d2c), d2exp_typ= None ()
}

implement
d2exp_cstsp (loc, cst) = '{
  d2exp_loc= loc, d2exp_node= D2Ecstsp cst, d2exp_typ= None ()
}

implement
d2exp_crypt (loc, knd, d2e) = '{
  d2exp_loc= loc, d2exp_node= D2Ecrypt (knd, d2e), d2exp_typ= None ()
}

implement
d2exp_deref (loc, d2e) = '{
  d2exp_loc= loc, d2exp_node= D2Ederef (d2e), d2exp_typ= None ()
}

implement
d2exp_dynload (loc, fil) = '{
  d2exp_loc= loc, d2exp_node= D2Edynload (fil), d2exp_typ= None ()
}

implement
d2exp_effmask (loc, effs, d2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Eeffmask (effs, d2e)
, d2exp_typ= None ()
} // end of [d2exp_effmask]

implement
d2exp_empty (loc) = '{
  d2exp_loc= loc, d2exp_node= D2Eempty (), d2exp_typ= None ()
}

implement
d2exp_exist (loc, s2a, d2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Eexist (s2a, d2e)
, d2exp_typ= None ()
}

implement
d2exp_extval (loc, s2e, code) = '{
  d2exp_loc= loc
, d2exp_node= D2Eextval (s2e, code)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_fix (
  loc, knd, d2v_fun, d2e_def
) = '{
  d2exp_loc= loc
, d2exp_node= D2Efix (knd, d2v_fun, d2e_def)
, d2exp_typ= None ()
} // end of [d2exp_fix]

(* ****** ****** *)

implement
d2exp_float (loc, f(*string*)) = '{
  d2exp_loc= loc, d2exp_node= D2Efloat (f), d2exp_typ= None ()
}

implement
d2exp_floatsp (loc, f(*string*)) = '{
  d2exp_loc= loc, d2exp_node= D2Efloatsp (f), d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_foldat
  (loc, s2as, d2e) = '{
  d2exp_loc= loc
, d2exp_node = D2Efoldat (s2as, d2e)
, d2exp_typ= None ()
}

implement
d2exp_for (
  loc, inv, ini, test, post, body
) = '{
  d2exp_loc= loc
, d2exp_node= D2Efor (inv, ini, test, post, body)
, d2exp_typ= None ()
}

implement
d2exp_freeat
  (loc, s2as, d2e) = '{
  d2exp_loc= loc
, d2exp_node = D2Efreeat (s2as, d2e)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_if (
  loc, inv
, d2e_cond, d2e_then, od2e_else
) = '{
  d2exp_loc= loc
, d2exp_node= D2Eif (inv, d2e_cond, d2e_then, od2e_else)
, d2exp_typ= None ()
} // end of [d2exp_if]

(* ****** ****** *)

implement
d2exp_int
  (loc, str, int) = '{
  d2exp_loc= loc
, d2exp_node= D2Eint (str, int)
, d2exp_typ= None ()
}

implement
d2exp_intsp (loc, str, int) = '{
  d2exp_loc= loc
, d2exp_node= D2Eintsp (str, int)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_lam_dyn (
  loc, lin, npf, arg, body
) = '{
  d2exp_loc= loc
, d2exp_node= D2Elam_dyn (lin, npf, arg, body)
, d2exp_typ= None ()
}

implement
d2exp_laminit_dyn (
  loc, lin, npf, arg, body
) = '{
  d2exp_loc= loc
, d2exp_node= D2Elaminit_dyn (lin, npf, arg, body)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_lam_met (
  loc, r, met, body
) = '{
  d2exp_loc= loc
, d2exp_node= D2Elam_met (r, met, body)
, d2exp_typ= None ()
} // end of [d2exp_lam_met]

implement
d2exp_lam_met_new
  (loc, met, body) = let
  val rd2vs =
    ref_make_elt<d2varlst> (nil ())
  // end of [val]
in
  d2exp_lam_met (loc, rd2vs, met, body)
end // end of [d2exp_lam_met_new]

(* ****** ****** *)

implement
d2exp_lam_sta (loc, s2vs, s2ps, body) = '{
  d2exp_loc= loc
, d2exp_node= D2Elam_sta (s2vs, s2ps, body)
, d2exp_typ= None ()
}

(* ****** ****** *)

implement
d2exp_lazy_delay
  (loc, d2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Elazy_delay d2e
, d2exp_typ= None ()
} // end of [d2exp_lazy_delay]

implement
d2exp_lazy_ldelay
  (loc, d2e1, d2e2) = '{
  d2exp_loc= loc
, d2exp_node= D2Elazy_ldelay (d2e1, d2e2)
, d2exp_typ= None ()
} // end of [d2exp_lazy_ldelay]

(* ****** ****** *)

implement
d2exp_let
  (loc, d2cs, d2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Elet (d2cs, d2e), d2exp_typ= None ()
} // end of [d2exp_let]

implement
d2exp_list
  (loc, npf, d2es) = '{
  d2exp_loc= loc
, d2exp_node= D2Elist (npf, d2es), d2exp_typ= None ()
} // end of [d2exp_list]

implement
d2exp_loopexn
  (loc, flag) = '{
  d2exp_loc= loc
, d2exp_node= D2Eloopexn (flag), d2exp_typ= None ()
} // end of [d2exp_loopexn]

implement
d2exp_lst (
  loc
, lin, os2e_elt, d2es_elt
) = '{
  d2exp_loc= loc
, d2exp_node= D2Elst (lin, os2e_elt, d2es_elt)
, d2exp_typ= None ()
} // end of [d2exp_lst]

(* ****** ****** *)

implement
d2exp_mac (loc, d2m) = '{
  d2exp_loc= loc, d2exp_node= D2Emac (d2m), d2exp_typ= None ()
} // end of [d2exp_mac]

implement
d2exp_macsyn (loc, knd, d2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Emacsyn (knd, d2e)
, d2exp_typ= None ()
} // end of [d2exp_macsyn]

(* ****** ****** *)

implement
d2exp_ptrof (loc, d2e) = '{
  d2exp_loc= loc, d2exp_node= D2Eptrof (d2e), d2exp_typ= None ()
} // end of [d2exp_ptrof]

implement
d2exp_raise (loc, d2e) = '{
  d2exp_loc= loc, d2exp_node= D2Eraise (d2e), d2exp_typ= None ()
} // end of [d2exp_raise]

implement
d2exp_rec (
  loc, recknd, npf, ld2es
) = '{
  d2exp_loc= loc
, d2exp_node= D2Erec (recknd, npf, ld2es)
, d2exp_typ= None ()
} // end of [d2exp_rec]

implement
d2exp_scaseof (
  loc, inv, s2e, sc2ls
) = '{
  d2exp_loc= loc
, d2exp_node= D2Escaseof (inv, s2e, sc2ls)
, d2exp_typ= None ()
} // end of [d2exp_scaseof]

implement
d2exp_sel (
  loc, d2e_root, d2ls_path
) = '{
  d2exp_loc= loc
, d2exp_node = D2Esel (d2e_root, d2ls_path)
, d2exp_typ= None ()
} // end of [d2exp_sel]

implement
d2exp_sel_ptr
  (loc, d2e, d2l) = let
  val d2e_root = d2exp_deref (d2e.d2exp_loc, d2e)
in '{
  d2exp_loc= loc
, d2exp_node= D2Esel (d2e_root, cons (d2l, nil ()))
, d2exp_typ= None ()
} end // end of [d2exp_selptr]

implement
d2exp_seq (loc, d2es) = '{
  d2exp_loc= loc, d2exp_node= D2Eseq (d2es), d2exp_typ= None ()
} // end of [d2exp_seq]

implement
d2exp_showtype (loc, d2e) = '{
  d2exp_loc= loc, d2exp_node= D2Eshowtype (d2e), d2exp_typ= None ()
} // end of [d2exp_showtype]

implement
d2exp_sif
  (loc, inv, s2e_cond, d2e_then, d2e_else) = '{
  d2exp_loc= loc
, d2exp_node= D2Esif (inv, s2e_cond, d2e_then, d2e_else)
, d2exp_typ= None ()
} // end of [d2exp_sif]

implement
d2exp_string (loc, str, len) = '{
  d2exp_loc= loc
, d2exp_node= D2Estring (str, len)
, d2exp_typ= None ()
}

implement
d2exp_struct (loc, ld2es) = '{
  d2exp_loc= loc
, d2exp_node= D2Estruct (ld2es)
, d2exp_typ= None ()
}

implement
d2exp_sym (loc, d2s) = '{
  d2exp_loc= loc, d2exp_node= D2Esym (d2s), d2exp_typ= None ()
}

implement
d2exp_tmpid (loc, d2e, ts2ess) = '{
  d2exp_loc= loc
, d2exp_node= D2Etmpid (d2e, ts2ess)
, d2exp_typ= None ()
}

implement
d2exp_top (loc) = '{
 d2exp_loc= loc, d2exp_node= D2Etop (), d2exp_typ= None ()
}

implement
d2exp_trywith (
  loc, res, d2e, c2ls
) = '{
  d2exp_loc= loc
, d2exp_node= D2Etrywith (res, d2e, c2ls)
, d2exp_typ= None ()
} // end of [d2exp_trywith]

implement
d2exp_var (loc, d2v) = '{
  d2exp_loc= loc, d2exp_node= D2Evar (d2v), d2exp_typ= None ()
}

implement
d2exp_viewat
  (loc, d2e) = '{
  d2exp_loc= loc
, d2exp_node= D2Eviewat (d2e), d2exp_typ= None ()
} // end of [d2exp_viewat]

implement
d2exp_where
  (loc, d2e, d2cs) = '{
  d2exp_loc= loc
, d2exp_node= D2Ewhere (d2e, d2cs), d2exp_typ= None ()
} // end of [d2exp_where]

implement
d2exp_while (
  loc, inv, d2e_test, d2e_body
) = '{
  d2exp_loc= loc
, d2exp_node= D2Ewhile (inv, d2e_test, d2e_body)
, d2exp_typ= None ()
} // end of [d2exp_while]

(* ****** ****** *)

implement
d2exp_tup (
  loc, knd, npf, d2es
) = let
  fun aux (
    i: int, d2es: d2explst
  ) : labd2explst = let
  in
    case+ d2es of
    | list_cons (d2e, d2es) => let
        val l = $Lab.label_make_int i
      in
        LABD2EXPLSTcons (l, d2e, aux (i+1, d2es))
      end // end of [list_cons]
    | list_nil () => LABD2EXPLSTnil ()
  end // end of [aux]
  val ld2es = aux (0, d2es)
in '{
  d2exp_loc= loc
, d2exp_node= D2Erec (knd, npf, ld2es)
, d2exp_typ= None ()
} end // end of [d2exp_tup]

(* ****** ****** *)

implement
d2lab_lab (loc, lab) = '{
  d2lab_loc= loc, d2lab_node= D2LABlab lab
}

implement
d2lab_ind (loc, ind) = '{
  d2lab_loc= loc, d2lab_node= D2LABind ind
}

(* ****** ****** *)

implement
i2nvarg_make (d2v, os2e) =
  '{ i2nvarg_var= d2v, i2nvarg_typ= os2e }
// end of [i2nvarg_make]

implement
i2nvresstate_nil = '{
  i2nvresstate_svs= nil ()
, i2nvresstate_gua= nil ()
, i2nvresstate_arg= nil ()
, i2nvresstate_met= None ()
}

implement
i2nvresstate_make
  (s2vs, s2ps, arg) = '{
  i2nvresstate_svs= s2vs
, i2nvresstate_gua= s2ps
, i2nvresstate_arg= arg
, i2nvresstate_met= None ()
} // end of [i2nvresstate_make]

implement
i2nvresstate_make_met
  (s2vs, s2ps, arg, met) = '{
  i2nvresstate_svs= s2vs
, i2nvresstate_gua= s2ps
, i2nvresstate_arg= arg
, i2nvresstate_met= met
} // end of [i2nvresstate_make]

implement
loopi2nv_make (
  loc
, s2vs, s2ps, met, arg, res
) = '{
  loopi2nv_loc= loc
, loopi2nv_svs= s2vs
, loopi2nv_gua= s2ps
, loopi2nv_met= met
, loopi2nv_arg= arg
, loopi2nv_res= res
} // end of [loopi2nv_make]

(* ****** ****** *)

local

fn i2nvarg_update (
  arg: i2nvarg
) : i2nvarg = let
  val d2v = arg.i2nvarg_var
in
  case+ d2var_get_view d2v of
  | D2VAROPTsome d2v_view => let
      val s2e_addr = (case+ d2var_get_addr d2v of
        | Some s2e_addr => s2e_addr
        | None => begin
            prerr_interror ();
            prerr ": i2nvresstate_tr: d2v = "; prerr d2v; prerr_newline ();
            $Err.abort {s2exp} ()
          end // end of [None]
      ) : s2exp // end of [val]
      val os2e_at = (case+ arg.i2nvarg_typ of
        | Some s2e => Some (s2exp_at_viewt0ype_addr_view (s2e, s2e_addr))
        | None () => None ()
      ) : s2expopt // end of [val]
    in
      i2nvarg_make (d2v_view, os2e_at)
    end // end of [D2VAROPTsome]
  | D2VAROPTnone () => arg
end (* end of [i2nvarg_update] *)

in // in of [local]

implement
i2nvresstate_update (res) = let
  val args = $Lst.list_map_fun (res.i2nvresstate_arg, i2nvarg_update)
in
  i2nvresstate_make (res.i2nvresstate_svs, res.i2nvresstate_gua, args)
end // end of [i2nvresstate_update]

implement
loopi2nv_update (i2nv) = let
  val i2nv_arg = $Lst.list_map_fun (i2nv.loopi2nv_arg, i2nvarg_update)
  val i2nv_res = i2nvresstate_update (i2nv.loopi2nv_res)
in
  loopi2nv_make (
    i2nv.loopi2nv_loc
  , i2nv.loopi2nv_svs
  , i2nv.loopi2nv_gua
  , i2nv.loopi2nv_met
  , i2nv_arg
  , i2nv_res
  ) // end of [loopi2nv_make]
end // end of [loopi2nv_update]

end // end of [local]

(* ****** ****** *)

implement
m2atch_make (loc, d2e, op2t) = '{
  m2atch_loc= loc, m2atch_exp= d2e, m2atch_pat= op2t
} // end of [m2atch_make]

implement
c2lau_make (
  loc
, p2t, gua, seq, neg, d2e
) = '{
  c2lau_loc= loc
, c2lau_pat= p2t
, c2lau_gua= gua
, c2lau_seq= seq
, c2lau_neg= neg
, c2lau_exp= d2e
} // end of [c2lau_make]

implement
sc2lau_make (loc, sp2t, d2e) = '{
  sc2lau_loc= loc, sc2lau_pat= sp2t, sc2lau_exp= d2e
}

(* ****** ****** *)

implement
s2tavar_make (loc, s2v) =
  '{ s2tavar_loc= loc, s2tavar_var = s2v }

implement
s2aspdec_make (
  fil, loc, s2c, def
) = '{
  s2aspdec_fil= fil
, s2aspdec_loc= loc
, s2aspdec_cst= s2c
, s2aspdec_def= def
} // end of [s2aspdec_make]

implement
v2aldec_make
  (loc, p2t, def, ann) = '{
  v2aldec_loc= loc
, v2aldec_pat= p2t, v2aldec_def= def, v2aldec_ann= ann
} // end of [v2aldec_make]

implement
f2undec_make
  (loc, d2v, def, ann) = '{
  f2undec_loc= loc
, f2undec_var= d2v, f2undec_def= def, f2undec_ann= ann
} // end of [f2undec_make]

implement
v2ardec_make (
  loc, knd
, d2v, s2v, typ, wth, ini
) = '{
  v2ardec_loc= loc
, v2ardec_knd= knd
, v2ardec_dvar= d2v
, v2ardec_svar= s2v
, v2ardec_typ= typ
, v2ardec_wth= wth
, v2ardec_ini= ini
} // end of [v2ardec_make]

implement
i2mpdec_make (
  loc, loc_id
, d2c, s2vpss, s2ess, s2pss, def
) = '{
  i2mpdec_loc= loc
, i2mpdec_loc_id= loc_id
, i2mpdec_cst= d2c
, i2mpdec_decarg= s2vpss
, i2mpdec_tmparg= s2ess, i2mpdec_tmpgua= s2pss
, i2mpdec_def= def
} // end of [i2mpdec_make]

(* ****** ****** *)

implement
d2ec_none (loc) = '{
  d2ec_loc= loc, d2ec_node= D2Cnone ()
}

implement
d2ec_list (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Clist d2cs
}

implement
d2ec_include (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cinclude d2cs
}

implement
d2ec_symintr (loc, ids) = '{
  d2ec_loc= loc, d2ec_node= D2Csymintr (ids)
}

implement
d2ec_symelim (loc, ids) = '{
  d2ec_loc= loc, d2ec_node= D2Csymelim (ids)
}

implement
d2ec_stavars (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cstavars d2cs
}

implement
d2ec_saspdec (loc, d2c) = '{
  d2ec_loc= loc, d2ec_node= D2Csaspdec d2c
}

implement
d2ec_dcstdec (loc, dck, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cdcstdec (dck, d2cs)
}

implement
d2ec_datdec (loc, dtk, s2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cdatdec (dtk, s2cs)
}

implement
d2ec_exndec (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cexndec (d2cs)
}

implement
d2ec_overload (loc, id, d2i) = '{
  d2ec_loc= loc, d2ec_node= D2Coverload (id, d2i)
}

implement
d2ec_extype (loc, name, s2e_def) = '{
  d2ec_loc= loc, d2ec_node= D2Cextype (name, s2e_def)
}

implement
d2ec_extval (loc, name, d2e_def) = '{
  d2ec_loc= loc, d2ec_node= D2Cextval (name, d2e_def)
}

implement
d2ec_extcode (loc, position, code) = '{
  d2ec_loc= loc, d2ec_node= D2Cextcode (position, code)
}

implement
d2ec_valdecs (loc, valknd, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cvaldecs (valknd, d2cs)
}

implement
d2ec_valdecs_par (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cvaldecs_par (d2cs)
}

implement
d2ec_valdecs_rec (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cvaldecs_rec (d2cs)
}

implement
d2ec_fundecs
  (loc, decarg, funknd, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cfundecs (decarg, funknd, d2cs)
}

implement
d2ec_vardecs (loc, d2cs) = '{
  d2ec_loc= loc, d2ec_node= D2Cvardecs (d2cs)
}

implement
d2ec_impdec (loc, d2c) = '{
  d2ec_loc= loc, d2ec_node= D2Cimpdec (d2c)
}

implement
d2ec_local (loc, d2cs1, d2cs2) = '{
  d2ec_loc= loc, d2ec_node= D2Clocal (d2cs1, d2cs2)
}

implement
d2ec_dynload (loc, fil) = '{
  d2ec_loc= loc, d2ec_node= D2Cdynload (fil)
}

implement
d2ec_staload (
  loc, qua, fil, loaded, loadflag, d2cs
) = '{
  d2ec_loc= loc
, d2ec_node= D2Cstaload (qua, fil, loaded, loadflag, d2cs)
} // end of [d2ec_staload]

(* ****** ****** *)

implement
l2val_make_d2exp
  (d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Earrsub (
      d2s_brackets, d2e_arr, loc_ind, d2ess_ind
    ) => let
      val isptr = d2exp_var_cst_is_ptr d2e_arr
    in
      if isptr then let
        val d2l = d2lab_ind (loc_ind, d2ess_ind)
      in
        L2VALptr (d2e_arr, cons (d2l, nil ()))
      end else begin
        L2VALarrsub (d2s_brackets, d2e_arr, loc_ind, d2ess_ind)
      end // end of [if]
    end (* end of [D2Earrsub] *)
  | D2Ederef d2e_ptr => L2VALptr (d2e_ptr, nil ())
  | D2Esel (d2e, d2ls) => begin case+ d2e.d2exp_node of
    | D2Evar d2v when d2var_is_linear d2v => L2VALvar_lin (d2v, d2ls)
    | D2Evar d2v when d2var_is_mutable d2v => L2VALvar_mut (d2v, d2ls)
    | D2Ederef d2e_ptr => L2VALptr (d2e_ptr, d2ls)
    | _ => L2VALnone (d2e0)
    end // end of [D2Esel]
  | D2Evar d2v when d2var_is_linear d2v => L2VALvar_lin (d2v, nil ())
  | D2Evar d2v when d2var_is_mutable d2v => L2VALvar_mut (d2v, nil ())
  | _ => L2VALnone (d2e0)
end // end of [l2val_make_d2exp]

(* ****** ****** *)

extern typedef "p2at_t" = p2at
extern typedef "d2exp_t" = d2exp

%{$

ats_void_type
atsopt_p2at_set_typ (
  ats_ptr_type p2t, ats_ptr_type os2e
) {
  ((p2at_t)p2t)->atslab_p2at_typ = os2e ; return ;
} // end of [atsopt_p2at_set_typ]

ats_void_type
atsopt_d2exp_set_typ (
  ats_ptr_type d2e, ats_ptr_type os2e
) {
  ((d2exp_t)d2e)->atslab_d2exp_typ = os2e ; return ;
} // end of [atsopt_d2exp_set_typ]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_dynexp2.dats] *)
