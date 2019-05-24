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

(* The first translation mainly resolves the issue of operator fixity *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef l0ab = $Syn.l0ab
val d0ynq_none = $Syn.d0ynq_none ()

(* ****** ****** *)

implement
p1at_ann (loc, p1t, s1e) = '{
  p1at_loc= loc, p1at_node= P1Tann (p1t, s1e)
}

implement
p1at_any (loc) = '{
  p1at_loc= loc, p1at_node= P1Tany ()
}
implement
p1at_any2 (loc) = '{
  p1at_loc= loc, p1at_node= P1Tany2 ()
}

implement
p1at_app_dyn
  (loc, p1t, loc_arg, npf, p1ts) = '{
  p1at_loc= loc, p1at_node= P1Tapp_dyn (p1t, loc_arg, npf, p1ts)
}

implement p1at_app_sta (loc, p1t, s1as) = '{
  p1at_loc= loc, p1at_node= P1Tapp_sta (p1t, s1as)
}

implement p1at_as (loc, id, p1t) = '{
  p1at_loc= loc, p1at_node= P1Tas (id, p1t)
}

implement p1at_char (loc, c) = '{
  p1at_loc= loc, p1at_node= P1Tchar c
}

implement p1at_empty (loc) = '{
  p1at_loc= loc, p1at_node= P1Tempty ()
}

implement p1at_exist (loc, s1as, p1t) = '{
  p1at_loc= loc, p1at_node= P1Texist (s1as, p1t)
}

implement p1at_float (loc, str) = '{
  p1at_loc= loc, p1at_node= P1Tfloat (str)
}

implement p1at_free (loc, p1t) = '{
  p1at_loc= loc, p1at_node= P1Tfree p1t
}

implement p1at_ide (loc, id) = '{
  p1at_loc= loc, p1at_node= P1Tqid (d0ynq_none, id)
}

implement p1at_int (loc, str) = '{
  p1at_loc= loc, p1at_node= P1Tint (str)
}

(* ****** ****** *)

implement
p1at_list
  (loc, p1ts) = let
//
fun aux_ifany (
  loc: loc_t, p1t: p1at
) : p1at = let
in
//
case+ p1t.p1at_node of
| P1Tany _ => p1at_any2 (loc)
| _ => '{ // singleton elimination
    p1at_loc= loc, p1at_node= p1t.p1at_node
  }
//
end // end of [aux_ifany]
//
in (* in of [let] *)
//
case+ p1ts of
| list_cons (
    p1t, list_nil ()
  ) => aux_ifany (loc, p1t)
| _ => '{
    p1at_loc= loc, p1at_node= P1Tlist (0, p1ts)
  }
//
end // end of [p1at_list]

implement
p1at_list2
  (loc, p1ts1, p1ts2) = let
  val npf = $Lst.list_length p1ts1
  val p1ts = $Lst.list_append (p1ts1, p1ts2)
in '{
  p1at_loc= loc, p1at_node= P1Tlist (npf, p1ts)
} end // end of [p1at_list2]

(* ****** ****** *)

implement p1at_lst (loc, p1ts) = '{
  p1at_loc= loc, p1at_node= P1Tlst (p1ts)
}

implement p1at_qid (loc, d0q, id) = '{
  p1at_loc= loc, p1at_node= P1Tqid (d0q, id)
}

implement p1at_rec (loc, recknd, lp1ts) = '{
  p1at_loc= loc, p1at_node= P1Trec (recknd, lp1ts)
}

implement p1at_ref (loc, id) = '{
  p1at_loc= loc, p1at_node= P1Tref (id)
}

implement p1at_refas (loc, id, p1t) = '{
  p1at_loc= loc, p1at_node= P1Trefas (id, p1t)
}

implement p1at_string (loc, str) = '{
  p1at_loc= loc, p1at_node= P1Tstring str
}

implement p1at_svararg (loc, s1arg) = '{
  p1at_loc= loc, p1at_node= P1Tsvararg s1arg
}

implement p1at_tup (loc, tupknd, p1ts) = '{
  p1at_loc= loc, p1at_node= P1Ttup (tupknd, 0, p1ts)
}

implement p1at_tup2
  (loc, tupknd, p1ts1, p1ts2) = let
  val npf = $Lst.list_length p1ts1
  val p1ts = $Lst.list_append (p1ts1, p1ts2)
in '{
  p1at_loc= loc, p1at_node= P1Ttup (tupknd, npf, p1ts)
} end // end of [p1at_tup2]

(* ****** ****** *)

fn prerr_loc_error1
  (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(1)")
// end of [prerr_loc_error1]

implement
p1at_make_e1xp (loc, e0) = let
//
  fun aux (e0: e1xp):<cloptr1> p1at = case+ e0.e1xp_node of
    | E1XPapp (e1, loc_arg, es2) => begin
        p1at_app_dyn (loc, aux e1, loc_arg, 0(*npf*), auxlst es2)
      end // end of [E1XPapp]
    | E1XPchar chr => p1at_char (loc, chr)
    | E1XPfloat str => p1at_float (loc, str)
    | E1XPide id => p1at_qid (loc, d0ynq_none, id)
    | E1XPint str => p1at_int (loc, str)
    | E1XPlist es => p1at_list (loc, auxlst es)
    | E1XPnone () => p1at_empty (loc)
    | E1XPstring (str, _(*len*)) => p1at_string (loc, str)
    | E1XPundef () => begin
        prerr_loc_error1 (loc);
        prerr ": incorrect use of undefined value."; prerr_newline ();
        $Err.abort ()
      end // end of [E1XPundef]
    | E1XPcstsp (cst) => begin
        prerr_loc_error1 (loc);
        prerr ": incorrect use of a special constant."; prerr_newline ();
        $Err.abort ()
      end // end of [E1XPcstsp]
  // end of [aux]
//
  and auxlst
    (es0: e1xplst):<cloptr1> p1atlst = case+ es0 of
    | cons (e, es) => cons (aux e, auxlst es) | nil () => nil ()
  // end of [auxlst]
in
  aux (e0)
end // end of [p1at_make_e1xp]

(* ****** ****** *)

implement
d1exp_ann_effc (loc, d1e, efc) = '{
  d1exp_loc= loc, d1exp_node= D1Eann_effc (d1e, efc)
}

implement
d1exp_ann_funclo (loc, d1e, fc) = '{
  d1exp_loc= loc, d1exp_node= D1Eann_funclo (d1e, fc)
}

implement
d1exp_ann_funclo_opt (loc, d1e, fc) = begin
  case+ d1e.d1exp_node of
  | D1Eann_funclo _ => d1e | _ => d1exp_ann_funclo (loc, d1e, fc)
end // end of [d1exp_ann_funclo_opt]

implement
d1exp_ann_type (loc, d1e, s1e) = '{
  d1exp_loc= loc, d1exp_node= D1Eann_type (d1e, s1e)
}

(* ****** ****** *)

implement
d1exp_app_dyn
  (loc, d1e, loc_arg, npf, d1es) = '{
  d1exp_loc= loc, d1exp_node= D1Eapp_dyn (d1e, loc_arg, npf, d1es)
} // end of [d1exp_app_dyn]

implement
d1exp_app_sta (loc, d1e, s1as) = '{
  d1exp_loc= loc, d1exp_node= D1Eapp_sta (d1e, s1as)
} // end of [d1exp_app_sta]

(* ****** ****** *)

implement
d1exp_arrinit (loc, s1e, od1e_asz, d1es_elt) = '{
  d1exp_loc= loc, d1exp_node= D1Earrinit (s1e, od1e_asz, d1es_elt)
}

implement
d1exp_arrpsz (loc, os1e_elt, d1es_elt) = '{
  d1exp_loc= loc, d1exp_node= D1Earrpsz (os1e_elt, d1es_elt)
}

implement
d1exp_arrsub (loc, d1e_arr, loc_ind, d1ess_ind) = '{
  d1exp_loc= loc, d1exp_node= D1Earrsub (d1e_arr, loc_ind, d1ess_ind)
}

(* ****** ****** *)

implement
d1exp_bool (loc, tf) = '{
  d1exp_loc= loc, d1exp_node= D1Ebool (tf)
} // end of [d1exp_bool]

(* ****** ****** *)

implement d1exp_caseof
  (loc, casknd, inv, d1es, c1ls) = let
  // empty
in '{
  d1exp_loc= loc
, d1exp_node = D1Ecaseof (casknd, inv, d1es, c1ls)
} end // end of [d1exp_caseof]

implement d1exp_char (loc, chr) = '{
  d1exp_loc= loc, d1exp_node= D1Echar chr
}

implement d1exp_cstsp (loc, cst) = '{
  d1exp_loc= loc, d1exp_node= D1Ecstsp cst
}

implement d1exp_crypt (loc, knd, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Ecrypt (knd, d1e)
}

implement
d1exp_decseq (loc, d1cs) = '{
  d1exp_loc= loc, d1exp_node= D1Edecseq (d1cs)
} // end of [d1exp_decseq]

implement
d1exp_dynload (loc, fil) = '{
  d1exp_loc= loc, d1exp_node= D1Edynload (fil)
}

implement
d1exp_effmask (loc, effs, d1e) = '{
 d1exp_loc= loc, d1exp_node= D1Eeffmask (effs, d1e)
}

implement
d1exp_empty (loc) = '{
  d1exp_loc= loc, d1exp_node= D1Eempty ()
}

implement
d1exp_exist (loc, s1a, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Eexist (s1a, d1e)
}

implement d1exp_extval (loc, s1e, code) = '{
  d1exp_loc= loc, d1exp_node = D1Eextval (s1e, code)
}

implement d1exp_float (loc, str) = '{
  d1exp_loc= loc, d1exp_node= D1Efloat str
}

implement d1exp_floatsp (loc, str) = '{
  d1exp_loc= loc, d1exp_node= D1Efloatsp str
}

implement d1exp_fix (loc, knd, id, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Efix (knd, id, d1e)
}

implement d1exp_foldat (loc, s1as, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Efoldat (s1as, d1e)
}

implement d1exp_for
  (loc, inv, ini, test, post, body) = '{
  d1exp_loc= loc, d1exp_node= D1Efor (inv, ini, test, post, body)
} // end of [d1exp_for]

implement d1exp_freeat (loc, s1as, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Efreeat (s1as, d1e)
}

(* ****** ****** *)

implement
d1exp_ide (loc, id) = '{
  d1exp_loc= loc, d1exp_node= D1Eqid (d0ynq_none, id)
} // end of [d1exp_ide]

implement
d1exp_idextapp
  (loc, id, ns, d1es) = '{ // for syndef
  d1exp_loc= loc, d1exp_node= D1Eidextapp (id, ns, d1es)
} // end of [d1exp_idextapp]

(* ****** ****** *)

implement d1exp_if (
  loc, inv, d1e_cond, d1e_then, od1e_else
) = let
in '{
  d1exp_loc= loc,
  d1exp_node = D1Eif (inv, d1e_cond, d1e_then, od1e_else)
} end // end of [d1exp_if]

(* ****** ****** *)

implement
d1exp_int (loc, str) = '{
  d1exp_loc= loc, d1exp_node= D1Eint (str)
}

implement
d1exp_intsp (loc, str) = '{
  d1exp_loc= loc, d1exp_node= D1Eintsp (str)
}

(* ****** ****** *)

implement
d1exp_lam_dyn (loc, lin, p1t, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elam_dyn (lin, p1t, d1e)
} // end of [d1exp_lam_dyn]

implement
d1exp_laminit_dyn (loc, lin, p1t, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elaminit_dyn (lin, p1t, d1e)
} // end of [d1exp_laminit_dyn]

(* ****** ****** *)

implement
d1exp_lam_met (loc, loc_arg, s1es, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elam_met (loc_arg, s1es, d1e)
}

implement
d1exp_lam_sta_ana (loc, loc_arg, s1as, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elam_sta_ana (loc_arg, s1as, d1e)
}

implement
d1exp_lam_sta_syn (loc, loc_arg, s1qs, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elam_sta_syn (loc_arg, s1qs, d1e)
}

(* ****** ****** *)

implement
d1exp_lazy_delay (loc, lin, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elazy_delay (lin, d1e)
}

implement d1exp_let (loc, d1cs, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Elet (d1cs, d1e)
}

(* ****** ****** *)

implement
d1exp_list
  (loc, d1es) = let
//
fun auxsin (
  d1es: d1explst
) : bool = let
in
//
case+ d1es of
| list_cons (
    d1e, list_nil ()
  ) => (
  case+ d1e.d1exp_node of
  | D1Elist (_, d1es) => auxsin (d1es) | _ => true
  ) // end of [cons]
| _ => false
//
end // end [auxsin]
//
val issin = auxsin (d1es)
//
in
//
if issin then let
  val-list_cons (d1e, _) = d1es in d1e
end else '{
  d1exp_loc= loc, d1exp_node= D1Elist (0, d1es)
} // end of [if]
end // end of [d1exp_list]

implement
d1exp_list2
  (loc, d1es1, d1es2) = let
  val npf = $Lst.list_length d1es1
  val d1es = $Lst.list_append (d1es1, d1es2)
in '{
  d1exp_loc= loc, d1exp_node= D1Elist (npf, d1es)
} end // end of [d1exp_list2]

(* ****** ****** *)

implement
d1exp_loopexn (loc, i) = '{
  d1exp_loc= loc, d1exp_node= D1Eloopexn (i)
} // end of [d1exp_loopexn]

(* ****** ****** *)

implement
d1exp_lst (loc, lin, os1e, d1es) = '{
  d1exp_loc= loc, d1exp_node= D1Elst (lin, os1e, d1es)
} // end of [d1exp_lst]

implement
d1exp_macsyn (loc, knd, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Emacsyn (knd, d1e)
} // end of [d1exp_macsyn]

implement
d1exp_ptrof (loc, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Eptrof d1e
} // end of [d1exp_ptrof]

implement
d1exp_qid (loc, q, id) = '{
  d1exp_loc= loc, d1exp_node= D1Eqid (q, id)
} // end of [d1exp_qid]

implement
d1exp_raise (loc, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Eraise (d1e)
} // end of [d1exp_raise]

implement
d1exp_rec (loc, recknd, ld1es) = '{
  d1exp_loc= loc, d1exp_node= D1Erec (recknd, ld1es)
} // end of [d1exp_rec]

implement
d1exp_scaseof (loc, inv, s1e, sc1ls) = '{
  d1exp_loc= loc, d1exp_node = D1Escaseof (inv, s1e, sc1ls)
} // end of [d1exp_scaseof]

implement
d1exp_sel (loc, knd, d1e, d1l) = '{
  d1exp_loc= loc, d1exp_node= D1Esel (knd, d1e, d1l)
} // end of [d1exp_sel]

implement
d1exp_seq (loc, d1es) = '{
  d1exp_loc= loc, d1exp_node= D1Eseq d1es
}

implement
d1exp_sexparg (loc, s1a) = '{
  d1exp_loc= loc, d1exp_node= D1Esexparg s1a
}

implement
d1exp_showtype (loc, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Eshowtype (d1e)
} // end of [d1exp_showtype]

implement
d1exp_sif
  (loc, inv, s1e_cond, d1e_then, d1e_else) = let
  // empty
in '{
  d1exp_loc= loc,
  d1exp_node = D1Esif (inv, s1e_cond, d1e_then, d1e_else)
} end // end of [d1exp_sif]

implement
d1exp_string (loc, str, len) = '{
  d1exp_loc= loc, d1exp_node= D1Estring (str, len)
}

implement
d1exp_struct (loc, ld1es) = '{
  d1exp_loc= loc, d1exp_node= D1Estruct (ld1es)
}

implement
d1exp_tmpid (loc, qid, ts1ess) = '{
  d1exp_loc= loc, d1exp_node= D1Etmpid (qid, ts1ess)
}

implement
d1exp_top (loc) = '{
  d1exp_loc= loc, d1exp_node= D1Etop ()
}

implement
d1exp_trywith (loc, res, d1e, c1ls) = '{
  d1exp_loc= loc, d1exp_node= D1Etrywith (res, d1e, c1ls)
}

(* ****** ****** *)

implement
d1exp_tup
  (loc, tupknd, d1es) =
  d1exp_tup_npf (loc, tupknd, 0, d1es)
// end of [d1exp_tup]

implement
d1exp_tup2
  (loc, tupknd, d1es1, d1es2) = let
  val npf = $Lst.list_length d1es1
  val d1es = $Lst.list_append (d1es1, d1es2)
in
 d1exp_tup_npf (loc, tupknd, npf, d1es)
end // end of [d1exp_tup2]

implement
d1exp_tup_npf (loc, tupknd, npf, d1es) = '{
  d1exp_loc= loc, d1exp_node= D1Etup (tupknd, npf, d1es)
} // end of [d1exp_tup_npf]

(* ****** ****** *)

implement
d1exp_viewat (loc, d1e) = '{
  d1exp_loc= loc, d1exp_node= D1Eviewat (d1e)
} // end of [d1exp_viewat]

implement
d1exp_where (loc, d1e, d1cs) = '{
  d1exp_loc= loc, d1exp_node= D1Ewhere (d1e, d1cs)
} // end of [d1exp_where]

implement
d1exp_while (loc, inv, test, body) = '{
  d1exp_loc= loc, d1exp_node= D1Ewhile (inv, test, body)
} // end of [d1exp_while]

(* ****** ****** *)

implement
d1exp_is_metric (d1e) = begin
  case+ d1e.d1exp_node of
  | D1Elam_dyn (_, _, d1e) => d1exp_is_metric d1e
  | D1Elam_met _ => true
  | D1Elam_sta_ana (_, _, d1e) => d1exp_is_metric d1e
  | D1Elam_sta_syn (_, _, d1e) => d1exp_is_metric d1e
  | _ => false
end // end of [d1exp_is_metric]

(* ****** ****** *)

implement
d1exp_make_e1xp (loc, e0) = let
//
  fun aux (e0: e1xp):<cloptr1> d1exp = case+ e0.e1xp_node of
    | E1XPapp (e1, loc_arg, es2) => begin
        d1exp_app_dyn (loc, aux e1, loc_arg, 0(*npf*), auxlst es2)
      end
    | E1XPchar chr => d1exp_char (loc, chr)
    | E1XPfloat str => d1exp_float (loc, str)
    | E1XPide id => d1exp_qid (loc, d0ynq_none, id)
    | E1XPint str => d1exp_int (loc, str)
    | E1XPlist es => d1exp_list (loc, auxlst es)
    | E1XPnone () => d1exp_empty (loc)
    | E1XPstring (str, len) => d1exp_string (loc, str, len)
    | E1XPundef () => begin
        prerr_loc_error1 (loc); prerr ": incorrect use of undefined value."; prerr_newline ();
        $Err.abort ()
      end // end of [E1XPundef]
    | E1XPcstsp (cst) => d1exp_cstsp (loc, cst)
  // end of [aux]
//
  and auxlst (es0: e1xplst)
    :<cloptr1> d1explst = case+ es0 of
    | cons (e, es) => cons (aux e, auxlst es) | nil () => nil ()
  // end of [auxlst]
//
in
//
  aux (e0)
//
end // end of [d1exp_make_e1xp]

(* ****** ****** *)

implement d1lab_lab (loc, lab) = '{
  d1lab_loc= loc, d1lab_node= D1LABlab lab
}
implement d1lab_ind (loc, ind) = '{
  d1lab_loc= loc, d1lab_node= D1LABind ind
}

(* ****** ****** *)

implement m1atch_make (loc, d1e, op1t) = '{
  m1atch_loc= loc, m1atch_exp= d1e, m1atch_pat= op1t
}

implement c1lau_make (loc, p1ts, gua, seq, neg, body) = '{
  c1lau_loc= loc
, c1lau_pat= p1ts
, c1lau_gua= gua
, c1lau_seq= seq
, c1lau_neg= neg
, c1lau_exp= body
} // end of [c1lau_make]

implement sc1lau_make (loc, sp1t, body) = '{
  sc1lau_loc= loc, sc1lau_pat= sp1t, sc1lau_exp= body
}

(* ****** ****** *)

implement
i1nvarg_make (
  loc, id, os1e
) = '{
  i1nvarg_loc= loc
, i1nvarg_sym= id
, i1nvarg_typ= os1e
} // end of [i1nvarg_make]

implement
i1nvresstate_make (s1qs, arg) = '{
  i1nvresstate_qua= s1qs, i1nvresstate_arg= arg
}

implement i1nvresstate_nil =
  i1nvresstate_make (list_nil (), list_nil ())
// end of [i1nvresstate_nil]

implement
loopi1nv_make (
  loc, qua, met, arg, res
) = '{
  loopi1nv_loc= loc
, loopi1nv_qua= qua
, loopi1nv_met= met
, loopi1nv_arg= arg
, loopi1nv_res= res
} // end of [loopi1nv_make]

implement
loopi1nv_nil (loc0) = begin
  loopi1nv_make (loc0, nil (), None (), nil (), i1nvresstate_nil)
end // end of [loopi1nv_nil]

(* ****** ****** *)

implement d1ec_none loc = '{
  d1ec_loc= loc, d1ec_node= D1Cnone ()
}

implement d1ec_list (loc, d1cs) = '{
  d1ec_loc= loc, d1ec_node= D1Clist d1cs
}

implement d1ec_include (loc, d1cs) = '{
  d1ec_loc= loc, d1ec_node= D1Cinclude d1cs
}

implement d1ec_symintr (loc, ids) = '{
  d1ec_loc= loc, d1ec_node= D1Csymintr ids
}

implement d1ec_symelim (loc, ids) = '{
  d1ec_loc= loc, d1ec_node= D1Csymelim ids
}

implement d1ec_e1xpdef (loc, id, def) = '{
  d1ec_loc= loc, d1ec_node= D1Ce1xpdef (id, def)
}

implement d1ec_datsrts (loc, para, d1cs_datsrt) = '{
  d1ec_loc= loc, d1ec_node= D1Cdatsrts (para, d1cs_datsrt)
}

implement d1ec_srtdefs (loc, d1cs_srtdef) = '{
  d1ec_loc= loc, d1ec_node= D1Csrtdefs d1cs_srtdef
}

implement d1ec_stacons (loc, impsrt, d1cs_stacon) = '{
  d1ec_loc= loc, d1ec_node= D1Cstacons (impsrt, d1cs_stacon)
}

implement d1ec_stacsts (loc, d1cs_stacst) = '{
  d1ec_loc= loc, d1ec_node= D1Cstacsts (d1cs_stacst)
}

implement d1ec_stavars (loc, d1cs_stavar) = '{
  d1ec_loc= loc, d1ec_node= D1Cstavars (d1cs_stavar)
}

implement d1ec_sexpdefs
  (loc, os1t, d1cs_sexpdef) = '{
  d1ec_loc= loc, d1ec_node= D1Csexpdefs (os1t, d1cs_sexpdef)
}

implement d1ec_saspdec (loc, d1c) = '{
  d1ec_loc= loc, d1ec_node= D1Csaspdec d1c
}

implement
d1ec_dcstdecs (loc, dck, s1qss, d1cs_dcst) = '{
  d1ec_loc= loc, d1ec_node= D1Cdcstdecs (dck, s1qss, d1cs_dcst)
} // end of [d1ec_dcstdecs]

implement d1ec_datdecs
  (loc, dk, d1cs_datdec, d1cs_sexpdef) = '{
  d1ec_loc= loc, d1ec_node= D1Cdatdecs (dk, d1cs_datdec, d1cs_sexpdef)
} // end of [d1ec_datdecs]

implement
d1ec_exndecs (loc, d1cs_exndec) = '{
  d1ec_loc= loc, d1ec_node= D1Cexndecs (d1cs_exndec)
} // end of [d1ec_exndecs]

implement
d1ec_classdec (loc, id, sup) = '{
  d1ec_loc= loc, d1ec_node= D1Cclassdec (id, sup)
} // end of [d1ec_classdec]

implement d1ec_overload (loc, id, qid) = '{
  d1ec_loc= loc, d1ec_node= D1Coverload (id, qid)
} // end of [d1ec_overload]

implement d1ec_extype (loc, name, s1e_def) = '{
  d1ec_loc= loc, d1ec_node= D1Cextype (name, s1e_def)
}

implement d1ec_extval (loc, name, d1e_def) = '{
  d1ec_loc= loc, d1ec_node= D1Cextval (name, d1e_def)
}

implement d1ec_extcode (loc, int_pos, str_code) = '{
  d1ec_loc= loc, d1ec_node= D1Cextcode (int_pos, str_code)
}

implement d1ec_valdecs (loc, valkind, d1cs_val) = '{
  d1ec_loc= loc, d1ec_node= D1Cvaldecs (valkind, d1cs_val)
}

implement d1ec_valdecs_par (loc, d1cs_val) = '{
  d1ec_loc= loc, d1ec_node= D1Cvaldecs_par d1cs_val
}

implement d1ec_valdecs_rec (loc, d1cs_val) = '{
  d1ec_loc= loc, d1ec_node= D1Cvaldecs_rec d1cs_val
}

implement d1ec_fundecs (loc, funkind, s1qss, d1cs_fun) = '{
  d1ec_loc= loc, d1ec_node= D1Cfundecs (funkind, s1qss, d1cs_fun)
}

implement d1ec_vardecs (loc, d1cs_var) = '{
  d1ec_loc= loc, d1ec_node= D1Cvardecs d1cs_var
}

implement d1ec_macdefs (loc, knd, d1cs_macdef) = '{
  // knd: 0/1/2 => short/long/long rec
  d1ec_loc= loc, d1ec_node= D1Cmacdefs (knd, d1cs_macdef)
}

implement d1ec_impdec (loc, i1mparg, d1c) = '{
  // i1mparg: s1arglstlst
  d1ec_loc= loc, d1ec_node= D1Cimpdec (i1mparg, d1c)
}

implement d1ec_local (loc, d1cs_head, d1cs_body) = '{
  d1ec_loc= loc, d1ec_node= D1Clocal (d1cs_head, d1cs_body)
}

implement d1ec_dynload (loc, fil) = '{
  d1ec_loc= loc, d1ec_node= D1Cdynload (fil)
}

implement d1ec_staload
  (loc, idopt, fil, loadflag, d1cs) = '{
  d1ec_loc= loc, d1ec_node= D1Cstaload (idopt, fil, loadflag, d1cs)
} // end of [d1ec_staload]

(* ****** ****** *)

implement d1atsrtcon_make (loc, id, s1ts) = '{
  d1atsrtcon_loc= loc, d1atsrtcon_sym= id, d1atsrtcon_arg= s1ts
} // end of [d2atsrtcon_make]

implement d1atsrtdec_make (loc, id, xs) = '{
  d1atsrtdec_loc= loc, d1atsrtdec_sym= id, d1atsrtdec_con= xs
} // end of [d1atsrtdec_make]

implement s1rtdef_make (loc, id, s1te) = '{
  s1rtdef_loc= loc
, s1rtdef_sym= id
, s1rtdef_def= s1te
} // end of [s1rtdef_make]

implement
s1tacon_make (fil, loc, id, arg, def) = '{
  s1tacon_fil= fil
, s1tacon_loc= loc
, s1tacon_sym= id
, s1tacon_arg= arg
, s1tacon_def= def
} // end of [s1tacon_make]

implement
s1tacst_make (fil, loc, id, arg, res) = '{
  s1tacst_fil= fil
, s1tacst_loc= loc
, s1tacst_sym= id
, s1tacst_arg= arg
, s1tacst_res= res
} // end of [s1tacst_make]

implement s1tavar_make (loc, id, s1t) = '{
  s1tavar_loc= loc, s1tavar_sym= id, s1tavar_srt= s1t
}

implement s1expdef_make (loc, id, arg, res, def) = '{
  s1expdef_loc= loc
, s1expdef_sym= id
, s1expdef_arg= arg
, s1expdef_res= res
, s1expdef_def= def
} // end of [s1expdef_make]

implement s1aspdec_make
  (fil, loc, qid, arg, res, def) = '{
  s1aspdec_fil= fil
, s1aspdec_loc= loc
, s1aspdec_qid= qid
, s1aspdec_arg= arg
, s1aspdec_res= res
, s1aspdec_def= def
} // end of [s1aspdec_make]

(* ****** ****** *)

implement d1cstdec_make (fil, loc, id, s1e, extdef) = '{
  d1cstdec_fil= fil
, d1cstdec_loc= loc
, d1cstdec_sym= id
, d1cstdec_typ= s1e
, d1cstdec_extdef= extdef
} // end of [d1cstdec_make]

implement d1atcon_make (loc, id, qua, npf, arg, ind) = '{
  d1atcon_loc= loc
, d1atcon_sym= id
, d1atcon_qua= qua
, d1atcon_npf= npf
, d1atcon_arg= arg
, d1atcon_ind= ind
} // end of [d1atcon_make]

implement d1atdec_make (fil, loc, id, arg, con) = '{
  d1atdec_fil= fil
, d1atdec_loc= loc
, d1atdec_sym= id
, d1atdec_arg= arg
, d1atdec_con= con
} // end of [d1atdec_make]

implement e1xndec_make (fil, loc, id, qua, npf, arg) = '{
  e1xndec_fil= fil
, e1xndec_loc= loc
, e1xndec_sym= id
, e1xndec_qua= qua
, e1xndec_npf= npf
, e1xndec_arg= arg
} // end of [e1xndec_make]

(* ****** ****** *)

implement v1aldec_make (loc, p1t, d1e, ann) = '{
  v1aldec_loc= loc
, v1aldec_pat= p1t
, v1aldec_def= d1e
, v1aldec_ann= ann
} // end of [v1aldec_make]

implement f1undec_make (loc, id, loc_id, d1e, ann) = '{
  f1undec_loc= loc
, f1undec_sym= id
, f1undec_sym_loc= loc_id
, f1undec_def= d1e
, f1undec_ann= ann
} // end of [f1undec_make]

implement v1ardec_make
  (loc, knd, id, loc_id, os1e, wth, od1e) = '{
  v1ardec_loc= loc
, v1ardec_knd= knd
, v1ardec_sym= id
, v1ardec_sym_loc= loc_id
, v1ardec_typ= os1e
, v1ardec_wth= wth // i0deopt
, v1ardec_ini= od1e
} // end of [v1ardec_make]

implement m1acdef_make (loc, id, arg, def) = '{
  m1acdef_loc= loc
, m1acdef_sym= id
, m1acdef_arg= arg
, m1acdef_def= def
} // end of [m1acdef_make]

implement i1mpdec_make (loc, qid, tmparg, def) = '{
  i1mpdec_loc= loc
, i1mpdec_qid= qid
, i1mpdec_tmparg= tmparg
, i1mpdec_def= def
} // end of [i1mpdec_make]

(* ****** ****** *)

(* end of [ats_dynexp1.dats] *)
