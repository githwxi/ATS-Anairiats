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

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol
overload prerr with $Loc.prerr_location

(* ****** ****** *)

typedef sym_t = $Sym.symbol_t

val MINUSGT = $Sym.symbol_MINUSGT
val s0rtq_none = $Syn.s0rtq_none ()
val s0taq_none = $Syn.s0taq_none ()

fn s0rtq_is_none (q: $Syn.s0rtq): bool =
  case+ q.s0rtq_node of $Syn.S0RTQnone () => true | _ => false

(* ****** ****** *)

implement
e1xp_app (
  loc, e_fun, loc_arg, es_arg
) = '{
  e1xp_loc= loc
, e1xp_node= E1XPapp (e_fun, loc_arg, es_arg)
} // end of [e1xp_app]

implement
e1xp_char
  (loc, c) = '{
  e1xp_loc= loc, e1xp_node= E1XPchar (c)
} // end of [e1xp_char]

implement
e1xp_float (loc, f) = '{
  e1xp_loc= loc, e1xp_node= E1XPfloat (f: string)
} // end of [e1xp_float]

implement
e1xp_ide (loc, id) = '{
  e1xp_loc= loc, e1xp_node= E1XPide (id: sym_t)
}

implement
e1xp_int (loc, int) = '{
  e1xp_loc= loc, e1xp_node= E1XPint (int: string)
}

implement
e1xp_list (loc, es) = '{
  e1xp_loc= loc, e1xp_node= E1XPlist (es: e1xplst)
}

implement
e1xp_string (loc, str, len) = '{
  e1xp_loc= loc, e1xp_node= E1XPstring (str, len)
}

implement
e1xp_undef (loc) = '{
  e1xp_loc= loc, e1xp_node= E1XPundef ()
} // end of [e1xp_undef]

implement
e1xp_cstsp (loc, cst) = '{
  e1xp_loc= loc, e1xp_node= E1XPcstsp (cst)
} // end of [e1xp_cstsp]

implement
e1xp_none (loc) = '{
  e1xp_loc= loc, e1xp_node= E1XPnone ()
} // end of [e1xp_none]

(* ****** ****** *)

implement e1xp_true
  (): e1xp = e1xp_int ($Loc.location_dummy, "1")
implement e1xp_false
  (): e1xp = e1xp_int ($Loc.location_dummy, "0")

(* ****** ****** *)

implement v1al_true = V1ALint 1
implement v1al_false = V1ALint 0

(* ****** ****** *)

(* functions for constructing sorts *)

implement s1rt_arrow (loc) = '{
  s1rt_loc= loc, s1rt_node= S1RTqid (s0rtq_none, MINUSGT)
}

(* '->' is a special sort constructor *)
implement
s1rt_is_arrow (s1t): bool =
  case+ s1t.s1rt_node of
  | S1RTqid (q, id) => begin
      if s0rtq_is_none q then id = MINUSGT else false
    end
  | _ => false
// end of [s1rt_is_arrow]

implement s1rt_app (loc, s1t_fun, s1ts_arg) =
  '{ s1rt_loc= loc, s1rt_node= S1RTapp (s1t_fun, s1ts_arg) }

implement s1rt_fun (loc, s1t1, s1t2) =
  let val s1ts = cons (s1t1, cons (s1t2, nil ())) in
    '{ s1rt_loc= loc, s1rt_node = S1RTapp (s1rt_arrow (loc), s1ts) }
  end

implement s1rt_ide (loc, id) = '{
  s1rt_loc= loc, s1rt_node= S1RTqid (s0rtq_none, id)
}

implement s1rt_list (loc, s1ts) = case+ s1ts of
  | cons (s1t, nil ()) => s1t (* singleton elimination *)
  | _ => '{ s1rt_loc= loc, s1rt_node= S1RTlist s1ts }

implement s1rt_qid (loc, q, id) =
  '{ s1rt_loc= loc,  s1rt_node = S1RTqid (q, id) }

implement s1rt_tup (loc, s1ts) =
  '{ s1rt_loc= loc, s1rt_node = S1RTtup s1ts }

(* ****** ****** *)

implement s1rtpol_make (loc, s1t, pol) = '{
  s1rtpol_loc= loc, s1rtpol_srt= s1t, s1rtpol_pol= pol
}

(* ****** ****** *)

implement d1atarg_srt (loc, s1tp) = '{
  d1atarg_loc= loc, d1atarg_node= D1ATARGsrt s1tp
}

implement d1atarg_idsrt (loc, id, s1tp) = '{
  d1atarg_loc= loc, d1atarg_node= D1ATARGidsrt (id, s1tp)
}

(* ****** ****** *)

implement s1arg_make (loc, id, os1t) = '{
  s1arg_loc= loc, s1arg_sym=id, s1arg_srt= os1t
}

implement sp1at_con (loc, q, id, args) = '{
  sp1at_loc= loc, sp1at_node= SP1Tcon (q, id, args)
}

(* ****** ****** *)
 
implement s1exp_ann (loc, s1e, s1t) = '{
  s1exp_loc= loc, s1exp_node= S1Eann (s1e, s1t)
} 

implement s1exp_any (loc) =
  '{ s1exp_loc= loc, s1exp_node= S1Eany () } 

implement s1exp_app (loc, s1e, loc_arg, s1es) = '{
  s1exp_loc= loc, s1exp_node= S1Eapp (s1e, loc_arg, s1es)
}

implement s1exp_char (loc, c) =
  '{ s1exp_loc= loc, s1exp_node= S1Echar c }

implement s1exp_exi (loc, knd(*funres*), s1qs, s1e) = '{
  s1exp_loc= loc, s1exp_node= S1Eexi (knd, s1qs, s1e)
}

implement
s1exp_extype (loc, name, arglst) = '{
  s1exp_loc= loc, s1exp_node= S1Eextype (name, arglst)
} // end of [s1exp_extype]

implement s1exp_ide (loc, id: sym_t) = '{
  s1exp_loc= loc, s1exp_node= S1Eqid (s0taq_none, id)
}

implement s1exp_imp (loc, ft, is_lin, is_prf, oefc) = '{
  s1exp_loc= loc, s1exp_node= S1Eimp (ft, is_lin, is_prf, oefc)
}

implement s1exp_int (loc, int: string) =
  '{ s1exp_loc= loc, s1exp_node= S1Eint int }

implement s1exp_invar (loc, refval, s1e) = '{
  s1exp_loc= loc, s1exp_node= S1Einvar (refval, s1e)
}

implement s1exp_lam (loc, arg, res, body) = '{
  s1exp_loc= loc, s1exp_node= S1Elam (arg, res, body)
}

implement s1exp_list (loc, s1es) = case+ s1es of
(*
  // HX: this one affects postion marking
  | cons (s1e, nil ()) => '{ // singleton elimination
      s1exp_loc= loc, s1exp_node= s1e.s1exp_node
    }
*)
  | cons (s1e, nil ()) => s1e // singleton elimination
  | _ => '{
      s1exp_loc= loc, s1exp_node= S1Elist (0, s1es)
    } // end of [_]
// end of [s1exp_list]

implement s1exp_list2
  (loc, s1es1, s1es2) = let
  val npf = $Lst.list_length s1es1
  val s1es = $Lst.list_append (s1es1, s1es2)
in '{
  s1exp_loc= loc, s1exp_node= S1Elist (npf, s1es)
} end // end of [s1exp_list2]

(*
// HX-2010-12-04: simplification
implement s1exp_mod (loc, q, id, ls1es) = '{
  s1exp_loc= loc, s1exp_node= S1Emod (q, id, ls1es)
}
*)

(*
// HX-2010-12-04: inadequate design
implement s1exp_named (loc, name, s1e) = '{
  s1exp_loc= loc, s1exp_node= S1Enamed (name, s1e)
}
*)

implement s1exp_qid (loc, q, id): s1exp =
  '{ s1exp_loc= loc, s1exp_node= S1Eqid (q, id) } 

implement s1exp_read (loc, s1e) = let
  fn err (loc: $Loc.location_t): s1exp = begin
    $Loc.prerr_location loc; prerr ": error(1)";
    prerr ": [read@] requires exactly two arguments."; prerr_newline ();
    $Err.abort ()
  end // end of [err]
in
  case+ s1e.s1exp_node of
  | S1Elist (_(*npf*), s1es) => begin case+ s1es of
    | cons (s1e1, cons (s1e2, nil ())) => '{
        s1exp_loc= loc, s1exp_node= S1Eread (s1e1, s1e2)
      } // end of [cons]
    | _ => err (loc)
    end // end of [S1Elist]
  | _ => err (loc)
end // end of [s1exp_read]

(*
// HX-2010-11-01: simplification
implement
s1exp_struct (loc, ls1es) = '{
  s1exp_loc= loc, s1exp_node= S1Estruct (ls1es)
} // end of [s1exp_struct]
*)

implement s1exp_top (loc, knd, s1e) = '{
  s1exp_loc= loc, s1exp_node= S1Etop (knd, s1e)
}

implement s1exp_trans (loc, s1e1, s1e2) = '{
  s1exp_loc= loc, s1exp_node= S1Etrans (s1e1, s1e2)
}

implement s1exp_tyarr (loc, s1e_elt, s1ess_dim) = '{
  s1exp_loc= loc, s1exp_node= S1Etyarr (s1e_elt, s1ess_dim)
}

implement s1exp_tyrec (loc, flat, ls1es) = '{
  s1exp_loc= loc, s1exp_node= S1Etyrec (flat, ls1es)
}

implement s1exp_tyrec_ext (loc, name, ls1es) = '{
  s1exp_loc= loc, s1exp_node= S1Etyrec_ext (name, ls1es)
}

implement s1exp_tytup (loc, flat, s1es) = '{
  s1exp_loc= loc, s1exp_node= S1Etytup (flat, s1es)
}

implement s1exp_tytup2 (loc, flat, s1es1, s1es2) = '{
  s1exp_loc= loc, s1exp_node= S1Etytup2 (flat, s1es1, s1es2)
}

implement s1exp_uni (loc, s1qs, s1e) = '{
  s1exp_loc= loc, s1exp_node= S1Euni (s1qs, s1e)
}

implement s1exp_union (loc, ind, ls1es) = '{
  s1exp_loc= loc, s1exp_node= S1Eunion (ind, ls1es)
}

(* ****** ****** *)

implement s1exparg_one (loc) = '{
  s1exparg_loc= loc, s1exparg_node= S1EXPARGone ()
}

implement s1exparg_all (loc) = '{
  s1exparg_loc= loc, s1exparg_node= S1EXPARGall ()
}

implement s1exparg_seq (loc, s1es) = '{
  s1exparg_loc= loc, s1exparg_node= S1EXPARGseq s1es
}

(* ****** ****** *)

implement s1rtext_srt (loc, s1t) = '{
  s1rtext_loc= loc, s1rtext_node= S1TEsrt s1t
}

implement s1rtext_sub (loc, id, s1te, s1ps) = '{
  s1rtext_loc= loc, s1rtext_node= S1TEsub (id, s1te, s1ps)
}

(*

// should [S1TElam] and [S1TEapp] be added?

implement s1rtext_lam (loc, s1as, s1te) = '{
  s1rtext_loc= loc, s1rtext_node= S1TElam (s1as, s1te)
}

implement s1rtext_app (loc, s1te, s1es) = '{
  s1rtext_loc= loc, s1rtext_node= S1TEapp (s1te, s1es)
}

*)

//

implement s1qua_prop (loc, s1e) =
  '{ s1qua_loc= loc, s1qua_node= S1Qprop s1e }

implement s1qua_vars (loc, ids, s1te) =
  '{ s1qua_loc= loc, s1qua_node= S1Qvars (ids, s1te) }

(* ****** ****** *)

implement s1exp_make_e1xp (loc0, e0) = let

fun aux (e0: e1xp):<cloptr1> s1exp = case+ e0.e1xp_node of
  | E1XPapp (e1, loc_arg, es2) => begin
      s1exp_app (loc0, aux e1, loc_arg, aux_list es2)
    end
  | E1XPide ide => s1exp_ide (loc0, ide)
  | E1XPchar chr => s1exp_char (loc0, chr)
  | E1XPint int => s1exp_int (loc0, int)
  | E1XPlist es => s1exp_list (loc0, aux_list es)
  | _ => begin
      prerr loc0;
      prerr "INTERNAL ERROR (ats_staexp1)";
      prerr ": illegal static expression."; prerr_newline ();
      $Err.abort ()
    end // end of [_]
// end of [aux]

and aux_list (es0: e1xplst):<cloptr1> s1explst = case+ es0 of
  | cons (e, es) => cons (aux e, aux_list es) | nil () => nil ()
// end of [aux_list]

in
  aux e0
end // end of [s1exp_make_e1xp]

(* ****** ****** *)

implement wths1explst_is_none (wths1es) = begin case+ wths1es of
  | WTHS1EXPLSTcons_some _ => false
  | WTHS1EXPLSTcons_none (wths1es) => wths1explst_is_none (wths1es)
  | WTHS1EXPLSTnil () => true
end // end of [wths1explst_is_none]

implement wths1explst_reverse (wths1es) = let
  fun aux (
      wths1es: wths1explst
    , res: wths1explst
    ) : wths1explst = case+ wths1es of
    | WTHS1EXPLSTcons_some (refval, s1e, wths1es) => begin
        aux (wths1es, WTHS1EXPLSTcons_some (refval, s1e, res))
      end
    | WTHS1EXPLSTcons_none (wths1es) => begin
        aux (wths1es, WTHS1EXPLSTcons_none res)
      end
    | WTHS1EXPLSTnil () => res // end of [WTHS1EXPLSTnil]
  // end of [aux]
in
  aux (wths1es, WTHS1EXPLSTnil ())
end // end of [wths1explst_reverse]

(* ****** ****** *)

(* end of [ats_staexp1.dats] *)
