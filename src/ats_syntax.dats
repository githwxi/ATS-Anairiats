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
// Time: July 2007
//
(* ****** ****** *)

(* ats_syntax: AST for source programs in ATS/Anairiats *)

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Fix = "ats_fixity.sats"
staload Glo = "ats_global.sats"
staload Lab = "ats_label.sats"
staload Lex = "ats_lexer.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_syntax.sats"

(* ****** ****** *)

%{^
#include "prelude/CATS/string.cats"
%} // end of [%{^]


(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

val combine = $Loc.location_combine

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

fn prerr_loc_error0
  (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(0)")
// end of [prerr_loc_error0]

fn prerr_interror () = prerr "INTERNAL ERROR (ats_syntax)"

(* ****** ****** *)

implement abskind_prop () = ABSKINDprop ()
implement abskind_type () = ABSKINDtype ()
implement abskind_t0ype () = ABSKINDt0ype ()
implement abskind_view () = ABSKINDview ()
implement abskind_viewtype () = ABSKINDviewtype ()
implement abskind_viewt0ype () = ABSKINDviewt0ype ()

(* ****** ****** *)

implement dcstkind_fun () = DCSTKINDfun ()
implement dcstkind_val () = DCSTKINDval ()
implement dcstkind_castfn () = DCSTKINDcastfn ()
implement dcstkind_praxi () = DCSTKINDpraxi ()
implement dcstkind_prfun () = DCSTKINDprfun ()
implement dcstkind_prval () = DCSTKINDprval ()

implement
dcstkind_is_fun (dk) = case+ dk of
  | DCSTKINDfun () => true | _ => false

implement
dcstkind_is_castfn (dk) = case+ dk of
  | DCSTKINDcastfn () => true | _ => false

implement
dcstkind_is_praxi (dk) = case+ dk of
  | DCSTKINDpraxi () => true | _ => false

implement
dcstkind_is_prfun (dk) = case+ dk of
  | DCSTKINDprfun () => true | _ => false

implement
dcstkind_is_prval (dk) = case+ dk of
  | DCSTKINDprval () => true | _ => false

implement
dcstkind_is_proof (dk) =
(
case+ dk of
  | DCSTKINDpraxi () => true
  | DCSTKINDprfun () => true
  | DCSTKINDprval () => true
  | _ => false
) // end of [dcstkind_is_proof]

implement
fprint_dcstkind (out, dk) = case+ dk of
  | DCSTKINDfun () => fprint_string (out, "DCSTKINDfun")
  | DCSTKINDval () => fprint_string (out, "DCSTKINDval")
  | DCSTKINDcastfn () => fprint_string (out, "DCSTKINDcastfn")
  | DCSTKINDpraxi () => fprint_string (out, "DCSTKINDpraxi")
  | DCSTKINDprfun () => fprint_string (out, "DCSTKINDprfun")
  | DCSTKINDprval () => fprint_string (out, "DCSTKINDprval")
// end of [fprint_dcstkind]

(* ****** ****** *)

implement datakind_prop () = DATAKINDprop ()
implement datakind_type () = DATAKINDtype ()
implement datakind_view () = DATAKINDview ()
implement datakind_viewtype () = DATAKINDviewtype ()

implement datakind_is_proof dk = case+ dk of
  | DATAKINDprop () => true
  | DATAKINDview () => true
  | _ => false
// end of [datakind_is_proof]

(* ****** ****** *)

implement stadefkind_generic () = STADEFKINDgeneric ()
implement stadefkind_prop (t) = STADEFKINDprop (t)
implement stadefkind_type (t) = STADEFKINDtype (t)
implement stadefkind_view (t) = STADEFKINDview (t)
implement stadefkind_viewtype (t) = STADEFKINDviewtype (t)

(* ****** ****** *)

implement valkind_val () = VALKINDval ()
implement valkind_valminus () = VALKINDvalminus ()
implement valkind_valplus () = VALKINDvalplus ()
implement valkind_prval () = VALKINDprval ()

implement valkind_is_proof vk = case+ vk of
  | VALKINDprval () => true
  | _ => false
// end of [valkind_is_proof]

(* ****** ****** *)

implement funkind_fn () = FUNKINDfn ()
implement funkind_fnstar () = FUNKINDfnstar ()
implement funkind_fun () = FUNKINDfun ()
implement funkind_castfn () = FUNKINDcastfn ()
implement funkind_prfn () = FUNKINDprfn ()
implement funkind_prfun () = FUNKINDprfun ()

implement
funkind_is_proof fk = case+ fk of
  | FUNKINDfn () => false
  | FUNKINDfnstar () => false
  | FUNKINDfun () => false
  | FUNKINDcastfn () => false
  | FUNKINDprfn () => true
  | FUNKINDprfun () => true
// end of [funkind_is_proof]

implement
funkind_is_recursive fk = case+ fk of
  | FUNKINDfn () => false
  | FUNKINDfnstar () => true
  | FUNKINDfun () => true
  | FUNKINDcastfn () => true
  | FUNKINDprfn () => false
  | FUNKINDprfun () => true
// end of [funkind_is_recursive]

implement funkind_is_tailrecur fk =
  case+ fk of FUNKINDfnstar () => true | _ => false
// end of [funkind_is_tailrecur]

(* ****** ****** *)

implement lamkind_lam (t) = LAMKINDlam (t)
implement lamkind_atlam (t) = LAMKINDatlam (t)
implement lamkind_llam (t) = LAMKINDllam (t)
implement lamkind_atllam (t) = LAMKINDatllam (t)

implement fixkind_fix (t) = LAMKINDfix (t)
implement fixkind_atfix (t) = LAMKINDatfix (t)

fun lamkind_get_loc
  (knd: lamkind): loc_t = case+ knd of
  | LAMKINDlam tok => tok.t0kn_loc
  | LAMKINDatlam tok => tok.t0kn_loc
  | LAMKINDllam tok => tok.t0kn_loc
  | LAMKINDatllam tok => tok.t0kn_loc
  | LAMKINDfix tok => tok.t0kn_loc
  | LAMKINDatfix tok => tok.t0kn_loc
  | LAMKINDifix loc => loc // HX: implicit FIX
// end of [lamkind_get_loc]

(* ****** ****** *)

implement srpifkindtok_if (t) = SRPIFKINDTOK (SRPIFKINDif (), t)
implement srpifkindtok_ifdef (t) = SRPIFKINDTOK (SRPIFKINDifdef (), t)
implement srpifkindtok_ifndef (t) = SRPIFKINDTOK (SRPIFKINDifndef (), t)

(* ****** ****** *)

implement
fprint_cstsp (pf | out, cst) = case+ cst of
  | CSTSPfilename () => fprint1_string (pf | out, "#FILENAME")
  | CSTSPlocation () => fprint1_string (pf | out, "#LOCATION")
// end of [fprint_cstsp]

(* ****** ****** *)

implement t0kn_make (loc) = @{ t0kn_loc= loc }

(* ****** ****** *)

implement c0har_make (loc, chr) =
  '{ c0har_loc= loc, c0har_val= chr }

implement e0xtcode_make (loc, int, str) =
  '{ e0xtcode_loc= loc, e0xtcode_pos= int, e0xtcode_cod= str }

implement f0loat_make (loc, str) =
  '{ f0loat_loc= loc, f0loat_val= str }

implement f0loatsp_make (loc, str) =
  '{ f0loatsp_loc= loc, f0loatsp_val= str }

implement i0nt_make (loc, str) =
  '{ i0nt_loc= loc, i0nt_val= str }

implement i0ntsp_make (loc, str) =
  '{ i0ntsp_loc= loc, i0ntsp_val= str }

implement s0tring_make (loc, str, len) =
  '{ s0tring_loc= loc, s0tring_val= str, s0tring_len= len }

(* ****** ****** *)

implement fprint_i0de (pf | out, id) =
  $Sym.fprint_symbol (pf | out, id.i0de_sym)

implement print_i0de id = print_mac (fprint_i0de, id)
implement prerr_i0de id = prerr_mac (fprint_i0de, id)

//

implement
fprint_i0delst
  {m} (pf | out, ids) = let
//
fun aux
(
  out: &FILE m, id0: i0de, ids: i0delst
) : void =
(
case+ ids of
| cons (id, ids) =>
  (
    fprint_i0de (pf | out, id); fprint1_string (pf | out, ", ")
  ) // end of [cons]
| nil () => fprint_i0de (pf | out, id0)
)
//
in
  case+ ids of cons (id, ids) => aux (out, id, ids) | nil () => ()
end // end of [fprint_i0delst]

//

implement i0de_make (loc, str) = let
(*
  val () =
  (
    print "i0de_make: sym = "; print str; print_newline ()
  ) // end of [val]
*)
in '{
  i0de_loc= loc, i0de_sym= $Sym.symbol_make_string str
} end // end of [i0de_make]

implement i0de_make_ampersand (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_AMPERSAND }
implement i0de_make_backslash (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_BACKSLASH }
implement i0de_make_bang (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_BANG }
implement i0de_make_eq (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_EQ }
implement i0de_make_gt (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_GT }
implement i0de_make_gtlt (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_GTLT }
implement i0de_make_lt (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_LT }
implement i0de_make_minusgt (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_MINUSGT }
implement i0de_make_minusltgt (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_MINUSLTGT }
implement i0de_make_r0ead (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_R0EAD }
implement i0de_make_tilde (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_TILDE }

implement i0de_make_t0ype (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_T0YPE }
// end of [i0de_make_t0ype]
implement i0de_make_viewt0ype (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_VIEWT0YPE }
// end of [i0de_make_viewt0ype]

//
implement i0de_make_DO (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_DO }
implement i0de_make_IN (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_IN }
implement i0de_make_WHILE (tok) =
  '{ i0de_loc= tok.t0kn_loc, i0de_sym= $Sym.symbol_WHILE }
//

implement
i0de_make_lrbrackets (t_l, t_r) = let
  val loc = combine (t_l.t0kn_loc, t_r.t0kn_loc)
in '{
  i0de_loc= loc, i0de_sym= $Sym.symbol_LRBRACKETS
} end // end of [i0de_make_lrbrackets]

//

implement i0delst_nil () = nil ()
implement i0delst_sing (x) = cons (x, nil ())
implement i0delst_cons (x, xs) = cons (x, xs)

implement i0delstlst_nil () = nil ()
implement i0delstlst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement l0ab_ide (ide) = let
  val lab = $Lab.label_make_sym (ide.i0de_sym)
in '{
  l0ab_loc= ide.i0de_loc, l0ab_lab= lab
} end // end of [l0ab_ide]

implement l0ab_int (int) = let
  val lab = $Lab.label_make_int (int_of_string int.i0nt_val)
in '{
  l0ab_loc= int.i0nt_loc, l0ab_lab= lab
} end // end of [l0ab_int]

(* ****** ****** *)

implement stai0de_make (ide) = let
  val name = "$" + $Sym.symbol_name (ide.i0de_sym)
in
  i0de_make (ide.i0de_loc, name)
end // end of [stai0de_make]

(* ****** ****** *)
//
// HX: omitted precedence is assumed to equal 0
//
implement p0rec_emp () = P0RECint 0
implement p0rec_int (i) = P0RECint (int_of_string i.i0nt_val)
implement p0rec_ide (id) = P0RECide (id)
implement p0rec_opr (id, opr, i) = case+ opr.i0de_sym of
  | s when s = $Sym.symbol_ADD => P0RECinc (id, int_of_string i.i0nt_val)
  | s when s = $Sym.symbol_SUB => P0RECdec (id, int_of_string i.i0nt_val)
  | s => begin
      prerr_loc_error0 (opr.i0de_loc);
      prerr ": the symbol ["; $Sym.prerr_symbol s;
      prerr "] must be either '+' or '-'.";
      prerr_newline ();
      $Err.abort {p0rec} ()
    end // end of [_]
// end of [p0rec_opr]

(* ****** ****** *)

implement e0xplst_nil () = nil ()
implement e0xplst_cons (x, xs) = cons (x, xs)

implement e0xpopt_none () = None ()
implement e0xpopt_some (x) = Some (x)

(* ****** ****** *)

implement e0xp_app (e1, e2) =
  let val loc = combine (e1.e0xp_loc, e2.e0xp_loc) in
    '{ e0xp_loc= loc, e0xp_node= E0XPapp (e1, e2) }
  end

implement e0xp_char c =
  '{ e0xp_loc= c.c0har_loc, e0xp_node= E0XPchar c.c0har_val }

implement e0xp_eval (t_beg, e, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  e0xp_loc= loc, e0xp_node= E0XPeval e
} end // end of [e0xp_eval]

implement e0xp_float f =
  '{ e0xp_loc= f.f0loat_loc, e0xp_node= E0XPfloat f.f0loat_val }

implement e0xp_ide id =
  '{ e0xp_loc= id.i0de_loc, e0xp_node= E0XPide id.i0de_sym }

implement e0xp_int i =
  '{ e0xp_loc= i.i0nt_loc, e0xp_node= E0XPint i.i0nt_val }

implement e0xp_list (t_beg, es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  e0xp_loc= loc, e0xp_node= E0XPlist es
} end // end of [e0xp_list]

implement e0xp_string s = '{
  e0xp_loc= s.s0tring_loc
, e0xp_node= E0XPstring (s.s0tring_val, s.s0tring_len)
}

implement e0xp_FILENAME (tok) = '{
  e0xp_loc= tok.t0kn_loc, e0xp_node= E0XPcstsp CSTSPfilename
}

implement e0xp_LOCATION (tok) = '{
  e0xp_loc= tok.t0kn_loc, e0xp_node= E0XPcstsp CSTSPlocation
}

(* ****** ****** *)

implement
fprint_s0rtq
  (pf | out, q) =
  case+ q.s0rtq_node of
  | S0RTQnone () => ()
  | S0RTQstr fname => begin
      fprint1_char (pf | out, '"');
      fprint1_string (pf | out, fname);
      fprint1_char (pf | out, '"');
      fprint1_char (pf | out, '.')
    end // end of [S0RTQstr]
  | S0RTQsym id => begin
      $Sym.fprint_symbol (pf | out, id);
      fprint1_char (pf | out, '.')
    end // end of [S0RTQsym]
// end of [fprint_s0rtq]

implement print_s0rtq (q) = print_mac (fprint_s0rtq, q)
implement prerr_s0rtq (q) = prerr_mac (fprint_s0rtq, q)

(* ****** ****** *)

implement s0rtq_none () = '{
  s0rtq_loc= $Loc.location_dummy, s0rtq_node= S0RTQnone ()
}

implement s0rtq_str (s) = '{
  s0rtq_loc= s.s0tring_loc, s0rtq_node= S0RTQstr s.s0tring_val
}

implement s0rtq_sym (id) = '{
  s0rtq_loc= id.i0de_loc, s0rtq_node= S0RTQsym id.i0de_sym
}

(* ****** ****** *)

implement fprint_s0rt (pf | out, s0t) = case+ s0t.s0rt_node of
  | S0RTapp (s0t_fun, s0t_arg) => begin
      fprint1_string (pf | out, "S0RTapp(");
      fprint_s0rt (pf | out, s0t_fun);
      fprint1_string (pf | out, ", ");
      fprint_s0rt (pf | out, s0t_arg);
      fprint1_string (pf | out, ")");
    end
  | S0RTide id => begin
      fprint1_string (pf | out, "S0RTid(");
      $Sym.fprint_symbol (pf | out, id);
      fprint1_string (pf | out, ")");
    end
  | S0RTqid (q, id) => begin
      fprint1_string (pf | out, "S0RTqid(");
      fprint_s0rtq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id);
      fprint1_string (pf | out, ")");
    end
  | S0RTlist s0ts => begin
      fprint1_string (pf | out, "S0RTlist(...)")
    end
  | S0RTtup  s0ts => begin
      fprint1_string (pf | out, "S0RTtup(...)")
    end

(* ****** ****** *)

implement s0rtlst_nil () = nil ()
implement s0rtlst_cons (x, xs) = cons (x, xs)

implement s0rtopt_none () = None ()
implement s0rtopt_some (x) = Some (x)

//

implement s0rt_prop (t) = '{
  s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_PROP
}

implement s0rt_type (t) = '{
  s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_TYPE
}

implement s0rt_t0ype (t) = '{
  s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_T0YPE
}

implement s0rt_view (t) = '{
  s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_VIEW
}

implement s0rt_viewtype (t) = '{
  s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_VIEWTYPE
}

implement s0rt_viewt0ype (t) = '{
  s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_VIEWT0YPE
}

//

implement s0rt_app (s0t_fun, s0t_arg) = begin
(*
  print "s0rt_app:"; print_newline ();
  print "loc_fun = "; print s0t_fun.s0rt_loc; print_newline ();
  print "loc_arg = "; print s0t_arg.s0rt_loc; print_newline ();
*)
  let val loc = combine (s0t_fun.s0rt_loc, s0t_arg.s0rt_loc) in
    '{ s0rt_loc= loc, s0rt_node= S0RTapp (s0t_fun, s0t_arg) }
  end
end // end of [s0rt_app]

implement s0rt_ide (id) = '{
  s0rt_loc= id.i0de_loc, s0rt_node= S0RTide id.i0de_sym
}

implement s0rt_qid (q, id) =
  let val loc = combine (q.s0rtq_loc, id.i0de_loc) in
    '{ s0rt_loc= loc, s0rt_node= S0RTqid (q, id.i0de_sym) }
  end

implement s0rt_list (t_beg, s0ts, t_end) = begin
(*
  print "s0rt_list:\n";
  print "t_beg.loc = "; print t_beg.t0kn_loc; print_newline ();
  print "t_end.loc = "; print t_end.t0kn_loc; print_newline ();
*)
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ s0rt_loc= loc, s0rt_node= S0RTlist s0ts }
  end
end

implement s0rt_tup (t_beg, s0ts, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ s0rt_loc= loc, s0rt_node= S0RTtup s0ts }
  end

(* ****** ****** *)

implement s0rtpol_make (s0t, pol) = '{
  s0rtpol_loc= s0t.s0rt_loc, s0rtpol_srt= s0t, s0rtpol_pol= pol
}

(* ****** ****** *)

implement d0atsrtcon_make_none (id) = '{
  d0atsrtcon_loc= id.i0de_loc, d0atsrtcon_sym= id.i0de_sym
, d0atsrtcon_arg= None ()
} // end of [d0atsrtcon_make_none]

implement d0atsrtcon_make_some (id, s0t) = let
  val loc = combine (id.i0de_loc, s0t.s0rt_loc)
in '{
  d0atsrtcon_loc= loc, d0atsrtcon_sym= id.i0de_sym, d0atsrtcon_arg= Some s0t
} end // end of [d0atsrtcom_make_some]

implement d0atsrtconlst_nil () = nil ()
implement d0atsrtconlst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement d0atsrtdec_make (id, xs) = let
  fun aux_loc
    (id: i0de, x: d0atsrtcon, xs: d0atsrtconlst): loc_t =
    case+ xs of
    | cons(x, xs) => aux_loc (id, x, xs)
    | nil () => combine (id.i0de_loc, x.d0atsrtcon_loc)
  // end of [aux_loc]
  val loc = case+ xs of
    | cons (x, xs) => aux_loc (id, x, xs) | nil () => id.i0de_loc
in '{
  d0atsrtdec_loc= loc, d0atsrtdec_sym= id.i0de_sym, d0atsrtdec_con= xs
} end // end of [d0atsrtdec_make]

implement d0atsrtdeclst_nil () = nil ()
implement d0atsrtdeclst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
fprint_funclo (pf | out, fc) = case+ fc of
  | FUNCLOclo (knd) => fprintf1_exn (pf | out, "clo(%i)", @(knd))
  | FUNCLOfun () => fprint1_string (pf | out, "fun")
// end of [fprint_funclo]

implement print_funclo (fc) = print_mac (fprint_funclo, fc)
implement prerr_funclo (fc) = prerr_mac (fprint_funclo, fc)

implement
eq_funclo_funclo (fc1, fc2) = begin
  case+ (fc1, fc2) of
  | (FUNCLOclo (knd1), FUNCLOclo (knd2)) => (knd1 = knd2)
  | (FUNCLOfun (), FUNCLOfun ()) => true
  | (_, _) => false
end // end of [eq_funclo_funclo]

(* ****** ****** *)

implement e0fftag_cst (i, id) = let
  val name = $Sym.symbol_name (id.i0de_sym)
in '{
  e0fftag_loc= id.i0de_loc, e0fftag_node= E0FFTAGcst (i, name)
} end // end of [e0fftag_cst]

local

fn name_is_prf (name: string): bool = name = "prf"

//

fn name_is_lin0 (name: string): bool = 
  if name = "lin" then true else name = "lin0"
fn name_is_lin1 (name: string): bool = name = "lin1"

//

fn name_is_fun0 (name: string): bool = 
  if name = "fun" then true else name = "fun0"
fn name_is_fun1 (name: string): bool = name = "fun1"

fn name_is_linfun0 (name: string): bool = 
  if name = "linfun" then true else name = "linfun0"
fn name_is_linfun1 (name: string): bool = name = "linfun1"

//

fn name_is_clo0 (name: string): bool =
  if name = "clo" then true else name = "clo0"
fn name_is_clo1 (name: string): bool = name = "clo1"

fn name_is_linclo0 (name: string): bool =
  if name = "linclo" then true else name = "linclo0"
fn name_is_linclo1 (name: string): bool = name = "linclo1"

//

fn name_is_cloptr0 (name: string): bool = 
  if name = "cloptr" then true else name = "cloptr0"
fn name_is_cloptr1 (name: string): bool = name = "cloptr1"

fn name_is_lincloptr0 (name: string): bool = 
  if name = "lincloptr" then true else name = "lincloptr0"
fn name_is_lincloptr1 (name: string): bool = name = "lincloptr1"

//

fn name_is_cloref0 (name: string): bool = 
  if name = "cloref" then true else name = "cloref0"
fn name_is_cloref1 (name: string): bool = name = "cloref1"

//

#define CLO 0
#define CLOPTR  1
#define CLOREF ~1

in (* in of [local] *)

implement e0fftag_var (id) = let
  val name = $Sym.symbol_name (id.i0de_sym)
  val node = (case+ name of
//
    | _ when name_is_prf name => E0FFTAGprf
//
    | _ when name_is_clo0 name => E0FFTAGclo (~1(*u*), CLO, 0)
    | _ when name_is_clo1 name => E0FFTAGclo (~1(*u*), CLO, 1)
    | _ when name_is_linclo0 name => E0FFTAGclo (1(*l*), CLO, 0)
    | _ when name_is_linclo1 name => E0FFTAGclo (1(*l*), CLO, 1)
//
    | _ when name_is_cloptr0 name => E0FFTAGclo (~1(*u*), CLOPTR, 0)
    | _ when name_is_cloptr1 name => E0FFTAGclo (~1(*u*), CLOPTR, 1)
    | _ when name_is_lincloptr0 name => E0FFTAGclo (1(*l*), CLOPTR, 0)
    | _ when name_is_lincloptr1 name => E0FFTAGclo (1(*l*), CLOPTR, 1)
//
    | _ when name_is_cloref0 name => E0FFTAGclo (0(*n*), CLOREF, 0)
    | _ when name_is_cloref1 name => E0FFTAGclo (0(*n*), CLOREF, 1)
//
    | _ when name_is_fun0 name => E0FFTAGfun (~1(*u*), 0)
    | _ when name_is_fun1 name => E0FFTAGfun (~1(*u*), 1)
    | _ when name_is_linfun0 name => E0FFTAGfun (1(*l*), 0)
    | _ when name_is_linfun1 name => E0FFTAGfun (1(*l*), 1)
//
    | _ when name_is_lin0 name => E0FFTAGlin 0
    | _ when name_is_lin1 name => E0FFTAGlin 1
//
    | _ => E0FFTAGvar id
   ) : e0fftag_node // end of [val]
//
in '{
  e0fftag_loc= id.i0de_loc, e0fftag_node= node
} end // end of [e0fftag_var]

end // end of [local]

implement e0fftag_var_fun (t) = '{
  e0fftag_loc= t.t0kn_loc, e0fftag_node= E0FFTAGfun (~1(*u*), 0)
} // end of [e0fftag_var_fun]

implement e0fftag_int (i) = '{
  e0fftag_loc= i.i0nt_loc, e0fftag_node= E0FFTAGcst (0, i.i0nt_val)
}

implement e0fftaglst_nil () = nil ()
implement e0fftaglst_cons (x, xs) = cons (x, xs)

implement e0fftaglstopt_none () = None ()
implement e0fftaglstopt_some (x) = Some (x)

(* ****** ****** *)

(* static qualifiers *)

implement s0taq_make 
  (loc, node) = '{ s0taq_loc= loc, s0taq_node= node }
// end of [s0taq]

implement
fprint_s0taq (pf | out, q) = case+ q.s0taq_node of
  | S0TAQnone () => ()
  | S0TAQfildot fil => begin
      fprint1_char (pf | out, '$');
      fprint1_char (pf | out, '"');
      fprint1_string (pf | out, fil);
      fprint1_char (pf | out, '"');
      fprint1_char (pf | out, '.')
    end
  | S0TAQsymcolon id => begin
      $Sym.fprint_symbol (pf | out, id); fprint1_char (pf | out, ':')
    end // end of [S0TAQsymcolon]
  | S0TAQsymdot id => begin
      $Sym.fprint_symbol (pf | out, id); fprint1_char (pf | out, '.')
    end // end of [S0TAQsymdot]
// end of [fprint_s0taq]

implement print_s0taq (q) = print_mac (fprint_s0taq, q)
implement prerr_s0taq (q) = prerr_mac (fprint_s0taq, q)

(* ****** ****** *)

implement s0taq_none () = '{
  s0taq_loc= $Loc.location_dummy, s0taq_node= S0TAQnone ()
} // end of [s0taq_node]

implement s0taq_fildot (fname) = '{
  s0taq_loc= fname.s0tring_loc, s0taq_node= S0TAQfildot (fname.s0tring_val)
} // end of [s0taq_fildot]

implement s0taq_symcolon (id) = '{
  s0taq_loc= id.i0de_loc, s0taq_node= S0TAQsymcolon (id.i0de_sym)
} // end of [s0taq_symcolon]

implement s0taq_symdot (id) = '{
  s0taq_loc= id.i0de_loc, s0taq_node= S0TAQsymdot (id.i0de_sym)
} // end of [s0taq_symdot]

(* ****** ****** *)

(* dynamic qualifiers *)

implement fprint_d0ynq
  (pf | out, q) = case+ q.d0ynq_node of
  | D0YNQfildot fil => begin
      fprint1_char (pf | out, '$');
      fprint1_char (pf | out, '"');
      fprint1_string (pf | out, fil);
      fprint1_char (pf | out, '"');
      fprint1_char (pf | out, '.')
    end
  | D0YNQfildot_symcolon (fil, id_colon) => begin
      fprint1_char (pf | out, '$');
      fprint1_char (pf | out, '"');
      fprint1_string (pf | out, fil);
      fprint1_char (pf | out, '"');
      $Sym.fprint_symbol (pf | out, id_colon);
      fprint1_char (pf | out, ':')
    end
  | D0YNQsymcolon id_colon => begin
      $Sym.fprint_symbol (pf | out, id_colon);
      fprint1_char (pf | out, ':')
    end
  | D0YNQsymdot id_dot => begin
      $Sym.fprint_symbol (pf | out, id_dot);
      fprint1_char (pf | out, '.')
    end
  | D0YNQsymdot_symcolon (id_dot, id_colon) => begin
      $Sym.fprint_symbol (pf | out, id_dot);
      $Sym.fprint_symbol (pf | out, id_colon);
      fprint1_char (pf | out, ':')
    end
  | D0YNQnone () => ()
// end of [fprint_d0ynq]

implement print_d0ynq (q) = print_mac (fprint_d0ynq, q)
implement prerr_d0ynq (q) = prerr_mac (fprint_d0ynq, q)

(* ****** ****** *)

implement d0ynq_none () = '{
  d0ynq_loc= $Loc.location_dummy, d0ynq_node= D0YNQnone ()
}

implement d0ynq_fildot (fname) = '{
  d0ynq_loc= fname.s0tring_loc, d0ynq_node= D0YNQfildot (fname.s0tring_val)
}

implement d0ynq_fildot_symcolon (fname, id) = let

val loc = combine (fname.s0tring_loc, id.i0de_loc)

in '{
  d0ynq_loc= loc
, d0ynq_node= D0YNQfildot_symcolon (fname.s0tring_val, id.i0de_sym)
} end // end of [d0ynq_fildot_symcolon]

implement d0ynq_symcolon (id) =
  '{ d0ynq_loc= id.i0de_loc, d0ynq_node= D0YNQsymcolon (id.i0de_sym) }

implement d0ynq_symdot (id) =
  '{ d0ynq_loc= id.i0de_loc, d0ynq_node= D0YNQsymdot (id.i0de_sym) }

implement d0ynq_symdot_symcolon (id_dot, id_colon) = let

val loc = combine (id_dot.i0de_loc, id_colon.i0de_loc)

in '{
  d0ynq_loc= loc
, d0ynq_node= D0YNQsymdot_symcolon (id_dot.i0de_sym, id_colon.i0de_sym)
} end // end of [d0ynq_symdot_symcolon]

(* ****** ****** *)

(* static qualified identifiers *)

implement sqi0de_make_some (q, id) = let
  val loc = combine (q.s0taq_loc, id.i0de_loc)
in '{
  sqi0de_loc= loc, sqi0de_qua= q, sqi0de_sym= id.i0de_sym
} end // end of [sqi0de_make_some]

implement sqi0de_make_none (id) =
  let val q = s0taq_none () in sqi0de_make_some (q, id) end

(* dynamic qualified identifiers *)

implement dqi0de_make_some (q, id) = let
  val loc = combine (q.d0ynq_loc, id.i0de_loc) in '{
  dqi0de_loc= loc, dqi0de_qua= q, dqi0de_sym= id.i0de_sym
} end // end of [dqi0de_make_some]

implement dqi0de_make_none (id) = begin
  let val q = d0ynq_none () in dqi0de_make_some (q, id) end
end // end of [dqi0de_make_none]

(* ****** ****** *)

implement
arrqi0de_make_some
  (q, id) = '{
  arrqi0de_loc= id.i0de_loc
, arrqi0de_qua= q, arrqi0de_sym= id.i0de_sym
} // end of [arrqi0de_make_some]

implement
arrqi0de_make_none (id) =
  let val q = d0ynq_none () in arrqi0de_make_some (q, id) end
// end of [arrqi0de_make_none]

(* ****** ****** *)

implement tmpqi0de_make_some (q, id) = let
  val loc = combine (q.d0ynq_loc, id.i0de_loc) in '{
  tmpqi0de_loc= loc, tmpqi0de_qua= q, tmpqi0de_sym= id.i0de_sym
} end // end of [tmpqi0de_make_some]

implement tmpqi0de_make_none (id) =
  let val q = d0ynq_none () in tmpqi0de_make_some (q, id) end
// end of [tmpqi0de_make_none]

(* ****** ****** *)

implement d0atarg_srt (s0tp) =
  '{ d0atarg_loc= s0tp.s0rtpol_loc, d0atarg_node= D0ATARGsrt s0tp }

implement d0atarg_id_srt (id, s0tp) =
  let val loc = combine (id.i0de_loc, s0tp.s0rtpol_loc) in
    '{ d0atarg_loc= loc, d0atarg_node= D0ATARGidsrt (id.i0de_sym, s0tp) }
  end

implement d0atarglst_nil () = nil ()
implement d0atarglst_cons (x, xs) = cons (x, xs)

implement d0atarglstopt_none () = None ()
implement d0atarglstopt_some (x) = Some (x)

(* ****** ****** *)

implement s0arg_make (id, osrt) = let
  val loc = (case+ osrt of
    | Some srt => combine (id.i0de_loc, srt.s0rt_loc)
    | None () => id.i0de_loc
  ) : loc_t
in '{
  s0arg_loc= loc, s0arg_sym= id.i0de_sym, s0arg_srt= osrt
} end // end of [s0arg_make]

implement s0arg_make_none (id) = '{
  s0arg_loc= id.i0de_loc, s0arg_sym= id.i0de_sym, s0arg_srt= None ()
}

implement s0arglst_nil () = nil ()
implement s0arglst_cons (x, xs) = cons (x, xs)

implement s0arglstlst_nil () = nil ()
implement s0arglstlst_cons (xs, xss) = cons (xs, xss)
implement s0arglstlst_cons_ide (id, xss) =
  let val x = s0arg_make_none (id) in cons (cons (x, nil), xss) end

(* ****** ****** *)

(* static patterns *)

implement
sp0at_con (qid, xs, t_end) = let
  val loc = combine (qid.sqi0de_loc, t_end.t0kn_loc)
in '{
  sp0at_loc= loc, sp0at_node= SP0Tcon (qid, xs)
} end // end of [s0pat_con]

(* ****** ****** *)

// for handling template ids
fn gtlt_t1mps0expseqseq_cons_loc (
    loc0: loc_t, s0es: s0explst, ts0ess: t1mps0explstlst
  ) : t1mps0explstlst = let
  fun aux
    (loc0: loc_t, s0e: s0exp, s0es: s0explst): loc_t =
    case+ s0es of
    | list_cons (s0e, s0es) => aux (loc0, s0e, s0es)
    | list_nil () => combine (loc0, s0e.s0exp_loc)
  // end of [aux]
  val loc = (case+ s0es of
    | list_cons (s0e, s0es) => aux (loc0, s0e, s0es)
    | list_nil () => loc0
  ) : loc_t // end of [val]
in
  T1MPS0EXPLSTLSTcons (loc, s0es, ts0ess)
end // end of [gtlt_t1mps0expseqseq_cons_loc]

implement gtlt_t1mps0expseqseq_nil () = T1MPS0EXPLSTLSTnil ()

implement gtlt_t1mps0expseqseq_cons_tok (t, s0es, ts0ess) =
  gtlt_t1mps0expseqseq_cons_loc (t.t0kn_loc, s0es, ts0ess)
// end of [gtltt1mps0expseqseq_cons_tok]

(* ****** ****** *)

(* static expressions *)

implement s0exp_ann (s0e, s0t) = let
  val loc = combine (s0e.s0exp_loc, s0t.s0rt_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eann (s0e, s0t)
} end // end of [s0exp_ann]

implement s0exp_app (s0e_fun, s0e_arg) = let
  val loc = combine (s0e_fun.s0exp_loc, s0e_arg.s0exp_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eapp (s0e_fun, s0e_arg)
} end // end of [s0exp_app]

implement s0exp_char (c) = '{
  s0exp_loc= c.c0har_loc, s0exp_node= S0Echar (c.c0har_val)
} // end of [s0exp_char]

implement
s0exp_exi (t_beg, knd, s0quas, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eexi (knd(*funres*), s0quas)
} end // end of [s0exp_exi]

(*
** HX-2010-12-05: for handling $extype with arguments
*)
implement
s0expext_nam (t, name) = S0EXT (t, name, nil)
implement
s0expext_app (s0ext, s0e) = let
  val+ S0EXT (t, name, s0es) = s0ext in S0EXT (t, name, cons (s0e, s0es))
end // end of [s0expext_app]
implement
s0exp_extern (s0ext) = let
  val+ S0EXT (t, name, s0es) = s0ext
  val loc = name.s0tring_loc
  val loc = loop (loc, s0es) where {
    fun loop (loc: loc_t, s0es: s0explst): loc_t =
      case+ s0es of
      | cons (s0e, s0es) => loop (s0e.s0exp_loc, s0es)
      | nil () => loc
    // end of [loop]
  } // end of [val]
  val loc = combine (t.t0kn_loc, loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eextype (name.s0tring_val, s0es)
} end // end of [s0exp_extern]

implement s0exp_ide (id) =  '{
  s0exp_loc= id.i0de_loc, s0exp_node= S0Eide id.i0de_sym
} // end of [s0exp_ide]

implement s0exp_int (i) = '{
  s0exp_loc= i.i0nt_loc, s0exp_node= S0Eint i.i0nt_val
} // end of [s0exp_int]

implement
s0exp_intsp_err (i) = let
  val () = prerr_loc_error0 (i.i0nt_loc)
  val () = prerr ": the specified integer ["
  val () = prerr (i.i0nt_val)
  val () = prerr "] is not allowed in statics."
  val () = prerr_newline ()
in
  $Err.abort {s0exp} ()
end // end of [s0exp_intsp_err]

implement
s0exp_imp (t_beg, efs, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eimp efs
} end // end of [s0exp_imp]

implement s0exp_imp_emp (t) = '{
  s0exp_loc= t.t0kn_loc, s0exp_node= S0Eimp (e0fftaglst_nil ())
} // end of [s0exp_imp_emp]

fn s0exp_lam ( // lam-expression construction
    loc: loc_t, arg: s0arglst, res: s0rtopt, body: s0exp
  ) : s0exp = '{
  s0exp_loc= loc , s0exp_node= S0Elam (arg, res, body)
} // end of [s0exp_lam]
 
implement
s0exp_lams (
  t_beg, args, res, body
) = let
  val loc = combine (t_beg.t0kn_loc, body.s0exp_loc)
  fun aux
    (arg0: s0arglst, args: s0arglstlst):<cloptr1> s0exp =
    case+ args of
    | cons (arg, args) => begin
        s0exp_lam (loc, arg0, s0rtopt_none (), aux (arg, args))
      end
    | nil () => s0exp_lam (loc, arg0, res, body)
  // end of [val]
in
  case+ args of
  | cons (arg, args) => aux (arg, args) | nil () => body
end // end of [s0exp_lams]

(* ****** ****** *)

implement s0exp_list (t_beg, s0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
  '{ s0exp_loc= loc, s0exp_node= S0Elist (s0es) }
end // end of [s0exp_list]

implement s0exp_list2
  (t_beg, s0es1, s0es2, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
  '{ s0exp_loc= loc, s0exp_node= S0Elist2 (s0es1, s0es2) }
end // end of [s0exp_list2]

(* ****** ****** *)

(*
// HX-2010-12-04: inadequate design
implement s0exp_named (ide, s0e) = let
  val loc = combine (ide.i0de_loc, s0e.s0exp_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Enamed (ide.i0de_sym, s0e)
} end // end of [s0exp_named]
*)

(* ****** ****** *)

implement s0exp_opide (t_op, id) = let
  val loc = combine (t_op.t0kn_loc, id.i0de_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eopide id.i0de_sym
} end // end of [s0exp_opide]

implement s0exp_qid (s0q, id) = let
  val loc = combine (s0q.s0taq_loc, id.i0de_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eqid(s0q, id.i0de_sym)
} end // end of [s0exp_qid]

(*
// HX-2010-11-01: simplification
implement
s0exp_struct (t_struct, ls0es, t_end) = let
  val loc = combine (t_struct.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Estruct ls0es
} end // end of [s0exp_struct]
*)

implement s0exp_tyarr (t_beg, elt, ind) = let
  val loc = combine (t_beg.t0kn_loc, ind.s0arrind_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Etyarr (elt, ind.s0arrind_ind)
} end // end of [s0exp_tyarr]

implement s0exp_tyrec
  (flat, t_beg, ls0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Etyrec (flat, ls0es)
} end // end of [s0exp_tyrec]

implement s0exp_tyrec_ext
  (t_beg, name(*s0tring*), ls0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Etyrec_ext (name.s0tring_val, ls0es)
} end // end of [s0exp_tyrec_ext]

implement s0exp_tytup
  (flat, t_beg, s0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Etytup (flat, s0es)
} end // end of [s0exp_tytup]

implement s0exp_tytup2
  (flat, t_beg, s0es1, s0es2, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Etytup2 (flat, s0es1, s0es2)
} end // end of [s0exp_tytup2]

implement s0exp_uni (t_beg, s0quas, t_end) =  let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Euni (s0quas)
} end // end of [s0exp_uni]

implement s0exp_union
  (t_union, ind, ls0es, t_end) = let
  val loc = combine (t_union.t0kn_loc, t_end.t0kn_loc)
in '{
  s0exp_loc= loc, s0exp_node= S0Eunion (ind, ls0es)
} end // end of [s0exp_union]

(* ****** ****** *)

implement s0explst_nil () = nil ()
implement s0explst_cons (x, xs) = cons (x, xs)

implement s0expopt_none () = None ()
implement s0expopt_some (x) = Some (x)

implement s0explstlst_nil () = nil ()
implement s0explstlst_cons (x, xs) = cons (x, xs)

implement s0explstopt_none () = None ()
implement s0explstopt_some (x) = Some (x)

(* ****** ****** *)

implement labs0explst_nil () = LABS0EXPLSTnil ()
implement labs0explst_cons (l, s0e, ls0es) = LABS0EXPLSTcons (l, s0e, ls0es)

(* ****** ****** *)

implement s0arrind_make_sing (s0es, t_rbracket) = '{
  s0arrind_loc= t_rbracket.t0kn_loc, s0arrind_ind= cons (s0es, nil ())
} // end of [s0arrind_make_sing]

implement s0arrind_make_cons (s0es, ind) = '{
  s0arrind_loc= ind.s0arrind_loc, s0arrind_ind= cons (s0es, ind.s0arrind_ind)
} // end of [s0arrind_make_cons]

(* ****** ****** *)

implement s0rtext_srt (s0t) =
  '{ s0rtext_loc= s0t.s0rt_loc, s0rtext_node= S0TEsrt s0t }

implement s0rtext_sub (t_beg, id, s0te, s0e, s0es, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ s0rtext_loc= loc, s0rtext_node= S0TEsub (id, s0te, s0e, s0es) }
  end

(* ****** ****** *)

implement s0qua_prop (s0e) = '{
  s0qua_loc= s0e.s0exp_loc, s0qua_node= S0QUAprop s0e
}

implement s0qua_vars (id, ids, s0te) =
  let val loc = combine (id.i0de_loc, s0te.s0rtext_loc) in
    '{ s0qua_loc= loc, s0qua_node= S0QUAvars (id, ids, s0te) }
  end

implement s0qualst_nil () = nil ()
implement s0qualst_cons (x, xs) = cons (x, xs)

implement s0qualstlst_nil () = nil ()
implement s0qualstlst_cons (x, xs) = cons (x, xs)

implement s0qualstopt_none () = None ()
implement s0qualstopt_some (x) = Some (x)

(* ****** ****** *)

implement
impqi0de_make_none (qid) = '{
  impqi0de_loc= qid.dqi0de_loc
, impqi0de_qua= qid.dqi0de_qua
, impqi0de_sym= qid.dqi0de_sym
, impqi0de_arg= gtlt_t1mps0expseqseq_nil ()
} // end of [impqi0de_make_none]

implement
impqi0de_make_some
  (qid, arg, args, t_gt) = let
  val loc_qid = qid.tmpqi0de_loc
  val loc_qid_end = $Loc.location_end_make loc_qid
  val loc = combine (loc_qid, t_gt.t0kn_loc)
  val args = gtlt_t1mps0expseqseq_cons_loc (loc_qid_end, arg, args)
in '{
  impqi0de_loc= loc
, impqi0de_qua= qid.tmpqi0de_qua
, impqi0de_sym= qid.tmpqi0de_sym
, impqi0de_arg= args
} end // end of [impqid0de_make_some]

(* ****** ****** *)

implement
i0nvarg_make_none (id) = '{
  i0nvarg_loc= id.i0de_loc
, i0nvarg_sym= id.i0de_sym, i0nvarg_typ= s0expopt_none ()
}

implement
i0nvarg_make_some (id, s0e) = let
  val loc = combine (id.i0de_loc, s0e.s0exp_loc)
in '{
  i0nvarg_loc= loc
, i0nvarg_sym= id.i0de_sym, i0nvarg_typ= s0expopt_some s0e 
} end // end of [i0nvarg_make_some]

implement i0nvarglst_nil () = nil ()
implement i0nvarglst_cons (x, xs) = cons (x, xs)

implement
i0nvresstate_none () = let
  val qua = s0qualstopt_none () and arg = i0nvarglst_nil ()
in '{
  i0nvresstate_qua= qua, i0nvresstate_arg= arg
} end // end of [i0nvresstate_none]

implement
i0nvresstate_some (qua, arg) = '{
  i0nvresstate_qua= qua, i0nvresstate_arg= arg
} // end of [i0nvresstate_some]

implement
loopi0nv_make (qua, met, arg, res) = '{
  loopi0nv_qua= qua
, loopi0nv_met= met
, loopi0nv_arg= arg
, loopi0nv_res= res
} // end of [loopi0nv_make]

(* ****** ****** *)

implement witht0ype_none () = WITHT0YPEnone ()
implement witht0ype_prop (s0e) = WITHT0YPEprop (s0e)
implement witht0ype_type (s0e) = WITHT0YPEtype (s0e)
implement witht0ype_view (s0e) = WITHT0YPEview (s0e)
implement witht0ype_viewtype (s0e) = WITHT0YPEviewtype (s0e)

(* ****** ****** *)

implement s0rtdef_make (id, def) = let
(*
  val () = print "s0rtdef_make:\n"
  val () = begin
    print "def.loc = "; print def.s0rtext_loc; print_newline ()
  end // end of [val]
*)
  val loc = combine (id.i0de_loc, def.s0rtext_loc)
in '{
  s0rtdef_loc= loc
, s0rtdef_sym= id.i0de_sym
, s0rtdef_def= def
} end // end of [s0rtdef_make]

implement s0rtdeflst_nil () = nil ()
implement s0rtdeflst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
s0tacon_make_none_none
  (id) = let
  val fil = $Fil.the_filename_get ()
in '{
  s0tacon_fil= fil
, s0tacon_loc= id.i0de_loc
, s0tacon_sym= id.i0de_sym
, s0tacon_arg= None ()
, s0tacon_def= None ()
} end // end of [s0tacon_make_none_none]

implement
s0tacon_make_some_none
  (id, arg) = let
  val fil = $Fil.the_filename_get ()
in '{
  s0tacon_fil= fil
, s0tacon_loc= id.i0de_loc
, s0tacon_sym= id.i0de_sym
, s0tacon_arg= Some arg
, s0tacon_def= None ()
} end // end of [s0tacon_make_some_none]

implement
s0tacon_make_none_some
  (id, def) = let
  val fil = $Fil.the_filename_get ()
  val loc = combine (id.i0de_loc, def.s0exp_loc) in '{
  s0tacon_fil= fil
, s0tacon_loc= loc
, s0tacon_sym= id.i0de_sym
, s0tacon_arg= None ()
, s0tacon_def= Some def
} end // end of [s0tacon_make_none_some]

implement
s0tacon_make_some_some
  (id, arg, def) = let
  val fil = $Fil.the_filename_get ()
  val loc = combine (id.i0de_loc, def.s0exp_loc) in '{
  s0tacon_fil= fil
, s0tacon_loc= loc
, s0tacon_sym= id.i0de_sym
, s0tacon_arg= Some arg
, s0tacon_def= Some def
} end // end of [s0tacon_make_some_some]

implement s0taconlst_nil () = nil ()
implement s0taconlst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
s0tacst_make_none
  (id, s0t) = let
  val fil = $Fil.the_filename_get ()
  val loc = combine (id.i0de_loc, s0t.s0rt_loc)
in '{
  s0tacst_fil= fil
, s0tacst_loc= loc
, s0tacst_sym= id.i0de_sym
, s0tacst_arg= None ()
, s0tacst_res= s0t
} end // end of [s0tacst_make_none]

implement
s0tacst_make_some
  (id, arg, s0t) = let
  val fil = $Fil.the_filename_get ()
  val loc = combine (id.i0de_loc, s0t.s0rt_loc)
in '{
  s0tacst_fil= fil
, s0tacst_loc= loc
, s0tacst_sym= id.i0de_sym
, s0tacst_arg= Some arg
, s0tacst_res= s0t
} end // end of [s0tacst_make_some]

implement s0tacstlst_nil () = nil ()
implement s0tacstlst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
s0tavar_make (id, s0t) = let
  val loc = combine (id.i0de_loc, s0t.s0rt_loc)
in '{
  s0tavar_loc= loc
, s0tavar_sym= id.i0de_sym
, s0tavar_srt= s0t
} end // end of [s0tavar_make]

implement s0tavarlst_nil () = nil ()
implement s0tavarlst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
s0expdef_make (
 id, arg, res, def
) = let
  val loc = combine (id.i0de_loc, def.s0exp_loc)
in '{
  s0expdef_loc= loc
, s0expdef_sym= id.i0de_sym
, s0expdef_loc_id= id.i0de_loc
, s0expdef_arg= arg
, s0expdef_res= res
, s0expdef_def= def
} end // end of [s0expdef_make]

implement s0expdeflst_nil () = nil ()
implement s0expdeflst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
s0aspdec_make
  (qid, arg, res, def) = let
  val fil = $Fil.the_filename_get ()
  val loc = combine (qid.sqi0de_loc, def.s0exp_loc)
in '{
  s0aspdec_fil= fil
, s0aspdec_loc= loc
, s0aspdec_qid= qid
, s0aspdec_arg= arg
, s0aspdec_res= res
, s0aspdec_def= def
} end // end of [s0aspdec_make]

(* ****** ****** *)

implement
d0atcon_make (
  qua, id, ind, arg
) = let
  val loc = id.i0de_loc
  val loc = (case+ arg of
    | Some s0e => combine (loc, s0e.s0exp_loc)
    | None () => begin case+ ind of
      | Some s0e => combine (loc, s0e.s0exp_loc) | _ => loc
      end // end of [None]
  ) : loc_t // end of [val]
in '{
  d0atcon_loc= loc
, d0atcon_sym= id.i0de_sym
, d0atcon_qua= qua
, d0atcon_arg= arg
, d0atcon_ind= ind
} end // end of [d0atcon_make]

implement d0atconlst_nil () = nil ()
implement d0atconlst_cons (x, xs) = cons (x, xs)

fun d0atdec_make
(
  id: i0de
, hdloc: loc_t
, arg: d0atarglstopt
, xs: d0atconlst
) : d0atdec = let
//
fun aux_loc
(
  id: i0de, x: d0atcon, xs: d0atconlst
) : loc_t =
(
case+ xs of
| cons (x, xs) => aux_loc (id, x, xs)
| nil () => combine (id.i0de_loc, x.d0atcon_loc)
) (* end of [aux_loc] *)
//
val fil = $Fil.the_filename_get ()
val loc =
(
case+ xs of
| cons (x, xs) => aux_loc (id, x, xs) | nil () => id.i0de_loc
) : loc_t
//
in '{
  d0atdec_fil= fil
, d0atdec_loc= loc
, d0atdec_headloc= hdloc
, d0atdec_sym= id.i0de_sym
, d0atdec_arg= arg
, d0atdec_con= xs
} end // end of [d0atdec_make]

implement
d0atdec_make_none (id, xs) =
(
  d0atdec_make (id, id.i0de_loc, None (), xs)
)

implement
d0atdec_make_some
  (id, arg, tok, xs) = let
  val loc_id = id.i0de_loc
  val loc = combine (loc_id, tok.t0kn_loc)
in
  d0atdec_make (id, loc, Some arg, xs)
end // end of [d0atdec_make_some]

implement d0atdeclst_nil () = list_nil ()
implement d0atdeclst_cons (x, xs) = list_cons (x, xs)

(* ****** ****** *)

implement
e0xndec_make
  (qua, id, arg) = let
  val loc = (case+ arg of
    | Some s0e => combine (id.i0de_loc, s0e.s0exp_loc)
    | None () => id.i0de_loc
  ) : loc_t
  val fil = $Fil.the_filename_get ()
in '{
  e0xndec_fil= fil
, e0xndec_loc= loc
, e0xndec_sym= id.i0de_sym
, e0xndec_qua= qua
, e0xndec_arg= arg
} end // end of [e0xndec_make]

implement e0xndeclst_nil () = list_nil ()
implement e0xndeclst_cons (x, xs) = list_cons (x, xs)

(* ****** ****** *)

implement p0arg_make_none (id) =
  '{ p0arg_loc= id.i0de_loc, p0arg_sym= id.i0de_sym, p0arg_ann= None () }

implement p0arg_make_some (id, s0e) = let
  val loc = combine (id.i0de_loc, s0e.s0exp_loc)
in '{
  p0arg_loc= loc, p0arg_sym= id.i0de_sym, p0arg_ann= Some s0e
} end // end of [p0arg_make_some]

implement p0arglst_nil () = list_nil ()
implement p0arglst_cons (x, xs) = list_cons (x, xs)

(* ****** ****** *)

implement
d0arg_var (id) = let
//
val arg =
  p0arglst_cons
    (p0arg_make_none id, p0arglst_nil ())
//
in '{
  d0arg_loc= id.i0de_loc, d0arg_node= D0ARGdyn arg
} end // end of [d0arg_var]

implement
d0arg_dyn (t_beg, arg, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ d0arg_loc= loc, d0arg_node= D0ARGdyn arg }
  end

implement
d0arg_dyn2 (t_beg, arg1, arg2, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ d0arg_loc= loc, d0arg_node= D0ARGdyn2 (arg1, arg2) }
  end

implement
d0arg_sta (t_beg, arg, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ d0arg_loc= loc, d0arg_node= D0ARGsta arg }
  end

implement d0arglst_nil () = nil ()
implement d0arglst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement m0acarg_one (x) = M0ACARGone (x)
implement m0acarg_lst (t_beg, xs, t_end) = M0ACARGlst (xs)

implement m0acarglst_nil () = nil ()
implement m0acarglst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement dcstextdef_is_mac (x) =
  case+ x of DCSTEXTDEFsome_mac _ => true | _ => false
// end of [dcstextdef_is_mac]

implement dcstextdef_is_sta (x) =
  case+ x of DCSTEXTDEFsome_sta _ => true | _ => false
// end of [dcstextdef_is_sta]

(* ****** ****** *)

implement extnamopt_none () = stropt_none
implement extnamopt_some (ext) = let
(*
  val () = begin
    print "extnamopt_some: ext = "; print ext.s0tring_val; print_newline ()
  end // end of [val]
*)
in
  stropt_some (string1_of_string ext.s0tring_val)
end // end of [extnamopt_some]

implement d0cstdec_make
  (id, arg, eff, res, extdef) = let
  val fil = $Fil.the_filename_get ()
  val loc = combine (id.i0de_loc, res.s0exp_loc)
in '{
  d0cstdec_fil= fil
, d0cstdec_loc= loc
, d0cstdec_sym= id.i0de_sym
, d0cstdec_arg= arg
, d0cstdec_eff= eff
, d0cstdec_res= res
, d0cstdec_extdef= extdef
} end // end of [d0cstdec_make]

implement d0cstdeclst_nil () = nil ()
implement d0cstdeclst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement s0vararg_one () = S0VARARGone ()
implement s0vararg_all () = S0VARARGall ()
implement s0vararg_seq (s0es) = S0VARARGseq s0es

(* ****** ****** *)

(*
** HX: dynamic patterns
*)

implement p0at_ann (p0t, s0e) =
  let val loc = combine (p0t.p0at_loc, s0e.s0exp_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tann (p0t, s0e) }
  end

fn p0at_app (p0t_fun: p0at, p0t_arg: p0at): p0at =
  let val loc = combine (p0t_fun.p0at_loc, p0t_arg.p0at_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tapp (p0t_fun, p0t_arg) }
  end

implement p0at_apps (p0t_fun, p0ts_arg) =
  case+ p0ts_arg of
    | cons (p0t_arg, p0ts_arg) =>
      let val p0t_fun = p0at_app (p0t_fun, p0t_arg) in
        p0at_apps (p0t_fun, p0ts_arg)
      end
    | nil () => p0t_fun

implement p0at_as (id: i0de, p0t: p0at) =
  let val loc = combine (id.i0de_loc, p0t.p0at_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tas(id, p0t) }
  end

implement p0at_char (c) = '{
  p0at_loc= c.c0har_loc, p0at_node= P0Tchar c.c0har_val
}

implement p0at_exist (t_beg, qua, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Texist qua }
  end

implement p0at_float (f) = '{
  p0at_loc= f.f0loat_loc, p0at_node= P0Tfloat f.f0loat_val
}

implement p0at_free (t_tilde, p0t) =
  let val loc = combine (t_tilde.t0kn_loc, p0t.p0at_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tfree p0t }
  end

implement p0at_ide (id) = '{
  p0at_loc= id.i0de_loc, p0at_node= P0Tide id.i0de_sym
}

implement p0at_int (int) = '{
  p0at_loc= int.i0nt_loc
, p0at_node= P0Tint (int.i0nt_val)
}

implement p0at_list (t_beg, p0ts, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tlist (p0ts) }
  end

implement p0at_list2 (t_beg, p0ts1, p0ts2, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tlist2 (p0ts1, p0ts2) }
  end

implement p0at_lst (t_beg, p0ts, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tlst (p0ts) }
  end

implement p0at_opide (t_op, id) = let
  val loc = combine (t_op.t0kn_loc, id.i0de_loc)
in '{
  p0at_loc= loc, p0at_node= P0Topide id.i0de_sym
} end // end of [p0at_opide]

implement p0at_qid (d0q, id) =
  let val loc = combine (d0q.d0ynq_loc, id.i0de_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tqid(d0q, id.i0de_sym) }
  end

implement p0at_rec (flat, t_beg, lp0ts, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Trec (flat, lp0ts) }
  end

implement p0at_ref (t_bang, ide) =
  let val loc = combine (t_bang.t0kn_loc, ide.i0de_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tref ide }
  end

implement p0at_refas (t_bang, ide, p0t) =
  let val loc = combine (t_bang.t0kn_loc, p0t.p0at_loc) in
    '{ p0at_loc= loc, p0at_node= P0Trefas (ide, p0t) }
  end

implement p0at_string (s) = '{
  p0at_loc= s.s0tring_loc, p0at_node= P0Tstring s.s0tring_val
}

implement p0at_svararg (t_beg, arg, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Tsvararg arg }
  end

implement p0at_tup (flat, t_beg, p0ts, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Ttup (flat, p0ts) }
  end

implement p0at_tup2 (flat, t_beg, p0ts1, p0ts2, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ p0at_loc= loc, p0at_node= P0Ttup2 (flat, p0ts1, p0ts2) }
  end

//

implement p0atlst_nil () = nil ()
implement p0atlst_cons (x, xs) = cons (x, xs)

implement p0atopt_none () = None ()
implement p0atopt_some (p0t) = Some p0t

implement labp0atlst_nil () = LABP0ATLSTnil ()
implement labp0atlst_dot () = LABP0ATLSTdot ()
implement labp0atlst_cons (l, x, lxs) = LABP0ATLSTcons (l, x, lxs)

(* ****** ****** *)

implement f0arg_sta1 (t_beg, s0qs, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ f0arg_loc= loc, f0arg_node= F0ARGsta1 s0qs }
  end

implement f0arg_sta2 (t_beg, s0as, t_end) =
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ f0arg_loc= loc, f0arg_node= F0ARGsta2 s0as }
  end

implement f0arg_dyn (p0t) = '{
  f0arg_loc= p0t.p0at_loc, f0arg_node= F0ARGdyn p0t
}

implement f0arg_met_none (t) = '{
  f0arg_loc= t.t0kn_loc, f0arg_node= F0ARGmet (s0explst_nil ())
}

implement f0arg_met_some (t_beg, s0es, t_end) = 
  let val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc) in
    '{ f0arg_loc= loc, f0arg_node= F0ARGmet s0es }
  end

implement f0arglst_nil () = nil ()
implement f0arglst_cons(x, xs) = cons (x, xs)

(* ****** ****** *)

implement s0elop_make (knd, t) = '{
  s0elop_loc= t.t0kn_loc, s0elop_knd= knd
}

(* ****** ****** *)

implement s0exparg_one () = S0EXPARGone ()
implement s0exparg_all () = S0EXPARGall ()
implement s0exparg_seq (s0es) = S0EXPARGseq s0es

(* ****** ****** *)

implement
d0exp_ann (d0e, s0e) = let
  val loc = combine
    (d0e.d0exp_loc, s0e.s0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eann (d0e, s0e)
} end // end of [d0exp_ann]

fn d0exp_app (
  d0e_fun: d0exp, d0e_arg: d0exp
) : d0exp = let
  val loc = combine
    (d0e_fun.d0exp_loc, d0e_arg.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eapp (d0e_fun, d0e_arg)
} end // end of [d0exp_app]

implement
d0exp_apps
  (d0e_fun, d0es_arg) =
  case+ d0es_arg of
  | cons (d0e_arg, d0es_arg) => let
      val d0e_fun = d0exp_app (d0e_fun, d0e_arg)
    in
      d0exp_apps (d0e_fun, d0es_arg)
    end // end of [cons]
  | nil () => d0e_fun // end of [nil]
// end of [d0exp_apps]

(* ****** ****** *)

implement
d0exp_arrinit (
  t_beg, s0e_elt, od0e_asz, d0es_elt, t_end
) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
  val () = // checking the syntax for array assignmnet
    case+ od0e_asz of
    | Some _ => begin case+ d0es_elt of
      // if the array size if given, the rules for using [d0es_elt] is
      // given as follows:
      // 1. if [d0es_elt] is empty, then the array is uninitialized;
      // 2. if [d0es_elt] contains only one element, then the array is
      //    initialized with this element.
      // 3. if [d0es_elt] contains two or more elements, it is illegal
      | list_cons (_, list_cons (_, _)) => begin
          prerr_loc_error0 (loc);
          prerr ": the syntax for array initialization is incorrect.";
          prerr_newline (); $Err.abort {void} ()
        end // end of [list_cons (_, list_cons)]
      | _ => () // [d0es_elt] contains at most one element
      end // end of [Some]
    | None () => ()
  // end of [val]
in '{
  d0exp_loc= loc, d0exp_node= D0Earrinit (s0e_elt, od0e_asz, d0es_elt)
} end // end of [d0exp_arrinit]

(* ****** ****** *)

implement
d0exp_arrinit_none
  (t_beg, s0e_elt, d0es_elt, t_end) =
  d0exp_arrinit (t_beg, s0e_elt, None (), d0es_elt, t_end)
// end of [d0exp_arrinit_none]

implement
d0exp_arrinit_some
  (t_beg, s0e_elt, d0e_asz, d0es_elt, t_end) =
  d0exp_arrinit (t_beg, s0e_elt, Some d0e_asz, d0es_elt, t_end)
// end of [d0exp_arrinit_some]

(* ****** ****** *)

implement
d0exp_arrpsz (
  t_beg, os0e, t_lp, d0es, t_rp
) = let
  val loc = combine (t_beg.t0kn_loc, t_rp.t0kn_loc)
  val d0e_elts = (case+ d0es of
    | cons (d0e, nil ()) => d0e
    | _ => d0exp_list (t_lp, d0es, t_rp)
  ) : d0exp // end of [val]
in '{
  d0exp_loc= loc, d0exp_node= D0Earrpsz (os0e, d0e_elts)
} end // end of [d0exp_arrpsz]

(* ****** ****** *)

implement
d0exp_arrsub (qid, ind) = let
  val loc_ind = ind.d0arrind_loc
  val loc = combine (qid.arrqi0de_loc, loc_ind)
in '{
  d0exp_loc= loc
, d0exp_node= D0Earrsub (qid, loc_ind, ind.d0arrind_ind)
} end // end of [d0exp_arrsub]

(* ****** ****** *)

implement
d0exp_char (c) = '{
  d0exp_loc= c.c0har_loc, d0exp_node= D0Echar c.c0har_val
} // end of [d0exp_char]

implement
d0exp_caseof (hd, d0e, t_of, c0ls) = let
  fun aux_loc (
    t_case: t0kn, c0l: c0lau, c0ls: c0laulst
  ) : loc_t =
    case+ c0ls of
    | cons (c0l, c0ls) => aux_loc (t_case, c0l, c0ls)
    | nil () => combine (t_case.t0kn_loc, c0l.c0lau_loc)
  // end of [aux_loc]
  val t_case = hd.casehead_tok; val loc = case+ c0ls of
    | cons (c0l, c0ls) => aux_loc (t_case, c0l, c0ls)
    | nil () => combine (t_case.t0kn_loc, t_of.t0kn_loc)
  // end of [val]
in
  '{ d0exp_loc= loc, d0exp_node= D0Ecaseof (hd, d0e, c0ls) }
end // end of [d0exp_caseof]

implement
d0exp_crypt (knd(*de/en*), t_crypt) = '{
  d0exp_loc= t_crypt.t0kn_loc, d0exp_node= D0Ecrypt knd
} // end of [d0exp_crypt]

implement
d0exp_decseq
  (t_lbrace, d0cs, t_rbrace) = let
  val loc = combine (
    t_lbrace.t0kn_loc, t_rbrace.t0kn_loc
  ) // end of [val]
in '{
  d0exp_loc= loc, d0exp_node= D0Edecseq (d0cs)
} end // end of [d0exp_decseq]

implement
d0exp_delay (lin, t_delay) = '{
  d0exp_loc= t_delay.t0kn_loc, d0exp_node= D0Edelay (lin)
} // end of [d0exp_delay]

implement
d0exp_dynload (t_delay) = '{
  d0exp_loc= t_delay.t0kn_loc, d0exp_node= D0Edynload ()
} // end of [d0exp_dynload]

implement
d0exp_empty (loc) = '{
  d0exp_loc= loc, d0exp_node= D0Eempty ()
} // end of [d0exp_empty]

implement
d0exp_exist
  (t_beg, s0a, t_bar, d0e, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
  val qualoc = combine (t_beg.t0kn_loc, t_bar.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eexist (qualoc, s0a, d0e)
} end // end of [d0exp_exist]

implement
d0exp_extval
  (t_beg, s0e, s0tr, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
  val code = s0tr.s0tring_val
in '{
  d0exp_loc= loc, d0exp_node= D0Eextval (s0e, code)
} end // end of [d0exp_extval]

implement
d0exp_fix
  (knd, id, arg, res, eff, d0e) = let
  val loc_knd = lamkind_get_loc (knd)
  val loc = combine (loc_knd, d0e.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Efix (knd, id, arg, res, eff, d0e)
} end // end of [d0exp_fix]

implement
d0exp_float (f) = '{
  d0exp_loc= f.f0loat_loc, d0exp_node= D0Efloat (f.f0loat_val)
} // end of [d0exp_float]

implement
d0exp_floatsp (f) = '{
  d0exp_loc= f.f0loatsp_loc, d0exp_node= D0Efloatsp (f.f0loatsp_val)
} // end of [d0exp_floatsp]

(* ****** ****** *)

implement
d0exp_foldat (t_foldat, d0es) = let
  fun aux (d0e: d0exp, d0es: d0explst):<cloptr1> loc_t =
    case+ d0es of
    | cons (d0e, d0es) => aux (d0e, d0es)
    | nil () => combine (t_foldat.t0kn_loc, d0e.d0exp_loc)
  val loc = case+ d0es of
    | cons (d0e, d0es) => aux (d0e, d0es) | nil () => t_foldat.t0kn_loc
in '{
  d0exp_loc= loc, d0exp_node= D0Efoldat d0es
} end // end of [d0exp_foldat]

(* ****** ****** *)

implement
d0exp_for_itp (hd, itp, body) = let
  val t_loop = hd.loophead_tok
  val loc_inv = t_loop.t0kn_loc
  val loc = $Loc.location_combine (loc_inv, body.d0exp_loc)
(*
  val () = begin
    $Loc.print_location loc; print ": d0exp_for_itp"; print_newline ()
  end // end of [val]
*)
  val inv = hd.loophead_inv
in '{
  d0exp_loc= loc
, d0exp_node= D0Efor (inv, loc_inv, itp.0, itp.1, itp.2, body)
} end // end of [d0exp_for_itp]

(* ****** ****** *)

implement
d0exp_freeat (t_freeat, d0es) = let
  fun aux (d0e: d0exp, d0es: d0explst):<cloptr1> loc_t =
    case+ d0es of
    | cons (d0e, d0es) => aux (d0e, d0es)
    | nil () => combine (t_freeat.t0kn_loc, d0e.d0exp_loc)
  val loc = case+ d0es of
    | cons (d0e, d0es) => aux (d0e, d0es) | nil () => t_freeat.t0kn_loc
in '{
  d0exp_loc= loc, d0exp_node= D0Efreeat d0es
} end // end of [d0exp_freeat]

(* ****** ****** *)

implement
d0exp_ide (id) = let
  val sym_id = id.i0de_sym
in
  if sym_id = $Sym.symbol_QMARK then begin
    '{ d0exp_loc= id.i0de_loc, d0exp_node= D0Etop () }
  end else begin
    '{ d0exp_loc= id.i0de_loc, d0exp_node= D0Eide sym_id }
  end // end of [if]
end (* end of [d0exp_ide] *)

implement
d0exp_idext (id) = '{
  d0exp_loc= id.i0de_loc, d0exp_node= D0Eidext (id.i0de_sym)
} // end of [d0exp_i0dext]

(* ****** ****** *)

implement
d0exp_if_none
  (hd, d0e_cond, d0e_then) = let
  val t_if = hd.ifhead_tok
  val loc = combine (t_if.t0kn_loc, d0e_then.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eif (hd, d0e_cond, d0e_then, None ())
} end // end of [d0exp_if_none]

implement
d0exp_if_some (
  hd, d0e_cond, d0e_then, d0e_else
) = let
  val t_if = hd.ifhead_tok
  val loc = combine (t_if.t0kn_loc, d0e_else.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eif (hd, d0e_cond, d0e_then, Some d0e_else)
} end // end of [d0exp_if_some]

(* ****** ****** *)

implement d0exp_int (i) = '{
  d0exp_loc= i.i0nt_loc, d0exp_node= D0Eint (i.i0nt_val)
} // end of [d0exp_int]

implement d0exp_intsp (i) = '{
  d0exp_loc= i.i0ntsp_loc, d0exp_node= D0Eintsp (i.i0ntsp_val)
} // end of [d0exp_intsp]

(* ****** ****** *)

implement d0exp_lam
  (knd, arg, res, eff, d0e) = let
  val loc_knd = lamkind_get_loc (knd)
  val loc = combine (loc_knd, d0e.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Elam (knd, arg, res, eff, d0e)
} end // end of [d0exp_lam]

(* ****** ****** *)

implement
d0exp_let_seq
  (t_beg, d0cs, t_in, d0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
  val d0e = d0exp_seq (t_in, d0es, t_end)
in '{
  d0exp_loc= loc, d0exp_node= D0Elet (d0cs, d0e)
} end // end of [d0exp_let_seq]

(* ****** ****** *)

implement
d0exp_list
  (t_beg, d0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Elist d0es
} end // end of [d0exp_list]

implement
d0exp_list2
  (t_beg, d0es1, d0es2, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Elist2 (d0es1, d0es2)
} end // end of [d0exp_list2]

(* ****** ****** *)

implement d0exp_loopexn (i, t) = 
  '{ d0exp_loc= t.t0kn_loc, d0exp_node= D0Eloopexn i }
// end of [d0exp_loopexn]

(* ****** ****** *)

implement
d0exp_lst (
  lin, t_beg, os0e, t_lp, d0es, t_rp
) = let
  val loc = combine (t_beg.t0kn_loc, t_rp.t0kn_loc)
  val d0e_elts = (case+ d0es of
    | cons (d0e, nil ()) => d0e
    | _ => d0exp_list (t_lp, d0es, t_rp)
  ) : d0exp // end of [val]
in '{
  d0exp_loc= loc, d0exp_node= D0Elst (lin, os0e, d0e_elts)
} end // end of [d0exp_lst]

implement
d0exp_lst_quote (
  t_beg, d0es_elt, t_end
) = let
  val d0e_elts = d0exp_list (t_beg, d0es_elt, t_end)
  val loc = d0e_elts.d0exp_loc
in '{
  d0exp_loc= loc, d0exp_node= D0Elst (0, s0expopt_none (), d0e_elts)
} end // end of [d0exp_lst_quote]

(* ****** ****** *)

local

fun d0exp_macsyn
  (loc: loc_t, knd: macsynkind, d0e: d0exp): d0exp = '{
  d0exp_loc= loc, d0exp_node= D0Emacsyn (knd, d0e)
} // end of [d0exp_macsyn]

in (* in of [local] *)

implement d0exp_macsyn_cross (t_beg, d0e, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in
  d0exp_macsyn (loc, MACSYNKINDcross, d0e)
end // end of [d0exp_macsyn_cross]

implement d0exp_macsyn_decode (t_beg, d0e, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in
  d0exp_macsyn (loc, MACSYNKINDdecode, d0e)
end // end of [d0exp_macsyn_decode]

implement d0exp_macsyn_encode_seq (t_beg, d0es, t_end) = let
  val d0e = d0exp_seq (t_beg, d0es, t_end)
in
  d0exp_macsyn (d0e.d0exp_loc, MACSYNKINDencode, d0e)
end // end of [d0exp_macsyn_encode_seq]

end // end of [local]

(* ****** ****** *)

implement d0exp_opide (t_op, id) = let
  val loc = combine (t_op.t0kn_loc, id.i0de_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eopide id.i0de_sym
} end // end of [d0exp_opide]

implement d0exp_ptrof (t_amp) =
  '{ d0exp_loc= t_amp.t0kn_loc, d0exp_node= D0Eptrof () }
// end of [d0exp_ptrof]

implement d0exp_qid (d0q, id) = let
  val loc_q = d0q.d0ynq_loc and loc_id = id.i0de_loc
  val loc = combine (loc_q, loc_id)
in '{
  d0exp_loc= loc, d0exp_node= D0Eqid(d0q, id.i0de_sym)
} end // end of [d0exp_qid]

implement
d0exp_raise (t_raise, d0e) = let
  val loc = combine (t_raise.t0kn_loc, d0e.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eraise (d0e)
} end // end of [d0exp_raise]

implement d0exp_rec
  (flat, t_beg, ld0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Erec (flat, ld0es)
} end // end of [d0exp_rec]

implement d0exp_scaseof (hd, s0e, t_of, sc0ls) = let
  fun aux_loc (t_case: t0kn, sc0l: sc0lau, sc0ls: sc0laulst): loc_t =
    case+ sc0ls of
    | cons (sc0l, sc0ls) => aux_loc (t_case, sc0l, sc0ls)
    | nil () => combine (t_case.t0kn_loc, sc0l.sc0lau_loc)
  // end of [aux_loc]
  val t_case = hd.casehead_tok
  val loc = case+ sc0ls of
    | cons (sc0l, sc0ls) => aux_loc (t_case, sc0l, sc0ls)
    | nil () => combine (t_case.t0kn_loc, t_of.t0kn_loc)
  // end of [val]
in '{
  d0exp_loc= loc, d0exp_node= D0Escaseof (hd, s0e, sc0ls)
} end // end of [d0exp_case]

implement d0exp_sel_lab (sel, lab) =
  let val loc = combine (sel.s0elop_loc, lab.l0ab_loc) in
    '{ d0exp_loc= loc, d0exp_node= D0Esel_lab (sel.s0elop_knd, lab.l0ab_lab) }
  end

implement d0exp_sel_ind (sel, ind) = let
  val loc = combine (sel.s0elop_loc, ind.d0arrind_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Esel_ind (sel.s0elop_knd, ind.d0arrind_ind)
} end // end of [d0exp_sel_ind]

implement d0exp_seq (t_beg, d0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in
  case+ d0es of
  | cons _ => '{ d0exp_loc= loc, d0exp_node= D0Eseq d0es }
  | nil () => d0exp_empty (loc)
end // end of [d0exp_seq]

implement
d0exp_sexparg
  (t_beg, s0a, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Esexparg s0a
} end // end of [d0exp_sexparg]

implement
d0exp_showtype (t_showtype, d0e) = let
  val loc = combine (t_showtype.t0kn_loc, d0e.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Eshowtype (d0e)
} end // end of [d0exp_showtype]

implement
d0exp_sif (
  hd, s0e_cond, d0e_then, d0e_else
) = let
  val t_sif = hd.ifhead_tok
  val loc = combine (t_sif.t0kn_loc, d0e_else.d0exp_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Esif (hd, s0e_cond, d0e_then, d0e_else)
} end // end of [d0exp_sif]

implement
d0exp_string (s) = '{
  d0exp_loc= s.s0tring_loc
, d0exp_node= D0Estring (s.s0tring_val, s.s0tring_len)
} // end of [d0exp_string]

implement
d0exp_tmpid
  (qid, arg, args, t_gt) = let
  val loc_qid = qid.tmpqi0de_loc
  val loc_qid_end = $Loc.location_end_make loc_qid
  val loc = combine (loc_qid, t_gt.t0kn_loc)
  val args = gtlt_t1mps0expseqseq_cons_loc (loc_qid_end, arg, args) 
in
  '{ d0exp_loc= loc, d0exp_node= D0Etmpid (qid, args) }
end // end of [d0exp_tmpid]

implement d0exp_trywith_seq (hd, d0es, t_with, c0ls) = let
  fun aux_loc
    (t_try: t0kn, c0l: c0lau, c0ls: c0laulst): loc_t =
    case+ c0ls of
    | cons (c0l, c0ls) => aux_loc (t_try, c0l, c0ls)
    | nil () => combine (t_try.t0kn_loc, c0l.c0lau_loc)
  // end of [aux_loc]
  val t_try = hd.tryhead_tok
  val loc = case+ c0ls of
    | cons (c0l, c0ls) => aux_loc (t_try, c0l, c0ls)
    | nil () => combine (t_try.t0kn_loc, t_with.t0kn_loc)
  // end of [val]
  val d0e = d0exp_seq (t_try, d0es, t_with)
in '{
  d0exp_loc= loc, d0exp_node= D0Etrywith (hd, d0e, c0ls)
} end // end of [d0exp_trywith]

implement d0exp_tup
  (flat, t_beg, d0es, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Etup (flat, d0es)
} end // end of [d0exp_tup]

implement d0exp_tup2
  (flat, t_beg, d0es1, d0es2, t_end) = let
  val loc = combine (t_beg.t0kn_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Etup2 (flat, d0es1, d0es2)
} end // end of [d0exp_tup2]

implement d0exp_viewat (t_viewat) = '{
  d0exp_loc= t_viewat.t0kn_loc, d0exp_node= D0Eviewat ()
} // end of [d0exp_viewat]

implement d0exp_where (d0e, d0cs, t_end) = let
  val loc = combine (d0e.d0exp_loc, t_end.t0kn_loc)
in '{
  d0exp_loc= loc, d0exp_node= D0Ewhere (d0e, d0cs)
} end // end of [d0exp_where]

implement d0exp_while (hd, test, body) = let
  val t_loop = hd.loophead_tok
  val loc_inv = t_loop.t0kn_loc
  val loc = combine (loc_inv, body.d0exp_loc)
  val inv = hd.loophead_inv
in '{ 
  d0exp_loc= loc, d0exp_node= D0Ewhile (inv, loc_inv, test, body)
} end // end of [d0exp_while]

// ------ ------

(*
** for special constants
*)

implement d0exp_FILENAME (tok) = '{
  d0exp_loc= tok.t0kn_loc, d0exp_node= D0Ecstsp CSTSPfilename
}

implement d0exp_LOCATION (tok) = '{
  d0exp_loc= tok.t0kn_loc, d0exp_node= D0Ecstsp CSTSPlocation
}

(* ****** ****** *)

implement d0explst_nil () = nil ()
implement d0explst_cons (x, xs) = cons (x, xs)
implement d0explst_sing (x) = cons (x, nil ())

implement d0expopt_none () = None ()
implement d0expopt_some (x) = Some (x)

implement labd0explst_nil () = LABD0EXPLSTnil ()
implement labd0explst_cons (l, x, lxs) = LABD0EXPLSTcons (l, x, lxs)

implement d0explstopt_none () = None ()
implement d0explstopt_some (xs) = Some (xs)

// ------ ------

implement d0arrind_make_sing (d0es, t_rbracket) = '{
  d0arrind_loc= t_rbracket.t0kn_loc, d0arrind_ind= cons (d0es, nil ())
} // end of [d0arrind_make_sing]

implement d0arrind_make_cons (d0es, ind) = '{
  d0arrind_loc= ind.d0arrind_loc, d0arrind_ind= cons (d0es, ind.d0arrind_ind)
} // end of [d0arrind_make_cons]

// ------ ------

implement initestpost_make
  (t1, d0es_ini, t2, d0es_test, t3, d0es_post, t4) = let
  val d0e_ini = d0exp_seq (t1, d0es_ini, t2)
  val d0e_test = d0exp_seq (t2, d0es_test, t3)
  val d0e_post = d0exp_seq (t3, d0es_post, t4)
in
  '(d0e_ini, d0e_test, d0e_post)
end // end of [initestpost_make]

// ------ ------

implement
m0atch_make_none (d0e) = '{
  m0atch_loc= d0e.d0exp_loc, m0atch_exp= d0e, m0atch_pat= p0atopt_none ()
} // end of [m0atch_make_none]

implement
m0atch_make_some (d0e, p0t) = let
  val loc = combine (d0e.d0exp_loc, p0t.p0at_loc)
in '{
  m0atch_loc= d0e.d0exp_loc, m0atch_exp= d0e, m0atch_pat= p0atopt_some p0t
} end // end of [m0atch_make_some]

// ------ ------

implement m0atchlst_nil () = nil ()
implement m0atchlst_cons (x, xs) = cons (x, xs)

// ------ ------

implement guap0at_make_none (p0t) = '{
  guap0at_loc= p0t.p0at_loc, guap0at_pat= p0t, guap0at_gua= m0atchlst_nil ()
} // end of [guap0at_make_none]

implement guap0at_make_some (p0t, m0ats) = let
  val loc = aux1 (p0t.p0at_loc, m0ats) where {
    fun aux1 (loc0: loc_t, m0ats: m0atchlst): loc_t =
      case+ m0ats of
      | list_cons (m0at, m0ats) => aux2 (loc0, m0at, m0ats)
      | list_nil () => loc0
    and aux2
      (loc0: loc_t, m0at: m0atch, m0ats: m0atchlst): loc_t =
      case+ m0ats of
      | list_cons (m0at, m0ats) => aux2 (loc0, m0at, m0ats)
      | list_nil () => combine (loc0, m0at.m0atch_loc)
  } // end of [where]
in '{
  guap0at_loc= p0t.p0at_loc, guap0at_pat= p0t, guap0at_gua= m0ats
} end // end of [guap0at_make_some]

// ------ ------

implement ifhead_make
  (t_if, inv) = '{ ifhead_tok= t_if, ifhead_inv= inv }
// end of [ifhead_make]

implement casehead_make (k, t_case, inv) = '{
  casehead_tok= t_case, casehead_knd= k, casehead_inv= inv
} // end of [casehead_make]

implement
loophead_make_none (t_loop) = '{
  loophead_tok= t_loop, loophead_inv= None ()
} // end of [loophead_make_none]

implement
loophead_make_some (t_loop, inv, t_eqgt) = let
  val loc = combine (t_loop.t0kn_loc, t_eqgt.t0kn_loc)
in '{
  loophead_tok= t_loop, loophead_inv= Some inv
} end // end of [loophead_make_some]

implement tryhead_make (t_try) = '{
  tryhead_tok= t_try, tryhead_inv= i0nvresstate_none ()
} // end of [tryhead_make]

(* ****** ****** *)

implement
c0lau_make (gp0t, seq, neg, body) = let
  val loc = combine (gp0t.guap0at_loc, body.d0exp_loc)
in '{
  c0lau_loc= loc
, c0lau_pat= gp0t
, c0lau_seq= seq
, c0lau_neg= neg
, c0lau_body= body
} end // end of [c0lau_make]

implement c0laulst_nil () = nil ()
implement c0laulst_cons (x, xs) = cons (x, xs)

implement
sc0lau_make (sp0t, d0e) = let
  val loc = combine (sp0t.sp0at_loc, d0e.d0exp_loc)
in '{
  sc0lau_loc= loc, sc0lau_pat= sp0t, sc0lau_body= d0e
} end // end of [sc0lau_make]

implement sc0laulst_nil () = nil ()
implement sc0laulst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement v0aldec_make (p0t, def, ann) = let
  val loc = (case+ ann of
    | WITHT0YPEnone () =>
      combine (p0t.p0at_loc, def.d0exp_loc)
    | WITHT0YPEprop (s0e) =>
      combine (p0t.p0at_loc, s0e.s0exp_loc)
    | WITHT0YPEtype (s0e) =>
      combine (p0t.p0at_loc, s0e.s0exp_loc)
    | WITHT0YPEview (s0e) =>
      combine (p0t.p0at_loc, s0e.s0exp_loc)
    | WITHT0YPEviewtype (s0e) =>
      combine (p0t.p0at_loc, s0e.s0exp_loc)
  ) : loc_t
in '{
  v0aldec_loc= loc, v0aldec_pat= p0t, v0aldec_def= def, v0aldec_ann= ann
} end // end of [v0aldec_make]

implement v0aldeclst_nil () = nil ()
implement v0aldeclst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

fun f0undec_make (
    id: i0de
  , arg: f0arglst
  , eff: e0fftaglstopt
  , res: s0expopt
  , def: d0exp
  , ann: witht0ype
  ) : f0undec = let

  val loc = case+ ann of
    | WITHT0YPEnone () =>
      combine (id.i0de_loc, def.d0exp_loc)
    | WITHT0YPEprop (s0e) =>
      combine (id.i0de_loc, s0e.s0exp_loc)
    | WITHT0YPEtype (s0e) =>
      combine (id.i0de_loc, s0e.s0exp_loc)
    | WITHT0YPEview (s0e) =>
      combine (id.i0de_loc, s0e.s0exp_loc)
    | WITHT0YPEviewtype (s0e) =>
      combine (id.i0de_loc, s0e.s0exp_loc)
in '{
  f0undec_loc= loc
, f0undec_sym= id.i0de_sym
, f0undec_sym_loc= id.i0de_loc
, f0undec_arg= arg
, f0undec_eff= eff
, f0undec_res= res
, f0undec_def= def
, f0undec_ann= ann
} end // end of [f0undec_make]

implement f0undec_make_none
  (id, arg, def, ann) = f0undec_make (
  id, arg, e0fftaglstopt_none(), s0expopt_none(), def, ann
) // end of [f0undec_make_none]

implement f0undec_make_some (id, arg, eff, res, def, ann) =
  f0undec_make (id, arg, eff, Some res, def, ann)

implement f0undeclst_nil () = nil ()
implement f0undeclst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement v0arwth_none () = None ()
implement v0arwth_some (id) = Some (id)

fn v0ardec_make (
    loc: loc_t
  , knd: int
  , id: i0de
  , typ: s0expopt
  , wth: i0deopt
  , ini: d0expopt
  ) : v0ardec = '{
  v0ardec_loc= loc
, v0ardec_knd= knd
, v0ardec_sym= id.i0de_sym
, v0ardec_sym_loc= id.i0de_loc
, v0ardec_typ= typ
, v0ardec_wth= wth
, v0ardec_ini= ini
} // end of [v0ardec_make]
 
implement
  v0ardec_make_some_none (stadyn, id, s0e, wth) = let
  val loc = combine (id.i0de_loc, s0e.s0exp_loc)
in
  v0ardec_make (
    loc, stadyn, id, s0expopt_some s0e, wth, d0expopt_none ()
  ) // end of [v0ardec_make]
end // end of [v0ardec_make_some_none]

implement
  v0ardec_make_none_some (stadyn, id, wth, d0e) = let
  val loc = combine (id.i0de_loc, d0e.d0exp_loc)
in
  v0ardec_make (
    loc, stadyn, id, s0expopt_none (), wth, d0expopt_some d0e
  ) // end of [v0ardec_make]
end // end of [v0ardec_make_none_some]

implement
  v0ardec_make_some_some (stadyn, id, s0e, wth, d0e) = let
  val loc = combine (id.i0de_loc, d0e.d0exp_loc)
in
  v0ardec_make (
    loc, stadyn, id, s0expopt_some s0e, wth, d0expopt_some d0e
  ) // end of [v0ardec_make]
end // end of [v0ardec_make_some_some]

implement v0ardeclst_nil () = nil ()
implement v0ardeclst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
m0acdef_make (id, arg, def) = let
  val loc = combine (id.i0de_loc, def.d0exp_loc)
in '{
  m0acdef_loc= loc
, m0acdef_sym= id.i0de_sym
, m0acdef_arg= arg
, m0acdef_def= def
} end // end of [m0acdef_make]

implement m0acdeflst_nil () = nil ()
implement m0acdeflst_cons (x, xs) = cons (x, xs)

(* ****** ****** *)

implement
i0mpdec_make
  (qid, arg, res, def) = let
  val loc = combine (qid.impqi0de_loc, def.d0exp_loc)
in '{
  i0mpdec_loc= loc
, i0mpdec_qid= qid
, i0mpdec_arg= arg
, i0mpdec_res= res
, i0mpdec_def= def
} end // end of [i0mpdec_make]

(* ****** ****** *)

(* declarations *)

(* ****** ****** *)

local

fun aux1_loc
  (loc0: loc_t, id: i0de, ids: i0delst): loc_t =
  case+ ids of
  | cons (id, ids) => aux1_loc (loc0, id, ids)
  | nil () => combine (loc0, id.i0de_loc)
// end of [aux1_loc]

fun aux2_loc (loc0: loc_t, ids: i0delst): loc_t =
  case+ ids of
  | cons (id, ids) => aux1_loc (loc0, id, ids)
  | nil () => loc0
// end of [aux2_loc]

in (* in of [local] *)

implement
d0ec_infix (
  t_infix, p, i, ids
) = let
  val loc = aux2_loc (t_infix.t0kn_loc, ids)
  val assoc = (case+ i of 
    | ~1 => $Fix.ASSOClft
    |  1 => $Fix.ASSOCrgt
    |  _ (*0*) => $Fix.ASSOCnon
  ) : assoc // end of [val]
in '{
  d0ec_loc= loc
, d0ec_node= D0Cfixity(F0XTYinf (p, assoc), ids)
} end // end of [d0ec_infix]

implement d0ec_prefix (t_prefix, p, ids) = let
  val loc = aux2_loc (t_prefix.t0kn_loc, ids)
in '{
  d0ec_loc= loc, d0ec_node= D0Cfixity(F0XTYpre p, ids)
} end // end of [d0ec_prefix]

implement d0ec_postfix (t_postfix, p, ids) = let
  val loc = aux2_loc (t_postfix.t0kn_loc, ids)
in '{
  d0ec_loc= loc, d0ec_node= D0Cfixity(F0XTYpos p, ids)
} end // end of [d0ec_postfix]

implement d0ec_nonfix (t_nonfix, ids) = let
  val loc = aux2_loc (t_nonfix.t0kn_loc, ids)
in '{
  d0ec_loc= t_nonfix.t0kn_loc, d0ec_node= D0Cnonfix ids
} end // end of [d0ec_nonfix]

end // end of [local]

(* ****** ****** *)

implement d0ec_include (stadyn, s) = '{
  d0ec_loc= s.s0tring_loc, d0ec_node= D0Cinclude (stadyn, s.s0tring_val)
} // end of [d0ec_include]

(* ****** ****** *)

implement d0ec_symintr (t_symintr, ids) = '{
  d0ec_loc= t_symintr.t0kn_loc, d0ec_node= D0Csymintr ids
} // end of [d0ec_symintr]

(* ****** ****** *)

implement d0ec_e0xpundef (id) = '{
  d0ec_loc= id.i0de_loc, d0ec_node= D0Ce0xpundef (id.i0de_sym)
} // end of [d0ec_e0xpundef]

implement d0ec_e0xpdef (id, oe) = let
  val loc = (case+ oe of
    | Some e => combine (id.i0de_loc, e.e0xp_loc)
    | None () => id.i0de_loc
  ) : loc_t // end of [val]
in '{
  d0ec_loc= loc, d0ec_node= D0Ce0xpdef (id.i0de_sym, oe)
} end // end of [d0ec_e0xpdef]

(* ****** ****** *)

implement d0ec_e0xpact_assert (e) = '{
  d0ec_loc= e.e0xp_loc, d0ec_node= D0Ce0xpact (E0XPACTassert, e)
} // end of [d0ec_e0xpact_assert]

implement d0ec_e0xpact_error (e) = '{
  d0ec_loc= e.e0xp_loc, d0ec_node= D0Ce0xpact (E0XPACTerror, e)
} // end of [d0ec_e0xpact_error]

implement d0ec_e0xpact_print (e) = '{
  d0ec_loc= e.e0xp_loc, d0ec_node= D0Ce0xpact (E0XPACTprint, e)
} // end of [d0ec_e0xpact_print]

(* ****** ****** *)

implement d0ec_srtdefs (x0, xs) = let
  fun aux_loc (x0: s0rtdef, x: s0rtdef, xs: s0rtdeflst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.s0rtdef_loc, x.s0rtdef_loc)
  // end of [aux_loc]
  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.s0rtdef_loc
  ) : loc_t
in '{
  d0ec_loc= loc, d0ec_node= D0Csrtdefs (x0, xs)
} end // end of [d0ec_srtdefs]

(* ****** ****** *)

implement d0ec_datsrts (para, x0, xs) = let
  fun aux_loc
    (x0: d0atsrtdec, x: d0atsrtdec, xs: d0atsrtdeclst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.d0atsrtdec_loc, x.d0atsrtdec_loc)

  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.d0atsrtdec_loc
  ) : loc_t
in '{
  d0ec_loc= loc, d0ec_node= D0Cdatsrts(para, x0, xs)
} end // end of [d0ec_datsrts]

(* ****** ****** *)

implement d0ec_stacons (k, x0, xs) = let
  fun aux_loc (x0: s0tacon, x: s0tacon, xs: s0taconlst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.s0tacon_loc, x.s0tacon_loc)

  val loc = case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.s0tacon_loc
in
  '{ d0ec_loc= loc, d0ec_node= D0Cstacons (k, x0, xs) }
end // end of [d0ec_stacons]

implement d0ec_stacsts (x0, xs) = let
  fun aux_loc
    (x0: s0tacst, x: s0tacst, xs: s0tacstlst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.s0tacst_loc, x.s0tacst_loc)
  // end of [aux_loc]

  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.s0tacst_loc
  ) : loc_t

in '{
  d0ec_loc= loc, d0ec_node= D0Cstacsts (x0, xs)
} end // end of [d0ec_stacsts]

implement d0ec_stavars (x0, xs) = let
  fun aux_loc
    (x0: s0tavar, x: s0tavar, xs: s0tavarlst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.s0tavar_loc, x.s0tavar_loc)

  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.s0tavar_loc
  ) : loc_t

in '{
  d0ec_loc= loc, d0ec_node= D0Cstavars (x0, xs)
} end // end of [d0ec_stavars]

(* ****** ****** *)

fn d0ec_sexpdefs_main
  (srt: s0rtopt, x0: s0expdef, xs: s0expdeflst) = let
  fun aux_loc
    (x0: s0expdef, x: s0expdef, xs: s0expdeflst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.s0expdef_loc, x.s0expdef_loc)
  // end of [aux_loc]
  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.s0expdef_loc
  ) : loc_t
in '{
  d0ec_loc= loc, d0ec_node= D0Csexpdefs (srt, x0, xs)
} end // end of [d0ec_sexpdefs_main]

implement d0ec_sexpdefs (k, x0, xs) = let
  val os0t = (case+ k of
    | STADEFKINDgeneric () => None ()
    | STADEFKINDprop t => Some '{
        s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_PROP
      }
    | STADEFKINDtype t => Some '{
        s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_T0YPE
      }
    | STADEFKINDview t => Some '{
        s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_VIEW
      }
    | STADEFKINDviewtype t => Some '{
        s0rt_loc= t.t0kn_loc, s0rt_node= S0RTide $Sym.symbol_VIEWT0YPE
      }
  ): s0rtopt // end of [case]
in
  d0ec_sexpdefs_main (os0t, x0, xs)
end // end of [d0ec_sexpdefs]

(* ****** ****** *)

implement d0ec_saspdec (x) = '{
  d0ec_loc= x.s0aspdec_loc, d0ec_node= D0Csaspdec (x)
} // end of [d0ec_saspdec]

(* ****** ****** *)

implement d0ec_dcstdecs (k, arg, x0, xs) = let
  fun aux_loc
    (x0: d0cstdec, x: d0cstdec, xs: d0cstdeclst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.d0cstdec_loc, x.d0cstdec_loc)
  // end of [aux_loc]
  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.d0cstdec_loc
  ) : loc_t
in '{
  d0ec_loc= loc, d0ec_node= D0Cdcstdecs (k, arg, x0, xs)
} end // end of [d0ec_dcstdecs]

(* ****** ****** *)

implement d0ec_datdecs (dk, x0, xs, ys) = let
  fun aux1_loc
    (x0: d0atdec, x: d0atdec, xs: d0atdeclst): loc_t =
    case+ xs of
    | cons (x, xs) => aux1_loc (x0, x, xs)
    | nil () => combine (x0.d0atdec_loc, x.d0atdec_loc)
  // end of [aux1_loc]
  fun aux2_loc
    (x0: d0atdec, y: s0expdef, ys: s0expdeflst): loc_t =
    case+ ys of
    | cons (y, ys) => aux2_loc (x0, y, ys)
    | nil () => combine (x0.d0atdec_loc, y.s0expdef_loc)
  // end of [aux2_loc]
  val loc = (case+ ys of
    | cons (y, ys) => aux2_loc (x0, y, ys)
    | nil () => begin case+ xs of
      | cons (x, xs) => aux1_loc (x0, x, xs)
      | nil () => x0.d0atdec_loc
      end
  ) : loc_t
in '{
  d0ec_loc= loc, d0ec_node= D0Cdatdecs (dk, x0, xs, ys)
} end // end of [d0ec_datdecs]

(* ****** ****** *)

implement
d0ec_exndecs (t_exception, x0, xs) = let
  fun aux_loc
    (loc0: loc_t, x: e0xndec, xs: e0xndeclst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (loc0, x, xs)
    | nil () => combine (loc0, x.e0xndec_loc)
  // end of [aux_loc]
  val loc = aux_loc (t_exception.t0kn_loc, x0, xs)
in '{
  d0ec_loc= loc, d0ec_node= D0Cexndecs (x0, xs)
} end // end of [d0ec_exndecs]

(* ****** ****** *)

implement
d0ec_classdec_none (t_class, id) = let
  val loc = combine (t_class.t0kn_loc, id.i0de_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cclassdec (id, None)
} end // end of [d0ec_classdec_none]

implement
d0ec_classdec_some (t_class, id, sup) = let
  val loc = combine (t_class.t0kn_loc, sup.s0exp_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cclassdec (id, Some sup)
} end // end of [d0ec_classdec_some]

(* ****** ****** *)

implement
d0ec_overload
  (t_overload, id, qid) = let
  val loc = combine (t_overload.t0kn_loc, qid.dqi0de_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Coverload (id, qid)
} end // end of [d0ec_overload]

implement
d0ec_overload_lrbrackets
  (t_overload, t_l, t_r, qid) = let
  val id = i0de_make_lrbrackets (t_l, t_r)
  val loc = combine (t_overload.t0kn_loc, qid.dqi0de_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Coverload (id, qid)
} end // end of [d0ec_overload_lrbrackets]

(* ****** ****** *)

implement d0ec_dynload (s) = '{
  d0ec_loc= s.s0tring_loc, d0ec_node= D0Cdynload (s.s0tring_val)
} // end of [d0ec_dynload]

//

implement
d0ec_staload_none (s) = let
  val name = s.s0tring_val // filename
in '{
  d0ec_loc= s.s0tring_loc, d0ec_node= D0Cstaload (None, name)
} end // end of [d0ec_staload_none]

implement
d0ec_staload_some (id, s) = let
  val name = s.s0tring_val // filename
  val loc = combine (id.i0de_loc, s.s0tring_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cstaload (Some id.i0de_sym, name)
} end // end of [d0ec_staload_some]

(* ****** ****** *)

implement d0ec_extype (name, s0e) = let
  val loc = combine (name.s0tring_loc, s0e.s0exp_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cextype (name.s0tring_val, s0e)
} end // end of [d2ec_extype]

implement d0ec_extval (name, d0e) = let
  val loc = combine (name.s0tring_loc, d0e.d0exp_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cextval (name.s0tring_val, d0e)
} end // end of [d2ec_extval]

(* ****** ****** *)

implement d0ec_extcode_dyn (code) = let
  val pos = code.e0xtcode_pos
  val loc = code.e0xtcode_loc
  val () =
    if (pos < 0) then begin
      prerr_loc_error0 (loc);
      prerr ": the sequence \"%{#\" is only for";
      prerr " including external code in a static file";
      prerr "; please use either \"%{\", \"%{^\", or \"%{$\" instead.";
      prerr_newline ();
      $Err.abort {void} ()
    end
  val cod = code.e0xtcode_cod
in '{ // external code
  d0ec_loc= loc, d0ec_node= D0Cextcode (pos, cod)
} end // end of [d0ec_extcode_dyn]

implement d0ec_extcode_sta (code) = let
  val pos = code.e0xtcode_pos
  val loc = code.e0xtcode_loc
  val () =
    if (pos >= 0) then begin
      prerr_loc_error0 (loc);
      prerr ": the sequence \"%{#\" should be used for";
      prerr " including external code in a static file.";
      prerr_newline ();
      $Err.abort {void} ()
    end
  val cod = code.e0xtcode_cod
in '{ // external code
  d0ec_loc= loc, d0ec_node= D0Cextcode (pos, cod)
} end // end of [d0ec_extcode_sta]

(* ****** ****** *)

local

fun aux1_loc
  (x0: v0aldec, xs: v0aldeclst): loc_t =
  case+ xs of
  | cons (x, xs) => aux2_loc (x0, x, xs)
  | nil () => x0.v0aldec_loc
// end [aux1_loc]

and aux2_loc
  (x0: v0aldec, x: v0aldec, xs: v0aldeclst): loc_t =
  case+ xs of
  | cons (x, xs) => aux2_loc (x0, x, xs)
  | nil () => combine (x0.v0aldec_loc, x.v0aldec_loc)
// end [aux2_loc]

in (* in of [local] *)

implement d0ec_valdecs (k, x0, xs) = let
  val loc = aux1_loc (x0, xs)
in '{
  d0ec_loc= loc, d0ec_node= D0Cvaldecs (k, x0, xs)
} end // end of [d0ec_valdecs]

implement d0ec_valdecs_par (x0, xs) = let
  val loc = aux1_loc (x0, xs)
in '{
  d0ec_loc= loc, d0ec_node= D0Cvaldecs_par (x0, xs)
} end // end of [d0ec_valdecs_par]

implement d0ec_valdecs_rec (x0, xs) = let
  val loc = aux1_loc (x0, xs)
in '{
  d0ec_loc= loc, d0ec_node= D0Cvaldecs_rec (x0, xs)
} end // end of [d0ec_valdecs_rec]

end // end of [local]

(* ****** ****** *)

implement
d0ec_fundecs (k, arg, x0, xs) = let
  fun aux_loc
    (x0: f0undec, x: f0undec, xs: f0undeclst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.f0undec_loc, x.f0undec_loc)
  // end of [aux_loc]
  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.f0undec_loc
  ) : loc_t
in '{
  d0ec_loc= loc, d0ec_node= D0Cfundecs (k, arg, x0, xs)
} end // end of [d0ec_fundecs]

(* ****** ****** *)

implement
d0ec_vardecs (x0, xs) = let
  fun aux_loc (
    x0: v0ardec, x: v0ardec, xs: v0ardeclst
  ) : loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.v0ardec_loc, x.v0ardec_loc)
  val loc = case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.v0ardec_loc
  // end of [val]
in '{
  d0ec_loc= loc, d0ec_node= D0Cvardecs (x0, xs)
} end // end of [d0ec_vardecs]

(* ****** ****** *)

implement
d0ec_macdefs
  (knd, x0, xs) = let
//
// knd: 0/1/2 => short/long/long rec
//
  fun aux_loc
    (x0: m0acdef, x: m0acdef, xs: m0acdeflst): loc_t =
    case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs)
    | nil () => combine (x0.m0acdef_loc, x.m0acdef_loc)
  // end of [aux_loc]
//
  val loc = (case+ xs of
    | cons (x, xs) => aux_loc (x0, x, xs) | nil () => x0.m0acdef_loc
  ) : loc_t // end of [val]
//
  val () = if knd < 0 then begin // error checking
    prerr_loc_error0 (loc);
    prerr ": only a macro in long form can be recursively defined";
    prerr ", which is introduced via [macrodef] instead of [macdef].";
    prerr_newline ();
    $Err.abort {void} ()
  end // end of [val]
//
in '{
  d0ec_loc= loc, d0ec_node= D0Cmacdefs (knd, x0, xs)
} end // end of [d0ec_macdefs]

(* ****** ****** *)
//
// [d0ecarg: s0arglstlst]
//
implement
d0ec_impdec
  (t_implement, i0mparg, i0mpdec) = let
  val loc = combine (t_implement.t0kn_loc, i0mpdec.i0mpdec_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cimpdec (i0mparg, i0mpdec)
} end // end of [d0ec_impdec]

(* ****** ****** *)

implement
d0ec_local
  (t_local, d0cs1, d0cs2, t_end) = let
  val loc = combine (t_local.t0kn_loc, t_end.t0kn_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Clocal (d0cs1, d0cs2)
} end // end of [d0ec_local]

(* ****** ****** *)

implement
d0ec_guadec (kndtok, gd0c) = let
  val SRPIFKINDTOK (knd, t_srpif) = kndtok
  val loc = combine (t_srpif.t0kn_loc, gd0c.guad0ec_loc)
in '{
  d0ec_loc= loc, d0ec_node= D0Cguadec (knd, gd0c)
} end // end of [d0ec_guadec]

(* ****** ****** *)

implement d0eclst_nil () = nil ()
implement d0eclst_cons (x, xs) = cons (x, xs)

implement d0ecllst_nil () = D0CLLSTnil ()
implement d0ecllst_cons (xs, x) = D0CLLSTcons (xs, x)

fun d0ecllst_revapp
  (xs: d0ecllst, ys: d0eclst): d0eclst = case+ xs of
  | ~D0CLLSTcons (xs, x) => d0ecllst_revapp (xs, cons (x, ys))
  | ~D0CLLSTnil () => ys
// end of [d0eclst_revapp]

implement
d0ecllst_reverse (xs) = d0ecllst_revapp (xs, nil ())

(* ****** ****** *)

implement
guad0ec_one
  (gua, d0cs_then, t_endif) = '{
  guad0ec_loc= t_endif.t0kn_loc
, guad0ec_node= GD0Cone (gua, d0cs_then)
} // end of [guad0ec_one]

implement
guad0ec_two
  (gua, d0cs_then, d0cs_else, t_endif) = '{
  guad0ec_loc= t_endif.t0kn_loc
, guad0ec_node= GD0Ctwo (gua, d0cs_then, d0cs_else)
} // end of [guad0ec_two]

implement
guad0ec_cons
  (gua, d0cs, kndtok, rst) = let
  val SRPIFKINDTOK (knd, _(*tok*)) = kndtok
in '{
  guad0ec_loc= rst.guad0ec_loc
, guad0ec_node= GD0Ccons (gua, d0cs, knd, rst.guad0ec_node)
} end // end of [guad0ec_cons]

(* ****** ****** *)

(* end of [ats_syntax.dats] *)
