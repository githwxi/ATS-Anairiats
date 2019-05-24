(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

module Err = Ats_error
module Loc = Ats_location

module P = Printf

open Ats_syntax
open Ats_staexp1
open Ats_dynexp1
open Ats_staexp2

(* ****** ****** *)

let srt1_tr_errmsg_id_undef (s1t: srt1) (id: srt_id) = begin
  P.eprintf "%a: undeclared sort: <%a>.\n"
    Loc.fprint s1t.srt1_loc fprint_srt_id id;
  Err.abort ();
end

let srt1_tr_errmsg_id_subset (s1t: srt1) (id: srt_id) = begin
  P.eprintf "%a: subset sort <%a> is not allowed.\n"
    Loc.fprint s1t.srt1_loc fprint_srt_id id;
  Err.abort ();
end

let srt1_tr_errmsg_list (s1t: srt1) = begin
  P.eprintf "%a: sort list is not supported.\n" Loc.fprint s1t.srt1_loc;
  Err.abort ();
end

let srt1_tr_errmsg_qid (s1t: srt1) = begin
  P.eprintf "%a: qualified sort identifier is not supported.\n"
    Loc.fprint s1t.srt1_loc;
  Err.abort ();
end

let srt1_app_tr_errmsg_1 (s1t: srt1) = begin
  P.eprintf "%a: unrecognized sort constructor: <%a>.\n"
    Loc.fprint s1t.srt1_loc fprint_srt1 s1t;
  Err.abort ();
end

(* ****** ****** *)

let decarg1_tr_errmsg_id (id: id) = begin
  P.eprintf
    "%a: a sort needs to be assigned to the static identifier: <%a>\n"
    Loc.fprint (loc_of_id id) fprint_id id;
  Err.abort ();
end
  
(* ****** ****** *)

let efftag_tr_errmsg_none (id: Syn.sid) = begin
  P.eprintf "%a: unrecognized static identifier: <%a>.\n"
    Loc.fprint (Syn.loc_of_sid id) Syn.fprint_sid id;
  Err.abort ();
end

let efftag_tr_errmsg_some (id: Syn.sid) = begin
  P.eprintf "%a: static identifier <%a> is not defined as a variable.\n"
    Loc.fprint (Syn.loc_of_sid id) Syn.fprint_sid id;
  Err.abort ();
end

(* ****** ****** *)

let sexp1_tr_up_errmsg_appid_none (s1e: sexp1) (id: squal_opt_id) =
  begin 
    P.eprintf "%a: unrecognized static identifier: <%a>.\n"
      Loc.fprint s1e.sexp1_loc fprint_squal_opt_id id;
    Err.abort ();
  end

let sexp1_tr_up_errmsg_invar (s1e: sexp1) = begin 
  P.eprintf "%a: illegal use of invariant view or invariant viewtype.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end

let sexp1_tr_up_errmsg_trans (s1e: sexp1) = begin 
  P.eprintf "%a: illegal use of view or viewtype transform.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end

let sexp1_tr_up_errmsg_lam_nosrt (s1e: sexp1) (id: sid) = begin
  P.eprintf
    "%a: sort annotation is needed for the static variable: <%a>.\n"
    Loc.fprint s1e.sexp1_loc fprint_sid id;
  Err.abort ();
end

let sexp1_tr_up_errmsg_mod_undef (s1e: sexp1) (id: squal_opt_id) =
  begin
    P.eprintf "%a: unrecognized static identifier: <%a>.\n"
      Loc.fprint s1e.sexp1_loc fprint_squal_opt_id id;
    Err.abort ();
  end

let sexp1_tr_up_errmsg_mod_unmod (s1e: sexp1) (id: squal_opt_id) =
  begin
    P.eprintf
      "%a: the static identifier <%a> is unrecognized as a modtype.\n"
      Loc.fprint s1e.sexp1_loc fprint_squal_opt_id id;
    Err.abort ();
  end

(* ****** ****** *)

let sexp1_list_tr_dn_errmsg_less loc = begin
  P.eprintf "%a: too few static expressions or too many sorts.\n"
    Loc.fprint loc;
  Err.abort ();
end

let sexp1_list_tr_dn_errmsg_more loc = begin
  P.eprintf "%a: too many static expressions or too few sorts.\n"
    Loc.fprint loc;
  Err.abort ();
end

(* ****** ****** *)

let sexp1_app_tr_up_errmsg_1 loc = begin
  P.eprintf
    "%a: the applied static expression is not of a function sort.\n"
    Loc.fprint loc;
  Err.abort ();
end 

let sexp1_app_tr_up_errmsg_2 loc = begin
  P.eprintf "%a: the application is given too many arguments.\n"
    Loc.fprint loc;
  Err.abort ();
end 

let sexp1_app_tr_up_errmsg_3 loc = begin
  P.eprintf "%a: the application is given too few arguments.\n"
    Loc.fprint loc;
  Err.abort ();
end 

let sexp1_app_id_tr_up_errmsg_none loc
  (qid: Syn.squal_opt_id) (s2tss: srt2 list list) =
  begin
    P.eprintf
      "%a: the arguments for <%a> are expected to be of different sorts: %a\n"
      Loc.fprint loc fprint_squal_opt_id qid fprint_srt2_list_list s2tss;
    Err.abort ();
  end

let sexp1_app_id_tr_up_errmsg_fil loc (qid: Syn.squal_opt_id) = begin
  P.eprintf
    "%a: the static constant <%a> is defined as a file qualifier.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

let sexp1_app_id_tr_up_errmsg_mod loc (qid: Syn.squal_opt_id) = begin
  P.eprintf
    "%a: the static constant <%a> is defined as a modtype.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

(* ****** ****** *)

let sexp1_app_datcon_tr_errmsg_arg loc (d2c: dcon2) = begin
  P.eprintf
    "%a: the constructor <%a> is overly used.\n"
    Loc.fprint loc fprint_dcon2 d2c;
  Err.abort ()
end

let sexp1_app_datcon_tr_errmsg_arity loc (d2c: dcon2) (i: int) =
  if i > 0 then begin
    P.eprintf
      "%a: the constructor <%a> require fewer arguments.\n"
      Loc.fprint loc fprint_dcon2 d2c;
    Err.abort ()
  end else begin
    P.eprintf
      "%a: the constructor <%a> require more arguments.\n"
      Loc.fprint loc fprint_dcon2 d2c;
    Err.abort ()
  end

(* ****** ****** *)

let sexp1_arrow_tr_up_errmsg_app loc = begin
  P.eprintf "%a: illegal static application.\n" Loc.fprint loc;
  Err.abort ();
end 

let sexp1_arrow_tr_up_errmsg_arg (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is required of an impredicative sort.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end 

let sexp1_arrow_tr_up_errmsg_vararg (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is required to be the last function argument.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end 

let sexp1_arrow_tr_up_errmsg_res (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is required of an impredicative sort.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end 

let sexp1_id_tr_up_errmsg_1 loc id = begin
  P.eprintf "%a: unrecognized static identifier: <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id id;
  Err.abort ();
end

let sexp1_id_tr_up_errmsg_2 loc id = begin
  P.eprintf "%a: unresolved static identifier: <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id id;
  Err.abort ();
end

let sexp1_id_tr_up_errmsg_3 loc id = begin
  P.eprintf
    "%a: the static constant <%a> is defined as a file qualifier.\n"
    Loc.fprint loc fprint_squal_opt_id id;
  Err.abort ();
end

let sexp1_id_tr_up_errmsg_4 loc id = begin
  P.eprintf
    "%a: the static constant <%a> is defined as a modtype.\n"
    Loc.fprint loc fprint_squal_opt_id id;
  Err.abort ();
end

let sexp1_tytup2_tr_up_errmsg (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is required of an impredicative sort.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end 

(* ****** ****** *)

let sexp1_tr_dn_errmsg_1 loc (s2t1: srt2) (s2t2: srt2) = begin
  P.eprintf
    "%a: the static expression is of sort <%a> and it is expected to be of sort <%a>.\n"
    Loc.fprint loc fprint_srt2 s2t1 fprint_srt2 s2t2;
  Err.abort ();
end

let sexp1_tr_dn_proof_errmsg (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is expected to be of a proof sort.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end

let sexp1_tr_dn_impredicative_errmsg (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is expected to be of an impredicative sort.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end

let sexp1_arg_tr_dn_impredicative_errmsg (s1e: sexp1) = begin
  P.eprintf
    "%a: the static expression is expected to be of an impredicative sort.\n"
    Loc.fprint s1e.sexp1_loc;
  Err.abort ();
end

let srtext1_tr_errmsg_1 loc (id: srt_id) = begin
  P.eprintf "%a: undeclared sort: <%a>.\n"
    Loc.fprint loc fprint_srt_id id;
  Err.abort ();
end

(* ****** ****** *)

let pat1_tr_errmsg_1 (p1t: pat1) = begin
  P.eprintf "%a: a constructor is required.\n"
    Loc.fprint p1t.pat1_loc;
  Err.abort ();
end 

let pat1_tr_errmsg_2 (p1t: pat1) = begin
  P.eprintf "%a: the pattern is illegal.\n"
    Loc.fprint p1t.pat1_loc;
  Err.abort ();
end

let pat1_app_dyn_tr_errmsg_1 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unrecognized constructor: <%a>.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

let pat1_app_dyn_tr_errmsg_2 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: <%a> is not declared as a constructor.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

let pat1_app_dyn_tr_errmsg_3 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unresolved dynamic identifier: <%a>.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

let pat1_con_tr_errmsg_1 loc (d2c: dcon2) = begin
  P.eprintf
    "%a: the constuctor <%a> is applied to too many static arguments.\n"
    Loc.fprint loc fprint_dcon2 d2c;
  Err.abort ();		
end

let pat1_free_tr_errmsg_1 loc = begin
  P.eprintf
    "%a: illegal freeing constructor pattern.\n"
    Loc.fprint loc;
  Err.abort ();
end

(* ****** ****** *)

let dexp1_tr_errmsg_1 loc (qid: Syn.squal_opt_id) = begin
  P.eprintf "%a: unrecognized static identifier: <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

let dexp1_tr_errmsg_2 loc (qid: Syn.squal_opt_id) = begin
  P.eprintf "%a: unresolved static identifier: <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

let dexp1_tr_errmsg_lam_sta_ana loc = begin
  P.eprintf
    "%a: illegal use of static lambda-abstraction in analysis form.\n"
    Loc.fprint loc;
  Err.abort ();
end

let dexp1_id_tr_errmsg_1 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unrecognized dynamic identifier: <%a>."
    Loc.fprint loc Syn.fprint_dqual_opt_id id;
  Err.abort ();
end

let dexp1_id_tr_errmsg_2 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unresolved dynamic identifier: <%a>.\n"
    Loc.fprint loc Syn.fprint_dqual_opt_id id;
  Err.abort ();		      
end

let dexp1_assgn_tr_errmsg_1 loc = begin
  P.eprintf "%a: the identifier := is reserved for assignment.\n"
    Loc.fprint loc;
  Err.abort ();
end

let dexp1_deref_tr_errmsg_1 loc = begin
  P.eprintf "%a: the identifier ! is reserved for dereference.\n"
    Loc.fprint loc;
  Err.abort ();
end

let dexp1_selptr_tr_errmsg_1 (d1e: dexp1) = begin
  P.eprintf "%a: illegal form of label.\n" Loc.fprint d1e.dexp1_loc;
  Err.abort ();
end 

let dexp1_selptr_tr_errmsg_2 loc = begin
  P.eprintf
    "%a: the identifier -> is reserved for selection through a pointer.\n"
    Loc.fprint loc;
  Err.abort ();
end

let dexp1_app_sta_id_tr_errmsg_1 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unresolved dynamic identifier: <%a>.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

let dexp1_app_sta_id_tr_errmsg_2 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unrecognized dynamic identifier: <%a>.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

let dexp1_app_dyn_id_tr_errmsg_1 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unresolved dynamic identifier: <%a>.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

let dexp1_app_dyn_id_tr_errmsg_2 loc (id: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unrecognized dynamic identifier: <%a>.\n"
    Loc.fprint loc fprint_dqual_opt_id id;
  Err.abort ();
end

(* ****** ****** *)

let dexp1_tr_dn_errmsg_lam_sta_ana loc s2e = begin
  P.eprintf
    "%a: a universal type is needed static lambda-abstraction in analysis form.\n"
    Loc.fprint loc;
  Err.abort ();
end

let dexp1_tr_dn_errmsg_lam_dyn_pfarg loc = begin
  P.eprintf "%a: proof arity mismatch.\n" Loc.fprint loc;
  Err.abort ();
end

let dexp1_tr_dn_errmsg_lam_dyn_arg loc (i: int) = begin
  if i > 0 then
    P.eprintf "%a: arity mismatch: too few arguments.\n"
      Loc.fprint loc
  else
    P.eprintf "%a: arity mismatch: too many arguments.\n"
      Loc.fprint loc;
  Err.abort ();
end

(* ****** ****** *)

let cla1_tr_errmsg_1 (c1l: cla1) = begin
  P.eprintf "%a: the clause contains too few patterns.\n"
    Loc.fprint c1l.cla1_loc;
  Err.abort ();
end

let cla1_tr_errmsg_2 (c1l: cla1) = begin
  P.eprintf "%a: the clause contains too many patterns.\n"
    Loc.fprint c1l.cla1_loc;
  Err.abort ();
end 

(* ****** ****** *)

let loopinv1_tr_errmsg_1 (id: did) = begin
  P.eprintf "%a: unrecognized dynamic identifer: <%a>.\n"
    Loc.fprint (Syn.loc_of_did id) fprint_did id;
  Err.abort ();
end

(* ****** ****** *)

let dec1_symelim_errmsg loc (id: did) = begin
  P.eprintf "%a: the symbol is not for overloading: <%a>.\n"
    Loc.fprint loc fprint_sid id;
  Err.abort ();
end

(* ****** ****** *)

let dec1_sexpdef_sasp_tr_aux_errmsg_1 loc (id: sid) = begin
  P.eprintf "%a: there is no sort annotaton for <%a>.\n"
    Loc.fprint loc fprint_sid id;
  Err.abort ();
end

let dec1_sexpdef_tr_rec_errmsg_1 loc = begin
  P.eprintf
    "%a: the sort of the definition does not match the sort of the defined static constant.\n"
    Loc.fprint loc;
  Err.abort ();
end 

let dec1_sexpdef_tr_norec_errmsg_1 loc = begin
  P.eprintf
    "%a: the sort of the definition does not match the sort of the defined static constant.\n"
    Loc.fprint loc;
  Err.abort ();
end

let dec1_sexpdef_list_tr_rec_errmsg_1 loc = begin
  P.eprintf
    "%a: the sort of the definition does not match the sort of the defined static constant.\n"
    Loc.fprint loc;
  Err.abort ();
end


let dec1_sexpdef_list_tr_rec_errmsg_2 loc = begin
  P.eprintf "%a: sort annotation is required.\n" Loc.fprint loc;
  Err.abort ();
end

let dec1_sasp_tr_errmsg_1 loc (qid: Syn.squal_opt_id) = begin
  P.eprintf
    "%a: the sort of the assumption does not match the sort of the static constant <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end 

let dec1_sasp_tr_errmsg_2 loc (qid: Syn.squal_opt_id) = begin
  P.eprintf "%a: the static constant <%a> is not abstract.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

let dec1_sasp_tr_errmsg_3 loc (qid: Syn.squal_opt_id) = begin
  P.eprintf "%a: unresolved static constant: <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

let dec1_sasp_tr_errmsg_4 loc (qid: Syn.squal_opt_id) = begin
  P.eprintf "%a: unrecognized static constant: <%a>.\n"
    Loc.fprint loc fprint_squal_opt_id qid;
  Err.abort ();
end

(* ****** ****** *)

let dec1_dat_tr_errmsg_1 loc (name: did) = begin
  P.eprintf "%a: the constructor <%a> needs fewer indexes.\n"
    Loc.fprint loc fprint_did name;
  Err.abort ();
end 

let dec1_dat_tr_errmsg_2 loc (name: did) = begin
  P.eprintf "%a: the constructor <%a> needs more indexes.\n"
    Loc.fprint loc fprint_did name;
  Err.abort ();
end 

let dec1_dat_tr_errmsg_3 loc (name: did) = begin
  P.eprintf "%a: the constructor <%a> needs no indexes.\n"
    Loc.fprint loc fprint_did name;
  Err.abort ();
end 

let dec1_dat_tr_errmsg_4 loc (name: did) = begin
  P.eprintf "%a: the constructor <%a> needs some indexes.\n"
    Loc.fprint loc fprint_did name;
  Err.abort ();
end 

(* ****** ****** *)

let dec1_overload_tr_errmsg_sym loc (did: did) = begin
  P.eprintf "%a: the symbol is not for overloading: <%a>.\n"
    Loc.fprint loc Syn.fprint_did did;
  Err.abort ();
end

let dec1_overload_tr_errmsg_qid loc (qid: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unrecognized dynamic identfier: <%a>.\n"
    Loc.fprint loc Syn.fprint_dqual_opt_id qid;
  Err.abort ();
end

let dec1_impl_tr_errmsg_qid loc (qid: Syn.dqual_opt_id) = begin
  P.eprintf "%a: unrecognized dynamic identfier: <%a>.\n"
    Loc.fprint loc Syn.fprint_dqual_opt_id qid;
  Err.abort ();
end

(* ****** ****** *)

(* end of [ats_errmsg2.ml] *)
