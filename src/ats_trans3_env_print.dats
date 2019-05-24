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
// Start Time: January 2008
//
(* ****** ****** *)

staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

implement
fprint_s3item (pf | out, s3i) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3i of
  | S3ITEMcstr c3t => begin
      prstr "S3ITEMcstr("; fprint_c3str (pf | out, c3t); prstr ")"
    end // end of [S3ITEMcstr]
  | S3ITEMcstr_ref _ => begin
      fprint1_string (pf | out, "S3ITEMcstr_ref(...)")
    end // end of [S3ITEMcstr_ref]
  | S3ITEMdisj s3iss => begin
      fprint1_string (pf | out, "S3ITEMdisj(...)")
    end // end of [S3ITEMdisj]
  | S3ITEMhypo h3p => begin
      prstr "S3ITEMhypo("; fprint_h3ypo (pf | out, h3p); prstr ")"
    end // end of [S3ITEMhypo]
  | S3ITEMsvar s2v => begin
      prstr "S3ITEMsvar("; fprint_s2var (pf | out, s2v); prstr ")"
    end // end of [S3ITEMsvar]
  | S3ITEMsVar s2V => let
      val () = prstr "S3ITEMsVar("
      val () = fprint_s2Var (pf | out, s2V)
      val () = (
        case+ s2Var_get_link (s2V) of
        | Some s2e => begin
            prstr "= "; fprint_s2exp (pf | out, s2e)
          end // end of [Some]
        | None () => () // end of [None]
      ) : void // end of [val]
      val () = prstr ")"
    in
      // empty
    end // end of [S3ITEMsVar]
end // end of [fprint_s3item]

(* ****** ****** *)

implement
fprint_s3itemlst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s3item)
// end of [fprint_s3itemlst]

implement print_s3itemlst (s3is) = print_mac (fprint_s3itemlst, s3is)
implement prerr_s3itemlst (s3is) = prerr_mac (fprint_s3itemlst, s3is)

(* ****** ****** *)

implement
fprint_s3itemlstlst (pf | out, xss) =
  $Lst.fprintlst (pf | out, xss, "; ", fprint_s3itemlst)
// end of [fprint_s3itemlstlst]

implement print_s3itemlstlst (s3iss) = print_mac (fprint_s3itemlstlst, s3iss)
implement prerr_s3itemlstlst (s3iss) = prerr_mac (fprint_s3itemlstlst, s3iss)

(* ****** ****** *)

implement
fprint_c3strkind (pf | out, knd) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ knd of
  | C3STRKINDmain () => prstr "main"
  | C3STRKINDmetric_nat () => prstr "metric_nat"
  | C3STRKINDmetric_dec () => prstr "metric_dec"
  | C3STRKINDpattern_match_exhaustiveness _ => prstr "pattern"
  | C3STRKINDvarfin _ => prstr "varfin"
  | C3STRKINDloop (knd) => begin
      prstr "loop("; fprint1_int (pf | out, knd); prstr ")"
    end (* end of [C3STRKINDloop] *)
end // end of [fprint_c3strkind]

(* ****** ****** *)

implement fprint_c3str (pf | out, c3t) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ c3t.c3str_node of
  | C3STRprop s2p => begin
      prstr "C3STRprop(";
      fprint_c3strkind (pf | out, c3t.c3str_kind);
      prstr "; ";
      fprint_s2exp (pf | out, s2p);
      prstr ")"
    end // end of [C3STRprop]
  | C3STRitmlst s3is => begin
      prstr "C3STRitmlst(";
      fprint_c3strkind (pf | out, c3t.c3str_kind);
      prstr "; ";
      fprint_s3itemlst (pf | out, s3is);
      prstr ")"
    end // end of [C3STRitmlst]
end // end of [fprint_c3str]

implement print_c3str (c3t) = print_mac (fprint_c3str, c3t)
implement prerr_c3str (c3t) = prerr_mac (fprint_c3str, c3t)

(* ****** ****** *)

implement fprint_h3ypo (pf | out, h3p) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ h3p.h3ypo_node of
  | H3YPOprop s2p => begin
      prstr "H2YPOprop("; fprint_s2exp (pf | out, s2p); prstr ")"
    end // end of [H3YPOprop]
  | H3YPObind (s2v, s2p) => begin
      prstr "H2YPObind(";
      fprint_s2var (pf | out, s2v);
      prstr ", ";
      fprint_s2exp (pf | out, s2p);
      prstr ")"
    end // end of [H3YPObind]
  | H3YPOeqeq (s2e1, s2e2) => begin
      prstr "H2YPOeqeq(";
      fprint_s2exp (pf | out, s2e1);
      prstr ", ";
      fprint_s2exp (pf | out, s2e2);
      prstr ")"
    end // end of [H3YPOeqeq]
end // end of [fprint_h3ypo]

implement print_h3ypo (h3p) = print_mac (fprint_h3ypo, h3p)
implement prerr_h3ypo (h3p) = prerr_mac (fprint_h3ypo, h3p)

(* ****** ****** *)

(* end of [ats_trans3_env_print.dats] *)
