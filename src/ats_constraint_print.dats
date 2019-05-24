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
// Start Time: February 2008
//
(* ****** ****** *)

(* for representing and handling constraints *)

(* ****** ****** *)

staload
IntInf = "ats_intinf.sats"
staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_constraint.sats"

(* ****** ****** *)

implement
fprint_s3aexp (pf | out, s3ae0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3ae0 of
  | S3AEcst s2c => begin
      prstr "S3AEcst("; fprint_s2cst (pf | out, s2c); prstr ")"
    end
  | S3AEexp s2e => begin
      prstr "S3AEexp("; fprint_s2exp (pf | out, s2e); prstr ")"
    end
  | S3AEvar s2v => begin
      prstr "S3AEvar("; fprint_s2var (pf | out, s2v); prstr ")"
    end
  | S3AEpadd (s3ae, s3ie) => begin
      prstr "S3AEpadd(";
      fprint_s3aexp (pf | out, s3ae);
      prstr "; ";
      fprint_s3iexp (pf | out, s3ie);
      prstr ")"
    end // end of [S3AEpadd]
  | S3AEnull => begin
      fprint1_string (pf | out, "S3AEnull()")
    end // end of [S3AEnull]
end // end of [fprint_s3aexp]

implement print_s3aexp (s3ae) = print_mac (fprint_s3aexp, s3ae)
implement prerr_s3aexp (s3ae) = prerr_mac (fprint_s3aexp, s3ae)

(* ****** ****** *)

implement
fprint_s3bexp (pf | out, s3be0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3be0 of
  | S3BEcst s2c => begin
      prstr "S3BEcst("; fprint_s2cst (pf | out, s2c); prstr ")"
    end
  | S3BEexp s2e => begin
      prstr "S3BEexp("; fprint_s2exp (pf | out, s2e); prstr ")"
    end
  | S3BEvar s2v => begin
      prstr "S3BEvar("; fprint_s2var (pf | out, s2v); prstr ")"
    end
  | S3BEbool b => begin
      prstr "S3BEbool("; fprint1_bool (pf | out, b); prstr ")"
    end
  | S3BEbneg s3be => begin
      prstr "S3BEbneg("; fprint_s3bexp (pf | out, s3be); prstr ")"
    end
  | S3BEbadd (s3be1, s3be2) => begin
      prstr "S3BEbadd(";
      fprint_s3bexp (pf | out, s3be1);
      prstr "; ";
      fprint_s3bexp (pf | out, s3be2);
      prstr ")"
    end // end of [S3BEbadd]
  | S3BEbmul (s3be1, s3be2) => begin
      prstr "S3BEbmul(";
      fprint_s3bexp (pf | out, s3be1);
      prstr "; ";
      fprint_s3bexp (pf | out, s3be2);
      prstr ")"
    end // end of [S3BEbmul]
  | S3BEiexp (knd, s3ie) => begin
      prstr "S3BEiexp(";
      prstr "knd=";
      fprint1_int (pf | out, knd);
      prstr "; ";
      fprint_s3iexp (pf | out, s3ie);
      prstr ")"
    end // end of [S3BEiexp]
end // end of [fprint_s3bexp]

implement print_s3bexp (s3be) = print_mac (fprint_s3bexp, s3be)
implement prerr_s3bexp (s3be) = prerr_mac (fprint_s3bexp, s3be)

(* ****** ****** *)

implement
fprint_s3bexplst (pf | out, xs) =
  $Lst.fprintlst (pf | out, xs, ", ", fprint_s3bexp)
// end of [fprint_s3bexplst]

implement print_s3bexplst (s3bes) = print_mac (fprint_s3bexplst, s3bes)
implement prerr_s3bexplst (s3bes) = prerr_mac (fprint_s3bexplst, s3bes)

(* ****** ****** *)

implement
fprint_s3iexp (pf | out, s3ie0) = let
  macdef prstr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s3ie0 of
  | S3IEcst s2c => begin
      prstr "S3IEcst("; fprint_s2cst (pf | out, s2c); prstr ")"
    end
  | S3IEexp s2e => begin
      prstr "S3IEexp("; fprint_s2exp (pf | out, s2e); prstr ")"
    end
  | S3IEvar s2v => begin
      prstr "S3IEvar("; fprint_s2var (pf | out, s2v); prstr ")"
    end
  | S3IEint i => begin
      prstr "S3IEint("; fprint1_int (pf | out, i); prstr ")"
    end
  | S3IEintinf i => begin
      prstr "S3IEintinf(";
      $IntInf.fprint_intinf (pf | out, i);
      prstr ")"
    end // end of [S2IEintinf]
  | S3IEineg (s3ie) => begin
      prstr "S3IEineg("; fprint_s3iexp (pf | out, s3ie); prstr ")"
    end // end of [S3IEineg]
  | S3IEiadd (s3ie1, s3ie2) => begin
      prstr "S3IEiadd(";
      fprint_s3iexp (pf | out, s3ie1);
      prstr "; ";
      fprint_s3iexp (pf | out, s3ie2);
      prstr ")"
    end // end of [S3IEiadd]
  | S3IEisub (s3ie1, s3ie2) => begin
      prstr "S3IEisub(";
      fprint_s3iexp (pf | out, s3ie1);
      prstr "; ";
      fprint_s3iexp (pf | out, s3ie2);
      prstr ")"
    end // end of [S3IEisub]
  | S3IEimul (s3ie1, s3ie2) => begin
      prstr "S3IEimul(";
      fprint_s3iexp (pf | out, s3ie1);
      prstr "; ";
      fprint_s3iexp (pf | out, s3ie2);
      prstr ")"
    end // end of [S3IEimul]
  | S3IEpdiff (s3ae1, s3ae2) => begin
      prstr "S3IEpdiff(";
      fprint_s3aexp (pf | out, s3ae1);
      prstr "; ";
      fprint_s3aexp (pf | out, s3ae2);
      prstr ")"
    end // end of [S3IEdiff]
end // end of [fprint_s3iexp]

implement print_s3iexp (s3ie) = print_mac (fprint_s3iexp, s3ie)
implement prerr_s3iexp (s3ie) = prerr_mac (fprint_s3iexp, s3ie)

(* ****** ****** *)

(* end of [ats_constraint_print.dats] *)
