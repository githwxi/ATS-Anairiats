(*
**
** HOLITMUS: a proof checker for higher-order logic
**
** Originally implemented in OCaml
**    by Chad Brown (cebrown AT mathgate DOT info)
** Time: March/September, 2008
**
** Translated to ATS
**    by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

staload "syntax.sats"

(* ****** ****** *)

fun fprint_stp_paren {m: file_mode} (
    pf: file_mode_lte (m, w) | out: &FILE m, stp: stp, paren: int
  ) : void = let
  macdef strpr (s) = fprint_string (pf | out, ,(s))
  macdef pr (stp, paren) = fprint_stp_paren (pf | out, ,(stp), ,(paren))
in
  case+ stp of
  | STPbas name => fprint_string (pf | out, name)
  | STPprp () => strpr "*"
  | STParr (stp1, stp2) => begin
      if paren > 0 then strpr "(";
      pr (stp1, 1); strpr ">"; pr (stp2, 0);
      if paren > 0 then strpr ")";
    end // end of [STParr]
end // end of [fprint_stp]

implement fprint_stp {m}
  (pf | out, stp) = fprint_stp_paren (pf | out, stp, 0)

implement print_stp (stp) = print_mac (fprint_stp, stp)
implement prerr_stp (stp) = prerr_mac (fprint_stp, stp)

(* ****** ****** *)

fun fprint_trm_paren {m:file_mode} (
    pf: file_mode_lte (m, w)
  | out: &FILE m, trm: trm, paren: int
  ) : void = let
  macdef strpr (s) = fprint_string (pf | out, ,(s))
  macdef pr (trm, paren) = fprint_trm_paren (pf | out, ,(trm), ,(paren))
in
  case+ trm of
  | TRMnam name => fprint_string (pf | out, name)
  | TRMdbi i => fprintf (pf | out, "^%i", @(i))
  | TRMlam (stp, trm) => begin
      if paren > 0 then strpr "(";
      strpr "\\_:"; fprint_stp (pf | out, stp); strpr "."; pr (trm, 0);
      if paren > 0 then strpr ")";
    end // end of [TRMlam]
  | TRMapp (trm1, trm2) => begin
      if paren > 0 then strpr "(";
      pr (trm1, 0); strpr " "; pr (trm2, 1);
      if paren > 0 then strpr ")";
    end // end of [TRMapp]
  | TRMall (stp, trm) => begin
    end // end of [TRMall]
  | TRMimp (trm1, trm2) => begin
      if paren > 0 then strpr "(";
      pr (trm1, 1); strpr ">"; pr (trm2, 0);
      if paren > 0 then strpr ")";
    end // end of [TRMimp]
  | TRMany (stp) => begin
      strpr "(_:"; fprint_stp (pf | out, stp); strpr ")";
    end // end of [TRMany]
end // end of [fprint_trm_paren]

implement fprint_trm {m}
  (pf | out, trm) = fprint_trm_paren (pf | out, trm, 0)

implement print_trm (trm) = print_mac (fprint_trm, trm)
implement prerr_trm (trm) = prerr_mac (fprint_trm, trm)

(* ****** ****** *)

fun fprint_pftrm_paren {m:file_mode} (
    pf: file_mode_lte (m, w) | out: &FILE m, pftrm: pftrm, paren: int
  ): void = let
  macdef strpr (s) = fprint_string (pf | out, ,(s))
  macdef pr (pftrm, paren) =
    fprint_pftrm_paren (pf | out, ,(pftrm), ,(paren))
in
  case+ pftrm of
  | PFTRMcon name => fprint_string (pf | out, name)
  | PFTRMdbi i => fprintf (pf | out, "^%i", @(i))
  | PFTRMtlam (stp, pftrm) => begin
      if paren > 0 then strpr "(";
      strpr "\\t_:";
      fprint_stp (pf | out, stp);
      strpr ".";
      pr (pftrm, 0);
      if paren > 0 then strpr ")";
    end // end of [TRMlam]
  | PFTRMplam (trm, pftrm) => begin
      if paren > 0 then strpr "(";
      strpr "\\p_:";
      fprint_trm_paren (pf | out, trm, 0);
      strpr ".";
      pr (pftrm, 0);
      if paren > 0 then strpr ")";
    end // end of [TRMlam]
  | PFTRMtapp (pftrm1, trm2) => begin
      if paren > 0 then strpr "(";
      pr (pftrm1, 0);
      strpr " ";
      fprint_trm_paren (pf | out, trm2, 1);
      if paren > 0 then strpr ")";
    end // end of [TRMapp]
  | PFTRMpapp (pftrm1, pftrm2) => begin
      if paren > 0 then strpr "(";
      pr (pftrm1, 0); strpr " "; pr (pftrm2, 1);
      if paren > 0 then strpr ")";
    end // end of [TRMapp]
  | PFTRMxi (pftrm) => begin
      if paren > 0 then strpr "(";
      strpr "'xi"; pr (pftrm, 1);
      if paren > 0 then strpr ")";
    end // end of [TRMany]
end // end of [fprint_pftrm_paren]

implement fprint_pftrm {m}
  (pf | out, pftrm) = fprint_pftrm_paren (pf | out, pftrm, 0)

implement print_pftrm (pftrm) = print_mac (fprint_pftrm, pftrm)
implement prerr_pftrm (pftrm) = prerr_mac (fprint_pftrm, pftrm)

(* ****** ****** *)

val _0 = lam {n:pos} => TRMdbi {n,0} (0)

implement prop_false {n} () = TRMall {n+1} (STPprp (), _0)
implement prop_true {n} () = TRMall {n+1} (STPprp (), TRMimp (_0, _0))

(* ****** ****** *)

implement eq_stp_stp (x1, x2) = eq (x1, x2) where {
  fun eq (x1: stp, x2: stp): bool =
    case+ (x1, x2) of
    | (STPbas nam1, STPbas nam2) => (nam1 = nam2)
    | (STPprp (), STPprp ()) => true
    | (STParr (x11, x12), STParr (x21, x22)) =>
        if eq (x11, x21) then eq (x12, x22) else false
    | (_, _) => false
} // end of [eq_stp_stp]

(* ****** ****** *)

implement eq_trm_trm (x1, x2) = eq (x1, x2) where {
  fun eq (x1: trm, x2: trm): bool =
    case+ (x1, x2) of
    | (TRMnam nam1, TRMnam nam2) => (nam1 = nam2)
    | (TRMdbi ind1, TRMdbi ind2) => (ind1 = ind2)
    | (TRMlam (stp1, trm1), TRMlam (stp2, trm2)) =>
        if stp1 = stp2 then eq (trm1, trm2) else false
    | (TRMall (stp1, trm1), TRMall (stp2, trm2)) =>
        if stp1 = stp2 then eq (trm1, trm2) else false
    | (TRMimp (trm11, trm12), TRMimp (trm21, trm22)) =>
        if eq (trm11, trm21) then eq (trm12, trm22) else false
    | (TRMany stp1, TRMany stp2) => (stp1 = stp2)
    | (_, _) => false
} // end of [eq_trm_trm]

(* ****** ****** *)

(* end of [syntax.dats] *)
