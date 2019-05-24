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

staload "parsedata.sats"

(* ****** ****** *)

fun fprint_arglst {m: file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, xs: List string): void = let
  fun loop
    (out: &FILE m, xs: List string, i: int): void = begin
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then fprint_string (pf | out, ", ")
      in
        fprint_string (pf | out, x); loop (out, xs, i+1)
      end
    | list_nil () => ()
  end // end of [loop]
in
  loop (out, xs, 0)
end // end of [fprint_arglst]

fun fprint_pretrm_paren {m: file_mode} (
    pf: file_mode_lte (m, w) | out: &FILE m, pt: pretrm, paren: int
  ) : void = let
  macdef strpr (s) = fprint_string (pf | out, ,(s))
  macdef pr (pt, paren) = fprint_pretrm_paren (pf | out, ,(pt), ,(paren))
in
  case+ pt of
  | PRETRMname name => fprint_string (pf | out, name)
  | PRETRMlam (xs, _, pt) => begin
      if paren > 0 then strpr "(";
      strpr "\\ ";
      fprint_arglst (pf | out, xs);
      strpr ".";
      pr (pt, 0);      
      if paren > 0 then strpr ")";
    end // end of [PRETRMlam]
  | PRETRMplam (xs, _, pt) => begin
      if paren > 0 then strpr "(";
      strpr "/ ";
      fprint_arglst (pf | out, xs);
      strpr ".";
      pr (pt, 0);      
      if paren > 0 then strpr ")";
    end // end of [PRETRMlam]
  | PRETRMapp (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 0); strpr " "; pr (pt2, 1);
      if paren > 0 then strpr ")";            
    end // end of [PRETRMapp]
  | PRETRMuni (xs, opt1, pt2) => begin
      if paren > 0 then strpr "(";
      strpr "!";
      fprint_arglst (pf | out, xs);
      begin case+ opt1 of
        | Some pt1 => (strpr ": ", pr (pt1, 1)) | None () => ()
      end;
      strpr ".";
      pr (pt2, 0);
      if paren > 0 then strpr ")";                  
    end // end of [PRETRMuni]
  | PRETRMexi (xs, opt1, pt2) => begin
      if paren > 0 then strpr "(";
      strpr "?";
      fprint_arglst (pf | out, xs);
      begin case+ opt1 of
        | Some pt1 => (strpr ": ", pr (pt1, 1)) | None () => ()
      end;
      strpr ".";
      pr (pt2, 0);
      if paren > 0 then strpr ")";                  
    end // end of [PRETRMexi]
  | PRETRMimp (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 1); strpr ">"; pr (pt2, 0);
      if paren > 0 then strpr ")";
    end // end of [PRETRMimp]
  | PRETRMeq (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 1); strpr "="; pr (pt2, 0);
      if paren > 0 then strpr ")";
    end // end of [PRETRMeq]
  | PRETRMequiv (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 1); strpr "<=>"; pr (pt2, 0);
      if paren > 0 then strpr ")";
    end // end of [PRETRMequiv]
  | PRETRMcoerce (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 0); strpr ":"; pr (pt2, 0);
      if paren > 0 then strpr ")";
    end // end of [PRETRMequiv]
  | PRETRMconj (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 1); strpr "&"; pr (pt2, 0);
      if paren > 0 then strpr ")";
    end // end of [PRETRMconj]
  | PRETRMdisj (pt1, pt2) => begin
      if paren > 0 then strpr "(";
      pr (pt1, 1); strpr "|"; pr (pt2, 0);
      if paren > 0 then strpr ")";
    end // end of [PRETRMdisj]
  | PRETRMbool (b) => begin
      if b then strpr "true" else strpr "false"
    end
  | PRETRMneg (pt) => begin
      if paren > 0 then strpr "(";
      strpr "~"; pr (pt, 1);
      if paren > 0 then strpr ")";
    end // end of [PRETRMneg]
  | PRETRMxirule (pt) => begin
      if paren > 0 then strpr "(";
      strpr "'xi"; pr (pt, 1);
      if paren > 0 then strpr ")";
    end // end of [PRETRMneg]
  | PRETRMblank () => strpr "_"
(*
  | _ => ()
*)
end // end of [fprint_pretrm_paren]

implement fprint_pretrm (pf | out, pt) =
  fprint_pretrm_paren (pf | out, pt, 0)

implement print_pretrm (pt) = print_mac (fprint_pretrm, pt)
implement prerr_pretrm (pt) = prerr_mac (fprint_pretrm, pt)

(* ****** ****** *)

(* end of [parsedata.dats] *)
