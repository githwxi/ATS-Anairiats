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

datatype pretrm =
  | PRETRMname of string
  | PRETRMlam of (List string, pretrmopt, pretrm)
  | PRETRMplam of (List string, pretrmopt, pretrm)
  | PRETRMapp of (pretrm, pretrm)
  | PRETRMuni of (List string, pretrmopt, pretrm)
  | PRETRMexi of (List string, pretrmopt, pretrm)
  | PRETRMimp of (pretrm, pretrm)
  | PRETRMbool of bool
  | PRETRMconj of (pretrm, pretrm)
  | PRETRMdisj of (pretrm, pretrm)
  | PRETRMneg of pretrm
  | PRETRMeq of (pretrm, pretrm)
  | PRETRMequiv of (pretrm, pretrm)
  | PRETRMcoerce of (pretrm, pretrm)
  | PRETRMxirule of pretrm
  | PRETRMblank of ()
  
where pretrmopt = Option (pretrm)

fun fprint_pretrm {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, pt: pretrm): void

fun print_pretrm (pt: pretrm): void
fun prerr_pretrm (pt: pretrm): void

(* ****** ****** *)

datatype docitem =
  | DOCITEMvars of (List string, pretrm)
  | DOCITEMhyp of (string, pretrm)
  | DOCITEMconst of (string, pretrm)
  | DOCITEMknown of (string, pretrm)
  | DOCITEMdef of (string, pretrmopt, pretrmopt)
  | DOCITEMabstract of List string
  | DOCITEMabstract_all of ()
  | DOCITEMallow_eta of ()
  | DOCITEMallow_xi of ()
  | DOCITEMallow_defaults of ()
  | DOCITEMclaim of (string, pretrm)
  | DOCITEMaccept of List string
  | DOCITEMaccept_all of ()
  | DOCITEMproof of (string, pretrm)
  | DOCITEMinconsistent of pretrm

(* ****** ****** *)

(* end of [parsedata.sats] *)
