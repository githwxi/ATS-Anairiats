(*
**
** Some utility functions for supporting syndef
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time

(* ****** ****** *)

staload Err = "ats_error.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

staload "atsyndef_util.sats"

(* ****** ****** *)

#define :: list_cons

(* ****** ****** *)

implement
prerr_loc_syndef (loc) =
  ($Loc.prerr_location loc; prerr ": error(syndef)")
// end of [prerr_loc_syndef]

(* ****** ****** *)

implement
d1exp_binop
  (loc0, fid, d1e1, d1e2) = let
  val loc_arg = $Loc.location_combine (d1e1.d1exp_loc, d1e2.d1exp_loc)
  val fqid = d1exp_qid (loc0, $Syn.d0ynq_none (), fid)
in
  d1exp_app_dyn (loc0, fqid, loc_arg, 0(*npf*), d1e1 :: d1e2 :: list_nil)
end // end of [d1exp_binop]

(* ****** ****** *)

implement
d1ec_sym_exp
  (loc0, x_id, d1e) = let
  val x_pat = p1at_ide (loc0, x_id)
  val x_valdec = v1aldec_make (loc0, x_pat, d1e, WITHT1YPEnone)
in
  d1ec_valdecs (loc0, $Syn.VALKINDval, x_valdec :: list_nil)
end // end of [d1ec_sym_exp]

(* ****** ****** *)

(* end of [atsyndef_util.dats] *)
