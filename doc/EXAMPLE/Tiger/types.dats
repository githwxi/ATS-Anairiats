(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "stamp.sats"
staload "symbol.sats"

(* ****** ****** *)

staload "types.sats"

(* ****** ****** *)

fn fprint_labtylst
  (out: FILEref, ltys: labtylst): void = let
  fun loop (out: FILEref, ltys: labtylst, i: int): void = let
    macdef prstr str = fprint_string (out, ,(str)) in
    case+ ltys of
    | LABTYLSTcons (lab, ty, ltys) => loop (out, ltys, i+1) where {
        val () = if i > 0 then prstr ", "
        val () = begin
          fprint_symbol (out, lab); prstr ": "; fprint_ty (out, ty)
        end // end of [val]
      } // end of [LABTYLSTcons]
    | LABTYLSTnil () => ()
  end // end of [loop]
in
  loop (out, ltys, 0)
end // end of [fprint_labtylst]

implement fprint_ty (out, ty) = let
  macdef prstr str = fprint_string (out, ,(str))
  macdef prty ty = fprint_ty (out, ,(ty))
in
  case+ ty of
  | TYarr (stamp, ty_elt) => begin
      prstr "TYarr("; prty ty_elt; prstr ")"
    end // end of [TYarr]
  | TYbase sym => fprint_symbol (out, sym)
  | TYname (sym, _) => fprint_symbol (out, sym)
  | TYnil () => begin
      prstr "TYnil("; prstr ")"
    end // end of [TYnil]
  | TYrec (stamp, ltys) => begin
      prstr "TYrec("; fprint_labtylst (out, ltys); prstr ")"
    end // end of [TYrec]
  | TYtop () => begin
      prstr "TYtop("; prstr ")"
    end // end of [TYnil]
  | TYunit () => begin
      prstr "TYunit("; prstr ")"
    end // end of [TYnil]
end // end of [fprint_ty]

(* ****** ****** *)

implement print_ty (ty) = fprint_ty (stdout_ref, ty)
implement prerr_ty (ty) = fprint_ty (stderr_ref, ty)

(* ****** ****** *)

implement ty_lnkrmv (r_ty) = case+ !r_ty of
  | TYname (_, r_ty1) => let
      val ty1 = ty_lnkrmv r_ty1 in !r_ty := ty1; ty1
    end // end of [TYname]
  | ty => ty
// end of [ty_lnkrmv]

implement ty_normalize (ty) = case+ ty of
  | TYname (_, r_ty) => ty_lnkrmv (r_ty) | _ => ty
// end of [ty_normalize]

implement join_ty_ty (ty1, ty2) = case+ (ty1, ty2) of
  | (TYname (_, r_ty1), _) => let
      val ty1 = ty_lnkrmv (r_ty1) in join_ty_ty (ty1, ty2)
    end // end of [TYname _, _]
  | (_, TYname (_, r_ty2)) => let
      val ty2 = ty_lnkrmv (r_ty2) in join_ty_ty (ty1, ty2)
    end // end of [_, TYname _]
  | (TYbase sym1, TYbase sym2) when (sym1 = sym2) => ty1
  | (TYunit _, TYunit _) => ty1
  | (TYrec (stamp1, _), TYrec (stamp2, _)) when (stamp1 = stamp2) => ty1
  | (TYrec _, TYnil _) => ty1
  | (TYnil _, TYrec _) => ty2
  | (TYnil _, TYnil _) => ty1
  | (TYarr (stamp1, _), TYarr (stamp2, _)) when (stamp1 = stamp2) => ty1
  | (_, _) => TYtop ()
// end of [join_ty_ty]

implement ty_normalize_max (ty, n) = case+ 0 of
  | _ when n > 0 => begin case+ ty of
    | TYname (_, r_ty1) => let
        val ty1 = ty_normalize_max (!r_ty1, n-1)
      in
        !r_ty1 := ty1; ty1
      end // end of [TYname]
    | _ => ty
    end // end of [_ when ...]
  | _ (* n = 0 *) => ty
// end of [ty_normalize_max]

(* ****** ****** *)

(* end of [types.dats] *)
