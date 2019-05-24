(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "fgnode.sats"

(* ****** ****** *)

assume fgnode_t = Nat

(* ****** ****** *)

implement fgnode_make_int (n) = n

(* ****** ****** *)

implement fprint_fgnode (out, fgn) = fprint_int (out, fgn)
implement print_fgnode (fgn) = fprint_fgnode (stdout_ref, fgn)
implement prerr_fgnode (fgn) = fprint_fgnode (stderr_ref, fgn)

(* ****** ****** *)

implement eq_fgnode_fgnode (fgn1, fgn2) = eq_int_int (fgn1, fgn2)

implement compare_fgnode_fgnode (fgn1, fgn2) = compare_int_int (fgn1, fgn2)

(* ****** ****** *)

assume fgnodelst_t = List (fgnode_t)

(* ****** ****** *)

implement fgnodelst_nil () = '[]
implement fgnodelst_sing (fgn) = '[fgn]

(* ****** ****** *)

implement fprint_fgnodelst
  (out, fgns) = loop (out, fgns, 0) where {
  fun loop (out: FILEref, fgns: fgnodelst_t, i: int): void =
    case+ fgns of
    | list_cons (fgn, fgns) => () where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_fgnode (out, fgn)
        val () = loop (out, fgns, i+1)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [fprint_fgnodelst]

implement print_fgnodelst (fgns) = fprint_fgnodelst (stdout_ref, fgns)
implement prerr_fgnodelst (fgns) = fprint_fgnodelst (stderr_ref, fgns)

(* ****** ****** *)

implement fgnodelst_ismem (fgns, fgn0) = case+ fgns of
  | list_cons (fgn, fgns) =>
      if fgn0 < fgn then false
      else if fgn0 > fgn then fgnodelst_ismem (fgns, fgn0)
      else true
    // end of [list_cons]
  | list_nil () => false
// end of [fgnodelst_ismem]

(* ****** ****** *)

implement fgnodelst_add (fgns, fgn0) = case+ fgns of
  | list_cons (fgn, fgns1) => begin
      if fgn0 < fgn then
        list_cons (fgn0, fgns)
      else if fgn0 > fgn then
        list_cons (fgn, fgnodelst_add (fgns1, fgn0))
      else fgns
    end // end of [list_cons]
  | list_nil () => list_cons (fgn0, list_nil)
// end of [fgnodelst_insert]

(* ****** ****** *)

(* end of [fgnode.sats] *)
