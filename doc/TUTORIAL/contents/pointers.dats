//
//
// code for illustration in pointers.html
//
//

(* ****** ****** *)

staload "prelude/DATS/pointer.dats"

(* ****** ****** *)

fn{a:viewt@ype} swap1 {l1,l2:addr}
  (pf1: !a @ l1, pf2: !a @ l2 | p1: ptr l1, p2: ptr l2): void =
  let
    val tmp = ptr_get_vt<a> (pf1 | p1)
  in
    ptr_set_vt<a> (pf1 | p1, ptr_get_vt (pf2 | p2));
    ptr_set_vt<a> (pf2 | p2, tmp)
  end

fn{a:viewt@ype} swap2 {l1,l2:addr}
  (pf1: !a @ l1, pf2: !a @ l2 | p1: ptr l1, p2: ptr l2): void =
  let
    val tmp = !p1
  in
    !p1 := !p2; !p2 := tmp
  end

(* ****** ****** *)

(* end of [pointer.dats] *)
