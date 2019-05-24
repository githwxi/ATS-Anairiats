//
// ProjectEuler: Problem 26
// Finding the integer d < 1000 such that 1/d has the longest recurring cycle
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

fun findcycle (d: int): int = let
  fun find {n:nat}
    (rs: !list_vt (int, n), r: int, c: int): int =
    case+ rs of
    | list_vt_cons (r1, !p_rs1) =>
        if (r = r1) then (fold@ rs; c) else
          let val res = find (!p_rs1, r, c+1) in fold@ rs; res end
        // end of [if]
    | list_vt_nil () => (fold@ rs; 0)
  // end of [find]
  fun find2 (r: int, rs: List_vt int):<cloref1> int =
    if r > 0 then let
      val c = find (rs, r, 1)
    in
      if c = 0 then find2 ((10 * r) mod d, list_vt_cons (r, rs)) else (list_vt_free rs; c)
    end else (list_vt_free rs; 0) (* no cycle *)
  // end of [loop]
in
  find2 (1, list_vt_nil)
end // end of [findcylcle]

(* ****** ****** *)

implement main () = () where {
  var cmax: int = 0
  var imax: int = 0
  var i: int // uninitialized
  val () = for
    (i := 2; i < 10; i := i+1) let
    val c = findcycle (i)
    val () = if c > cmax then (cmax := c; imax := i)
  in
    // nothing
  end // end of [val]
  val ans = imax
  val () = (print "ans(10) = "; print ans; print_newline ())
  val () = for
    (i := 2; i < 1000; i := i+1) let
    val c = findcycle (i)
    val () = if c > cmax then (cmax := c; imax := i)
  in
    // nothing
  end // end of [val]
  val ans = imax
  val () = assert_errmsg (ans = 983, #LOCATION)
  val () = (print "ans(1000) = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem26-hwxi.dats] *)
