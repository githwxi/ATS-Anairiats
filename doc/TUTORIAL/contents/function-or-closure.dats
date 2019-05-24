//
//
// code for illustration in function-or-closure.html
//
//

(* ****** ****** *)

staload "libc/SATS/stdlib.sats"

(* ****** ****** *)

fn add (x: int): int -<cloref1> int =
  let fn add_x (y: int):<cloref1> int = x + y in add_x end
// end of [add]

(* ****** ****** *)

fn test_qsort () = let
  fun pr_loop {n,i:nat | i <= n} .<n-i>.
    (A: &(@[int][n]), n: size_t n, i: size_t i): void =
    if i < n then begin
      if i > 0 then print ", "; print A.[i]; pr_loop (A, n, i+1)
    end // end of [if]
  // end of [pr_loop]

  // creating a linear array of size 10
  val (pf_gc, pf_arr | p_arr, asz) = $arrsz {int} (1, 9, 2, 8, 3, 7, 4, 6, 5, 0)

  val () = (print "before quicksort:\n")
  val () = pr_loop (!p_arr, asz, 0)
  val () = print_newline ()

  val () = begin
    qsort {int} (!p_arr, asz, sizeof<int>, lam (x, y) => compare (x, y))
  end // end of [val]

  val () = (print "after quicksort:\n")
  val () = pr_loop (!p_arr, asz, 0)
  val () = print_newline ()
in
  array_ptr_free {int} (pf_gc, pf_arr | p_arr)
end // end of [test_qsort]

(* ****** ****** *)

fn add1 (x: int):<fun> int -<cloref> int = let
  fn add1_x (y: int):<cloref> int = x + y in add1_x
end // end of [add1]

(* ****** ****** *)

implement
main () = () where {
  val () = test_qsort ()
} // end of [main]

(* ****** ****** *)

(* end of [function-or-closure.dats] *)
