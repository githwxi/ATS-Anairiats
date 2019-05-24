//
// ProjectEuler: Problem 10
// Calculating the sum of all primes < 2M
//

(* ****** ****** *)
//
// Author Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Summer, 2008
//
(* ****** ****** *)

macdef  true = int8_of_int 1
macdef false = int8_of_int 0

typedef bool = int8

fn sumprimes {m:nat} (m: int m): uint64 = let
//
  val m_sz = size1_of_int1 m
  val [l:addr] (pf_gc, pf | A) =
    array_ptr_alloc_tsz {bool} (m_sz, sizeof<bool>)
  var _true: bool = true
  val () = array_ptr_initialize_elt_tsz {bool} (!A, m_sz, _true, sizeof<bool>)
//
  fun loop1
    (pf: !array_v (bool, m, l) | i: Nat, j: Nat):<cloptr1> void =
    if (j < m) then
      (if A[j] = true then A[j] := false; loop1 (pf | i, j+i))
    // end of [if]
  // end of [loop1]

  fun loop2 (pf: !array_v (bool, m, l) | i: Nat, c: uint64):<cloptr1> uint64 =
    if i < m then
      if A[i] = true then (loop1 (pf | i, i+i); loop2 (pf | i+1, c+(uint64_of)i))
      else loop2 (pf | i+1, c)
    else c
  // end of [loop2]
//
  val sum = loop2 (pf | 2, (uint64_of)0)
//
  val () = array_ptr_free {bool?} (pf_gc, pf | A)
in
  sum
end // end of [sumprimes]

(* ****** ****** *)

implement
main (argc, argv) = () where {
//
  val sum10 = sumprimes (10)
  val () = (
    print ("The sum of all the primes < 10 = "); print (sum10); print_newline ()
  ) // end of [val]
//
  val sum2M = sumprimes (2000000)
  val () = assert_errmsg (sum2M = (uint64_of)142913828922ULL, #LOCATION)
  val () = (
    print ("The sum of all the primes < 2M = "); print (sum2M); print_newline ()
  ) // end of [val]
//
} // end of [main]

(* ****** ****** *)

(* end of [problem10-hwxi.dats] *)
