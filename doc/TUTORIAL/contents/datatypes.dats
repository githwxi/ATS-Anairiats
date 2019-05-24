//
//
// code demonstrating some typical uses of datatypes
//
//

datatype intlst0 = // simple datatype
  | INTLST0nil // the first bar (|) is optional
  | INTLST0cons of (int, intlst0)

fun length_intlst0 (xs: intlst0): int =
  case+ xs of // [case+] demands exhaustive pattern matching
  // the bar (|) in the first clause is optional
  | INTLST0cons (_, xs) => 1 + length_intlst0 (xs)
  | INTLST0nil () => 0
// end of [length_intlst0]

(* ****** ****** *)

datatype intlst1 (int) = // dependent datatype
  | INTLST1nil (0) // the first bar (|) is optional
  | {n:nat} INTLST1cons (n+1) of (int, intlst1 n)
// end of [intlst1]

fun length_intlst1 {n:nat} (xs: intlst1 n): int n =
  case+ xs of // the bar (|) in the first clause is optional
  // the bar (|) in the first clause is optional
  | INTLST1cons (_, xs) => 1 + length_intlst1 (xs)
  | INTLST1nil () => 0
// end of [length_intlst1]

// the index is a natural number less than the size of the indexed length
fun nth_intlst1 {n,i:int | 0 <= i; i < n} (xs: intlst1 n, i: int i): int =
  // [val+] demands exhaustive pattern matching
  let val+ INTLST1cons (x, xs) = xs in
    if i > 0 then nth_intlst1 (xs, i-1) else x
  end // end of [let]
// end of [nth_intlst1]

(* ****** ****** *)

datatype list
  (a:t@ype+, int) = // polymorphic datatype
  | nil (a, 0)
  | {n:nat} cons (a, n+1) of (a, list (a, n))
// end of [list]

fun{a:t@ype} append_list {m,n:nat}
  (xs: list (a, m), ys: list (a, n)): list (a, m+n) =
  case+ xs of
  | cons (x, xs) => cons (x, append_list (xs, ys))
  | nil () => ys
// end of [append_list]

fun{a1,a2:t@ype} zip_list {n:nat}
  (xs1: list (a1, n), xs2: list (a2, n)): list ('(a1, a2), n) =
  case+ (xs1, xs2) of
  | (cons (x1, xs1), cons (x2, xs2)) => cons ('(x1, x2), zip_list (xs1, xs2))
  | (nil (), nil ()) => nil ()
  | (_, _) =/=>> () // other cases cannot occur
// end of [zip_list]

(* ****** ****** *)

// a simple test

fun{a:t@ype} foreach_list {n:nat}
  (f: a -> void, xs: list (a, n)): void = case+ xs of
  | cons (x, xs) => (f x; foreach_list (f, xs)) | nil () => ()
// end of [foreach_list]

implement main (argc, argv) = let
  val xs = cons (1, cons (2, cons (3, nil ())))
  val ys = cons (1.0, cons (2.0, cons (3.0, nil ())))
  val xs2 = append_list (xs, xs)
  val ys2 = append_list (ys, ys)
  val xys2 = zip_list (xs2, ys2)
  val yxs2 = zip_list (ys2, xs2)
  typedef T1 = '(int, double)
  typedef T2 = '(double, int)
  val () =  foreach_list<T1>
    (lam '(x, y) => printf ("(%i, %.2f)\n", @(x, y)), xys2) ;
  val () = foreach_list<T2>
    (lam '(y, x) => printf ("(%.2f, %i)\n", @(y, x)), yxs2)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [datatypes.dats] *)
