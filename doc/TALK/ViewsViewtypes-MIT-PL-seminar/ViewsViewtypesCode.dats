(* ****** ****** *)

datatype list (a:type, int) =
  | nil (a, 0) of ()
  | {n:int | n >= 0} cons (a, n+1) of (a, list (a, n))

(* ****** ****** *)

datatype FIB (int, int) =
  | FIB0 (0, 0) of () // fib(0) = 0
  | FIB1 (1, 1) of () // fib(1) = 1
  | {n:nat}{r0,r1:nat} // fib(n+2) = fib(n)+fib(n+1)
    FIB2 (n+2, r0+r1) of (FIB (n, r0), FIB (n+1, r1))

extern
fun fib {n:nat}
  (n: int (n)): [r:nat] (FIB (n, r) | int (r))

(* ****** ****** *)

implement fib (n) =
  case+ n of
  | 0 => (FIB0 () |  0)
  | 1 => (FIB1 () |  1)
  | _ =>> let
      val (pf0 | r0) = fib (n-2)
      val (pf1 | r1) = fib (n-1)
    in
      (FIB2 (pf0, pf1) | r0 + r1)
    end
// end of [fib]

implement
fib {n} (n) = let
  fun loop
    {i:nat | i < n} {r0,r1:nat} (
    pf0: FIB (i, r0), pf1: FIB (i+1, r1)
  | ni: int (n-i), r0: int r0, r1: int r1
  ) : [r:nat] (FIB (n, r) | int r) =
    if ni > 1 then
      loop {i+1} (pf1, FIB2 (pf0, pf1) | ni-1, r1, r0+r1)
    else (pf1 | r1)
in
  case+ n of
  | 0 => (FIB0 () |  0)
  | 1 => (FIB1 () |  1)
  | _ =>> loop {0} (FIB0, FIB1 | n, 0, 1)
end // end of [fib]

(* ****** ****** *)

extern
fun{a:type}
ptrget {l:addr}
  (pf: a@l | p: ptr l): (a@l | a)
// end of [ptrget]

extern
fun{a:type}
ptrset {l:addr}
  (pf: (a?)@l | p: ptr l, x: a): (a@l | void)
// end of [ptrset]

fun{a:type}
swap {l1,l2:addr} (
  pf1: a@l1, pf2:a@l2 | p1: ptr l1, p2: ptr l2
) : (a@l1, a@l2 | void) = let
  val (pf1 | x1) = ptrget<a> (pf1 | p1)
  val (pf2 | x2) = ptrget<a> (pf2 | p2)
  val (pf1 | ()) = ptrset<a> (pf1 | p1, x2)
  val (pf2 | ()) = ptrset<a> (pf2 | p2, x1)
in
  (pf1, pf2 | ())
end // end of [swap]

extern
fun{a:type}
ptrget {l:addr}
  (pf: !a@l | p: ptr l): a
// end of [ptrget]

extern
fun{a:type}
ptrset {l:addr}
  (pf: !(a?)@l | p: ptr l, x: a): void
// end of [ptrset]

fun{a:type}
swap {l1,l2:addr} (
  pf1: !a@l1, pf2: !a@l2
| p1: ptr l1, p2: ptr l2
) : void = let
  val tmp = !p1 in !p1 := !p2; !p2 := tmp
end // end of [swap]

fun{a:type}
swap (x1: &a, x2: &a): void = let
  val tmp = x1 in x1 := x2; x2 := tmp
end // end of [swap]

dataview array_v (a:type, int, addr) =
  | {l:addr}
    array_v_nil (a,0,l)
  | {n:nat}{l:addr}
    array_v_cons (a,n+1,l) of (a@l, array_v (a,n,l+1))

extern
prfun split
  {a:t@ype}
  {n:int}{i:nat | i <= n}
  {l:addr} (
  pf: array_v (a, n, l)
) : (array_v (a, i, l), array_v (a, n-i, l+i))

extern
prfun unsplit
  {a:t@ype}
  {n1,n2:nat}{l:addr} (
  pf1: array_v (a, n1, l), pf2: array_v (a, n2, l+n1)
) : array_v (a, n1+n2, l)

extern
prfun takeout
  {a:type}
  {n:int}{i:nat | i < n}
  {l:addr} (
  pf: array_v (a, n, l)
) : (a @ l+i, a @ l+i -<lin> array_v (a, n, l))

fun{a:type}
arrsub
  {n:int}{i:nat | i < n}
  {l:addr} (
  pf: !array_v (a, n, l) | p: ptr l, i: int i
) : a = x where {
  prval (pfat, fpf) = takeout {a}{n}{i} (pf)
  val x = ptrget<a> (pfat | p+i)
  prval () = pf := fpf (pfat)
} // end of [arrsub]

dataviewtype
list_vt (a:type, int) =
  | {n:nat}
    list_vt_cons (a, n+1) of (a, list_vt (a, n))
  | list_vt_nil (a, 0)
// end of [list_vt]

fun{a:type}
revapp {m,n:nat} (
  xs: list_vt (a, m)
, ys: list_vt (a, n)
) : list_vt (a, m+n) =
  case+ xs of
  | list_vt_cons
      (_, !ptl) => let
      val tl = !ptl; val () = !ptl := ys
      prval () = fold@ (xs)
    in
      revapp (tl, xs)
    end
  | ~list_vt_nil () => ys
// end of [revapp]

fun{a:type}
reverse {n:nat} (
  xs: list_vt (a, n)
) : list_vt (a, n) = revapp (xs, list_vt_nil)

(* ****** ****** *)

absviewtype queue (a:viewtype, n:int)

extern
fun{a:viewtype} queue_new (): queue (a, 0)
extern
fun{a:viewtype} queue_free (obj: queue (a, 0)): void

extern
fun{a:viewtype}
queue_enque {n:nat} (
  obj: !queue (a, n) >> queue (a, n+1), x: a
) : void // end of [queue_enque]

extern
fun{a:viewtype}
queue_deque {n:pos}
  (obj: !queue (a, n) >> queue (a, n-1)): a

(* ****** ****** *)

absviewtype mylock (v:view)

extern
fun mylock_create
  {v:view} (pf: v | (*none*)): mylock(v)

extern
fun mylock_destroy
  {v:view} (lock: mylock v): (v | void)

extern
fun mylock_acquire
  {v:view} (lock: !mylock v): (v | void)

extern
fun mylock_release
  {v:view} (pf: v | lock: !mylock v): void

(* ****** ****** *)

(* end of [code.dats] *)
