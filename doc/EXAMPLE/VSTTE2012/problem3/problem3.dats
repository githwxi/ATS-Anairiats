(*
**
** VSTTE 2012 Verification Competition
**
** Problem 3
**
** the following code gives you a verfied template-implementation
** of ring buffers.
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

staload "queue_alg.sats"

(* ****** ****** *)
//
// a: element type
// m: maximal capacity
// xs: the current content of the queue
//
absviewtype
ringbuf (a:t@ype, m:int, xs: ilist)

(* ****** ****** *)

sortdef elt = int

abst@ype E (a:t@ype, x:elt) = a // [x] is just a stamp

(* ****** ****** *)

extern
fun{a:t@ype}
create {m:pos} // [m] must be positive
  (m: int (m)): ringbuf (a, m, nil)
// end of [create]

extern
fun rbfree {a:t@ype}
  {m:nat} {xs:ilist} (rb: ringbuf (a, m, xs)): void
// end of [rbfree]

(* ****** ****** *)

extern
fun{a:t@ype}
clear {m:nat} {xs:ilist} (
  rb: !ringbuf (a, m, xs) >> ringbuf (a, m, nil)
) : void // end of [clear]

(* ****** ****** *)
//
// the type says that if [x] is the first element of [xs]
// and the ringbuf is indexed by [xs], then the return value
// is stamped by [x] (while the ringbuf is unchanged)
//
extern
fun{a:t@ype}
head {m:nat} {xs:ilist} {x:elt} (
  pf: HQ (xs, x) | rb: !ringbuf (a, m, xs)
) : E (a, x)

(* ****** ****** *)
//
// the type says that if [x] is the stamp of the pushed element
// and the ringbuf is indexed by [xs], then the new ringbuf is
// indexed by [xs1], where ENQUE (x, xs, xs1) holds. Note that
// ENQUE is defined in [queue_alg.sats].
//
extern
fun{a:t@ype}
push {m,n:nat | n < m}
  {x:elt} {xs:ilist} {xs1:ilist} (
  pf1: LENGTH (xs, n), pf2: ENQUE (x, xs, xs1)
| rb: !ringbuf (a, m, xs) >> ringbuf (a, m, xs1), x: E (a, x)
) : void // end of [push]

(* ****** ****** *)
//
// the type says that if the ringbuf is indexed by [xs], then
// the new ringbuf is indexed by [xs1] and an element stamped by
// [x] is returned, where DEQUE (xs, xs1, x) holds. Note that
// DEQUE is defined in [queue_alg.sats].
//
extern
fun{a:t@ype}
pop {m,n:nat | m >= n; n > 0}
  {xs:ilist} {xs1:ilist} {x:elt} (
  pf1: LENGTH (xs, n), pf2: DEQUE (xs, xs1, x)
| rb: !ringbuf (a, m, xs) >> ringbuf (a, m, xs1)
) : E (a, x) // end of [pop]

(* ****** ****** *)
//
// This is a *static* asserting function
//
prfn sassert
  {a:t@ype}
  {x,y:elt | x == y}
  (_: E (a, x), _: E (a, y)): void = ()
// end of [sassert]

(* ****** ****** *)
//
// VT3: Harness (20 points)
//
fun{a:t@ype}
test {x,y,z:elt}
  (x: E (a, x), y: E (a, y), z: E (a, z)) = let
  val rb = create<a> (2)
//
  prval pflen0 = LENGTHnil ()
  prval pfenq0 = ENQUE () // x :: nil
  val () = push (pflen0, pfenq0 | rb, x)
//
  prval pflen1 = LENGTHcons (LENGTHnil ())
  prval pfenq1 = ENQUE ()
  val () = push (pflen1, pfenq1 | rb, y)
//
  prval pflen2 = LENGTHcons (pflen1)
  prval pfdeq2 = DEQUE_cons (DEQUE_nil ())
  val h = pop (pflen2, pfdeq2 | rb)
  prval () = sassert (h, x) // Yes, [h] and [x] are the same
//
  prval pflen1 = LENGTHcons (LENGTHnil ())
  prval pfenq1 = ENQUE ()
  val () = push (pflen1, pfenq1 | rb, z)
//
  prval pflen2 = LENGTHcons (pflen1)
  prval pfdeq2 = DEQUE_cons (DEQUE_nil ())
  val h = pop (pflen2, pfdeq2 | rb)
  prval () = sassert (h, y) // Yes, [h] and [y] are the same
//
  prval pflen1 = LENGTHcons (LENGTHnil ())
  prval pfdeq1 = DEQUE_nil ()
  val h = pop (pflen1, pfdeq1 | rb)
  prval () = sassert (h, z) // Yes, [h] and [z] are the same
//
in
  rbfree (rb) // this is needed as [b] is a linear resource
end // end of [test]

(* ****** ****** *)
//
// It is unclear how much verification we should do. Here we
// introduce an abstract view arrseg_v (a, l, xs, f, n) to describe
// a segment of an array located at the address [l]; the type of the
// elements is [a]; the sequence of the elements is [xs]; the starting
// position of the segment is [f] and the length of the segment
// is [n]. While [arrseg_v] can be defined in terms more primitive
// views, we will *not* do so in this solution.
//
absview
arrseg_v (a:t@ype, l:addr, xs: ilist, f:int, n:int)
absview arrseg0_v (a:t@ype, l:addr, f:int, n:int) // unoccupied segment

extern
praxi
arrseg0_v_of_arrseg_v {a:t@ype}
  {l:addr} {xs:ilist} {f,n:nat} (pf: arrseg_v (a, l, xs, f, n)): arrseg0_v (a, l, f, n)
// end of [arrseg0_v_of_arrseg_v]

extern
praxi
lemma_arrseg_v_length {a:t@ype}
  {l:addr} {xs:ilist} {f,n:nat} (pf: !arrseg_v (a, l, xs, f, n)): LENGTH (xs, n)
// end of [lemma_arrseg_v_length]

extern
praxi
arrseg_v_split {a:t@ype}
  {l:addr} {xs:ilist} {f,n:nat} {i:nat | i <= n} (
  pf: arrseg_v (a, l, xs, f, n)
) : [xs1,xs2:ilist] (
  APPEND (xs1, xs2, xs), arrseg_v (a, l, xs1, f, f+i), arrseg_v (a, l, xs2, f+i, n-i)
) // end of [arrseg_v_split]

extern
praxi
arrseg_v_unsplit {a:t@ype}
  {l:addr} {xs1,xs2:ilist} {f:nat} {n1,n2:nat} (
  pf1: arrseg_v (a, l, xs1, f, n1), pf2: arrseg_v (a, l, xs2, f+n1, n2)
) : [xs:ilist] (
  APPEND (xs1, xs2, xs),arrseg_v (a, l, xs, f, n1+n2)
) // end of [arrseg_v_unsplit]

(* ****** ****** *)
//
// HX: reverse NTH
//
dataprop
RNTH (x0:int, ilist, int) =
  | {xs:ilist} {n:nat}
    RNTHbas (x0, ilist_cons (x0, xs), n) of LENGTH (xs, n)
  | {x:int} {xs:ilist} {n:nat}
    RNTHind (x0, ilist_cons (x, xs), n) of RNTH (x0, xs, n)
// end of [RNTH]

extern
fun{a:t@ype}
arrseg_get
  {l:addr}
  {x:elt}
  {xs:ilist}
  {f,n:nat}
  {i:nat | i < n} (
  pf1: RNTH (x, xs, i), pf2: !arrseg_v (a, l, xs, f, n)
| p: ptr l, f: int f, i: int i
) : E (a, x) // end of [arrseg_get]

extern
fun{a:t@ype}
arrseg0_set
  {l:addr} {x:elt} {xs:ilist} {f:nat} (
  pf: !arrseg0_v (a, l, f, 1) >> arrseg_v (a, l, ilist_sing(x), f, 1)
| p: ptr l, f: int f, x: E (a, x)
) : void // end of [arrseg0_set]

(* ****** ****** *)

dataview
ringbuf_v (
  a:t@ype, l:addr, m:int, xs:ilist, int(*f*), int(*n*)
) =
  | {f,n:nat | f < m; f+n <= m}
    ringbuf_v_one (a, l, m, xs, n, f) of
      (arrseg_v (a, l, xs, f, n), arrseg0_v (a, l, f, m-f-n), arrseg0_v (a, l, 0, f))
  | {f,n:nat | f < m; n <= m; m < f+n} {xs1,xs2:ilist}
    ringbuf_v_two (a, l, m, xs, n, f) of (
      APPEND (xs1, xs2, xs)
    , arrseg_v (a, l, xs1, f, m-f), arrseg_v (a, l, xs2, 0, f+n-m), arrseg0_v (a, l, f+n-m, m-n)
    ) // end of [ringbuf_v_two]
// end of [ringbuf_v]

extern
praxi
ringbuf_v_of_array_v
  {a:t@ype}
  {m:nat} {l:addr}
  {f:nat} (
  pf: array_v (a?, m, l)
) : ringbuf_v (a, l, m, nil, f, 0)

extern
praxi
array_v_of_ringbuf_v
  {a:t@ype}
  {l:addr} {m:nat} {xs:ilist}
  {f,n:nat} (
  pf: ringbuf_v (a, l, m, xs, f, n)
) : array_v (a?, m, l)

extern
praxi
lemma_ringbuf_v_length {a:t@ype}
  {l:addr} {m:nat} {xs:ilist} {f,n:nat}
  (pf: !ringbuf_v (a, l, m, xs, f, n)): LENGTH (xs, n)
// end of [lemma_ringbuf_v_length]

(* ****** ****** *)

local

typedef
ringbuf_struct (
  l:addr, m:int, f:int, n:int
) = @{
  data= ptr (l)
, size= int (m)
, first= int (f)
, len= int (n)
} // end of [ringbuf_struct]

typedef
ringbuf0_struct = ringbuf_struct (null, 0, 0, 0) // a dummy

assume
ringbuf (
  a:t@ype, m:int, xs:ilist
) = [l0:addr;l:addr;f,n:nat] @{
  atview=
    ringbuf_struct (l, m, f, n) @ l0
, bufview= ringbuf_v (a, l, m, xs, f, n)
, gcview= free_gc_v (ringbuf0_struct?, l0)
, gcview_arr= free_gc_v (a?, m, l)
, ptr= ptr l0
} // end of [ringbuf]

in

(*
extern
fun{a:t@ype}
create {m:nat}
  (m: int (m)): ringbuf (a, m, nil)
// end of [create]
*)
implement{a}
create (m) = let
  val [l:addr] (pfgc, pfat | p) = ptr_alloc<ringbuf0_struct> ()
  val [l_arr:addr] (pfgc_arr, pf_arr | p_arr) = array_ptr_alloc<a> ((size1_of_int1)m)
//
  val () = p->data := p_arr
  val () = p->size := m
  val () = p->first := 0
  val () = p->len := 0
//
  prval pfbuf = ringbuf_v_of_array_v {a} (pf_arr) 
//
in #[
  l,l_arr,0,0
| @{
  atview=pfat
, bufview=pfbuf
, gcview=pfgc
, gcview_arr=pfgc_arr
, ptr= p
} ] end // end of [create]

(* ****** ****** *)

implement
rbfree {a} (rb) = let
  val p = rb.ptr
  prval pfat = rb.atview
  prval pf_arr = array_v_of_ringbuf_v (rb.bufview)
  val () = array_ptr_free {a?} (rb.gcview_arr, pf_arr | p->data)
  val () = ptr_free {ringbuf0_struct?} (rb.gcview, pfat | p)
in
  // nothing
end // end of [rbfree]

(* ****** ****** *)

(*
extern
fun{a:t@ype}
clear {m:nat} {xs:ilist} (
  rb: !ringbuf (a, m, xs) >> ringbuf (a, m, nil)
) : void // end of [clear]
*)
implement{a}
clear (rb) = let
  val p = rb.ptr
  prval pfat = rb.atview
  val () = p->len := 0
  prval pf_arr = array_v_of_ringbuf_v {a} (rb.bufview)
  prval () = rb.bufview := ringbuf_v_of_array_v {a} (pf_arr)
  prval () = rb.atview := pfat
in
  // nothing
end // end of [clear]

(* ****** ****** *)

(*
extern
fun{a:t@ype}
head {m:nat} {xs:ilist} {x:elt} (
  pf: HQ (xs, x) | rb: !ringbuf (a, m, xs)
) : E (a, x)
*)
(*
dataview
ringbuf_v (
  a:t@ype, l:addr, m:int, xs:ilist, int(*f*), int(*n*)
) // end of [ringbuf_v]
*)
extern
praxi
ringbuf_v_head
  {a:t@ype}
  {l:addr} {m:nat}
  {xs:ilist} {x:elt}
  {f,n:nat} (
  pfhq: HQ (xs, x)
, pfbuf: ringbuf_v (a, l, m, xs, f, n)
) : (
  arrseg_v (a, l, ilist_sing(x), f, 1)
, arrseg_v (a, l, ilist_sing(x), f, 1) -<lin,prf> ringbuf_v (a, l, m, xs, f, n)
) // end of [ringbuf_v_head]

implement{a}
head (pfhq | rb) = let
  val p = rb.ptr
  prval pfat = rb.atview
  prval (pf1, fpf2) = ringbuf_v_head (pfhq, rb.bufview)
  val x = arrseg_get (RNTHbas (LENGTHnil), pf1 | p->data, p->first, 0)
  prval () = rb.bufview := fpf2 (pf1)
  prval () = rb.atview := pfat
in
  x (* return value *)
end // end of [head]

(* ****** ****** *)

(*
extern
fun{a:t@ype}
push {m,n:nat | n < m}
  {x:elt} {xs:ilist} {xs1:ilist} (
  pf1: LENGTH (xs, n), pf2: ENQUE (x, xs, xs1)
| rb: !ringbuf (a, m, xs) >> ringbuf (a, m, xs1), x: E (a, x)
) : void // end of [push]
*)
extern
praxi
ringbuf_v_push
  {a:t@ype}
  {l:addr} {m:nat}
  {x:elt} {xs:ilist} {xs1:ilist}
  {f,n:nat | n < m} (
  pfenq: ENQUE (x, xs, xs1)
, pfbuf: ringbuf_v (a, l, m, xs, f, n)
) : [f1:nat] (
  MOD (f+n, m, f1)
, arrseg0_v (a, l, f1, 1)
, arrseg_v (a, l, ilist_sing(x), f1, 1) -<lin,prf> ringbuf_v (a, l, m, xs1, f, n+1)
) // end of [ringbuf_v_push]

implement{a}
push (
  pflen, pfenq | rb, x
) = let
  val p = rb.ptr
  prval pfat = rb.atview
  prval pflen_alt = lemma_ringbuf_v_length {a} (rb.bufview)
  prval () = length_isfun (pflen, pflen_alt)
  prval (pfmod, pf1, fpf2) = ringbuf_v_push {a} (pfenq, rb.bufview)
  val f = p->first and n = p->len
  val (pfmod_alt | f1) = op nmod2 (f+n, p->size)
  prval () = divmod_isfun (pfmod, pfmod_alt)
  val () = arrseg0_set (pf1 | p->data, f1, x)
  prval () = rb.bufview := fpf2 (pf1)
  val () = p->len := n + 1
  prval () = rb.atview := pfat
in
  // nothing
end // end of [push]

(* ****** ****** *)

extern
praxi
ringbuf_v_pop
  {a:t@ype}
  {l:addr} {m:nat}
  {xs:ilist} {xs1:ilist} {x:elt}
  {f,n:nat | n > 0} (
  pfenq: DEQUE (xs, xs1, x)
, pfbuf: ringbuf_v (a, l, m, xs, f, n)
) : [f1:nat] (
  MOD (f+1, m, f1)
, arrseg_v (a, l, ilist_sing(x), f, 1)
, arrseg0_v (a, l, f, 1) -<lin,prf> ringbuf_v (a, l, m, xs1, f1, n-1)
) // end of [ringbuf_v_pop]
(*
extern
fun{a:t@ype}
pop {m,n:nat | n > 0}
  {xs:ilist} {xs1:ilist} {x:elt} (
  pf1: LENGTH (xs, n), pf2: DEQUE (xs, xs1, x)
| rb: !ringbuf (a, m, xs) >> ringbuf (a, m, xs1)
) : E (a, x) // end of [pop]
*)
implement{a}
pop (pflen, pfdeq | rb) = let
  val p = rb.ptr
  prval pfat = rb.atview
  prval pflen_alt = lemma_ringbuf_v_length {a} (rb.bufview)
  prval () = length_isfun (pflen, pflen_alt)
  prval (pfmod, pf1, fpf2) = ringbuf_v_pop {a} (pfdeq, rb.bufview)
  val f = p->first and n = p->len
  val x = arrseg_get (RNTHbas (LENGTHnil), pf1 | p->data, f, 0)
  prval () = rb.bufview := fpf2 (arrseg0_v_of_arrseg_v (pf1))
  val () = p->len := n-1
  val (pfmod_alt | f1) = op nmod2 (f+1, p->size)
  prval () = divmod_isfun (pfmod, pfmod_alt)
  val () = p->first := f1
  prval () = rb.atview := pfat
in
  x (* return value *)
end // end of [pop]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)
//
// The following code is solely for testing
// the functions implemented above; it is not
// needed if you do not want to test.
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

local

staload UN = "prelude/SATS/unsafe.sats"
staload _(*anon*) = "prelude/DATS/unsafe.dats"

in

implement{a}
arrseg_get
  {l}{x}{xs}{f,n}{i}
  (pf1, pf2 | p, f, i) = let
  val fi = f+i
  val pi = p + (size1_of_int1)fi*sizeof<a>
in
  $UN.ptrget ($UN.cast2Ptr1(pi))
end // end of [arrseg_get]

implement{a}
arrseg0_set
  {l}{x}{xs}{f}
  (pf | p, f, x) = let
  val pi = p + (size1_of_int1)f*sizeof<a>
  val () = $UN.ptrset ($UN.cast2Ptr1(pi), x)
  prval () = __assert (pf) where {
    extern prfun __assert (
      pf: !arrseg0_v (a, l, f, 1) >> arrseg_v (a, l, ilist_sing(x), f, 1)
    ) : void
  } // end of [prval]
in
  // nothing
end // end of [arrseg0_set]

end // end of [local]

(* ****** ****** *)

implement
main () = () where {
  typedef dbl = double
  val rb = create<dbl> (2)
//
  extern castfn encode {a:t@ype} (x: a): [x:int] E (a,x)
  extern castfn decode {a:t@ype} {x:int} (x: E (a, x)): a
//
  val x = encode {dbl} (1.0)
  val y = encode {dbl} (2.0)
  val z = encode {dbl} (3.0)
//
  prval pflen0 = LENGTHnil ()
  prval pfenq0 = ENQUE () // x :: nil
  val () = push (pflen0, pfenq0 | rb, x)
//
  prval pflen1 = LENGTHcons (LENGTHnil ())
  prval pfenq1 = ENQUE ()
  val () = push (pflen1, pfenq1 | rb, y)
//
  prval pflen2 = LENGTHcons (pflen1)
  prval pfdeq2 = DEQUE_cons (DEQUE_nil ())
  val h = pop (pflen2, pfdeq2 | rb)
  prval () = sassert (h, x) // Yes, [h] and [x] are the same
  val () = println! ("h = ", (decode)h)
//
  prval pflen1 = LENGTHcons (LENGTHnil ())
  prval pfenq1 = ENQUE ()
  val () = push (pflen1, pfenq1 | rb, z)
//
  prval pflen2 = LENGTHcons (pflen1)
  prval pfdeq2 = DEQUE_cons (DEQUE_nil ())
  val h = pop (pflen2, pfdeq2 | rb)
  prval () = sassert (h, y) // Yes, [h] and [y] are the same
  val () = println! ("h = ", (decode)h)
//
  prval pflen1 = LENGTHcons (LENGTHnil ())
  prval pfdeq1 = DEQUE_nil ()
  val h = pop (pflen1, pfdeq1 | rb)
  prval () = sassert (h, z) // Yes, [h] and [z] are the same
  val () = println! ("h = ", (decode)h)
//
  val () = rbfree (rb)
} // end of [main]

(* ****** ****** *)

(* end of [problem3.dats] *)
