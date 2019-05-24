(*
**
** An Example of Stack Algebra
** See Section 8.5.2 in Dines Bjorner's SE book
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)

staload "stack_alg.sats"
staload "stack_array.sats"

(* ****** ****** *)

dataview stack_v (
  a:t@ype, ilist(*xs*), addr(*l0*), addr(*l*)
) =
  | {l:addr} stack_v_nil (a, nil, l, l)
  | {x:int} {xs:ilist} {l0,l:addr}
    stack_v_cons (a, cons (x, xs), l0, l+sizeof(a)) of (E(a,x)@l, stack_v (a, xs, l0, l))
// end of [stack_v]

(* ****** ****** *)

prfun stack_v_lemma1 {a:t@ype}
  {xs:ilist} {l0,l:addr} {m:int} .<xs>. (
  pfstk: !stack_v (a, xs, l0, l), pflen: LENGTH (xs, m)
) : MUL (m, sizeof(a), l-l0) =
  case+ pflen of
  | LENGTHcons (pflen1) => let
      prval stack_v_cons (pfat, pfstk1) = pfstk
      prval pfmul1 = stack_v_lemma1 (pfstk1, pflen1)
      prval () = pfstk := stack_v_cons (pfat, pfstk1)
    in
      mul_add_const {1} (pfmul1)
    end // end of [LENGTHcons]
  | LENGTHnil () => let
      prval stack_v_nil () = pfstk
      prval () = pfstk := stack_v_nil ()
    in
      mul_make {0,sizeof(a)} ()
    end // end of [LENGTHnil]
// end of [stack_v_lemma1]

(* ****** ****** *)
//
// HX-2010-12-07:
// [n] is the number of available slots
//
viewtypedef
stack_struct (
  a:t@ype
, xs:ilist, m: int, n:int, l0:addr, l1:addr
) = @{
  pfgc=free_gc_v (a, m+n, l0)
, ptr0= ptr (l0)
, pfstk= stack_v (a, xs, l0, l1)
, pfarr= array_v (a?, n, l1)
, ptr1= ptr (l1)
, pflen= LENGTH (xs, m)
, cap= size_t (m+n)
} // end of [stack_struct]

(* ****** ****** *)

assume Stack
  (a:t@ype, xs:ilist, n:int) = [m:int;l0,l1:addr] stack_struct (a, xs, m, n, l0, l1)
assume Stack0 = stack_struct (void, nil, 0, 0, null, null)

(* ****** ****** *)

implement{a}
initialize {n} (S, n) = let
  val [l:addr] (pfgc, pfarr | arrp) = array_ptr_alloc<a> (n)
  prval () = S.pfgc := pfgc
  prval () = S.pfstk := stack_v_nil ()
  prval () = S.pfarr := pfarr
  val () = S.ptr0 := arrp
  val () = S.ptr1 := arrp
  prval () = S.pflen := LENGTHnil ()
  val () = S.cap := n
in
  ()
end // end of [make_nil]

implement
un_initialize_nil {a} (S) = let
  prval LENGTHnil () = S.pflen
  prval stack_v_nil () = S.pfstk in
  array_ptr_free (S.pfgc, S.pfarr | S.ptr0)
end // end of [un_initialize_nil]

(* ****** ****** *)

implement
is_empty {a} {xs} {n} (S) = let
(*
  prval () = __assert () where {
    extern prfun __assert (): [sizeof(a) > 0] void
  } // end of [prval]
*)
  val arrp0 = S.ptr0 and arrp1 = S.ptr1
  prval [m:int] (pflen) = length_istot {xs} ()
  prval pfmul = stack_v_lemma1 (S.pfstk, pflen)
  prval () = mul_nat_nat_nat (pfmul)
//
extern prfun lemma0 (pf: MUL (m, sizeof(a), 0)): [m==0] void
extern prfun lemma1 {d:int | d <> 0} (pf: MUL (m, sizeof(a), d)): [m <> 0] void
//
in
  if arrp0 = arrp1 then let
    prval () = lemma0 (pfmul)
    prval LENGTHnil () = pflen in (IS_EMPTY_nil () | true)
  end else let
    prval () = lemma1 (pfmul)
    prval LENGTHcons _ = pflen in (IS_EMPTY_cons () | false)
  end // end of [if]
end // end of [is_empty]

(* ****** ****** *)

implement{a}
size (S) = let
//
  prval () = __assert () where {
    extern prfun __assert (): [sizeof(a) > 0] void
  } // end of [prval]
//
  prval pfmul = stack_v_lemma1 (S.pfstk, S.pflen)
  extern fun divexact
    {p: int} {q:pos} {r:int}
    (pf: MUL (p, q, r) | r: ptrdiff_t (r), q: size_t q):<> size_t p
    = "div_size_size"
  // end of [divexact]
  val d = S.ptr1 - S.ptr0
  stavar m: int
  val m = divexact {m} (pfmul | d, sizeof<a>)
  prval () = length_isnat (S.pflen)
in
  (S.pflen | m)
end // end of [size]

(* ****** ****** *)

implement
capacity {a} (S) = let
  prval () = length_isnat (S.pflen) in (S.pflen | S.cap)
end // end of [capacipty]

(* ****** ****** *)

implement{a}
top (pf | S) = let
  prval IS_EMPTY_cons () = pf
  prval stack_v_cons (pfat, pfstk1) = S.pfstk
  val x = ptr_get_t (pfat | S.ptr1-sizeof<a>)
  prval () = S.pfstk := stack_v_cons (pfat, pfstk1)
in
  (TOP | x)
end // end of [top]

(* ****** ****** *)

implement{a}
pop (pf | S) = let
  prval IS_EMPTY_cons () = pf
  prval stack_v_cons (pfat, pfstk1) = S.pfstk
  prval () = S.pfstk := pfstk1
  prval () = S.pfarr := array_v_cons (pfat, S.pfarr)
  prval LENGTHcons (pflen1) = S.pflen
  prval () = S.pflen := pflen1
  val () = S.ptr1 := S.ptr1 - sizeof<a>
in
  (POP | ())
end // end of [pop]

(* ****** ****** *)

implement{a}
push {x} {xs} (S, e) = let
  prval (pfat, pfarr1) = array_v_uncons {a?} (S.pfarr)
  prval () = S.pfarr := pfarr1
  val p = S.ptr1; val () = !p := e
  prval () = S.pfstk := stack_v_cons (pfat, S.pfstk)
  prval () = length_isnat (S.pflen)
  prval () = S.pflen := LENGTHcons (S.pflen)
  val () = S.ptr1 := p + sizeof<a>
in
  (PUSH | ())
end // end of [push]

(* ****** ****** *)

(* end of [stack_array.dats] *)
