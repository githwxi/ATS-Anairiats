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

%{#
#ifndef STACK_ARRAY_SATS
#define STACK_ARRAY_SATS
typedef struct {
  ats_ptr_type atslab_ptr0 ;
  ats_ptr_type atslab_ptr1 ;
  ats_size_type atslab_cap ;
} stack_struct ; // end of [stack_struct]
#endif // end of [STACK_ARRAY_SATS]
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)

staload "stack_alg.sats"

(* ****** ****** *)

abst@ype E (a:t@ype, x:int) = a
castfn encelt {a:t@ype} (x: a):<> [i:int] E (a, i)
castfn decelt {a:t@ype} {i:int} (x: E (a, i)):<> a

(* ****** ****** *)
//
// HX-2010-12-07:
// [n] is the number of available slots
//
absviewt@ype Stack0 = $extype"stack_struct"
absviewt@ype Stack (a:t@ype, xs:ilist, n:int) = Stack0

(* ****** ****** *)

fun{a:t@ype}
initialize {n:nat}
  (S: &Stack0? >> Stack (a, nil, n), n: size_t n): void
// end of [make_nil]

fun un_initialize_nil
  {a:t@ype} {n:nat} (S: &Stack (a, nil, n) >> Stack0?): void
// end of [un_initialize_nil]

(* ****** ****** *)

fun is_empty {a:t@ype} {xs:ilist} {n:nat}
  (S: &Stack (a, xs, n)): [b:bool] (IS_EMPTY (xs, b) | bool (b))
// end of [is_empty]

fun{a:t@ype}
size {xs:ilist} {n:nat}
  (S: &Stack (a, xs, n)): [m:nat] (LENGTH (xs, m) | size_t m)
// end of [size]

fun capacity {a:t@ype} {xs:ilist} {n:nat}
  (S: &Stack (a, xs, n)): [m:nat] (LENGTH (xs, m) | size_t (m+n))
// end of [capacity]

(* ****** ****** *)

fun{a:t@ype}
top {xs:ilist} {n:nat} (
  pf: IS_EMPTY (xs, false) | S: &Stack (a, xs, n)
) : [x:int] (TOP (xs, x) | E (a, x)) // end of [top]

fun{a:t@ype}
pop {xs1:ilist} {n:nat} (
  pf: IS_EMPTY (xs1, false)
| S: &Stack (a, xs1, n) >> Stack (a, xs2, n+1)
) : #[xs2:ilist] (POP (xs1, xs2) | void) // end of [pop]

fun{a:t@ype}
push {x:int} {xs1:ilist} {n:pos} (
  S: &Stack (a, xs1, n) >> Stack (a, xs2, n-1), e: E (a, x)
): #[xs2:ilist] (PUSH (x, xs1, xs2) | void) // end of [push]

(* ****** ****** *)

(* end of [stack_array.sats] *)
