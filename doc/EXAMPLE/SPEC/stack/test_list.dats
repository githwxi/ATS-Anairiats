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

staload "stack_alg.sats"
staload "stack_list.sats"
macdef enc(x) = encelt ,(x)
macdef dec(x) = decelt ,(x)

(* ****** ****** *)

staload _(*anon*) = "stack_list.dats"

(* ****** ****** *)
//
typedef T0 = float
//
val (pf0 | stack0) = make_nil<T0> ()
prval EMPTY () = pf0
//
val (pf1 | stack1) = push<T0> (enc(1.0f), stack0)
prval PUSH () = pf1
val (pf2 | stack2) = push<T0> (enc(2.0f), stack1)
prval PUSH () = pf2
//
val (_ | e) = top<T0> (IS_EMPTY_cons () | stack2)
val () = println! ("e(2.0) = ", dec(e))
val (pf3 | stack3) = pop<T0> (IS_EMPTY_cons () | stack2)
prval POP () = pf3
//
val (_ | e) = top<T0> (IS_EMPTY_cons () | stack3)
val () = println! ("e(1.0) = ", dec(e))
val (pf4 | stack4) = pop<T0> (IS_EMPTY_cons () | stack3)
prval POP () = pf4
//
(* ****** ****** *)
//
typedef T1 = Stack (T0)
//
val (pf0 | Stack0) = make_nil<T1> ()
prval EMPTY () = pf0
//
val (pf1 | Stack1) = push<T1> (enc(stack1), Stack0)
prval PUSH () = pf1
//
(* ****** ****** *)

implement
main () = () where {
  val () = println! ("The test is finished successfully")
} // end of [main]

(* ****** ****** *)

(* end of [test.dats] *)
