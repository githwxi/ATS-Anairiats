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

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

staload "stack_alg.sats"
staload "stack_array.sats"
macdef enc(x) = encelt ,(x)
macdef dec(x) = decelt ,(x)

(* ****** ****** *)

staload _(*anon*) = "stack_array.dats"

(* ****** ****** *)

implement
main () = () where {
//
typedef T0 = float
//
var mystack: Stack0
//
val () = initialize<T0> (mystack, 1024)
//
val (pf1 | ()) = push<T0> (mystack, enc(1.0f))
prval PUSH () = pf1
val (pf2 | ()) = push<T0> (mystack, enc(2.0f))
prval PUSH () = pf2
//
val (_ | e) = top<T0> (IS_EMPTY_cons () | mystack)
val () = println! ("e(2.0) = ", dec(e))
val (pf3 | ()) = pop<T0> (IS_EMPTY_cons () | mystack)
prval POP () = pf3
//
val (_ | e) = top<T0> (IS_EMPTY_cons () | mystack)
val () = println! ("e(1.0) = ", dec(e))
val (pf4 | stack4) = pop<T0> (IS_EMPTY_cons () | mystack)
prval POP () = pf4
//
val () = un_initialize_nil (mystack)
//
val () = println! ("The test is finished successfully")
//
} // end of [main]

(* ****** ****** *)

(* end of [test2.dats] *)
