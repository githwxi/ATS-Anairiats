//
// code used for illustration in basics.html
//

staload "libc/SATS/math.sats" // for [sqrt]

(* ****** ****** *)

val radius = 1.0
val pi = 3.1415926
val area = pi * radius * radius

//

val square = lam (x: double): double => x * x
val area = pi * square (radius)

//

val zero_and_one = '(1, 2)

// function values

val add_double_double_1 = lam (x: double, y: double): double => x + y
val add_double_double_2 = lam (x: double) (y: double): double => x + y

// val fib = fix fib (x: Nat): Nat => if x >= 2 then fib (x-1) + fib (x-2) else x

// function declarations

// val fib = fix fib (x: Nat): Nat => if x >= 2 then fib (x-1) + fib (x-2) else x
val rec fib: Nat -> Nat = lam x => if x >= 2 then fib (x-1) + fib (x-2) else x

//

fun is_even (x: int): bool = if x > 0 then is_odd  (x-1) else true
and is_odd  (x: int): bool = if x > 0 then is_even (x-1) else false

// local bindings

// computing roots for [Axx + Bx + C]
fn foo (A: double, B: double, C: double): @(double, double) = let
  val Delta = B * B - 4.0 * A * C
  val () = if Delta < 0.0 then (prerr "no real roots!\n"; exit {void} 1)
  val Delta_sqrt = sqrt (Delta)
  val root1 = (~B + Delta_sqrt) / (2.0 * A)
  val root2 = (~B - Delta_sqrt) / (2.0 * A)
in
  @(root1, root2)
end // end of [foo]

val fact10 = fact 10 where {
  fun fact (x: int): int = if x > 0 then x * fact (x-1) else 1
}

//

// postfix 80 !!
// fun !! (x: Nat): Nat = if x >= 2 then x nmul (x-2) !! else 1

//

implement main () = let
  val @(r1, r2) = foo (1.0, 4.0, 4.0)
in
  printf ("r1 = %f and r2 = %f\n", @(r1, r2))
end // end of [main]

(* ****** ****** *)

(* end of [basics.dats] *)