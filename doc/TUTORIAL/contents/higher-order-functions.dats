//
//
// code for illustration in higher-order-functions.html
//
//

(* ****** ****** *)

fn find_root (f: int -<cloref1> int): int = let
  fun aux (f: int -<cloref1> int, n: int): int =
    if f (n) = 0 then n else begin
      if n <= 0 then aux (f, ~n + 1) else aux (f, ~n)
    end
in
  aux (f, 0)
end // end of [fint_root]

// a simple test

val () = let
  val root = find_root (lam n => n * n + n - 10100)
in
  print "The polynomial x*x+x-10100 has a root: ";
  print root;
  print_newline ()
end // end of [let]

(* ****** ****** *)
//
// Newton-Raphson's method for finding roots
//
typedef
fdouble = double -<cloref1> double
//
macdef epsilon = 1E-6 (* precision *)
//
// [f1] is the derivative of [f]
//
fn newton_raphson (
    f: fdouble, f1: fdouble, x0: double
  ) : double = let
  fun loop (
    f: fdouble, f1: fdouble, x0: double
  ) : double = let
    val y0 = f x0
  in
    if abs (y0 / x0) < epsilon then x0 else begin
      let val y1 = f1 x0 in loop (f, f1, x0 - y0 / y1) end
    end
  end // end of [loop]
in
  loop (f, f1, x0)
end // end of [newton_raphson]

// square root function
fn sqrt (c: double): double =
  newton_raphson (lam x => x * x - c, lam x => 2.0 * x, 1.0)
// cubic root function
fn cbrt (c: double): double =
  newton_raphson (lam x => x * x * x - c, lam x => 3.0 * x * x, 1.0)

(* ****** ****** *)

// some simple tests

implement main (argc, argv) = let

val sqrt2 = sqrt 2.0
val cbrt3 = cbrt 3.0

in

printf ("sqrt2 = %.6f\n", @(sqrt2));
printf ("(sqrt2)^2 = %.6f\n", @(sqrt2 * sqrt2));
printf ("cbrt3 = %.6f\n", @(cbrt3));
printf ("(cbrt3)^3 = %.6f\n", @(cbrt3 * cbrt3 * cbrt3));

end // end of [main]

(* ****** ****** *)

(* end of [higher-order-functions.dats] *)
