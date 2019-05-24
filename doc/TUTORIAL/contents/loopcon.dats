//
//
// code demonstrating some typical uses of loop constructs
//
//

(* ****** ****** *)

// a simple while-loop
fn fact (n: int): int = let
  var x: int = n
  var res: int = 1 // initialized
  val () = while (x > 0) (res := res * x; x := x - 1)
in
  res // res = n!
end // end of [fact]

(* ****** ****** *)

// a simple for-loop 
fn fact (n: int): int = let
  var x: int
  var res: int = 1 // initialized
  val () = for (x := 1 ; x <= n ; x := x+1) res := res * x
in
  res // res = n!
end // end of [fact]

val fact10 = fact 10
val () = printf ("fact(10) = %i\n", @(fact10))

(* ****** ****** *)

// a simple for-loop with omissions involving [break]
fn fact (n: int): int = let
  var x: int = 1 // initialized
  var res: int = 1 // initialized
  val () = for ( ; ; ) // infinite loop
    if x <= n then (res := res * x; x := x+1) else break
  // end of [val]
in
  res // res = n!
end // end of [fact]

val fact10 = fact 10
val () = printf ("fact(10) = %i\n", @(fact10))

(* ****** ****** *)

// a simple for-loop with omissions involving [break] and [continue]
fn fact (n: int): int = let
  var x: int = 1 // initialized
  var res: int = 1 // initialized
  val () = for ( ; ; x := x+1) // no loop test
(*
** note that [continue] means to loop again *after* post increment!
*)
    if x <= n then (res := res * x; continue) else break
  // end of [val]
in
  res // res = n!
end // end of [fact]

val fact10 = fact 10
val () = printf ("fact(10) = %i\n", @(fact10))

(* ****** ****** *)

fn bsearch {n:nat} ( // while-loop version
    A: &(@[double][n]), n: int n, key: double
  ) :<> int = let
  var l: int = 0 and u: int = n-1; var res: int = ~1
  val () = while*
    {i,j:int | 0 <= i; i <= j+1; j < n} .<j+1-i>. (l: int i, u: int j) =>
    (l <= u) let
      val m = l + (u-l) / 2
      val sgn = compare (key, A.[m])
    in
      case+ 0 of
      | _ when sgn < 0 => (u := m-1; continue)
      | _ when sgn > 0 => (l := m+1; continue)
      | _ => (res := m; break)
    end // end of [val]
in
  res // 0 <= res < n if [key] is found; or res = ~1 if not
end // end of [bsearch]

(* ****** ****** *)

(*
// this one implements the standard
fn bsearch {n:nat} ( // binary search algorithm
    A: &(@[double][n]), n: int n, key: double
  ) :<> int = let
  var l: int and u: int; var res: int = ~1
  val () = for*
    {i,j:int | 0 <= i; i <= j+1; j < n} .<j+1-i>. (l: int i, u: int j) =>
    (l := 0, u := n-1; l <= u; (*none*)) let
      val m = l + (u-l) / 2
      val sgn = compare (key, A.[m])
    in
      case+ 0 of
      | _ when sgn < 0 => (u := m-1; continue)
      | _ when sgn > 0 => (l := m+1; continue)
      | _ => (res := m; break)
    end // end of [val]
in
  res
end // end of [bsearch]
*)

(* ****** ****** *)

fn fact {n:nat} (n: int n): int = let
  var x: int
  var res: int = 1
(*
  // the loop invariant indicates that
  // the value of [x] is [n+1] at the point where the loop exits
*)
  val () = for* {i:nat | i <= n+1} .<n+1-i>.
    (x: int i): (x: int (n+1)) => (x := 0; x <= n ; x := x+1) res := res * x
  // end of [val]
in
  res
end // end of [fact]

(* ****** ****** *)

(*
** this program echos the commandline:
*)
implement main (argc, argv) = let
  var i: Nat // unintialized
  val () = for
    (i := 0; i < argc; i := i+1) begin
    if i > 0 then print ' '; print argv.[i]
  end // end of [val]
  val () = print_newline ()
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [loopcon.dats] *)
