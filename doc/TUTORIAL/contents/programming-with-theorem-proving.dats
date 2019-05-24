//
//
// A Verified Implementation of the Factorial Function
//
// Author: Hongwei Xi (August, 2007)
//
// Two verified implementations of the factorial function:
// one is recurisve but not tail-recursive while the other
// is tail-recursive
//

(*

The mathematical definition of factorials:

fact (0) = 1
fact (n) = n * fact (n-1) ; if n > 0

The following two implementations are verified:

// non-tail-recursive
fun fact {n:nat} (n: int n): Nat =
  if n > 0 then n nmul fact (n-1) else 1

// tail-recursive
fn fact {n:nat} (n: int n): Nat = let
  fun loop {n:nat} (n: int n, res: Nat): Nat =
    if n > 0 then loop (n-1, n nmul res) else res
in
  loop (n, 1)
end // end of [fact]

*)

(* ****** ****** *)

// [FACT (n, x)] is inhabited if and only if [fact (n) = x]
dataprop FACT (int, int) =
  | FACTbas (0, 1)
  | {n:int | n > 0} {r,r1:int}
    FACTind (n, r) of (FACT (n-1, r1), MUL (n, r1, r))

(*

// already declared in "prelude/basic_dyn.dats"
// [MUL (p, q, pq)] is inhabited if and only of [p * q = pq]
fun imul2 : {p,q:int} (int p, int q) -> [pq:int] (MUL (p, q, pq) | int pq)

*)

// [fact1] implements the factorial function in a non-tail-recursive manner
fun fact1 {n:nat} .< n >.
  (n: int n): [r:int] (FACT (n, r) | int r) =
  if n > 0 then
    let
       val (pf_fac_n1_r1 | r1) = fact1 (n-1)
       val (pf_mul_n_r1_r | r) = n imul2 r1
    in
       (FACTind (pf_fac_n1_r1, pf_mul_n_r1_r) | r)
    end
  else (FACTbas () | 1)

(* ****** ****** *)

// Some lemmas on multiplication are stated (without proofs)
extern prval MULlem00 : {x,y:int} () -<prf> [xy:int] MUL (x, y, xy)

// 1 * x = x
extern prval MULlem10 : {x,y:int} MUL (1, x, y) -<prf> [x==y] void
// x * 1 = x
extern prval MULlem11 : {x,y:int} MUL (x, 1, y) -<prf> [x==y] void

// multiplication is associative: (xy)z = x(yz)
extern prval MULlem20 : {x,y,z,xy,yz,xyz:int}
  (MUL (x, y, xy), MUL (y, z, yz), MUL (xy, z, xyz)) -<prf> MUL (x, yz, xyz)

// [fact2] implements the factorial function in a tail-recursive style
fn fact2 {n:nat} (n: int n): [r0: int] (FACT (n, r0) | int r0) =
  let
    // [loop] is tail-recusive
    fun loop {n:nat; x:int} .< n >. (n: int n, x: int x)
      : [r,r0:int] (FACT (n, r), MUL (x, r, r0) | int r0) =
      if n > 0 then let
        val (pf_mul_x_n_xn | xn) = x imul2 n
        val (pf_fac_n1_r1, pf_mul_xn_r1_r0 | res) = loop (n-1, xn)
        prval pf_mul_n_r1_nr1 = MULlem00 ()
        prval pf_mul_x_nr1_r0 = MULlem20 (pf_mul_x_n_xn, pf_mul_n_r1_nr1, pf_mul_xn_r1_r0)
        prval pf_fac_n_nr1 = FACTind (pf_fac_n1_r1, pf_mul_n_r1_nr1)
      in
        (pf_fac_n_nr1, pf_mul_x_nr1_r0 | res)
      end else let
        prval pf_mul_x_1_y = MULlem00 () // x * 1 = y
        prval () = MULlem11 (pf_mul_x_1_y) // x = y
      in
        (FACTbas (), pf_mul_x_1_y | x)
      end

    val (pf_fac, pf_mul | res) = loop (n, 1)
    prval () = MULlem10 (pf_mul)
  in
    (pf_fac | res)
  end

(* ****** ****** *)

// for a simple test: are there any dounts :)

implement main (argc, argv) = case+ argc of
  | 2 => begin
      let
        val n = int1_of argv.[1]
        val () = assert_prerrf_bool1 (
          n >= 0, "Exit: negative argument: %i\n", @(n)
        )
        val (pf1 | res1) = fact1 n
        val (pf2 | res2) = fact2 n
      in
        printf ("The value of fact1(%i) is %i.\n", @(n, res1));
        printf ("The value of fact2(%i) is %i.\n", @(n, res2))
      end
    end // end of [2]
  | _ => let
      val cmd = argv.[0]
    in
      printf ("Usage: %s [integer]\n", @(cmd))
    end // end of [_]
// end of [main]

(* ****** ****** *)

(* end of [programming-with-theorem-proving.dats] *)
