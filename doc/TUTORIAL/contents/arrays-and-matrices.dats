//
//
// code for illustration in arrays-and-matrices.html
//
//

%{^

#include "prelude/CATS/array.cats"
#include "prelude/CATS/matrix.cats"

%}

(* ****** ****** *)

staload "prelude/DATS/array.dats"
staload "prelude/DATS/matrix.dats"

(* ****** ****** *)

// persistent arrays

// digits: array (int, 10)
val digits = array $arrsz {int} (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)

typedef digit = [i:nat | i < 10] int (i)

// digits: array (digit, 10)
val digits = array $arrsz {digit} (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)

prval pf = unit_v ()
val digits =
  array_make_clo_tsz {digit} {unit_v} (pf | 10, !p_f, sizeof<digit>) where {
  var !p_f = @lam
    (pf: !unit_v | i: sizeLt 10, x: &digit? >> digit): void =<clo> x := int1_of_size1 (i)
} // end of [val]
prval unit_v () = pf

fn array_square {n:nat}
  (A: array (double, n), sz: int n): void = loop (0) where {
  fun loop {i:nat | i <= n} .<n-i>. (i: int i):<cloref1> void =
    if i < sz then
      let val x = A[i] in A[i] := x * x; loop (i+1) end
    else ()
} // end of [array_square]

// printing an array

fun{a:t@ype} prarr {n:nat}
  (pr: a -> void, A: array (a, n), sz: int n): void = let
  fun loop {i:nat | i <= n} (n: int n, i: int i):<cloptr1> void =
    if i < n then (if i > 0 then print ", "; pr A[i]; loop (n, i+1))
in
  loop (sz, 0); print_newline ()
end // end of [prarr]

(* ****** ****** *)

// persistent matrices

val mat_10_10 = matrix (10, 10) $arrsz (
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9
, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19
, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29
, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39
, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49
, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59
, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69
, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79
, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89
, 90, 91, 92, 93, 94, 99, 96, 97, 98, 99
) : matrix (Int, 10, 10) // end of [val]

// template function for transposing a square matrix

fn{a:t@ype} matrix_transpose {n:nat}
  (A: matrix (a, n, n), n: int n): void = let
  fn get {i,j:nat | i < n; j < n}
   (A: matrix (a, n, n), i: int i, j: int j):<cloref1> a =
   matrix_get_elt_at__intsz (A, i, n, j)

  fn set {i,j:nat | i < n; j < n}
   (A: matrix (a, n, n), i: int i, j: int j, x: a):<cloref1> void =
   matrix_set_elt_at__intsz (A, i, n, j, x)

  overload [] with get; overload [] with set

  // [fn*] indicates a request for tail-call optimization
  fn* loop1 {i:nat | i <= n} .< n-i+1, 0 >.
    (i: int i):<cloptr1> void = begin
    if i < n then loop2 (i, 0) else ()
  end

  and loop2 {i,j:nat | i < n; j <= i} .< n-i, i-j+1 >.
    (i: int i, j: int j):<cloptr1> void = begin
    if j < i then
      let val x = A[i,j] in A[i,j] := A[j,i]; A[j,i] := x; loop2 (i, j+1) end
    else begin
      loop1 (i+1)
    end
  end // end of [loop2]
in
  loop1 0
end // end of [matrix_transpose]

// printing a matrix

fn{a:t@ype} prmat {m,n:nat}
  (pr: a -> void, M: matrix (a, m, n), m: int m, n: int n)
  : void = let
  fn* loop1 {i:nat | i <= m} (i: int i):<cloptr1> void =
    if i < m then loop2 (i, 0) else print_newline ()
  and loop2 {i,j:nat | i < m; j <= n}
    (i: int i, j: int j):<cloptr1> void = begin
    if j < n then begin
      if (j > 0) then print ", "; pr M[i, n, j]; loop2 (i, j+1)
    end else begin
      print_newline (); loop1 (i+1)
    end
  end // end of [loop2]
in
  loop1 0
end // end of [prmat]

(* ****** ****** *)

implement main (argc, argv) = let

fn pr1 (x: Int): void = print x
fn pr2 (x: Int): void = printf ("%2i", @(x))

in

// testing prarr
prarr (pr1, digits, 10); print_newline ();

// testing prmat
print "before matrix transposition:\n";
prmat (pr2, mat_10_10, 10, 10);

// testing matrix_transpose
matrix_transpose (mat_10_10, 10);

// testing prmat_
print "after matrix transposition:\n";
prmat (pr2, mat_10_10, 10, 10);

end // end of [main]

(* ****** ****** *)

(* end of [arrays-and-matrices.dats] *)
