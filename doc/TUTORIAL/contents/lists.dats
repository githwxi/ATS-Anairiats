//
//
// code for illustration in lists.html
//
//

(* ****** ****** *)

(*

datatype list (a:t@ype+, int) = // t@ype+: covariant
  | list_nil (a, 0)
  | {n:int | n >= 0} list_cons (a, n+1) of (a, list (a, n))

*)

#define nil list_nil
#define cons list_cons
#define :: list_cons

// This implementation is not tail-recursive
fun{a:t@ype} length {n:nat} (xs: list (a, n)): int n =
  case+ xs of _ :: xs => 1 + length xs | nil () => 0

// This implementation is tail-recursive
fn{a:t@ype}
length {n:nat} (xs: list (a, n)): int n = let
  fun loop {i,j:nat} .<i>.
    (xs: list (a, i), j: int j): int (i+j) =
    case+ xs of _ :: xs => loop (xs, j+1) | nil () => j
in
  loop (xs, 0)
end // end of [length]

fun{a:t@ype}
append {m,n:nat} (
  xs: list (a, m), ys: list (a, n)
) : list (a, m+n) =
  case+ xs of
  | cons (x, xs) => cons (x, append (xs, ys)) | nil () => ys
// end of [append]

fun{a:t@ype} merge {n1,n2:nat}
  (lte: (a, a) -> bool, xs10: list (a, n1), xs20: list (a, n2))
  : list (a, n1+n2) = begin
  case+ xs10 of
  | x1 :: xs1 => begin case+ xs20 of
    | x2 :: xs2 =>
        if lte (x1, x2) then x1 :: merge (lte, xs1, xs20)
        else x2 :: merge (lte, xs10, xs2)
    | nil () => xs10 
    end // end of [case]
  | nil () => xs20
end // end of [merge]

(* ****** ****** *)

(* end of [lists.dats] *)
