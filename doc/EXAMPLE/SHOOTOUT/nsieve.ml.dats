//
// nsieve.ml -- naive Sieve of Eratosthenes
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// This (not so elegant) code is largely *translated* from
// the following ocaml code.
//
// Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

abst@ype barray (int) = $extype "barray"

extern fun barray_make {n:nat}
  (n: int n, b: bool): barray n = "barray_make"
extern fun barray_free {n:nat}
  (A: barray n): void = "barray_free"

extern fun barray_get {n:nat}
  (A: barray n, i: natLt n): bool = "barray_get"

extern fun barray_set {n:nat}
  (A: barray n, i: natLt n, b: bool): void = "barray_set"

overload [] with barray_get
overload [] with barray_set

//

#define max_array_length  16 * (4194303 / 16)

//

fn array_make_true {n:nat} (n: int n)
  : (barray(min(n, max_array_length)), barray(max(0,n-max_array_length))) =
  (barray_make (min(n, max_array_length), true),
   barray_make (max(0, n-max_array_length), true))

fn clear {n:nat}
  (a1: barray(min(n, max_array_length)),
   a2: barray(max(0, n-max_array_length)),
   i: natLt n): void =
  if i < max_array_length then (if a1[i] then a1[i] := false)
  else (if a2[i-max_array_length] then a2[i-max_array_length] := false)

fn get {n:nat}
  (a1: barray(min(n, max_array_length)),
   a2: barray(max(0, n-max_array_length)),
   i: natLt n): bool =
  if i < max_array_length then a1[i] else a2[i-max_array_length]

//

fn nsieve {m:nat} (m: int m): void =
  let
    val (a1, a2) = array_make_true m
    var i: Nat = 2 and j: Nat = 0
    var count: Nat = 0
  in
    while (i < m) begin
      if get {m} (a1, a2, i) then begin
        count := count + 1; j := i + i ;
        while (j < m) (clear {m} (a1, a2, j); j := j + i)
      end ;
      i := i + 1 ;
    end ;
    printf ("Primes up to %8i %8i\n", @(m, count))
  end

implement main (argc, argv) = begin
  nsieve (5120000) ;
  nsieve (2560000) ;
  nsieve (1280000) ;
end

%{^

typedef ats_ptr_type barray ;

ats_ptr_type
barray_make (ats_int_type n, ats_bool_type f) {
  int i;
  ats_bool_type *p0, *p ;

  p0 = malloc(n * sizeof(ats_bool_type)) ;
  p = p0 ;

  for (i = 0; i < n; ++i) { *p = f; ++p; }
  return p0 ;
}

ats_void_type
barray_free (ats_ptr_type A) { free (A) ; return ; }

ats_bool_type
barray_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_bool_type *)A)[i] ;
}

ats_void_type
barray_set (ats_ptr_type A, ats_int_type i, ats_bool_type f) {
  ((ats_bool_type *)A)[i] = f ; return ;
}

%}

////

(* nsieve.ml -- naive Sieve of Eratosthenes
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Christophe TROESTLER
 * Modified by Vladimir Silyaev
 *)

let max_array_length = 16*(4194303/16)

let array_make_true n =
  (Array.create (min n max_array_length) true),(Array.create (max 0 (n - max_array_length)) true)

let clear (a1,a2) n =
  if n < max_array_length then (if a1.(n) then a1.(n) <- false)
  else if a2.(n-max_array_length) then a2.(n-max_array_length) <- false

let get (a1,a2) n :bool =
  if n < max_array_length then a1.(n) else a2.(n-max_array_length)


let nsieve m =
  let a = array_make_true m in
  let count = ref 0 in
  for i = 2 to m - 1 do
    if get a i then (
      incr count;
      let j = ref(i lsl 1) in while !j < m do clear a !j ; j := !j+i done;
    )
  done;
  Printf.printf "Primes up to %8u %8u\n" m !count


let () =
  (* Use [Array.get] so it raises an exception even if compiled with -unsafe *)
  let n = try int_of_string (Array.get Sys.argv 1) with _ -> 2 in
  for i = 0 to 2 do nsieve(10000 lsl (n-i)) done
