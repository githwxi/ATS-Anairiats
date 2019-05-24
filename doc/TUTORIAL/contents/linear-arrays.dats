//
//
// code for illustration in linear-arrays.html
//
//

(* ****** ****** *)

fn{a:t@ype}
  array_ptr_initialize_list {n:nat}
  (A: &(@[a?][n]) >> @[a][n], xs: list (a, n))
  :<> void = loop (view@ A | &A, xs) where {
  fun loop {n: nat} {l:addr} .<n>. ( // [loop] is tail-recursive!
      pf_arr: !array_v (a?, n, l) >> array_v (a, n, l) | p_arr: ptr l, xs: list (a, n)
    ) :<> void = case+ xs of
    | list_cons (x, xs) => let
        prval (pf1_at, pf2_arr) = array_v_uncons {a?} (pf_arr)
        val () = !p_arr := x
        val () = loop (pf2_arr | p_arr + sizeof<a>, xs)
      in
        pf_arr := array_v_cons {a} (pf1_at, pf2_arr)
      end // end of [list_cons]
    | list_nil () => let
        prval () = array_v_unnil {a?} (pf_arr) in pf_arr := array_v_nil {a} ()
      end // end of [list_nil]
  // end of [loop]
} // end of [array_ptr_initialize_list]  

(* ****** ****** *)

fn{a:t@ype} array_ptr_swap
  {n:nat} {i,j:nat | i < n; j < n}
  (A: &(@[a][n]), i: int i, j: int j):<> void = begin
  let val tmp = A.[i] in A.[i] := A.[j]; A.[j] := tmp end
end // endof [array_ptr_swap]

(* ****** ****** *)

fn{a:t@ype} array_ptr_swap
  {n:nat} {i,j:nat | i < n; j < n}
  (A: &(@[a][n]), i: int i, j: int j):<> void = begin
  let val tmp = A[i] in A[i] := A[j]; A[j] := tmp end
end // endof [array_ptr_swap]

(* ****** ****** *)

extern fun{a:t@ype} search {n:nat} {l:addr} {cmp:eff}
  (cmp: (a, a) -<cmp> Sgn, A: & @[a][n], key: a, n: int n)
  :<cmp> intBtw (~1, n)

// this implementation of binary search can probably be classified
// as 100% C-style
implement{a} search {n} {l} (cmp, A, key, n) = let
   var l = 0 and u = n-1 and res = ~1
   var m: Int?; val () =  while*
     {l,u:int | 0<=l; l <= u+1; u+1 <= n} .<u-l+1>.
     (l: int l, u: int u, res: int ~1)
     : (res: intBtw (~1, n)) => (l <= u) begin
       m := l + (u-l) / 2; case+ cmp (A.[m], key) of
       | ~1 => (l := m + 1; continue) | 1 => (u := m - 1; continue)
       | 0 => (res := m; break)
   end // end of [while*]
in
  res
end // end of [search]

implement main (argc, argv) = let

val (pf_gc, pf_arr | arr, sz) = $arrsz{double}(
  0.0, 2.0, 4.0, 6.0, 8.0, 10.0, 12.0, 14.0, 16.0, 18.0
)

val sz = int1_of_size1 (sz)

fn cmp (x: double, y: double):<> Sgn = compare (x, y)

val ans10 = search<double> (cmp, !arr, 10.0, sz)
val ans11 = search<double> (cmp, !arr, 11.0, sz)
val ans17 = search<double> (cmp, !arr, 17.0, sz)
val ans18 = search<double> (cmp, !arr, 18.0, sz)
val () = array_ptr_free {double} (pf_gc, pf_arr | arr)

in

print "ans10 (5) = "; print ans10; print_newline ();
print "ans11 (-1) = "; print ans11; print_newline ();
print "ans17 (-1) = "; print ans17; print_newline ();
print "ans18 (9) = "; print ans18; print_newline ();

end // end of [main]

(* ****** ****** *)

(* end of [linear-arrays.dats] *)
