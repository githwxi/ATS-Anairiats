//
// insertion sort
//
// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
//

(* ****** ****** *)

#if undefined (ARG_INSORT_DATS) #then

absviewt@ype T

extern fun lte_T_T (x: !T, y: !T):<> bool
extern fun compare_T_T (x: !T, y: !T):<> Sgn

overload compare with compare_T_T
overload <= with lte_T_T

#endif // end of [undefined (ARG_INSORT_DATS)]

stadef sz = sizeof (T)

fun insert_one {n,i:nat | i < n} {A:addr} {ofs:int} (
    pf_mul: MUL (i, sz, ofs)
  , pf1: array_v (T, i, A)
  , pf21: T? @ (A+ofs)
  , pf22: array_v (T, n-i-1, A+ofs+sz)
  | x: T, p: ptr (A+ofs), i: int i
  ) : (array_v (T, n, A) | void) = begin
  case+ i of
  | _ when i > 0 => let
      prval pf1_mul = mul_add_const {~1} (pf_mul)
      prval (pf11, pf12) = array_v_unextend {T} (pf_mul, pf1)
      val p1 = p - sizeof<T>
      val x1 = ptr_get_vt<T> (pf12 | p1)
    in
      if x1 <= x then let
        val () = ptr_set_vt<T> (pf12 | p1, x1)
        prval pf1 = array_v_extend {T} (pf1_mul, pf11, pf12)
        val () = !p := x
        prval pf2 = array_v_cons {T} (pf21, pf22)
        prval pf = array_v_unsplit {T} (pf_mul, pf1, pf2)
      in
        (pf | ())
      end else let
        val () = !p := x1
        prval pf2 = array_v_cons {T} (pf21, pf22)
      in
        insert_one (pf1_mul, pf11, pf12, pf2 | x, p1, i-1)
      end
    end
  | _ => let
      val () = assert (i = 0)
      prval MULbas () = pf_mul
      prval () = array_v_unnil {T} (pf1)
      val () = !p := x
      prval pf = array_v_cons {T} (pf21, pf22)
    in
      (pf | ())
    end
end // end of [insert]

(* ****** ****** *)
  
fun insert_all {n,i:nat | i <= n} {A:addr} {ofs:int} (
    pf_mul: MUL (i, sz, ofs)
  , pf: !array_v (T, n, A)
  | p: ptr (A+ofs), i: int i, n: int n
  ) : void = begin
  if i < n then let
    prval (pf1, pf2) = array_v_split {T} (pf_mul, pf)
    prval (pf21, pf22) = array_v_uncons {T} (pf2)
    val x = ptr_get_vt<T> (pf21 | p)
    val (pf_new | ()) = insert_one (pf_mul, pf1, pf21, pf22 | x, p, i)
    prval () = pf := pf_new
  in
    insert_all (mul_add_const {1} (pf_mul), pf | p+sizeof<T>, i+1, n)
  end else begin
    // empty
  end
end // end of [insert_all]

(* ****** ****** *)

fun insort {n:nat} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, n: int n): void = begin
  if n >= 2 then let
    prval pf_mul = MULind (MULbas ())
  in
    insert_all (pf_mul, pf | A+sizeof<T>, 1, n)
  end else begin
    // empty
  end
end // end of [insort]
  
(* ****** ****** *)

(* end of [insort.dats] *)
