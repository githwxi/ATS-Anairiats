(*
** The Computer Language Benchmarks Game
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi
** contributed by Zhiqiang Ren
**
** compilation command:
**   atscc -O3 -msse2 spectral-norm2.dats -o spectral-norm2 -lm
**
*)

//
// relying on XMM to speed up the computation
//

(* ****** ****** *)

// staload "libc/SATS/SIMD_v2df.sats"
// this is only needed for backward compatibility
%{^
#include "libc/CATS/SIMD_v2df.cats"
%}
abst@ype v2df = $extype "ats_v2df_type"
extern val v2df_0_0: v2df = "atslib_v2df_0_0"
extern val v2df_1_1: v2df = "atslib_v2df_1_1"
extern fun v2df_make_int_int
  (i0: int, i1: int): v2df = "atslib_v2df_make_int_int"
extern fun v2df_get_fst (dd: v2df): double = "atslib_v2df_get_fst"
extern fun v2df_get_snd (dd: v2df): double = "atslib_v2df_get_snd"
extern fun add_v2df_v2df (_: v2df, _: v2df): v2df = "atslib_add_v2df_v2df"
overload + with add_v2df_v2df
extern fun mul_v2df_v2df (_: v2df, _: v2df): v2df = "atslib_mul_v2df_v2df"
overload * with mul_v2df_v2df
extern fun div_v2df_v2df (_: v2df, _: v2df): v2df = "atslib_div_v2df_v2df"
overload / with div_v2df_v2df

(* ****** ****** *)

%{^
#include <malloc.h>
static inline ats_ptr_type
darr_make (ats_int_type n, ats_double_type f) {
  int i; double *p0, *p ;
  // proper alignment is needed of v2df-processing
  p0 = (double*)memalign(64, n * sizeof(double)) ;
  p = p0; for (i = 0; i < n; ++i) *p++ = f ;
  return p0 ;
} // end of [darr_make]
static inline ats_void_type
darr_free (ats_ptr_type A) { free (A) ; return ; }
%} // end of [%{^]

(* ****** ****** *)

typedef dbl = double
typedef darr (n:int) = @[dbl][n] and v2dfarr (n:int) = @[v2df][n]

extern
fun darr_make {n:nat} (n: int n, ini: double)
  : [l:addr] (darr n @ l | ptr l) = "darr_make"

extern fun darr_free {n:nat}
  {l:addr} (pf: darr n @ l | p: ptr l): void = "darr_free"

(* ****** ****** *)

macdef denom (i, j) =
  (,(i) + ,(j)) * (,(i) + ,(j) + 1) / 2 + ,(i) + 1
macdef eval_A (i,j) = 1.0 / denom (,(i), ,(j))

fn eval_A_0 (i: int, j: int): v2df = let // two divisions at a time
  val k1 = denom(i,j); val k2 = denom (i,j+1) in v2df_1_1 / v2df_make_int_int (k1, k2)
end // end of [eval_A_0]

fn eval_A_1 (i: int, j: int): v2df = let // two divisions at a time
  val k1 = denom(i,j); val k2 = denom (i+1,j) in v2df_1_1 / v2df_make_int_int (k1, k2)
end // end of [eval_A_1]

(* ****** ****** *)

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))

fn eval_A_times_u {N:nat} {l: addr}
  (flag: int, N: int N, u: &darr N, tmp: &darr N): void = let
  val N2 = N / 2; stadef N2 = N / 2
  fun loop2_0
    {i,j:nat | j <= N2} {l:addr} .<N2-j>. (
      pf: !v2dfarr (N2-j) @ l
    | p_dd: ptr l, sum: &v2df, i: int i, j: int j
    ) :<cloref1> void =
    if j < N2 then let
      prval (pf1, pf2) = array_v_uncons {v2df} (pf)
      val () = sum += !p_dd * eval_A_0 (i, 2*j)
      val () = loop2_0 (pf2 | p_dd + sizeof<v2df>, sum, i, j+1)
    in
      pf := array_v_cons {v2df} (pf1, pf2)
    end // end of [if]
  // end of [loop2_0]
  fun loop2_1
    {i,j:nat | j <= N2} {l:addr} .<N2-j>. (
      pf: !v2dfarr (N2-j) @ l
    | p_dd: ptr l, sum: &v2df, i: int i, j: int j
    ) :<cloref1> void =
    if j < N2 then let
      prval (pf1, pf2) = array_v_uncons {v2df} (pf)
      val () = sum += !p_dd * eval_A_1 (2*j, i)
      val () = loop2_1 (pf2 | p_dd + sizeof<v2df>, sum, i, j+1)
    in
      pf := array_v_cons {v2df} (pf1, pf2)
    end // end of [if]
  // end of [loop2_1]
  fun loop1 {i:nat| i <= N} {l:addr} .<N-i>.
    (pf: !darr N @ l | i:int i, p_u: ptr l, tmp: &darr N):<cloref1> void = let
    viewdef V1 = darr N @ l; viewdef V2 = v2dfarr (N2) @ l
  in
    if i < N then let
      prval (pf1, fpf2) = __cast (pf) where {
        extern praxi __cast (pf: darr N @ l): (V2, V2 -<lin,prf> V1)
      }
      var sum: v2df = v2df_0_0
      val () = if flag = 0 then
        loop2_0 (pf1 | p_u, sum, i, 0) else loop2_1 (pf1 | p_u, sum, i, 0)
      // end of [if]
      prval () = pf := fpf2 (pf1)
      val () = tmp.[i] := v2df_get_fst(sum) + v2df_get_snd(sum)
      val () = if N > N2+N2 then tmp.[i] += eval_A(i,N-1) * p_u->[N-1]
    in
      loop1 (pf | i+1, p_u, tmp)
    end // end of [if]
  end // end of [loop1]
in
  loop1 (view@ u | 0, &u, tmp)
end // end of [eval_A_times_u]

(* ****** ****** *)

fn eval_AtA_times_u {N:nat}
  (N: int N, u: &darr N, v: &darr N, tmp: &darr N): void = () where {
  val () = eval_A_times_u (0, N, u, tmp); val () = eval_A_times_u (1, N, tmp, v)
} // end of [eval_AtA_times_u]

(* ****** ****** *)

staload M = "libc/SATS/math.sats"

(* ****** ****** *)

implement
main (argc, argv) = let
  val () =
  assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val [N:int] N = int1_of_string argv.[1]
  val () =
  assert_errmsg_bool1
  (
    N >= 0, "The input integer needs to be a natural number.\n"
  ) (* end of [val] *)
  val (pf_u | p_u) = darr_make (N, 1.0)
  val (pf_v | p_v) = darr_make (N, 0.0)
  val (pf_tmp | p_tmp) = darr_make (N, 0.0)
//  
  #define TIMES 10
  var i: Nat // uninitialized
  val () = for
    (i := 0; i < TIMES; i := i+1) let
    val () = eval_AtA_times_u (N, !p_u, !p_v, !p_tmp)
    val () = eval_AtA_times_u (N, !p_v, !p_u, !p_tmp)
  in (*nothing*) end
//
  var vBv: double = 0.0 and vv: double = 0.0
  val () = for (i := 0; i < N; i := i+1) let
    val ui = p_u->[i] and vi = p_v->[i] in vBv += ui*vi; vv += vi*vi
  end // end of [val]
//
  // val () = printf ("vBv = %f and vv = %f\n", @(vBv, vv))
  val () = darr_free (pf_u | p_u)
  val () = darr_free (pf_v | p_v)
  val () = darr_free (pf_tmp | p_tmp)
in
  printf("%0.9f\n", @($M.sqrt (vBv/vv)))
end // end of [main]

(* ****** ****** *)

(* end of [spectral-norm2.dats] *)
