(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -D_ATS_MULTITHREAD -fomit-frame-pointer -O3 fannkuch_smp.dats -o fannkuch_smp -lpthread
*)

absviewt@ype intarr = $extype "intarr" // integer arrays

%{^

ATSinline()
ats_ptr_type
intarr_make (ats_int_type n) {
  return malloc((n+1) * sizeof(ats_int_type)) ;
}

ATSinline()
ats_void_type intarr_free (ats_ptr_type A) { free (A) ; return ; }

ATSinline()
ats_int_type // unsafe
intarr_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_int_type*)A)[i] ;
}

ATSinline()
ats_void_type // unsafe
intarr_set (ats_ptr_type A, ats_int_type i, ats_int_type x) {
  ((ats_int_type*)A)[i] = x ; return ;
}

%}

extern fun intarr_make (sz: int): [l:addr] (intarr @ l | ptr l)
  = "intarr_make"
extern fun intarr_free {l:addr} (pf: intarr @ l | p: ptr l): void
  = "intarr_free"

// unsafe version
extern fun intarr_get (A: &intarr, i: int): int = "intarr_get"
extern fun intarr_set (A: &intarr, i: int, x: int): void = "intarr_set"

overload [] with intarr_get
overload [] with intarr_set

(* ****** ****** *)

%{^

ATSinline()
ats_void_type intarr_copy
  (ats_ptr_type src, ats_ptr_type dst, ats_int_type sz) {
  memcpy ((int*)dst+1, (int*)src+1,  sz * sizeof(ats_int_type)) ;
  return ;
} /* end of intarr_copy */

%}

extern fun intarr_copy
  (src: &intarr, dst: &intarr, sz: int): void = "intarr_copy"

(* ****** ****** *)

// printing an integer array
fun print_intarr (A: &intarr, sz: int): void = let
  var i: int = 1
in
  while (i <= sz) (print_int A[i]; i := i+1); print_newline ()
end // end of [print_intarr]

fun perm_rotate (P: &intarr, i: int): void = let
  var k: int = 1; val P1 = P[1]
  val () = while (k < i) begin
    let val k1 = k+1 in P[k] := P[k1]; k := k1 end
  end // end of [while]
  val () = P[i] := P1
in
  // empty
end // end of [perm_rotate]

// counting permutations
fun perm_next
  (C: &intarr, P: &intarr, i: int): int = let
  val x = C[i]; val x1 = x - 1; val () = perm_rotate (P, i)
in
  case+ 0 of
  | _ when x1 > 0 => (C[i] := x1; i) | _ (* x1 = 0 *) => begin
      C[i] := i; perm_next (C, P, i+1)
    end
end // end of [perm_next]

(* ****** ****** *)

%{^

#undef PERM_TEST_IS_ALLOWED

ATSinline()
ats_bool_type perm_test
  (ats_ptr_type P0, ats_int_type sz) {
  int i, *P ;
#ifdef PERM_TEST_IS_ALLOWED
  for (i = sz, P = &((int*)P0)[sz]; i > 0; i -= 1, P -= 1) {
    if ( *P == i ) return ats_false_bool ;
  }
#else // perm test is not allowed
  if (((int*)P0)[1] == 1) return ats_false_bool ;
  if (((int*)P0)[sz] == sz) return ats_false_bool ;
#endif
  return ats_true_bool ;
} /* end of [perm_test] */

%}

extern fun perm_test (P: &intarr, sz: int): bool = "perm_test"

(* ****** ****** *)

#define NPRINT 30

(* ****** ****** *)

fn fannkuch_one
  (P: &intarr, S: &intarr, sz: int): int = let
  fun rev (S: &intarr, l: int, u: int): void =
    if (l < u) then let
      val tmp = S[l] in S[l] := S[u]; S[u] := tmp; rev (S, l+1, u-1)
    end
  fun loop (S: &intarr, cnt: int): int = let
    val x = S[1]
  in
    if x > 1 then (rev (S, 1, x); loop (S, cnt + 1)) else cnt
  end
in
  case+ 0 of
  | _ when perm_test (P, sz) => (intarr_copy (P, S, sz); loop (S, 0))
  | _ => ~1 // this one is skipped
end // end of [fannkuch_one]

(* ****** ****** *)

fn fannkuch_all (
    ans: &int? >> int
  , C: &intarr, P: &intarr, S: &intarr
  , sz: int
  ) : void = let
  fun loop (
      C: &intarr
    , P: &intarr
    , S: &intarr
    , sz: int, max: int
    ) : int = let
    val times = fannkuch_one (P, S, sz)
    val max = if (times > max) then times else max
    val i = perm_next (C, P, 2)
  in
    if i > sz then max else loop (C, P, S, sz, max)
  end // end of [loop]
in
  ans := loop (C, P, S, sz, 0)
end // end of [fannkuch_all]

(* ****** ****** *)

fun intarr_init (A: &intarr, i: int, n: int): void =
    if i <= n then (A[i] := i; intarr_init (A, i+1, n)) else ()

fn usage (cmd: string): void = printf ("usage: %s [integer]\n", @(cmd))

implement main (argc, argv) = let
  val () = if argc < 2 then (usage argv.[0]; exit (1))
  val () = assert (argc >= 2)
  val sz = int_of_string argv.[1]
  val [l_C:addr] (pf_C | p_C) = intarr_make (sz+1)
  val [l_P:addr] (pf_P | p_P) = intarr_make (sz+1)
  val () = intarr_init (!p_C, 2, sz+1)
  val () = intarr_init (!p_P, 1, sz+1)
  val () = if 0 < NPRINT then print_intarr (!p_P, sz) else ()
  val () = loop (!p_C, !p_P, sz, 1) where {
    fun loop (C: &intarr, P: &intarr, sz: int, n: int) : void =
      if n < NPRINT then let
        val _(*int*) = perm_next (C, P, 2) in
        print_intarr (P, sz); loop (C, P, sz, n+1)
      end // end of [if]
  }  // end of [where]
  var ans: int = 0
  val () = intarr_init (!p_C, 2, sz+1)
  val () = intarr_init (!p_P, 1, sz+1)
  val [l_S:addr] (pf_S | p_S) = intarr_make (sz)
  val () = fannkuch_all (ans, !p_C, !p_P, !p_S, sz)
  val () = intarr_free (pf_C | p_C)
  val () = intarr_free (pf_P | p_P)
  val () = intarr_free (pf_S | p_S)
in
  printf ("Pfannkuchen(%i) = %i\n", @(sz, ans))
end // end of [main]

(* ****** ****** *)

(* end of [fannkuch.dats] *)
