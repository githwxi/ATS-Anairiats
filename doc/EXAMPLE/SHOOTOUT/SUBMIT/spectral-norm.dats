(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 -msse2 spectral-norm.dats -o spectral-norm -lm
**
*)

staload M = "libc/SATS/math.sats"

%{^

static inline
ats_ptr_type
darray_make (ats_int_type n, ats_double_type f) {
  int i;
  ats_double_type *p0, *p ;

  p0 = malloc(n * sizeof(ats_double_type)) ;
  p = p0 ;

  for (i = 0; i < n; ++i) { *p = f; ++p; }
  return p0 ;
}

static inline
ats_void_type
darray_free (ats_ptr_type A) { free (A) ; return ; }

static inline
ats_double_type
darray_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_double_type*)A)[i] ;
}

static inline
ats_void_type
darray_set (ats_ptr_type A, ats_int_type i, ats_double_type f) {
  ((ats_double_type*)A)[i] = f ; return ;
}

%}

// it is equally good the define this as a function
macdef eval_A(i,j) = // hygenic macro definition
  1.0 / ((,(i)+,(j)) * (,(i)+,(j)+1) / 2 + ,(i) + 1)

(* ****** ****** *)

absviewt@ype darray (n:int) // it is linear, so it cannot be leaked.

extern fun darray_make {n:nat}
  (n: int n, d: double): [l:addr] (darray n @ l | ptr l) = "darray_make"

extern fun darray_free
  {n:nat} {l:addr} (pf: darray n @ l | p: ptr l): void = "darray_free"

extern fun darray_get
  {n:nat} (A: &darray n, i: natLt n): double = "darray_get"

extern fun darray_set
  {n:nat} (A: &darray n, i: natLt n, d: double): void = "darray_set"

overload [] with darray_get; overload [] with darray_set

(* ****** ****** *)

fn eval_A_times_u {N:nat}
  (N: int N, u: &darray N, Au: &darray N): void = let
  fun loop_one {i,j:nat | i < N; j <= N} .<N-j>.
    (u: &darray N, Au: &darray N, i: int i, j: int j):<cloptr1> void =
    if j < N then begin
      Au[i] := Au[i] + eval_A(i, j) * u[j]; loop_one (u, Au, i, j+1)
    end
  fun loop_all {i:nat | i <= N} .<N-i>.
    (u: &darray N, Au: &darray N, i: int i):<cloptr1> void =
    if i < N then begin
      Au[i] := 0.0; loop_one (u, Au, i, 0); loop_all (u, Au, i+1)
    end
in
  loop_all (u, Au, 0)
end // end of [eval_A_times_u]

(* ****** ****** *)

fn eval_At_times_u {N:nat}
  (N: int N, u: &darray N, Au: &darray N): void = let
  fun loop_one {i,j:nat | i < N; j <= N} .<N-j>.
    (u: &darray N, Au: &darray N, i: int i, j: int j):<cloptr1> void =
    if j < N then begin
      Au[i] := Au[i] + eval_A(j, i) * u[j]; loop_one (u, Au, i, j+1)
    end
  fun loop_all {i:nat | i <= N} .<N-i>.
    (u: &darray N, Au: &darray N, i: int i):<cloptr1> void =
    if i < N then begin
      Au[i] := 0.0; loop_one (u, Au, i, 0); loop_all (u, Au, i+1)
    end
in
  loop_all (u, Au, 0)
end // end of [eval_At_times_u]

fn eval_AtA_times_u {N:nat}
  (N: int N, u: &darray N, AtAu: &darray N):<cloptr1> void = let
  val (pf | p_v) = darray_make (N, 0.0)
in
  eval_A_times_u(N, u, !p_v);
  eval_At_times_u (N, !p_v, AtAu);
  darray_free (pf | p_v)
end // end of [eval_AtT_times_u]

(* ****** ****** *)

#define TIMES 10

implement main (argc, argv) = let
  val () = assert_errmsg (argc = 2, "Exit: wrong command format!\n")
  val [N:int] N = int1_of_string argv.[1]
  val () = assert_errmsg (
    N >= 0, "The input integer needs to be a natural number.\n"
  )
  val (pf_u | p_u) = darray_make (N, 1.0)
  val (pf_v | p_v) = darray_make (N, 0.0)
  fun loop1 {i:nat | i <= TIMES} .<TIMES-i>.
    (u: &darray N, v: &darray N, i: int i):<cloptr1> void =
    if (i < TIMES) then begin
      eval_AtA_times_u(N, u, v); eval_AtA_times_u(N, v, u); loop1 (u, v, i+1)
    end
  val () = loop1 (!p_u, !p_v, 0)
  fun loop2 {i:nat| i <= N} .<N-i>.
    (u: &darray N, v: &darray N,
     vBv: double, vv: double, i: int i):<cloptr1> @(double, double) =
    if i < N then let
      val ui = u[i] and vi = v[i]
      val () = printf ("u[%i] = %f and v[%i] = %f\n", @(i, ui, i, vi))
    in
      loop2 (u, v, vBv+ui*vi, vv+vi*vi, i+1)
    end else (vBv, vv)
  val @(vBv, vv) = loop2 (!p_u, !p_v, 0.0, 0.0, 0)
  val () = printf ("vBv = %f and vv = %f\n", @(vBv, vv))
  val () = (darray_free (pf_u | p_u); darray_free (pf_v | p_v))
in
  printf("%0.9f\n", @($M.sqrt (vBv/vv)))
end // end of [main]

(* ****** ****** *)

(* end of [spectral-norm.dats] *)
