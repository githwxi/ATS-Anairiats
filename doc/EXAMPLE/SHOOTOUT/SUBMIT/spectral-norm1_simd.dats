(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 -msse2 spectral-norm1_simd.dats -o spectral-norm -lm
**
*)

staload M = "libc/SATS/math.sats"

staload _(*anonymous*) = "prelude/DATS/array.dats"

(* ****** ****** *)

macdef A(i,j) = // macro definition
  1.0 / ((,(i) + ,(j)) * (,(i) +,(j) + 1) / 2 + ,(i) + 1)

(* ****** ****** *)

%{^
 
// vector of two doubles
typedef double v2df __attribute__((vector_size(16))) ;
typedef v2df ats_v2df_type ;

%}

abst@ype v2df = $extype "ats_v2df_type"

(* ****** ****** *)

%{^

ats_v2df_type ats_zero_v2df = { 0.0, 0.0 } ;

static inline
ats_double_type
ats_v2df_fst_get (ats_v2df_type dd) { return ((double*)&dd)[0] ; }

static inline
ats_double_type
ats_v2df_snd_get (ats_v2df_type dd) { return ((double*)&dd)[1] ; }

static inline
ats_void_type
ats_v2df_set2
  (ats_ptr_type dd, ats_double_type d0, ats_double_type d1) {
  ((ats_double_type*)dd)[0] = d0;
  ((ats_double_type*)dd)[1] = d1;
  return ;
}

static inline
ats_v2df_type
ats_add_v2df_v2df (ats_v2df_type dd1, ats_v2df_type dd2) {
  return (dd1 + dd2) ;
}

static inline
ats_v2df_type
ats_mul_v2df_v2df (ats_v2df_type dd1, ats_v2df_type dd2) {
  return (dd1 * dd2) ;
}

%}

extern val zero_v2df: v2df = "ats_zero_v2df"

extern fun v2df_fst_get (dd: v2df): double = "ats_v2df_fst_get"
extern fun v2df_snd_get (dd: v2df): double = "ats_v2df_snd_get"

extern fun v2df_set2
  (dd: &v2df?>>v2df, d0: double, d1: double): void = "ats_v2df_set2"

extern fun add_v2df_v2df (_: v2df, _: v2df): v2df = "ats_add_v2df_v2df"
extern fun mul_v2df_v2df (_: v2df, _: v2df): v2df = "ats_mul_v2df_v2df"
overload + with add_v2df_v2df
overload * with mul_v2df_v2df

(* ****** ****** *)

%{^

static inline
ats_v2df_type ddarr_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_v2df_type*)A)[i] ;
}

static inline
ats_void_type ddarr_set2 (
  ats_ptr_type A, ats_int_type i, ats_double_type d0, ats_double_type d1
) {
  ats_v2df_type *p ;
  p = &((ats_v2df_type*)A)[i];
  ((ats_double_type*)p)[0] = d0; ((ats_double_type*)p)[1] = d1;
  return ;
}

// [stdlib.h]
extern void* memalign(size_t boundary, size_t size) ;

static inline
ats_ptr_type ddarr_make (ats_int_type n) {
  v2df *p0 ;
  p0 = memalign(sizeof(v2df), n * sizeof(v2df)) ;
  if (!p0) exit (1) ;
  return p0 ;
}

static inline
ats_ptr_type ddarr_make_elt (ats_int_type n, ats_double_type f) {
  int i;
  v2df *p0, *p ;
  p0 = ddarr_make (n) ;
  for (i = 0, p = p0; i < n; ++i, ++p) {
    ((double*)p)[0] = f ; ((double*)p)[1] = f ;
  }
  return p0 ;
}

static inline
ats_void_type ddarr_free (ats_ptr_type A) { free (A) ; return ; }
%}

(* ****** ****** *)

abst@ype ddarr (n:int)

local

assume ddarr (n:int) = @[v2df][n]

in // in of [local]

extern fun ddarr_make {n:nat}
  (n: int n): [l:addr] (ddarr n @ l | ptr l) = "ddarr_make"
extern fun ddarr_make_elt {n:nat}
  (n: int n, f: double): [l:addr] (ddarr n @ l | ptr l) = "ddarr_make_elt"
extern fun ddarr_free {n:nat} {l:addr}
  (pf: ddarr n @ l | p: ptr l): void = "ddarr_free"
  
extern fun ddarr_get {n:nat}
 (A: &ddarr n, i: natLt n): v2df = "ddarr_get"
extern fun ddarr_set2 {n:nat}
  (A: &ddarr n, i: natLt n, d0: double, d1: double): void = "ddarr_set2"
  
end // end of [local]

overload [] with ddarr_get

(* ****** ****** *)

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))

fn eval_A_times_u {N:nat}
  (N: int N, u: &ddarr N, Au: &ddarr N): void = let
  var d0: double? and d1: double?
  var dd: v2df?
  var AA: v2df?
  var i: natLte N = 0; var j: int?; var i2: Nat = 0; var j2: int?
in
  while (i < N) begin
    dd := zero_v2df; j := 0; j2 := 0;
    while*
      (dd: v2df, i: natLt N, j: natLte N, i2:Nat, j2:Nat) => (j < N) begin
      v2df_set2 (AA, A(i2,j2), A(i2,j2+1));
      dd += AA * u[j]; j += 1; j2 += 2;
    end;
    d0 := v2df_fst_get (dd) + v2df_snd_get (dd) ;

    dd := zero_v2df; j := 0; j2 := 0;
    while* (dd: v2df, i: natLt N, j: natLte N, i2:Nat, j2:Nat) => (j < N) begin
      v2df_set2 (AA, A(i2+1,j2), A(i2+1,j2+1));
      dd += AA * u[j];
      j += 1; j2 += 2;
    end;
    d1 := v2df_fst_get (dd) + v2df_snd_get (dd) ;

    ddarr_set2 (Au, i, d0, d1);

    i += 1; i2 += 2;
  end // end of [while]
end // end of [eval_A_times_u]

fn eval_At_times_u {N:nat}
  (N: int N, u: &ddarr N, Au: &ddarr N): void = let
  var d0: double? and d1: double?
  var dd: v2df?
  var AA: v2df?
  var i: natLte N = 0; var j: int?; var i2: Nat = 0; var j2: int?
in
  while (i < N) begin
    dd := zero_v2df; j := 0; j2 := 0;
    while* (dd: v2df, i: natLt N, j:natLte N, i2:Nat, j2:Nat) => (j < N) begin
      v2df_set2 (AA, A(j2,i2), A(j2+1,i2));
      dd += AA * u[j]; j += 1; j2 += 2;
    end;
    d0 := v2df_fst_get (dd) + v2df_snd_get (dd) ;

    dd := zero_v2df; j := 0; j2 := 0;
    while* (dd: v2df, i: natLt N, j:natLte N, i2:Nat, j2:Nat) => (j < N) begin
      v2df_set2 (AA, A(j2,i2+1), A(j2+1,i2+1));
      dd += AA * u[j]; j += 1; j2 += 2;
    end;
    d1 := v2df_fst_get (dd) + v2df_snd_get (dd) ;

    ddarr_set2 (Au, i, d0, d1);

    i += 1; i2 += 2;
  end // end of [while]
end // end of [eval_At_times_u]


(* ****** ****** *)

fn eval_AtA_times_u {N:nat}
  (N: int N, u: &ddarr N, AtAu: &ddarr N): void = let
  val (pf_v | p_v) = ddarr_make (N)
in
  eval_A_times_u(N, u, !p_v); eval_At_times_u (N, !p_v, AtAu);
  ddarr_free (pf_v | p_v)
end // end of [eval_AtT_times_u]

(* ****** ****** *)

#define TIMES 10

implement
main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val [N:int] N = int1_of_string argv.[1]
  val () = assert_errmsg_bool1 (
    N > 0, "The input integer needs to be positive.\n"
  )
  val N2 = N / 2
  val () = assert_errmsg_bool1 (
    N2 + N2 = N, "The input integer needs to be even.\n"
  )
  val (pf_u | p_u) = ddarr_make_elt (N2, 1.0)
  val (pf_v | p_v) = ddarr_make_elt (N2, 0.0)
  var i: Nat = 0; val () = while (i < TIMES) begin
    eval_AtA_times_u (N2, !p_u, !p_v);
    eval_AtA_times_u (N2, !p_v, !p_u);
    i += 1;
  end
  var vBv: v2df = zero_v2df and vv: v2df = zero_v2df
  var i: Nat = 0; val () = while (i < N2) let
    val ui = ddarr_get (!p_u, i) and vi = ddarr_get (!p_v, i)
  in
    vBv += ui*vi; vv += vi*vi; i += 1
  end
  val vBv1 = v2df_fst_get (vBv) + v2df_snd_get (vBv)
  val vv1 = v2df_fst_get (vv) + v2df_snd_get (vv)
// (*
  val () = printf ("vBv1 = %f and vv1 = %f\n", @(vBv1, vv1))
// *)
  val () = (ddarr_free (pf_u | p_u); ddarr_free (pf_v | p_v))
in
  printf("%0.9f\n", @($M.sqrt (vBv1/vv1)))
end // end of [main]

(* ****** ****** *)

(* end of [spectral-norm1_simd.dats] *)
