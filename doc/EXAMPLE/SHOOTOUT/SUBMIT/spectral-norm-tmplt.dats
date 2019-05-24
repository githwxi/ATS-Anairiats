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

staload _(*anonymous*) = "prelude/DATS/array.dats"

(* ****** ****** *)

macdef A(i,j) = // macro definition
  1.0 / ((,(i) + ,(j)) * (,(i) +,(j) + 1) / 2 + ,(i) + 1)

(* ****** ****** *)

%{^
static inline
ats_ptr_type darr_make (ats_int_type n) {
  ats_double_type *p0 ;
  p0 = malloc(n * sizeof(ats_double_type)) ; if (!p0) exit (1) ;
  return p0 ;
}

static inline
ats_ptr_type darr_make_elt (ats_int_type n, ats_double_type f) {
  int i;
  ats_double_type *p0, *p ;
  p0 = darr_make (n) ; for (i = 0, p = p0; i < n; ++i, ++p) *p = f ;
  return p0 ;
}

static inline
ats_void_type darr_free (ats_ptr_type A) { free (A) ; return ; }
%}

(* ****** ****** *)

abst@ype darr (n:int)

local

assume darr (n:int) = @[double][n]

in // in of [local]

fn darr_get {n:nat} (A: &darr n, i: natLt n): double =
  atarray_get_elt_at<double> (A, i)
fn darr_set {n:nat} (A: &darr n, i: natLt n, f: double): void =
  atarray_set_elt_at<double> (A, i, f)
  
extern fun darr_make {n:nat}
  (n: int n): [l:addr] (darr n @ l | ptr l) = "darr_make"
extern fun darr_make_elt {n:nat}
  (n: int n, f: double): [l:addr] (darr n @ l | ptr l) = "darr_make_elt"
extern fun darr_free {n:nat} {l:addr}
  (pf: darr n @ l | p: ptr l): void = "darr_free"
  
end // end of [local]

overload [] with darr_get; overload [] with darr_set

(* ****** ****** *)

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))

fn{knd:int} eval_A_times_u {N:nat}
  (N: int N, u: &darr N, Au: &darr N): void = let
  var i: natLte N; var j: natLte N
in
  for (i := 0; i < N; i += 1) begin
    Au[i] := 0.0 ;
sif :(i: natLt N) => knd == 0 then begin
    for* (i: natLt N) => (j := 0; j < N; j += 1) (Au[i] += A(i,j) * u[j])
end else begin
    for* (i: natLt N) => (j := 0; j < N; j += 1) (Au[i] += A(j,i) * u[j])
end ; // end of [sif]
  end
end // end of [eval_A_times_u]

(* ****** ****** *)

fn eval_AtA_times_u {N:nat}
  (N: int N, u: &darr N, AtAu: &darr N): void = let
  val (pf_v | p_v) = darr_make (N)
in
  eval_A_times_u<0> (N, u, !p_v); eval_A_times_u<1> (N, !p_v, AtAu);
  darr_free (pf_v | p_v)
end // end of [eval_AtT_times_u]

(* ****** ****** *)

#define TIMES 10

implement main (argc, argv) = let
  val () = assert_errmsg
    (argc = 2, "Exit: wrong command format!\n")
  val [N:int] N = int1_of_string argv.[1]
  val () = assert_errmsg (
    N >= 0, "The input integer needs to be a natural number.\n"
  )
  val (pf_u | p_u) = darr_make_elt (N, 1.0)
  val (pf_v | p_v) = darr_make_elt (N, 0.0)
  val () = for (i := 0; i < TIMES; i += 1) begin
    eval_AtA_times_u (N, !p_u, !p_v); eval_AtA_times_u (N, !p_v, !p_u)
  end where {
    var i: Nat
  } // end of [val]
  var vBv: double = 0.0 and vv: double = 0.0
  val () = for (i := 0; i < N; i += 1) let
    val ui = darr_get (!p_u, i) and vi = darr_get (!p_v, i)
  in
    vBv += ui*vi; vv += vi*vi; i += 1
  end where {
    var i: Nat
  } // end of [val]
  val () = (darr_free (pf_u | p_u); darr_free (pf_v | p_v))
in
  printf("%0.9f\n", @($M.sqrt (vBv/vv)))
end // end of [main]

(* ****** ****** *)

(* end of [spectral2-norm.dats] *)
