//
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

//
// This implementation even beats the C version by
// a handy margin (about 10%)
//

(*

machine: dml.bu.edu
command: spectral 5500
output:  1.274224153

ATS:    30.084u 0.012s 0:30.13 99.8% 0+0k 0+0io 0pf+0w
C:	33.347u 0.011s 0:33.41 99.8% 0+0k 0+0io 0pf+0w

*)

staload M = "libc/SATS/math.sats"

%{^

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
  return ((ats_double_type *)A)[i] ;
}

static inline
ats_void_type
darray_set (ats_ptr_type A, ats_int_type i, ats_double_type f) {
  ((ats_double_type *)A)[i] = f ; return ;
}

static inline
ats_double_type eval_A (ats_int_type i, ats_int_type j) { 
  return 1.0/((i+j)*(i+j+1)/2+i+1);
}

%}

absviewt@ype darray (n:int) // it is linear, so it cannot be leaked.

extern fun darray_make {n:nat}
  (n: int n, d: double): [l:addr] (darray n @ l | ptr l)
  = "darray_make"

extern fun darray_free
  {n:nat} {l:addr} (pf: darray n @ l | p: ptr l): void
  = "darray_free"

extern fun darray_get {n:nat}
  (A: &darray n, i: natLt n): double = "darray_get"

extern fun darray_set {n:nat}
  (A: &darray n, i: natLt n, d: double): void = "darray_set"

overload [] with darray_get
overload [] with darray_set

//

extern fun eval_A (i: int, j: int): double = "eval_A"

(*

// It is baffling why a macro definition leads to slower execution

macdef eval_A(i, j) =
 1.0 / double_of ((i+j) * (i+j+1) / 2+(i+1))

*)

fn print_A {N:nat} (N: int N, A: &darray N): void = let
  fun loop_pr {i:nat | i <= N} .<N-i>.
    (A: &darray N, i: int i):<cloptr1> void =
    if i < N then
      (printf ("A[%i] = %f\n", @(i, A[i])); loop_pr (A, i+1))
    else print_newline ()
in
  loop_pr (A, 0)
end // end of [print_A]

fn eval_A_times_u {N:nat}
  (N: int N, u: &darray N, Au: &darray N): void = let
  fun loop2 {i,j:nat | i < N; j <= N} .<N-j>.
    (u: &darray N, Au: &darray N, i: int i, j: int j):<cloptr1> void =
    if j < N then begin
      Au[i] := Au[i] + eval_A(i, j) * u[j]; loop2 (u, Au, i, j+1)
    end

  fun loop1 {i:nat | i <= N} .<N-i>.
    (u: &darray N, Au: &darray N, i: int i):<cloptr1> void =
    if i < N then begin
      Au[i] := 0.0; loop2 (u, Au, i, 0); loop1 (u, Au, i+1)
    end
in
  loop1 (u, Au, 0)
end // end of [eval_A_times_u]

//

fn eval_At_times_u {N:nat}
  (N: int N, u: &darray N, Au: &darray N): void = let
  fun loop2 {i,j:nat | i < N; j <= N} .<N-j>.
    (u: &darray N, Au: &darray N, i: int i, j: int j):<cloptr1> void =
    if j < N then begin
      Au[i] := Au[i] + eval_A(j, i) * u[j]; loop2 (u, Au, i, j+1)
    end

  fun loop1 {i:nat | i <= N} .<N-i>.
    (u: &darray N, Au: &darray N, i: int i):<cloptr1> void =
    if i < N then begin
      Au[i] := 0.0; loop2 (u, Au, i, 0); loop1 (u, Au, i+1)
    end
in
  loop1 (u, Au, 0)
end // end of [eval_At_times_u]

fn eval_AtA_times_u {N:nat}
  (N: int N, u: &darray N, AtAu: &darray N):<cloptr1> void = let
  val (pf | p_v) = darray_make (N, 0.0)
in
  eval_A_times_u(N, u, !p_v);
  eval_At_times_u (N, !p_v, AtAu);
  darray_free (pf | p_v)
end // end of [eval_AtA_times_u]

//

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
    if i < N then begin
      let val ui = u[i] and vi = v[i] in loop2 (u, v, vBv+ui*vi, vv+vi*vi, i+1) end
    end else (vBv, vv)
  val (vBv, vv) = loop2 (!p_u, !p_v, 0.0, 0.0, 0)
  val () = (darray_free (pf_u | p_u); darray_free (pf_v | p_v))
in
  printf("%0.9f\n", @($M.sqrt (vBv/vv)))
end // end of [main]

(* ****** ****** *)

(* end of [spectral-norm.dats] *)

////

/* -*- mode: c -*-
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Sebastien Loisel
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

double eval_A(int i, int j) { return 1.0/((i+j)*(i+j+1)/2+i+1); }

void eval_A_times_u(int N, const double u[], double Au[])
{
  int i,j;
  for(i=0;i<N;i++)
    {
      Au[i]=0;
      for(j=0;j<N;j++) Au[i]+=eval_A(i,j)*u[j];
    }
}

void eval_At_times_u(int N, const double u[], double Au[])
{
  int i,j;
  for(i=0;i<N;i++)
    {
      Au[i]=0;
      for(j=0;j<N;j++) Au[i]+=eval_A(j,i)*u[j];
    }
}

void eval_AtA_times_u(int N, const double u[], double AtAu[])
{ double v[N]; eval_A_times_u(N,u,v); eval_At_times_u(N,v,AtAu); }

int main(int argc, char *argv[])
{
  int i;
  int N = ((argc == 2) ? atoi(argv[1]) : 2000);
  double u[N],v[N],vBv,vv;
  for(i=0;i<N;i++) u[i]=1;
  for(i=0;i<10;i++)
    {
      eval_AtA_times_u(N,u,v);
      eval_AtA_times_u(N,v,u);
    }
  vBv=vv=0;
  for(i=0;i<N;i++) { vBv+=u[i]*v[i]; vv+=v[i]*v[i]; }
  printf("%0.9f\n",sqrt(vBv/vv));
  return 0;
}

/* end of [spectral-norm.c] */
