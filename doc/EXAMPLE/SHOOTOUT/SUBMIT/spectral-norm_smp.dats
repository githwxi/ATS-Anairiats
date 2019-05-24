(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
	atscc -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -msse2 spectral-norm_smp.dats -o spectral-norm_smp -lm -lpthread
**
*)

staload M = "libc/SATS/math.sats"

%{^

static inline
ats_ptr_type darray_make (ats_int_type n, ats_double_type f) {
  int i; ats_double_type *p0, *p ;
  p0 = malloc(n * sizeof(ats_double_type)) ;
  for (i = 0, p = p0; i < n; ++i, ++p) *p = f;
  return p0 ;
}

static inline
ats_void_type darray_free (ats_ptr_type A) { free (A) ; return ; }

static inline
ats_double_type darray_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_double_type*)A)[i] ;
}

static inline
ats_void_type
darray_set (ats_ptr_type A, ats_int_type i, ats_double_type f) {
  ((ats_double_type*)A)[i] = f ; return ;
}

static inline
ats_double_type eval_A (ats_int_type i, ats_int_type j) { 
  return 1.0/((i+j)*(i+j+1)/2+i+1) ;
}

%}

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

//

extern fun eval_A (i: int, j: int): double = "eval_A"

//

%{^

ats_void_type loop_one_ij
  (ats_int_type N, ats_ptr_type u, ats_ptr_type Aui, ats_int_type i) {
  int j ; double sum = 0.0 ;
  for (j = 0 ; j < N ; j += 1) sum += eval_A (i, j) * ((double*)u)[j] ;
  *(double*)Aui = sum ;
  return ;
}  

ats_void_type
loop_all_ij (
  ats_int_type N
, ats_int_type beg
, ats_int_type fin
, ats_ptr_type u
, ats_ptr_type Au
) {
  int i ;
  for (i = beg ; i < fin ; i += 1) loop_one_ij (N, u, &((double*)Au)[i], i) ;
  return ;
}

ats_void_type loop_one_ji
  (ats_int_type N, ats_ptr_type u, ats_ptr_type Aui, ats_int_type i) {
  int j ; double sum = 0.0 ;
  for (j = 0 ; j < N ; j += 1) sum += eval_A (j, i) * ((double*)u)[j] ;
  *(double*)Aui = sum ;
  return ;
}

ats_void_type
loop_all_ji (
  ats_int_type N
, ats_int_type beg
, ats_int_type fin
, ats_ptr_type u
, ats_ptr_type Au
) {
  int i ;
  for (i = beg ; i < fin ; i += 1) loop_one_ji (N, u, &((double*)Au)[i], i) ;
  return ;
}

%}

extern fun loop_all_ij {N,s,f:int | 0 <= s; f <= N}
  (N: int N, beg: int s, fin: int f, u: &darray N, Au: &darray N): void = "loop_all_ij"

extern fun loop_all_ji {N,s,f:int | 0 <= s; f <= N}
  (N: int N, beg: int s, fin: int f, u: &darray N, Au: &darray N): void = "loop_all_ji"
  
(* ****** ****** *)

%{^

#include <pthread.h>

static pthread_mutex_t mutex_fin = PTHREAD_MUTEX_INITIALIZER;

static inline
ats_void_type finlock_lock () {
  pthread_mutex_lock (&mutex_fin) ; return ;
}

static the_nticket ;
static the_nthread ;
static pthread_mutex_t mutex_nticket = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t mutex_nthread = PTHREAD_MUTEX_INITIALIZER;

static inline
ats_void_type thread_v_return () {
  int n ;
  pthread_mutex_lock (&mutex_nthread) ;
  n = the_nthread ; the_nthread = n - 1;
  pthread_mutex_unlock (&mutex_nthread) ;
  if (n == 1) {
    pthread_mutex_unlock (&mutex_fin) ; // conditional wait?
  } // end of [if]
  return ;
}

ats_int_type nticket_get () {
  int n ;
  pthread_mutex_lock (&mutex_nticket) ;
  n = the_nticket ; the_nticket = n + 1 ;
  pthread_mutex_unlock (&mutex_nticket) ;
  return n ;
}

static inline
ats_void_type main_init () {
  pthread_mutex_lock (&mutex_fin) ; return ;
}

static inline
ats_void_type nthread_init (ats_int_type n) {
  the_nticket = 0 ; the_nthread = n ; return ;
}

%}

absview thread_v; absview nthread_v (int)

extern fun thread_v_return
  (pf: thread_v | (*none*)): void = "thread_v_return"

extern praxi nthread_v_take {n:pos}
  (pf: !nthread_v n >> nthread_v (n-1)): thread_v

extern praxi nthread_v_elim (pf: nthread_v 0):<> void

extern fun nticket_get
  (pf: !thread_v | (*none*)): Nat = "nticket_get"
  
// [!ref] prevents it from being called in a thread
extern fun nthread_init {n:nat} (n: int n):<!ref> (nthread_v n | void)
  = "nthread_init"

(* ****** ****** *)

staload "libc/SATS/pthread.sats"

(* ****** ****** *)

#define NTHREAD 4; #define STRIDE 4

fn eval_A_times_u_knd {N:nat}
  (knd: int, N: int N, u: &darray N, Au: &darray N): void = let
  fun worker {l_u, l_Au:addr} (
      pf_thread: thread_v
    , pf_u: darray N @ l_u, pf_Au: darray N @ l_Au
    | knd: int, N: int N, p_u: ptr l_u, p_Au: ptr l_Au
    ) : void = let
    val n = nticket_get (pf_thread | (*none*)); val beg = n * STRIDE
  in
    case+ 0 of
    | _ when beg < N => let
        val fin = beg + STRIDE
        val fin = (if fin < N then fin else N): natLte N
        val () = case+ 0 of
          | _ when knd = 0 => loop_all_ij (N, beg, fin, !p_u, !p_Au)
          | _ (* knd = 1 *) => loop_all_ji (N, beg, fin, !p_u, !p_Au)
      in
        worker (pf_thread, pf_u, pf_Au | knd, N, p_u, p_Au)
      end
    | _ => let
        extern praxi darray_v_elim {l:addr} (pf: darray N @ l): void
        prval () = darray_v_elim (pf_u)
        prval () = darray_v_elim (pf_Au)
      in
        thread_v_return (pf_thread | (*none*));
      end
  end // end of [worker]
  val p_u = &u and p_Au = &Au
  fun worker_gen {n:nat}
    (pf_nthread: nthread_v n | n: int n):<cloref1> void =
    if n > 0 then let
      extern praxi darray_v_copy {l:addr} (p: ptr l): darray N @ l
      prval pf_u = darray_v_copy (p_u)
      prval pf_Au = darray_v_copy (p_Au)
      prval pf_thread = nthread_v_take (pf_nthread)
      var tid: pthread_t // uninitialized
      val () = pthread_create_detached_cloptr (
        lam () =<lin,cloptr1> worker (pf_thread, pf_u, pf_Au | knd, N, p_u, p_Au), tid
      ) // end of [pthread_create_detached_cloptr]
    in
      worker_gen (pf_nthread | n-1)
    end else begin
      let prval () = nthread_v_elim (pf_nthread) in () end
    end // end of [if]
  val (pf_nthread | ()) = nthread_init (NTHREAD)
  val () = worker_gen (pf_nthread | NTHREAD)  
  val () = finlock_lock () where {
    extern fun finlock_lock (): void = "finlock_lock"
  }
in
  // empty
end // end of [eval_A_times_u]

(* ****** ****** *)

fn eval_A_times_u {N:nat} (N: int N, u: &darray N, Au: &darray N): void =
  eval_A_times_u_knd (0, N, u, Au)

fn eval_At_times_u {N:nat} (N: int N, u: &darray N, Au: &darray N): void =
  eval_A_times_u_knd (1, N, u, Au)

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

(* ****** ****** *)

implement
main (argc, argv) = let
  val () =
  assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val [N:int] N = int1_of_string (argv.[1])
  val () =
  assert_errmsg_bool1
  (
    N >= 0, "The input integer needs to be a natural number.\n"
  ) (* end of [val] *)
  val () = main_init () where {
    extern fun main_init (): void = "main_init"
  }
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
    if i < N then
      let val ui = u[i] and vi = v[i] in
        loop2 (u, v, vBv+ui*vi, vv+vi*vi, i+1)
      end
    else (vBv, vv)
  val @(vBv, vv) = loop2 (!p_u, !p_v, 0.0, 0.0, 0)
  val () = (darray_free (pf_u | p_u); darray_free (pf_v | p_v))
in
  printf("%0.9f\n", @($M.sqrt (vBv/vv)))
end // end of [main]

(* ****** ****** *)

(* end of [spectral-norm_smp.dats] *)
