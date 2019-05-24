(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
	atscc -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd_smp mandelbrot_simd_smp.dats -lpthread
**
*)

%{^
 
// vector of two doubles
typedef double v2df __attribute__ ((vector_size(16))) ;
typedef v2df ats_v2df_type ;

%}

(* ****** ****** *)

abst@ype v2df = $extype "ats_v2df_type"

#define TIMES 50
#define LIMIT 2.0; #define LIMIT2 (LIMIT * LIMIT)

(* ****** ****** *)

%{^

ats_v2df_type ats_zero_v2df = { 0.0, 0.0 } ;

ats_v2df_type
ats_v2df_make
  (ats_double_type d0, ats_double_type d1) {
  v2df dd ;
  ((double*)&dd)[0] = d0 ; ((double*)&dd)[1] = d1 ;
  return dd ;
}

static inline
ats_double_type
ats_v2df_fst (ats_v2df_type dd) { return ((double*)&dd)[0] ; }

static inline
ats_double_type
ats_v2df_snd (ats_v2df_type dd) { return ((double*)&dd)[1] ; }

static inline
ats_v2df_type
ats_dbl_v2df (ats_v2df_type dd) { return (dd + dd) ; }

static inline
ats_v2df_type
ats_add_v2df_v2df (ats_v2df_type dd1, ats_v2df_type dd2) {
  return (dd1 + dd2) ;
}

static inline
ats_v2df_type
ats_sub_v2df_v2df (ats_v2df_type dd1, ats_v2df_type dd2) {
  return (dd1 - dd2) ;
}

static inline
ats_v2df_type
ats_mul_v2df_v2df (ats_v2df_type dd1, ats_v2df_type dd2) {
  return (dd1 * dd2) ;
}

%}

extern val zero_v2df: v2df = "ats_zero_v2df"

extern fun v2df_make (d0: double, d1: double): v2df = "ats_v2df_make"

extern fun v2df_fst (dd: v2df): double = "ats_v2df_fst"
extern fun v2df_snd (dd: v2df): double = "ats_v2df_snd"

extern fun dbl_v2df (_: v2df): v2df = "ats_dbl_v2df"
extern fun add_v2df_v2df (_: v2df, _: v2df): v2df = "ats_add_v2df_v2df"
extern fun sub_v2df_v2df (_: v2df, _: v2df): v2df = "ats_sub_v2df_v2df"
extern fun mul_v2df_v2df (_: v2df, _: v2df): v2df = "ats_mul_v2df_v2df"
overload + with add_v2df_v2df
overload - with sub_v2df_v2df
overload * with mul_v2df_v2df

(* ****** ****** *)

%{^

#include <pthread.h>

static pthread_mutex_t mutex_fin = PTHREAD_MUTEX_INITIALIZER;

static inline
ats_void_type finlock_acquire () {
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
ats_void_type mandelbrot_init (ats_int_type n) {
  the_nticket = 0 ; the_nthread = n ; pthread_mutex_lock (&mutex_fin) ; return ;
}

%}

absview thread_v
absview nthread_v (int)

extern fun thread_v_return
  (pf: thread_v | (*none*)): void = "thread_v_return"

extern prfun nthread_v_take {n:pos}
  (pf: !nthread_v n >> nthread_v (n-1)): thread_v

extern prfun nthread_v_elim (pf: nthread_v 0):<> void

extern fun nticket_get
  (pf: !thread_v | (*none*)): int = "nticket_get"

(* ****** ****** *)

// [!ref] prevents it from being called in a thread
extern fun mandelbrot_init {n:nat} (n: int n):<!ref> (nthread_v n | void)
  = "mandelbrot_init"
  
(* ****** ****** *)

#define i2d double_of_int

%{^

static inline
ats_ptr_type bytearr_malloc (ats_int_type sz) {
  void *p = malloc (sz) ;
  if (!p) {
    fprintf (stderr, "Exit: [malloc] failed.\n"); exit (1) ;
  }
  return p ;
}

static inline
ats_void_type bytearr_free (ats_ptr_type p) { free (p); return ; }

%}

absviewtype bytearr
extern fun bytearr_make (sz: int): [l:addr] (bytearr @ l | ptr l) =
  "bytearr_malloc"
extern fun bytearr_free {l:addr} (pf: bytearr @ l | p: ptr l): void =
  "bytearr_free"

%{^

static inline
ats_void_type
bytearr_set (ats_ptr_type A, ats_int_type i, ats_byte_type b) {
  ((ats_byte_type*)A)[i] = b ; return ;
}

static inline
ats_void_type
bytearr_output (ats_ptr_type A, ats_int_type sz) {
  int n, lft ;
  lft = sz ;
  while (lft > 0) {
    n = fwrite (A, 1, lft, stdout) ; lft -= n ;
  }
  return ;
}

%}

extern fun bytearr_set (A: &bytearr, i: int, b: byte): void = "bytearr_set"
overload [] with bytearr_set

extern fun bytearr_output (A: &bytearr, sz: int): void = "bytearr_output"

(* ****** ****** *)

staload "libc/SATS/pthread.sats"

(* ****** ****** *)

#define NTHREAD 32

fn mandelbrot (h: int, w: int): void = let

val w8 = (w + 7) >> 3
val sz = h * w8
val [l0:addr] (pf0_A | p_A) = bytearr_make (sz)
val h_r = 1.0 / (i2d h) and w_r = 1.0 / (i2d w)
val (pf_nthread | ()) = mandelbrot_init (NTHREAD)

fun test (h_r: double, w_r: double, x: int, y: int): int = let
  val x2 = i2d (x << 1)
  val Cr0 = x2 * w_r - 1.5
  val Cr1 = (x2 + 2.0) * w_r - 1.5
  val y2 = i2d (y << 1)
  val Ci0 = y2 * h_r - 1.0
  val Ci1 = Ci0
  val Crv = v2df_make (Cr0, Cr1)
  val Civ = v2df_make (Ci0, Ci1)

  fun loop (
      eo: int
    , Cr: double, Ci: double, Zr: double, Zi: double
    , times: int
    ) :<fun1> int = let
    val Tr = Zr * Zr and Ti = Zi * Zi; val Tri = Tr + Ti
  in
    case+ 0 of
    | _ when Tri <= LIMIT2 => begin
        if times = 0 then eo else let
          val Zr_new = Tr - Ti + Cr; val Zi_new = 2.0 * (Zr * Zi) + Ci
        in
          loop (eo, Cr, Ci, Zr_new, Zi_new, times-1)
        end // end of [if]
      end // end of [_ when ...]
    | _ => 0
  end // end of [loop]

  fun loopv
    (Zrv: v2df, Ziv: v2df, times: int):<cloref1> int = let
    val Trv = Zrv * Zrv and Tiv = Ziv * Ziv; val Triv = Trv + Tiv
    val Tri0 = v2df_fst (Triv) and Tri1 = v2df_snd (Triv)
    val Zrv_new = Trv - Tiv + Crv; val Ziv_new = dbl_v2df (Zrv * Ziv) + Civ
  in
    case+ 0 of
    | _ when Tri0 <= LIMIT2 => begin case+ 0 of
      | _ when Tri1 <= LIMIT2 => begin
          if times = 0 then 0x3 else loopv (Zrv_new, Ziv_new, times-1)
        end // end of [_ when ...]
      | _ => begin
          if times = 0 then 0x2 else let
            val Zr0_new = v2df_fst (Zrv_new) and Zi0_new = v2df_fst (Ziv_new)
          in
            loop (0x2(*eo*), Cr0, Ci0, Zr0_new, Zi0_new, times-1)
          end // end of [if]
        end // end of [_]
      end // end of [_ when ...]
    | _ => begin case+ 0 of
      | _ when Tri1 <= LIMIT2 => begin
          if times = 0 then 0x1 else let
            val Zr1_new = v2df_snd (Zrv_new) and Zi1_new = v2df_snd (Ziv_new)
          in
            loop (0x1(*eo*), Cr1, Ci1, Zr1_new, Zi1_new, times-1)
          end // end of [if]
        end // end of [_ when ...]
      | _ => 0x0 // return value
      end // end of [_]
  end // end of [loopv]
in
  loopv (zero_v2df, zero_v2df, TIMES)
end // end of [test]

(* ****** ****** *)

#define i2b byte_of_int

fun output_one
  (h: int, w: int, h_r: double, w_r: double, A: &bytearr, x: int, y: int, i: int, b: byte, n: natLte 8)
  : void = begin
  if x < w then let
    val res = test (h_r, w_r, x, y); val res = i2b res
  in
    case+ 0 of
    | _ when n >= 2 => begin
        output_one (h, w, h_r, w_r, A, x + 2, y, i, (b << 2) + res, n - 2)
      end // end of [_ when ...]
    | _ (*n=0*) => begin
        A[i] := b; output_one (h, w, h_r, w_r, A, x + 2, y, i + 1, res, 6)
      end // end of [_]
  end else begin
    A[i] := (b << n)
  end // end of [if]
end // end of [output_one]

(* ****** ****** *)

fun output_worker (
    pf_thread: thread_v, pf_A: bytearr @ l0
  | h: int, w: int, h_r: double, w_r: double, w8: int, p_A: ptr l0
  ) : void = let
  extern prfun bytearr_v_elim (pf_A: bytearr @ l0): void
  val y = nticket_get (pf_thread | (*none*))
in
  case+ 0 of
  | _ when y < h => let
      val i = y * w8
      val () = output_one (h, w, h_r, w_r, !p_A, 0, y, i, i2b 0, 8)
    in
      output_worker (pf_thread, pf_A | h, w, h_r, w_r, w8, p_A)
    end
  | _ (* y >= h *) => let
      prval () = bytearr_v_elim (pf_A)
    in
      thread_v_return (pf_thread | (*none*))
    end
end // end of [output_worker]

val () = output_all (pf_nthread, pf0_A | NTHREAD) where {
  fun output_all {n:nat}
    (pf_nthread: nthread_v n, pf0_A: !bytearr @ l0 | n: int n)
    :<cloptr1> void = begin
    if n > 0 then let
      prval pf_thread = nthread_v_take (pf_nthread)
      prval pf_A = bytearr_v_copy (pf0_A) where {
        extern prfun bytearr_v_copy (pf0_A: !bytearr @ l0): bytearr @ l0
      }
      var tid: pthread_t // unintialized
      val () = pthread_create_detached_cloptr (
         lam () =<lin,cloptr1> output_worker (pf_thread, pf_A | h, w, h_r, w_r, w8, p_A), tid
      ) // end of [pthread_create_detached_cloptr]
    in
      output_all (pf_nthread, pf0_A | n - 1)
    end else begin
      let prval () = nthread_v_elim (pf_nthread) in () end
    end // end of [if]
  end // end of [output_all]
} // end of [output_all]

val () = finlock_acquire () where {
  extern fun finlock_acquire (): void = "finlock_acquire"
}

val () = begin
  printf ("P4\n%i %i\n", @(h, w)); bytearr_output (!p_A, sz)
end

val () = bytearr_free (pf0_A | p_A)

(* ****** ****** *)

in

// empty

end // end of [mandelbrot]

(* ****** ****** *)

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val i = int1_of_string argv.[1]
  val () = assert_errmsg_bool1
    (i >= 2, "The input integer needs to be at least 2.\n")
in
  mandelbrot (i, i)
end // end of [main]

(* ****** ****** *)

(* end of [mandelbrot_simd.dats] *)
