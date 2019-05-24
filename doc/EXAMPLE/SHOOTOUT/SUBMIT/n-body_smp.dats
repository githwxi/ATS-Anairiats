(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -msse2 -mfpmath=sse -O3 n-body.dats -o n-body -lm
*)

staload M = "libc/SATS/math.sats"

%{^

typedef ats_ptr_type darray ;

static inline
ats_ptr_type darray_make (ats_int_type n) {
  return malloc(n * sizeof(ats_double_type)) ;
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

%}

abst@ype darray (n:int) = $extype "darray"

extern fun darray_make {n:nat} (n: int n): darray n = "darray_make"
extern fun darray_free {n:nat} (A: darray n): void = "darray_free"

extern fun darray_get {n:nat}
  (A: darray n, i: natLt n): double = "darray_get"

extern fun darray_set {n:nat}
  (A: darray n, i: natLt n, x: double): void = "darray_set"

overload [] with darray_get
overload [] with darray_set

//

typedef body =
  (double, double, double, double, double, double, double)

val sun: body = (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0)

val jupiter: body = (
  4.84143144246472090,
 ~1.16032004402742839,
 ~1.03622044471123109e-1,
  1.66007664274403694e-3,
  7.69901118419740425e-3,
 ~6.90460016972063023e-5,
  9.54791938424326609e-4
)

val saturn: body = (
  8.34336671824457987,
  4.12479856412430479,
 ~4.03523417114321381e-1,
 ~2.76742510726862411e-3,
  4.99852801234917238e-3,
  2.30417297573763929e-5,
  2.85885980666130812e-4
)

val neptune: body = (
  1.28943695621391310e+1,
 ~1.51111514016986312e+1,
 ~2.23307578892655734e-1,
  2.96460137564761618e-3,
  2.37847173959480950e-3,
 ~2.96589568540237556e-5,
  4.36624404335156298e-5
)

val uranus: body = (
  1.53796971148509165e+1,
 ~2.59193146099879641e+1,
  1.79258772950371181e-1,
  2.68067772490389322e-3,
  1.62824170038242295e-3,
 ~9.51592254519715870e-5,
  5.15138902046611451e-5
)

#define PI 3.1415926535898
#define SOLAR_MASS (4.0 * PI * PI)
#define DAYS_PER_YEAR 365.24

typedef bodylst (n: int) = list (body, n)
#define nil list_nil; #define :: list_cons

%{^
#define N 5
#define NTHREAD 2
%}
#define N 5
#define NTHREAD 2

val theBodies: bodylst N =
  sun :: jupiter :: saturn :: neptune :: uranus :: nil ()

val x: darray N = darray_make (N)
val y: darray N = darray_make (N)
val z: darray N = darray_make (N)

val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N}
    (i: int i, bs: bodylst j): void =
    if i < N then let
      val+ b :: bs = bs
    in
      x[i] := b.0 ; y[i] := b.1 ; z[i] := b.2 ; loop (i+1, bs)
    end
}

val vx: darray N = darray_make (N)
val vy: darray N = darray_make (N)
val vz: darray N = darray_make (N)

val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N} (i: int i, bs: bodylst j): void =
    if i < N then let
      val+ b :: bs = bs
    in
      vx[i] := b.3 * DAYS_PER_YEAR ;
      vy[i] := b.4 * DAYS_PER_YEAR ;
      vz[i] := b.5 * DAYS_PER_YEAR ;
      loop (i+1, bs)
    end // end of [if]
} // end of [where]

dynload "libc/DATS/math.dats"

val m: darray N = darray_make (N)
val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N} (i: int i, bs: bodylst j): void =
    if i < N then let
      val+ b :: bs = bs
    in
      m[i] := b.6 * SOLAR_MASS; loop (i+1, bs)
    end
} // end of [where]

(* one step *)

fun pl (dt: double, i: natLte N): void =
  if i < N then begin
    x[i] := x[i]+dt*vx[i]; y[i] := y[i]+dt*vy[i]; z[i] := z[i]+dt*vz[i];
    pl (dt, i+1)
  end

#define NP 10
#assert (NP = N * (N - 1) / 2)
#define NP2 (NP / 2)
#define NP5 (NP / 5)
#define NP10 (NP / 10)

extern fun ij_i (ij: int): natLt N = "ij_i"
extern fun ij_j (ij: int): natLt N = "ij_j"

%{^

#define NP 10

typedef struct {
  ats_int_type atslab_0;
  ats_int_type atslab_1;
} intpair_t ;

intpair_t ijarr[NP] = {
  {0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}
} ;

static inline
int ij_i (ats_int_type ij) { return ijarr[ij].atslab_0 ; }

static inline
int ij_j (ats_int_type ij) { return ijarr[ij].atslab_1 ; }

%}

(* ****** ****** *)

%{^

#include <pthread.h>

static pthread_mutex_t vxyz_lock_arr[N] ;

static inline
ats_void_type vxyz_lock_arr_init () {
  int i ;
  for (i = 0; i < N; i += 1) {
    pthread_mutex_init (&vxyz_lock_arr[i], NULL) ;
  }
  return ;
}

static inline
ats_void_type vxyz_lock_acquire (ats_int_type i) {
  pthread_mutex_lock (&vxyz_lock_arr[i]) ; return ;
}

static inline
ats_void_type vxyz_lock_release (ats_int_type i) {
  pthread_mutex_unlock (&vxyz_lock_arr[i]) ; return ;
}

%}

val () = vxyz_lock_arr_init () where {
  extern fun vxyz_lock_arr_init (): void = "vxyz_lock_arr_init"
}

absview vxyz_v (int)

extern fun vxyz_lock_acquire
  {i:nat | i < N} (i: int i): (vxyz_v (i) | void) = "vxyz_lock_acquire"
extern fun vxyz_lock_release
  {i:nat | i < N} (pf: vxyz_v i | i: int i): void = "vxyz_lock_release"

fn vxyz_dec {i:nat | i < N}
  (pf: !vxyz_v i | i: int i, dx: double, dy: double, dz: double, mj: double)
  : void = begin
  vx[i] := vx[i] - dx * mj; vy[i] := vy[i] - dy * mj; vz[i] := vz[i] - dz * mj
end // end of [vxyz_dec]

fn vxyz_inc {j:nat | j < N}
  (pf: !vxyz_v j | j: natLt N, dx: double, dy: double, dz: double, mi: double)
  : void = begin
  vx[j] := vx[j] + dx * mi; vy[j] := vy[j] + dy * mi; vz[j] := vz[j] + dz * mi
end // end of [vxyz_dec]

(* ****** ****** *)

fun vl_one (dt: double, ij: natLt NP): void = let
  val i = ij_i (ij) and j = ij_j (ij)
(*
  val () = begin
    printf ("vl_one: i = %i and j = %i", @(i, j)); print_newline ()
  end
*)
  val dx = x[i] - x[j] and dy = y[i] - y[j] and dz = z[i] - z[j]
  val dist2 = dx * dx + dy * dy + dz * dz
  val dist = $M.sqrt (dist2); val mag = dt / (dist * dist2)
  val mi = m[i] * mag and mj = m[j] * mag
  val (pf | ()) = vxyz_lock_acquire (i)
  val () = vxyz_dec (pf | i, dx, dy, dz, mj)
  val () = vxyz_lock_release (pf | i)
  val (pf | ()) = vxyz_lock_acquire (j)
  val () = vxyz_inc (pf | j, dx, dy, dz, mi)
  val () = vxyz_lock_release (pf | j)
in
  // empty
end // end of [vl_one]

fun vl_two (dt: double, ij: natLt NP2): void = let
  val ij2 = ij + ij
in
  vl_one (dt, ij2); vl_one (dt, ij2 + 1)
end

fun vl_five (dt: double, ij: natLt NP5): void = let
  val ij5 = 5 * ij
in
  vl_one (dt, ij5);
  vl_one (dt, ij5 + 1);
  vl_one (dt, ij5 + 2);
  vl_one (dt, ij5 + 3);
  vl_one (dt, ij5 + 4)
end

fun vl_ten (dt: double, ij: natLt NP10): void = let
  val ij10 = 10 * ij
in
  vl_one (dt, ij10);
  vl_one (dt, ij10 + 1);
  vl_one (dt, ij10 + 2);
  vl_one (dt, ij10 + 3);
  vl_one (dt, ij10 + 4);
  vl_one (dt, ij10 + 5);
  vl_one (dt, ij10 + 6);
  vl_one (dt, ij10 + 7);
  vl_one (dt, ij10 + 8);
  vl_one (dt, ij10 + 9);
end

(* ****** ****** *)

%{^

#include <pthread.h>

static pthread_mutex_t the_mutexarr_sta[NTHREAD] ;

static the_nthread_sta ;
static inline
ats_void_type stalock_lock (ats_int_type i) {
  pthread_mutex_lock (&the_mutexarr_sta[i]) ; return ;
}

static pthread_mutex_t the_mutex_fin = PTHREAD_MUTEX_INITIALIZER;

static inline
ats_void_type finlock_wait () {
  pthread_mutex_lock (&the_mutex_fin) ; return ;
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
    pthread_mutex_unlock (&the_mutex_fin) ; // conditional wait?
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
  int i ;
  for (i = 0; i < NTHREAD; i += 1) {
    pthread_mutex_init (&the_mutexarr_sta[i], NULL) ;
    pthread_mutex_lock (&the_mutexarr_sta[i]) ;
  }
  pthread_mutex_lock (&the_mutex_fin) ; 
  return ;
}

static inline
ats_void_type advance_vl_init () {
  int i ;
  the_nticket = 0 ; the_nthread = NTHREAD ;
  for (i = 0; i < NTHREAD; i += 1) {
    pthread_mutex_unlock (&the_mutexarr_sta[i]) ;
  }
  return ;
}

static inline
ats_void_type advance_vl_fini () {
  pthread_mutex_lock (&the_mutex_fin) ; return ;
}

%}

absview thread_v

extern fun thread_v_return
  (pf: thread_v | (*none*)): void = "thread_v_return"

extern fun nticket_get (pf: !thread_v | (*none*)): Nat = "nticket_get"

(* ****** ****** *)

(* calculate initial velocity for the sun *)
fn offmoment (): void = let
  fun loop (i: natLte N, px: double, py: double, pz: double): void =
    if i < N then let
      val mi = m[i]
    in
      loop (i+1, px+vx[i]*mi, py+vy[i]*mi, pz+vz[i]*mi)
    end else begin
      vx[0] := ~px / SOLAR_MASS; vy[0] := ~py / SOLAR_MASS; vz[0] := ~pz / SOLAR_MASS
    end // end of [if]
in
  loop (1, 0.0, 0.0, 0.0)
end // end of [offmoment]

fn energy (): double = let // mutual recursion
  fn* l (i: natLt N, j: natLte N, e: double): double =
    if j < N then let
      val dx = x[i] - x[j] and dy = y[i] - y[j] and dz = z[i] - z[j]
      val dist2 = dx * dx + dy * dy + dz * dz
      val dist = $M.sqrt (dist2)
    in
      l (i, j+1, e-m[i]*m[j]/dist)
    end else l0 (i+1, e)

  and l0 (i: natLte N, e: double): double =
    if i < N then let
      val vxi = vx[i] and vyi = vy[i] and vzi = vz[i]
    in
      l (i, i+1, e + 0.5*m[i]*(vxi*vxi+vyi*vyi+vzi*vzi))
    end else e
in
  l0 (0, 0.0)
end // end of [energy]

(* ****** ****** *)

staload "libc/SATS/pthread.sats"

extern fun stalock_lock
  (id: natLt NTHREAD): (thread_v | void) = "stalock_lock"

fun worker {id:nat | id < NTHREAD}
  (dt: double, id: int id): void = let
  val (pf | ()) = stalock_lock (id)
  val () = loop (pf | (*none*)) where {
    fun loop (pf: thread_v | (*none*)):<cloref1> void = let
      val ij = nticket_get (pf | (*none*))
    in
      case+ 0 of
(*
      | _ when ij < NP => let
          val () = vl_one (dt, ij) in loop (pf | (*none*))
        end // end of [_ when ...]
      | _ when ij < NP2 => let
          val () = vl_two (dt, ij) in loop (pf | (*none*))
        end // end of [_ when ...]
*)
      | _ when ij < NP5 => let
          val () = vl_five (dt, ij) in loop (pf | (*none*))
        end // end of [_ when ...]
(*
      | _ when ij < NP10 => let
          val () = vl_ten (dt, ij) in loop (pf | (*none*))
        end // end of [_ when ...]
*)
      | _ => thread_v_return (pf | (*none*))
    end
  } // end of [where]
in
  worker (dt, id)
end // end of [worker]

fun workerlst_gen {i: nat | i <= NTHREAD} (dt: double, i: int i) : void =
  if i < NTHREAD then let
    var tid: pthread_t // uninitialized
    val () = (
      pthread_create_detached_cloptr (lam () =<lin,cloptr1> worker (dt, i), tid)
    ) // end of [val]
  in
    workerlst_gen (dt, i + 1)
  end // end of [if]

(* ****** ****** *)

fun advances (dt: double, n: Nat): void = let
  extern fun advance_vl_init (): void = "advance_vl_init"
  extern fun advance_vl_fini (): void = "advance_vl_fini"
  val () = workerlst_gen (dt, 0) // starting [NTHREAD] working threads
  val () = loop (dt, n) where {
    fun loop (dt: double, n: Nat): void =
      if n > 0 then let
        val () = advance_vl_init () // the threads are working
        val () = advance_vl_fini () // the threads are blocked
        val () = pl (dt, 0)
      in
        loop (dt, n - 1)
      end
  } // end of [wkere]
in
  // empty
end // end of [advances]

(* ****** ****** *)

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val n = int1_of_string argv.[1]
  val () = assert_errmsg_bool1
    (n >= 2, "The input integer needs to be a natural number.\n")
  val () = main_init () where {
    extern fun main_init (): void = "main_init"
  }
in
  offmoment();
  printf ("%.9f\n", @(energy()));
  advances (0.01, n);
  printf ("%.9f\n", @(energy()));
end // end of [main]
