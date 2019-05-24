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

#define N 5

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
  fun loop {i,j:nat | i+j == N}
    (i: int i, bs: bodylst j): void =
    if i < N then let
      val+ b :: bs = bs
    in
      vx[i] := b.3 * DAYS_PER_YEAR ;
      vy[i] := b.4 * DAYS_PER_YEAR ;
      vz[i] := b.5 * DAYS_PER_YEAR ;
      loop (i+1, bs)
    end
}

dynload "libc/DATS/math.dats"

val m: darray N = darray_make (N)
val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N}
    (i: int i, bs: bodylst j): void =
    if i < N then let
      val+ b :: bs = bs
    in
      m[i] := b.6 * SOLAR_MASS; loop (i+1, bs)
    end
}

(* one step *)

fn advance (dt: double): void = let
  fun pl (dt: double, i: natLte N): void =
    if i < N then begin
      x[i] := x[i]+dt*vx[i]; y[i] := y[i]+dt*vy[i]; z[i] := z[i]+dt*vz[i];
      pl (dt, i+1)
    end
  fun vl (dt: double, i: Nat, j: Nat): void =
    if i < N then
      if j < N then let
        val dx = x[i] - x[j] and dy = y[i] - y[j] and dz = z[i] - z[j]
        val dist2 = dx * dx + dy * dy + dz * dz
        val dist = $M.sqrt (dist2); val mag = dt / (dist * dist2)
        val mi = m[i] * mag and mj = m[j] * mag
      in
        vx[i] := vx[i] - dx * mj ; vx[j] := vx[j] + dx * mi ;
        vy[i] := vy[i] - dy * mj ; vy[j] := vy[j] + dy * mi ;
        vz[i] := vz[i] - dz * mj ; vz[j] := vz[j] + dz * mi ;
        vl (dt, i, j+1)
      end else begin
        vl (dt, i+1, i+2)
      end
    else begin
      pl (dt, 0)
    end // end of [if]
in
  vl (dt, 0, 1)
end // end of [advance]

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

fun advances (i: Nat): void =
  if i > 0 then (advance 0.01 ; advances (i-1)) else ()

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val n = int1_of_string argv.[1]
  val () = assert_errmsg_bool1
    (n >= 2, "The input integer needs to be a natural number.\n")
in
  offmoment();
  printf ("%.9f\n", @(energy()));
  advances n;
  printf ("%.9f\n", @(energy()));
end // end of [main]
