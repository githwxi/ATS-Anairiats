//
// nbody.dats
//
// The code is directly translated from the ML version
// attached below. Its performance is much better than
// ML. It is only 10% slower than the C version that is
// attached at the end of this file.
//
// Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

machine: dml.bu.edu
command: nbody 20000000

output:

-0.169075164
-0.169031665

ATS:	21.575u 0.017s 0:21.84 98.8%	0+0k 0+0io 0pf+0w
C:	19.568u 0.002s 0:19.60 99.7%	0+0k 0+0io 0pf+0w

*)

staload M = "libc/SATS/math.sats"

%{^

typedef ats_ptr_type darray ;

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

#define :: cons
datatype bodylst (int) =
  | nil (0) | {n:nat} cons (n+1) of (body, bodylst n)

#define N 5
val theBodies: bodylst N =
  sun :: jupiter :: saturn :: neptune :: uranus :: nil ()

val x: darray N = darray_make (N)
val y: darray N = darray_make (N)
val z: darray N = darray_make (N)

val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N}
    (i: int i, bs: bodylst j): void =
    if i < N then
      let val b :: bs = bs in
        x[i] := b.0 ;
        y[i] := b.1 ;
        z[i] := b.2 ;
        loop (i+1, bs)
      end
    else ()
}

val DAYS_PER_YEAR: double = 365.24

val vx: darray N = darray_make (N)
val vy: darray N = darray_make (N)
val vz: darray N = darray_make (N)

val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N}
    (i: int i, bs: bodylst j): void =
    if i < N then
      let val b :: bs = bs in
        vx[i] := b.3 * DAYS_PER_YEAR ;
        vy[i] := b.4 * DAYS_PER_YEAR ;
        vz[i] := b.5 * DAYS_PER_YEAR ;
        loop (i+1, bs)
      end
    else ()
}

dynload "libc/DATS/math.dats"

val PI = $M.M_PI
val SOLAR_MASS: double = 4.0 * PI * PI

val m: darray N = darray_make (N)
val () = loop (0, theBodies) where {
  fun loop {i,j:nat | i+j == N}
    (i: int i, bs: bodylst j): void =
    if i < N then
      let val b :: bs = bs in
        m[i] := b.6 * SOLAR_MASS ;
        loop (i+1, bs)
      end
    else ()
}

(* one step *)
fn advance (dt: double): void =
  let
    fun pl (i: natLte N):<cloptr1> void =
      if i < N then begin
        x[i] := x[i]+dt*vx[i];
        y[i] := y[i]+dt*vy[i];
        z[i] := z[i]+dt*vz[i];
        pl (i+1)
      end

    fun vl (i: Nat, j: Nat):<cloptr1> void =
      if i < N then
        if j < N then
          let
            val dx = x[i] - x[j]
            and dy = y[i] - y[j]
            and dz = z[i] - z[j]
            val dist = $M.sqrt (dx * dx + dy * dy + dz * dz)
            val mag = dt / (dist * dist * dist)
            val mi = m[i] * mag and mj = m[j] * mag
          in
            vx[i] := vx[i] - dx * mj ; vx[j] := vx[j] + dx * mi ;
            vy[i] := vy[i] - dy * mj ; vy[j] := vy[j] + dy * mi ;
            vz[i] := vz[i] - dz * mj ; vz[j] := vz[j] + dz * mi ;
            vl (i, j+1)
          end
        else vl (i+1, i+2)
      else pl 0
  in
    vl (0, 1)
  end

(* calculate initial velocity for the sun *)
fn offmoment (): void =
  let
    fun loop (i: natLte N, px: double, py: double, pz: double): void =
      if i < N then
        let val mi = m[i] in
          loop (i+1, px+vx[i]*mi, py+vy[i]*mi, pz+vz[i]*mi)
        end
      else begin
        vx[0] := ~px / SOLAR_MASS;
        vy[0] := ~py / SOLAR_MASS;
        vz[0] := ~pz / SOLAR_MASS;
      end
  in
    loop (1, 0.0, 0.0, 0.0)
  end

fn energy (): double =
  let // mutual recursion
    fn* l (i: natLt N, j: natLte N, e: double): double =
      if j < N then
        let
          val dx = x[i] - x[j]
          and dy = y[i] - y[j]
          and dz = z[i] - z[j]
          val dist = $M.sqrt (dx * dx + dy * dy + dz * dz)
        in
          l (i, j+1, e-m[i]*m[j]/dist)
        end
      else l0 (i+1, e)

    and l0 (i: natLte N, e: double): double =
      if i < N then
        let val vxi = vx[i] and vyi = vy[i] and vzi = vz[i] in
          l (i, i+1, e + 0.5*m[i]*(vxi*vxi+vyi*vyi+vzi*vzi))
        end
      else e
  in
    l0 (0, 0.0)
  end

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

%{

ats_ptr_type
darray_make (ats_int_type n) {
  return malloc(n * sizeof(ats_double_type)) ;
}

ats_void_type
darray_free (ats_ptr_type A) { free (A) ; return ; }

ats_double_type
darray_get (ats_ptr_type A, ats_int_type i) {
  return ((ats_double_type *)A)[i] ;
}

ats_void_type
darray_set (ats_ptr_type A, ats_int_type i, ats_double_type f) {
  ((ats_double_type *)A)[i] = f ; return ;
}

%}

////

(* nbody.sml
 *   The Computer Language Shootout
 *   http://shootout.alioth.debian.org/
 *   (Loosely based on the Oberon version.)
 *
 * Copyright (c) 2004 by The Fellowship of SML/NJ
 *
 * Author: Matthias Blume (blume@tti-c.org)
 * Ported to MLton by Vesa Karvonen.
 *)

infix 8 $
val op$ = Array.sub
infix 3 <-
fun (a, i) <- x = Array.update (a, i, x)

val SOLAR_MASS = 4.0 * Math.pi * Math.pi
val DAYS_PER_YEAR = 365.24

(* sun, jupiter, saturn, neptune, uranus *)

val N = length bodies
fun sm x = x * SOLAR_MASS
fun dpy x = x * DAYS_PER_YEAR
fun get sel = Array.fromList (map sel bodies)
val (x, y, z) = (get #1, get #2, get #3)
val (vx, vy, vz) = (get (dpy o #4), get (dpy o #5), get (dpy o #6))
val m = get (sm o #7)

(* one step *)
fun advance dt =
    let fun pl i = if i>=N then ()
                   else ((x, i) <- x$i+dt*vx$i
                       ; (y, i) <- y$i+dt*vy$i
                       ; (z, i) <- z$i+dt*vz$i
                       ; pl (i+1))
        fun vl (i, j) =
            if i>=N then pl 0
            else if j>=N then vl (i+1, i+2)
            else let val (dx, dy, dz) = (x$i-x$j, y$i-y$j, z$i-z$j)
                     val dist = Math.sqrt(dx*dx+dy*dy+dz*dz)
                     val mag = dt/(dist*dist*dist)
                     val (mi, mj) = (m$i*mag, m$j*mag)
                 in (vx, i) <- vx$i-dx*mj ; (vx, j) <- vx$j+dx*mi
                  ; (vy, i) <- vy$i-dy*mj ; (vy, j) <- vy$j+dy*mi
                  ; (vz, i) <- vz$i-dz*mj ; (vz, j) <- vz$j+dz*mi
                  ; vl (i, j+1)
                 end
    in vl (0, 1) end

(* calculate initial velocity for the sun *)
fun offmoment () =
    let fun %v = ~v / SOLAR_MASS
        fun loop (i, px, py, pz) =
            if i>=N then ((vx, 0) <- %px ; (vy, 0) <- %py ; (vz, 0) <- %pz)
            else loop (i+1, px+vx$i*m$i, py+vy$i*m$i, pz+vz$i*m$i)
    in loop (1, 0.0, 0.0, 0.0) end

fun energy () =
    let fun l (i, j, e) =
            if j >= N then l0 (i+1, e)
            else let val (dx, dy, dz) = (x$i-x$j, y$i-y$j, z$i-z$j)
                     val dist = Math.sqrt(dx*dx+dy*dy+dz*dz)
                 in l (i, j+1, e-m$i*m$j/dist) end
        and l0 (i, e) =
            if i>=N then e
            else let val (x, y, z) = (vx$i, vy$i, vz$i)
                 in l (i, i+1, e + 0.5*m$i*(x*x+y*y+z*z)) end
    in l0 (0, 0.0) end

fun addloop i = if i > 0 then (advance 0.01 ; addloop (i-1)) else ()

fun pr x = app print [(String.translate (fn #"~" => "-" | c => str c) o
                       Real.fmt (StringCvt.FIX (SOME 9))) x, "\n"]

val n = valOf (Int.fromString (hd (CommandLine.arguments ()))) handle _ => 1

val _ = (offmoment () ; pr (energy ()) ; addloop n ; pr (energy ()))

////

/*
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * contributed by Christoph Bauer
 *
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define pi 3.141592653589793
#define solar_mass (4 * pi * pi)
#define days_per_year 365.24

struct planet {
  double x, y, z;
  double vx, vy, vz;
  double mass;
};

void advance(int nbodies, struct planet * bodies, double dt)
{
  int i, j;

  for (i = 0; i < nbodies; i++) {
    struct planet * b = &(bodies[i]);
    for (j = i + 1; j < nbodies; j++) {
      struct planet * b2 = &(bodies[j]);
      double dx = b->x - b2->x;
      double dy = b->y - b2->y;
      double dz = b->z - b2->z;
      double distance = sqrt(dx * dx + dy * dy + dz * dz);
      double mag = dt / (distance * distance * distance);
      b->vx -= dx * b2->mass * mag;
      b->vy -= dy * b2->mass * mag;
      b->vz -= dz * b2->mass * mag;
      b2->vx += dx * b->mass * mag;
      b2->vy += dy * b->mass * mag;
      b2->vz += dz * b->mass * mag;
    }
  }
  for (i = 0; i < nbodies; i++) {
    struct planet * b = &(bodies[i]);
    b->x += dt * b->vx;
    b->y += dt * b->vy;
    b->z += dt * b->vz;
  }
}

double energy(int nbodies, struct planet * bodies)
{
  double e;
  int i, j;

  e = 0.0;
  for (i = 0; i < nbodies; i++) {
    struct planet * b = &(bodies[i]);
    e += 0.5 * b->mass * (b->vx * b->vx + b->vy * b->vy + b->vz * b->vz);
    for (j = i + 1; j < nbodies; j++) {
      struct planet * b2 = &(bodies[j]);
      double dx = b->x - b2->x;
      double dy = b->y - b2->y;
      double dz = b->z - b2->z;
      double distance = sqrt(dx * dx + dy * dy + dz * dz);
      e -= (b->mass * b2->mass) / distance;
    }
  }
  return e;
}

void offset_momentum(int nbodies, struct planet * bodies)
{
  double px = 0.0, py = 0.0, pz = 0.0;
  int i;
  for (i = 0; i < nbodies; i++) {
    px += bodies[i].vx * bodies[i].mass;
    py += bodies[i].vy * bodies[i].mass;
    pz += bodies[i].vz * bodies[i].mass;
  }
  bodies[0].vx = - px / solar_mass;
  bodies[0].vy = - py / solar_mass;
  bodies[0].vz = - pz / solar_mass;
}

#define NBODIES 5
struct planet bodies[NBODIES] = {
  {                               /* sun */
    0, 0, 0, 0, 0, 0, solar_mass
  },
  {                               /* jupiter */
    4.84143144246472090e+00,
    -1.16032004402742839e+00,
    -1.03622044471123109e-01,
    1.66007664274403694e-03 * days_per_year,
    7.69901118419740425e-03 * days_per_year,
    -6.90460016972063023e-05 * days_per_year,
    9.54791938424326609e-04 * solar_mass
  },
  {                               /* saturn */
    8.34336671824457987e+00,
    4.12479856412430479e+00,
    -4.03523417114321381e-01,
    -2.76742510726862411e-03 * days_per_year,
    4.99852801234917238e-03 * days_per_year,
    2.30417297573763929e-05 * days_per_year,
    2.85885980666130812e-04 * solar_mass
  },
  {                               /* uranus */
    1.28943695621391310e+01,
    -1.51111514016986312e+01,
    -2.23307578892655734e-01,
    2.96460137564761618e-03 * days_per_year,
    2.37847173959480950e-03 * days_per_year,
    -2.96589568540237556e-05 * days_per_year,
    4.36624404335156298e-05 * solar_mass
  },
  {                               /* neptune */
    1.53796971148509165e+01,
    -2.59193146099879641e+01,
    1.79258772950371181e-01,
    2.68067772490389322e-03 * days_per_year,
    1.62824170038242295e-03 * days_per_year,
    -9.51592254519715870e-05 * days_per_year,
    5.15138902046611451e-05 * solar_mass
  }
};

int main(int argc, char ** argv)
{
  int n = atoi(argv[1]);
  int i;

  offset_momentum(NBODIES, bodies);
  printf ("%.9f\n", energy(NBODIES, bodies));
  for (i = 1; i <= n; i++)
    advance(NBODIES, bodies, 0.01);
  printf ("%.9f\n", energy(NBODIES, bodies));
  return 0;
}

