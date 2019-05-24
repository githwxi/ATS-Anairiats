//
// mandelbrot.dats
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// The code is largely translated from the SML code attached below
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

machine: dml.bu.edu
command: mandelbrot 3000 > /dev/null

ATS:		    4.061u 0.014s 0:04.09 99.5% 0+0k 0+0io 0pf+0w
C(w/o sse):	    3.835u 0.026s 0:03.89 98.9%	0+0k 0+0io 0pf+0w
C(w/  sse):	    2.603u 0.014s 0:02.64 98.8%	0+0k 0+0io 0pf+0w

*)

#define i2b byte_of_int
#define i2d double_of

#define TIMES 50
macdef LIMIT2 = 2.0 * 2.0

fn mandelbrot (h: int, w: int): void = let
  fn p (x: int, y: int):<cloptr1> int = let
    val Cr = i2d (2 * x) / i2d w - 1.5
    and Ci = i2d (2 * y) / i2d h - 1.0
    fun lp (r: double, i: double, k: int):<cloptr1> int =
      let val r2 = r * r and i2 = i * i in
        if r2+i2 <= LIMIT2 then
          if k=0 then 1 else lp (r2-i2+Cr, 2.0*r*i+Ci, k-1)
        else 0
      end
  in
    lp (0.0, 0.0, TIMES)
  end // end of [p]

  fun xl (x: int, y: int, b: byte, n: natLte 8):<cloptr1> void =
    if x < w then let
      val pxy = p (x, y); val pxy = i2b pxy
    in
      if n > 0 then xl (x+1, y, (b << 1) + pxy, n-1) else (print b; xl (x+1, y, pxy, 7))
    end else begin
      print (b << n); if (y < h-1) then xl (0, y+1, i2b 0, 8)
    end // end of [if]
in 
   printf ("P4\n%i %i\n", @(h, w)); if h > 0 then xl (0, 0, i2b 0, 8)
end // end of [mandelbrot]

//

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val i = int1_of_string argv.[1]
  val () = assert_errmsg_bool1
    (i >= 2, "The input integer needs to be at least 2.\n")
in
  mandelbrot (i, i)
end // end of [main]

////

(* mandelbrot.sml
 *
 *   Mandelbrot (fractal generation) benchmark.
 *     (Loosely based on the C version.)
 *
 * Copyright (c) 2004 by The Fellowship of SML/NJ
 *
 * Author: Matthias Blume (blume@tti-c.org)
 * Modified and ported to MLton by Vesa Karvonen.
 *)

val (K, L2) = (50, 4.0)

fun out b = TextIO.output1 (TextIO.stdOut, Byte.byteToChar b)

fun mandel (h, w) =
   let fun p (x, y) =
          let val (Cr, Ci) = (real x*2.0/real w-1.5, real y*2.0/real h-1.0)
              fun lp (r, i, k) =
                  let val (r2, i2) = (r*r, i*i)
                  in r2+i2 <= L2 andalso
                     (k=0 orelse lp (r2-i2+Cr, (r+r)*i+Ci, k-1)) end
          in lp (0.0, 0.0, K) end
       fun xl (x, y, b, n) =
          if x = w then (out (Word8.<< (b, n)) ; yl (y+1))
          else let val (b, n) = if n=0w0 then (out b ; (0w0, 0w8)) else (b, n)
               in xl (x+1, y, b+b+(if p (x, y) then 0w1 else 0w0), n-0w1) end
       and yl y = if y < h then xl (0, y, 0w0, 0w8) else ()
   in app print ["P4\n", Int.toString h, " ", Int.toString w, "\n"] ; yl 0 end

val n = valOf (Int.fromString (hd (CommandLine.arguments ()))) handle _ => 600

val _ = mandel (n, n)

////

/* The Computer Language Shootout
   http://shootout.alioth.debian.org/

   contributed by Greg Buchholz

   for the debian (AMD) machine...
   compile flags:  -O3 -ffast-math -march=athlon-xp -funroll-loops

   for the gp4 (Intel) machine...
   compile flags:  -O3 -ffast-math -march=pentium4 -funroll-loops
*/

#include<stdio.h>

int main (int argc, char **argv)
{
    int w, h, bit_num = 0;
    char byte_acc = 0;
    int i, iter = 50;
    double x, y, limit = 2.0;
    double Zr, Zi, Cr, Ci, Tr, Ti;

    w = h = atoi(argv[1]);

    printf("P4\n%d %d\n",w,h);

    for(y=0;y<h;++y)
    {
        for(x=0;x<w;++x)
        {
            Zr = Zi = Tr = Ti = 0.0;
            Cr = (2.0*x/w - 1.5); Ci=(2.0*y/h - 1.0);

            for (i=0;i<iter && (Tr+Ti <= limit*limit);++i)
            {
                Zi = 2.0*Zr*Zi + Ci;
                Zr = Tr - Ti + Cr;
                Tr = Zr * Zr;
                Ti = Zi * Zi;
            }

            byte_acc <<= 1;
            if(Tr+Ti <= limit*limit) byte_acc |= 0x01;

            ++bit_num;

            if(bit_num == 8)
            {
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
            else if(x == w-1)
            {
                byte_acc <<= (8-w%8);
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
        }
    }
}

////

/*The Computer Language Shootout
  http://shootout.alioth.debian.org/

  contributed by Greg Buchholz

  Uses SSE packed doubles to run the inner loop computations in parallel.
  I don't have a machine with SSE to test with, but the assembly looks
  pretty nice.  With gcc-3.4.2 there's no difference in the assembly
  between -msse2 and -msse3, YMMV.  It uses gcc's vector extentions
  ( http://gcc.gnu.org/onlinedocs/gcc-4.0.0/gcc/Vector-Extensions.html ),
  so it will run (slowly) on hardware without SSE.

  compile (AMD):
  gcc -D_ISOC9X_SOURCE -O3 -mfpmath=sse -msse2 -march=athlon-xp
      -ffast-math -funroll-loops -o mandelbrot.gcc-3.gcc_run mandelbrot.c -lm

  compile (INTEL):
  gcc -D_ISOC9X_SOURCE -O3 -mfpmath=sse -msse2 -march=pentium4
      -ffast-math -funroll-loops -o mandelbrot.gcc-3.gcc_run mandelbrot.c -lm
*/

#include<stdio.h>
#include<math.h>
#include<fenv.h>
typedef double v2df __attribute__ ((mode(V2DF))); // vector of two double floats

int main (int argc, char **argv)
{
    int w, h, bit_num = 0;
    char byte_acc = 0;
    int i, iter = 50;
    double x, y, limit_sqr = 4.0;
    v2df Zrv, Ziv, Crv, Civ, Trv, Tiv;
    v2df zero, one, _1p5, two;
    double *Zr = (double*)&Zrv, *Zi = (double*)&Ziv,
           *Cr = (double*)&Crv, *Ci = (double*)&Civ,
           *Tr = (double*)&Trv, *Ti = (double*)&Tiv;

#define initv(name, val) *((double*)&name)   = (double) val; \
                         *((double*)&name+1) = (double) val
    initv(zero,0.0); initv(one,1.0); initv(_1p5,1.5); initv(two,2.0);

    w = h = atoi(argv[1]);

    printf("P4\n%d %d\n",w,h);

    for(y=0;y<h;++y)
    {
        for(x=0;x<w;x+=2)
        {
            Zrv = Ziv = Trv = Tiv = zero;
            *Cr = x/w;  *(Cr+1) = (x+1.0)/w;
            *Ci = y/h;  *(Ci+1) = *Ci;
            Crv = two * Crv - _1p5;
            Civ = two * Civ - one;

            for (i=0;i<iter && (islessequal( *Tr    +  *Ti,   limit_sqr) ||
                                islessequal(*(Tr+1) + *(Ti+1),limit_sqr)   ); ++i)
            {
                Ziv = two*Zrv*Ziv + Civ;
                Zrv = Trv - Tiv + Crv;
                Trv = Zrv * Zrv;
                Tiv = Ziv * Ziv;
            }

            byte_acc <<= 2;
            if(islessequal(*Tr + *Ti, limit_sqr))
                byte_acc |= 0x02;

            if(islessequal(*(Tr+1) + *(Ti+1), limit_sqr))
                byte_acc |= 0x01;

            bit_num+=2;

            if(bit_num == 8)
            {
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
            else if(x == w-1)
            {
                byte_acc <<= (8-w%8);
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
        }
    }
}
