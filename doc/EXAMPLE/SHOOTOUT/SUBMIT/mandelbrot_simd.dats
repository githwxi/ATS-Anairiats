(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot mandelbrot_simd.dats
**
*)

(* ****** ****** *)

#define TIMES 50
#define LIMIT 2.0; #define LIMIT2 (LIMIT * LIMIT)

(* ****** ****** *)

staload "libc/SATS/SIMD_v2df.sats" // no dynamic loading

(* ****** ****** *)

#define i2d double_of_int
fn mandelbrot (h: int, w: int): void = let

val h_recip = 1.0 / (i2d h) and w_recip = 1.0 / (i2d w)

fun test (x: int, y: int):<cloref1> int = let
  val x2 = i2d (x << 1)
  val Cr0 = x2 * w_recip - 1.5
  val Cr1 = (x2 + 2.0) * w_recip - 1.5
  val y2 = i2d (y << 1)
  val Ci0 = y2 * h_recip - 1.0
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
    val Tri0 = v2df_get_fst (Triv) and Tri1 = v2df_get_snd (Triv)
    val Zrv_new = Trv - Tiv + Crv
    val Ziv_new = (x + x) + Civ  where { val x = Zrv * Ziv }
  in
    case+ 0 of
    | _ when Tri0 <= LIMIT2 => begin case+ 0 of
      | _ when Tri1 <= LIMIT2 => begin
          if times = 0 then 0x3 else loopv (Zrv_new, Ziv_new, times-1)
        end // end of [_ when ...]
      | _ => begin
          if times = 0 then 0x2 else let
            val Zr0_new = v2df_get_fst (Zrv_new) and Zi0_new = v2df_get_fst (Ziv_new)
          in
            loop (0x2(*eo*), Cr0, Ci0, Zr0_new, Zi0_new, times-1)
          end // end of [if]
        end // end of [_]
      end // end of [_ when ...]
    | _ => begin case+ 0 of
      | _ when Tri1 <= LIMIT2 => begin
          if times = 0 then 0x1 else let
            val Zr1_new = v2df_get_snd (Zrv_new) and Zi1_new = v2df_get_snd (Ziv_new)
          in
            loop (0x1(*eo*), Cr1, Ci1, Zr1_new, Zi1_new, times-1)
          end // end of [if]
        end // end of [_ when ...]
      | _ => 0x0 // return value
      end // end of [_]
  end // end of [loopv]
in
  loopv (v2df_0_0, v2df_0_0, TIMES)
end // end of [test]

(* ****** ****** *)

#define i2b byte_of_int

fun output
  (x: int, y: int, b: byte, n: natLte 8):<cloref1> void = begin
  case+ 0 of
  | _ when x < w => let
      val res = test (x, y); val res = i2b res
    in
      case+ 0 of
      | _ when n >= 2 => output (x + 2, y, (b << 2) + res, n - 2)
      | _ (*n=0*) => begin
          let val () = print_byte b in output (x + 2, y, res, 6) end
        end // end of [_]
    end // end of [_ when ...]
  | _ => let
      val () = print_byte (b << n); val y1 = y + 1
    in
      if (y1 < h) then output (0, y1, i2b 0, 8) else ()
    end // end of [_]
end // end of [output]

(* ****** ****** *)

in

printf ("P4\n%i %i\n", @(h, w)); if (h > 0) then output (0, 0, i2b 0, 8)

end // end of [mandelbrot]

(* ****** ****** *)

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc >= 2, "Exit: wrong command format!\n")
  val i = int1_of_string argv.[1]
  val () = assert_errmsg_bool1
    (i >= 2, "The input integer needs to be at least 2.\n")
in
  mandelbrot (i, i)
end // end of [main]

(* ****** ****** *)

(* end of [mandelbrot_simd.dats] *)
