(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** This code is a direct translation from a C submission by
** Sean Bartell, which is based on the Scheme PLT #4 version
**
** compilation command:
**   atscc -O3 -fomit-frame-pointer pidigits.dats -o pidigits -lgmp
*)

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

var tmp: mpz_vt with pf_tmp
viewdef v_tmp = mpz_vt @ tmp
val () = mpz_init (tmp)

var acc: mpz_vt with pf_acc
viewdef v_acc = mpz_vt @ acc
val () = mpz_init_set (acc, 0)

var num: mpz_vt with pf_num
viewdef v_num = mpz_vt @ num
val () = mpz_init_set (num, 1)

var den: mpz_vt with pf_den
viewdef v_den = mpz_vt @ den
val () = mpz_init_set (den, 1)

(* ****** ****** *)

viewdef v_all = @(v_tmp, v_acc, v_num, v_den)
prval pf_all = @(pf_tmp, pf_acc, pf_num, pf_den)
prval pfbox_all =
  vbox_make {v_all} (pf_all) where {
  extern prfun vbox_make {v:view} (pf: v): vbox (v)
} // end of [val]

(* ****** ****** *)

fn extract_digit (
    pf_tmp: !v_tmp, pf_acc: !v_acc, pf_num: !v_num, pf_den: !v_den
  | nth: uint
  ) :<(*pure*)> uint = let
  val () = begin
    mpz_mul (tmp, num, nth); mpz_add (tmp, acc); mpz_tdiv_q (tmp, den)
  end // end of [val]
in
  mpz_get_uint (tmp)
end // end of [extract_digit]

(* ****** ****** *)

fn next_term (
    pf_tmp: !v_tmp, pf_acc: !v_acc, pf_num: !v_num, pf_den: !v_den
  | k: uint
  ) :<(*pure*)> void = () where {
  val y2 = k * 2U + 1U (* : uint *); val () = begin
    mpz_addmul (acc, num, 2U); mpz_mul (acc, y2); mpz_mul (num, k); mpz_mul (den, y2)
  end // end of [val]
} // end of [next_term]

(* ****** ****** *)

fn eliminate_digit (
    pf_acc: !v_acc, pf_num: !v_num, pf_den: !v_den | d: uint
  ) :<(*pure*)> void = () where {
  val () = begin
    mpz_submul (acc, den, d); mpz_mul (acc, 10); mpz_mul (num, 10)
  end // end of [val]
} // end of [eliminate_digit]

(* ****** ****** *)

fn pidigits (
    pf_tmp: !v_tmp, pf_acc: !v_acc, pf_num: !v_num, pf_den: !v_den
  | n: int
  ) : void = () where {
  var i: int = 0 and m: int = 0
  var d: uint with pf_d = 0U and k: uint with pf_k = 0U
  val () = while (true) let
    fun loop (
        pf_tmp: !v_tmp, pf_acc: !v_acc, pf_num: !v_num, pf_den: !v_den
      , pf_k: !uint @ k, pf_d: !uint @ d
      | (*none*)
      ) :<cloref1> void = let
      val () = k := k + 1U
      val () = next_term (pf_tmp, pf_acc, pf_num, pf_den | k)
      val sgn = mpz_cmp (num, acc)
    in
      if sgn > 0 then loop
        (pf_tmp, pf_acc, pf_num, pf_den, pf_k, pf_d | (*none*))
      else let
        val () =
          d := extract_digit (pf_tmp, pf_acc, pf_num, pf_den | 3U)
        // end of [val]
        val d4 = extract_digit (pf_tmp, pf_acc, pf_num, pf_den | 4U)
      in
        if d <> d4 then loop
          (pf_tmp, pf_acc, pf_num, pf_den, pf_k, pf_d | (*none*))
        // end of [if]
      end // end of [if]
    end (* end of [loop] *)
    val () = loop
      (pf_tmp, pf_acc, pf_num, pf_den, pf_k, pf_d | (*none*))
    // end of [val]
    val () = print (char_of_uint (d + uint_of_char '0'))
    val () = i := i + 1
    val () = m := i mod 10
    val () = if m = 0 then printf ("\t:%d\n", @(i))
    val () = if (i >= n) then break
    val () = eliminate_digit (pf_acc, pf_num, pf_den | d)
  in
    // empty
  end // end of [val]
  
  val () = if (m > 0) then let
    fun loop (i: int): void = if i > 0 then (print (' '); loop (i-1))
  in
    loop (10-m); printf ("\t:%d\n", @(n))
  end // end of [val]
} (* end of [pidigits] *)

(* ****** ****** *)

implement main (argc, argv) = let
  val n = (if argc > 1 then int_of_string (argv.[1]) else 27): int
  prval vbox pf_all = pfbox_all
in
  $effmask_ref (pidigits (pf_all.0, pf_all.1, pf_all.2, pf_all.3 | n))
end // end of [main]
  
(* ****** ****** *)

(* end of [pidigits2.dats] *)

////

/* The Computer Language Shootout
  http://shootout.alioth.debian.org/

  contributed by Sean Bartell
  based on the Scheme PLT #4 version
  with a few things from the C GNU gcc version
*/

#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>

static mpz_t numer, accum, denom, tmp;

static unsigned int extract_digit(unsigned int n)
{
  mpz_mul_ui(tmp, numer, n);
  mpz_add(tmp, tmp, accum);
  mpz_tdiv_q(tmp, tmp, denom);
  return mpz_get_ui(tmp);
}

static void next_term(unsigned int k)
{
  unsigned int y2 = k*2 + 1;
  mpz_addmul_ui(accum, numer, 2);
  mpz_mul_ui(accum, accum, y2);
  mpz_mul_ui(numer, numer, k);
  mpz_mul_ui(denom, denom, y2);
}

static void eliminate_digit(unsigned int d)
{
  mpz_submul_ui(accum, denom, d);
  mpz_mul_ui(accum, accum, 10);
  mpz_mul_ui(numer, numer, 10);
}

static void pidigits(unsigned int n)
{
  unsigned int d, i = 0, k = 0, m;
  mpz_init(tmp);
  mpz_init_set_ui(numer, 1);
  mpz_init_set_ui(accum, 0);
  mpz_init_set_ui(denom, 1);

  for(;;)
  {
    do {
      k++;
      next_term(k);
    } while(mpz_cmp(numer, accum)>0
        || (d = extract_digit(3)) != extract_digit(4));

    putchar(d + '0');

    i++;
    m = i%10;
    if(m == 0)
      printf("\t:%d\n", i);
    if(i >= n)
      break;
    eliminate_digit(d);
  }

  if(m) {
    m = 10 - m;
    while(m--)
      putchar(' ');
    printf("\t:%d\n", n);
  }
}

int main(int argc, char **argv)
{
  pidigits(argc > 1 ? atoi(argv[1]) : 27);
  return 0;
}
