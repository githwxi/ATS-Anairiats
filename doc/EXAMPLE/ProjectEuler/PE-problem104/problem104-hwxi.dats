//
// ProjectEuler: Problem 104
// Finding the first Fib number whose first 9 and last 9 digits are 1-9 pandigital
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun test1 (x: ulint): bool = let
  var !p_arr with pf_arr = @[int][10](0)
  fun loop {i:nat}
    (ds: &(@[int][10]), x: ulint, i: int i): bool =
    if i <= 9 then let
      val r = x mod 10UL
      val r = uint_of_ulint (r)
      val [r:int] r = uint1_of_uint (r)
      val r = int1_of_uint1 (r)
      prval () = __assert () where {
        extern prfun __assert (): [0 <= r; r < 10] void
      } // end of [prval]
    in
      if r = 0 then false
      else let
        val flag = ds.[r] in
        if (flag > 0) then false else (ds.[r] := 1; loop (ds, x / 10UL, i+1))
      end // end of [if]
    end else true
in
  loop (!p_arr, x, 1)
end // end of [test1]

(* ****** ****** *)

fun test2
  (x: &mpz_vt): bool = let
  val str = mpz_get_str (10, x)
  val [m,n:int] @(pf_gc, pf_buf | p) =  strbuf_of_strptr (str)
  val n = strbuf_length (!p)
  val () = assert (n >= 9)
  var !p_arr with pf_arr = @[int][10](0)
  val res = loop (!p_arr, !p, 0) where {
    fun loop {i:nat| i <= 9}
      (ds: &(@[int][10]), buf: &strbuf(m, n), i: int i): bool =
      if i < 9 then let
        val c = buf[i]
        val r = c - '0'
        val [r:int] r = int1_of_int (r)
        prval () = __assert () where {
          extern prfun __assert (): [0 <= r; r < 10] void
        } // end of [prval]
      in
        if r = 0 then false
        else let
          val flag = ds.[r] in
          if (flag > 0) then false else (ds.[r] := 1; loop (ds, buf, i+1))
        end // end of [if]
      end else true // end of [if]
    // end of [loop]      
  } // end of [val]
  val () = strbufptr_free @(pf_gc, pf_buf | p)
in
  res
end // end pf [test2]

(* ****** ****** *)

macdef N = 1000000000UL
fun search
  (f1: ulint, f2: ulint, n: ulint, x: &mpz_vt): ulint =
  if test1 (f1) then let
(*
    val () = (print "search: n = "; print n; print_newline ())
*)
    val () = mpz_fib_ui (x, n)
  in
    if test2 (x) then n else search (f2, (f1+f2) mod N, n+1UL, x)
  end else search (f2, (f1+f2) mod N, n+1UL, x)
// end of [search]

(* ****** ****** *)

implement
main () = () where {
  var x: mpz_vt; val () = mpz_init (x)
  val ans = search (1UL, 1UL, 1UL, x)
  val () = mpz_clear (x)
  val () = assert_errmsg (ans = 329468UL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem104-hwxi.dats] *)
