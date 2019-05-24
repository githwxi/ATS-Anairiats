//
// ProjectEuler: Problem 42
// Finding the number of the triangle words in a given list of common words
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "libc/SATS/stdio.sats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

typedef word = string
viewtypedef wordlst = List_vt (word)

fun getWord
  (fil: &FILE r): word = let
  val i = fgetc_err (file_mode_lte_r_r | fil)
  val QUOTE = (int_of)'"'
  val () = assert_errmsg (i = QUOTE, #LOCATION)
  val cs = loop (fil, list_vt_nil) where {
    fun loop
      (fil: &FILE r, cs: List_vt char):<cloref1> List_vt char = let
      val i = fgetc_err (file_mode_lte_r_r | fil)
    in
      if i <> QUOTE then let
        val c = (char_of_int)i
        val () = assert_errmsg (char_isalpha(c), #LOCATION)
      in
        loop (fil, list_vt_cons (c, cs))
      end else cs
    end // end of [loop]
  } // end of [val]
  val n = list_vt_length (cs)
  val sb = string_make_list_rev_int (__cast cs, n) where {
    extern castfn __cast {n:nat} (xs: !list_vt (char, n)):<> list (char, n)
  } // end of [val]
  val () = list_vt_free (cs)
in
  string_of_strbuf (sb)
end // end of [getWord]

(* ****** ****** *)

fun getRest (fil: &FILE r): wordlst = let
  fun loop (fil: &FILE r, xs: wordlst): wordlst = let
    val i = fgetc_err (file_mode_lte_r_r | fil)
  in
    if (i = int_of(',')) then let
      val x = getWord (fil) in loop (fil, list_vt_cons (x, xs))
    end else xs
  end // end of [loop]
  val xs = loop (fil, list_vt_nil)
in
  list_vt_reverse (xs)
end // end of [getRest]

(* ****** ****** *)

val theWords = let
  val (pf | p) = fopen_exn ("words.txt", file_mode_r)
  val x = getWord (!p)
  val xs = getRest (!p)
  val () = fclose_exn (pf | p)
  val xs = list_vt_cons {word} (x, xs)
  var !p_clo = @lam (x1: &word, x2: &word): Sgn =<clo> compare (x1, x2)
in
  list_vt_mergesort<word> (xs, !p_clo)
end // end of [theWords]

(* ****** ****** *)

fun evalWord
  (x: word): int = let
  val [n:int] x = string1_of_string (x)
  val n = string1_length (x)
  fun loop {i:nat | i <= n} .<n-i>.
    (i: int i, res: int):<cloref> int =
    if i < n then let
      val c = x[i]
    in
      loop (i+1, res + (c - 'A') + 1)
    end else res
  // end of [loop]
in
  loop (0, 0)
end // end of [evalWord]

(* ****** ****** *)
//
// HX:
// n(n+1) / 2 = x => n^2 + n - 2x =0
// n = (isqrt (1 + 8x) - 1) / 2
//

fun isqrt (x: int): int = int_of (sqrt (x + 0.5))

fun isTriangle
  (x: int): bool = let
  val d = 8 * x + 1
  val xq = isqrt (d) in
  if xq * xq = d then (xq - 1) mod 2 = 0 else false
end // end of [isTriangle]

val () = assert (isTriangle (1))
val () = assert (~isTriangle (2))
val () = assert (isTriangle (3))
val () = assert (~isTriangle (4))
val () = assert (~isTriangle (5))
val () = assert (isTriangle (6))
val () = assert (~isTriangle (7))
val () = assert (~isTriangle (8))
val () = assert (~isTriangle (9))
val () = assert (isTriangle (10))
val () = assert (isTriangle (55))

(* ****** ****** *)

val () = () where {
//
val ans = loop (theWords, 1, 0) where {
  fun loop (xs: wordlst, i: int, res: int): int =
    case+ xs of
    | ~list_vt_cons (x, xs) => let
        val n = evalWord (x) in
        if isTriangle (n) then loop (xs, i+1, res+1) else loop (xs, i+1, res)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => res
  // end of [loop]
} // end of [val]
//
val () = assert_errmsg (ans = 162, #LOCATION)
val () = (print "ans = "; print ans; print_newline ())
//
} // end of [val]

implement main () = ()

(* ****** ****** *)

(* end of [problem42-hwxi.dats] *)
