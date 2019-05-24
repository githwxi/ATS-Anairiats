//
// ProjectEuler: Problem 22
// Finding the total of all the name scores for some given names
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

typedef name = string
viewtypedef namelst = List_vt (name)

fun getName
  (fil: &FILE r): name = let
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
end // end of [getName]

(* ****** ****** *)

fun getRest (fil: &FILE r): namelst = let
  fun loop (fil: &FILE r, xs: namelst): namelst = let
    val i = fgetc_err (file_mode_lte_r_r | fil)
  in
    if (i = int_of(',')) then let
      val x = getName (fil) in loop (fil, list_vt_cons (x, xs))
    end else xs
  end // end of [loop]
  val xs = loop (fil, list_vt_nil)
in
  list_vt_reverse (xs)
end // end of [getRest]

(* ****** ****** *)

val theNames = let
  val (pf | p) = fopen_exn ("names.txt", file_mode_r)
  val x = getName (!p)
  val xs = getRest (!p)
  val () = fclose_exn (pf | p)
  val xs = list_vt_cons {name} (x, xs)
  var !p_clo = @lam (x1: &name, x2: &name): Sgn =<clo> compare (x1, x2)
in
  list_vt_mergesort<name> (xs, !p_clo)
end // end of [theNames]

(* ****** ****** *)

fun evalName
  (x: name): int = let
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
end // end of [evalName]

(* ****** ****** *)

val () = () where {
//
val ans = loop (theNames, 1, 0ULL) where {
  fun loop (xs: namelst, i: int, res: ullint): ullint =
    case+ xs of
    | ~list_vt_cons (x, xs) => let
        val res = res + ullint_of (i * evalName x) in loop (xs, i+1, res)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => res
  // end of [loop]
} // end of [val]
//
val () = assert_errmsg (ans = 871198282ULL, #LOCATION)
val () = (print "ans = "; print ans; print_newline ())
//
} // end of [val]

implement main () = ()

(* ****** ****** *)

(* end of [problem22-hwxi.dats] *)
