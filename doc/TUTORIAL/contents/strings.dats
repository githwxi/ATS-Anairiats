//
// code used for illustration in strings.html
//

(* ****** ****** *)

#define NUL '\000'

(* ****** ****** *)

fn string_length {n:nat}
  (s: string n):<> size_t n = loop (s, 0) where {
  fun loop {i:nat | i <= n} .<n-i>.
    (s: string n, i: size_t i):<> size_t n =
    if string_is_at_end (s, i) then i else loop (s, i+1)
  // end of [loop]
} // end of [string_length]

(* ****** ****** *)

fn strbuf_toupper {m,n:nat}
  (s: &strbuf (m, n)):<> void = loop (s, 0) where {
  extern fun toupper (c: c1har):<> c1har = "atspre_char_toupper"
  fun loop {i:nat | i <= n} .<n-i>. (s: &strbuf (m, n), i: size_t i):<> void =
    if strbuf_is_at_end (s, i) then ()
    else let
      val () = s[i] := toupper (s[i]) in loop (s, i+1)
    end // end of [if]
} // end of [strbuf_toupper]

(* ****** ****** *)

extern fun strlen {m,n:nat} (s: &strbuf (m, n)):<> size_t n

implement strlen {m,n} (s) = let
  stadef bsz = sizeof(byte)
  macdef bsz = sizeof<byte>
  fun loop {m,n:nat} {l:addr} {ofs:int} .<m>. (
      pf: !strbuf (m, n) @ l
    , pf_mul: MUL (n, bsz, ofs)
    | p: ptr l
    ) :<> ptr (l + ofs) = let
    prval (pf1, pf2) = strbuf_v_uncons (pf)
    val c = !p
  in
    if (c = NUL) then let
      prval strbufopt_v_none pf2 = pf2
      prval MULbas () = pf_mul
    in
      pf := strbuf_v_null (pf1, pf2); p
    end else let
      prval () = eqsize_byte_char ()
      prval strbufopt_v_some pf2 = pf2
      prval pf1_mul = mul_add_const {~1} (pf_mul)
      val p_end = loop (pf2, pf1_mul | p+bsz)
    in
      pf := strbuf_v_cons (pf1, pf2); p_end
    end // end of [if]
  end // end of [loop]
  val p_beg = &s
  prval pf_mul = mul_istot {n,bsz} ()
  val p_end = loop (view@ s, pf_mul | p_beg)
  prval () = eqsize_byte_one () where {
    extern praxi eqsize_byte_one (): [bsz == 1] void
  } // end of [val]
  prval () = mul_elim {n,1} (pf_mul)
in
  size1_of_ptrdiff1 (p_end - p_beg)
end // end of [strlen]

(* ****** ****** *)

extern fun strbuf_initialize_cloptr
  {m,n:nat | n < m} {l:addr} (
    pf_buf: !b0ytes m @ l >> strbuf (m, n) @ l
  | p_buf: ptr l, n: size_t n, f: !sizeLt n -<cloptr> c1har
  ) :<> void

implement strbuf_initialize_cloptr {m,n}
  (pf_buf | p_buf, n, f) = loop (pf_buf | p_buf, f, 0) where {
  fun loop {i:nat | i <= n} {l:addr} .<n-i>. (
      pf: !b0ytes (m-i) @ l >> strbuf (m-i, n-i) @ l
    | p: ptr l, f: !sizeLt n -<cloptr> c1har, i: size_t i)
    :<cloref> void = let
    prval () = eqsize_byte_char ()
    prval (pf1, pf2) = array_v_uncons {byte?} (pf)
    prval pf1 = char_v_of_b0yte_v (pf1)
  in
    if i < n then let
      val () = !p := f (i)
      val () = loop (pf2 | p + sizeof<byte>, f, i + 1)
      prval () = pf := strbuf_v_cons (pf1, pf2)
    in
      // empty
    end else let
      val () = !p := NUL
      prval () = pf := strbuf_v_null (pf1, pf2)
    in
      // empty
    end // end of [if]
  end // end of [loop]
} // end of [val]

(* ****** ****** *)

extern fun string_make_substring
  {n:int} {st,ln:nat | st + ln <= n}
  (str: string n, st: size_t st, ln: size_t ln):<> string ln

implement string_make_substring (str, st, ln) = let
  val (pf_gc, pf_buf | p_buf) = malloc_gc (ln + 1)
  val () = strbuf_initialize_cloptr (pf_buf | p_buf, ln, lam (i) => str[st + i])
in
  string1_of_strbuf @(pf_gc, pf_buf | p_buf)
end // end of [string_make_substring]

(* ****** ****** *)

(* end of [strings.dats] *)
