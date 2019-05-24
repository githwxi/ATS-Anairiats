(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats"
staload "libc/SATS/string.sats"
staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

%{^

typedef ats_ptr_type ats_string_type ;
typedef struct { char *ptr ; int len ; } ptr_len_struct ;
typedef ptr_len_struct symbol_t ;

%}

(* ****** ****** *)

abstype dna_t // boxed type
abst@ype symbol_t = $extype "symbol_t"

(* ****** ****** *)

extern fun print_symbol (sym: symbol_t): void = "print_symbol"

extern fun symbol_make_dnaseg
  (dna: dna_t, off: int, len: int): symbol_t = "symbol_make_dnaseg"
extern fun symbol_make_strint
  {n:nat} (str: string n, n: int n): symbol_t = "symbol_make_strint"

extern fun cmp_symbol_symbol
  (sym1: symbol_t, sym2: symbol_t):<> Sgn = "cmp_symbol_symbol"

%{$

ats_void_type print_symbol (symbol_t sym) {
  char *ptr ; int len ;
  ptr = sym.ptr ; len = sym.len ;
  while (len > 0) { fputc (*ptr, stdout) ; --len ; ++ptr ; }
  return ;
} /* print_symbol */

symbol_t symbol_make_strint (ats_ptr_type str, ats_int_type len) {
  symbol_t sym ;
  sym.ptr = (char*)str ; sym.len = len ;
  return sym ;
}

symbol_t symbol_make_dnaseg
  (ats_ptr_type dna, ats_int_type off, ats_int_type len) {
  symbol_t sym ;
  sym.ptr = ((char*)dna)+off ; sym.len = len ;
  return sym ;
}

ats_bool_type cmp_symbol_symbol (symbol_t sym1, symbol_t sym2) {
  int len1, len2, len, ans ;
  len1 = sym1.len ; len2 = sym2.len ;
  len = (len1 <= len2 ? len1 : len2) ;
  ans = strncmp(sym1.ptr, sym2.ptr, len) ;
  if (!ans) {
    if (len < len1) return  1 ;
    if (len < len2) return -1 ;
    return 0 ;
  }
  return ans ;
}

%}

(* ****** ****** *)

// a linear datatype
dataviewtype frqlst = FRQLSTnil | FRQLSTcons of (symbol_t, float, frqlst)

fun frqlst_sort (frqs: frqlst): frqlst = let
  fun ins (sym: symbol_t, f: float, frqs: frqlst): frqlst =
    case+ frqs of
    | FRQLSTcons (sym1, f1, !frqs1) =>
        if f >= f1 then begin
          fold@ frqs; FRQLSTcons (sym, f, frqs)
        end else begin
          !frqs1 := ins (sym, f, !frqs1); fold@ frqs; frqs
        end // end of [if]
    | FRQLSTnil () => begin
        fold@ frqs; FRQLSTcons (sym, f, frqs)
      end
in
  case+ frqs of
  | ~FRQLSTcons (sym, f, frqs) => ins (sym, f, frqlst_sort frqs)
  | ~FRQLSTnil () => FRQLSTnil ()
end // end of [frqlst_sort]    

fun print_free_frqlst (kfs: frqlst): void = case+ kfs of
  | ~FRQLSTcons (k, f, kfs) => begin
      print_symbol k; printf (" %.3f\n", @(double_of f)); print_free_frqlst kfs
    end // end of [FRQLSTcons]
  | ~FRQLSTnil () => ()
// end of [print_free_frqlst]

(* ****** ****** *)

staload MS = "funmset_avltree.dats"

(* ****** ****** *)

fn cmp_symbol_symbol_cloref
  (sym1: symbol_t, sym2: symbol_t):<cloref> Sgn =
  cmp_symbol_symbol (sym1, sym2)

(* ****** ****** *)

fn dna_count {n,k:nat | k <= n}
  (dna: dna_t, n: int n, k: int k): $MS.mset_t symbol_t = let
  val ms = $MS.funmset_empty {symbol_t} ()
  val nk = n - k
  fun loop {i:nat}
    (ms: $MS.mset_t symbol_t, i: int i)
    :<cloref1> $MS.mset_t symbol_t =
    if i <= nk then let
      val sym = symbol_make_dnaseg (dna, i, k)
      val ms = $MS.funmset_insert (ms, sym, cmp_symbol_symbol_cloref)
    in
      loop (ms, i+1)
    end else begin
      ms // return value
    end // end of [if]
in
  loop (ms, 0)
end // end of [dna_count]

(* ****** ****** *)

fn write_frequencies {n,k:nat | k <= n}
  (dna: dna_t, n: int n, k: int k): void = let
  val ms = dna_count (dna, n, k)
  val total = $MS.funmset_size (ms)
  val ftotal = float_of total
  var frqs: frqlst = FRQLSTnil (); viewdef V2 = frqlst @ frqs
  var !p_f2 = @lam (pf: !V2 | k: symbol_t, cnt: int): void =<clo> let
    val fval = 100 * (float_of cnt) / ftotal in frqs := FRQLSTcons (k, fval, frqs)
  end // end of [f2]
  val () = $MS.funmset_foreach_clo {V2} (view@ frqs | ms, !p_f2)
in
  print_free_frqlst (frqlst_sort frqs)
end // end of [write_frequencies]

(* ****** ****** *)

macdef sz2i = int1_of_size1

fn write_count {n,k:nat}
  (dna: dna_t, n: int n, seq: string k): void = let
  val k = string1_length seq
  val k = (sz2i)k
  val () = assert (k <= n)
  val ms = dna_count (dna, n, k)
  val sym = symbol_make_strint (seq, k)
  val cnt = begin
    $MS.funmset_member<symbol_t> (ms, sym, cmp_symbol_symbol_cloref)
  end // end of [val]
in
  printf ("%d\t%s\n", @(cnt, seq))
end // end of [write_count]

(* ****** ****** *)

extern fun getline (): string = "__getline"
extern fun getrest (sz: &size_t? >> size_t n): #[n:nat] string n = "__getrest"

%{$

#define LINEBUFSZ 1024
char theLineBuffer[LINEBUFSZ] ;
ats_ptr_type __getline () {
  void *ptr = fgets (theLineBuffer, LINEBUFSZ, stdin) ; return theLineBuffer ;
} /* end of [getline] */

#define RESTBUFSZ (128 * 1024 * 1024)
char theRestBuffer[RESTBUFSZ] ;

ats_ptr_type __getrest (ats_ref_type p_n) {
  int c ; size_t i ; char *s ;
  s = theRestBuffer ; i = 0 ;
  while ((c = fgetc(stdin)) != EOF) {
    if (c != '\n') { *s++ = toupper(c) ; i++ ; }
  }
  *s = '\000' ; *((size_t*)p_n) = i ;
  if (i >= RESTBUFSZ) {
    fprintf (stderr, "exit(ATS): too much data for processing\n") ; exit(1) ;
  }
  return theRestBuffer ;
} /* end of [__getrest] */

%} // end of [%{$]

(* ****** ****** *)

fun is_three (s: string): bool =
  if strncmp (s, ">THREE", 6) = 0 then true else false
// end of [is_three]

(* ****** ****** *)

extern fun dna_of_string (s: string): dna_t = "dna_of_string"

%{$

ats_ptr_type dna_of_string (ats_string_type s) { return s ; }

ats_bool_type is_three (ats_ptr_type s0) {
  char *s = (char*) s0 ;

  if (*s != '>') return ats_false_bool ; ++s ;
  if (*s != 'T') return ats_false_bool ; ++s ;
  if (*s != 'H') return ats_false_bool ; ++s ;
  if (*s != 'R') return ats_false_bool ; ++s ;
  if (*s != 'E') return ats_false_bool ; ++s ;
  if (*s != 'E') return ats_false_bool ;
  return ats_true_bool ;
}

%}

implement main (argc, argv) = let
val () = gc_chunk_count_limit_max_set (~1) // no max

fun dna_three_get
  (n: &size_t? >> size_t n): #[n:nat] string n = let
  val s = getline (); val is3 = is_three (s)
in
  if is3 then getrest (n) else dna_three_get (n)
end // end of [dna_three_get]
var n: size_t // uninitialized
val dna_three = dna_three_get (n)
val n = (sz2i)n
val () = assert (n >= 2)
val dna3 = dna_of_string dna_three where {
  extern castfn dna_of_string (str: string): dna_t
}

in

write_frequencies (dna3, n, 1) ; print_newline () ;
write_frequencies (dna3, n, 2) ; print_newline () ;

write_count (dna3, n, "GGT") ;
write_count (dna3, n, "GGTA") ;
write_count (dna3, n, "GGTATT") ;
write_count (dna3, n, "GGTATTTTAATT") ;
write_count (dna3, n, "GGTATTTTAATTTATAGT") ;

end // end of [main]

(* ****** ****** *)

(* end of [k-nucleotide_mset.dats] *)
