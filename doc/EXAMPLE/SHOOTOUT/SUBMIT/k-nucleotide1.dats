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
staload _(*anonymous*) = "prelude/DATS/reference.dats"

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
  {n:nat} (str: string n, n: size_t n): symbol_t = "symbol_make_strint"

extern fun hash_string (s: string):<> uint = "hash_string"
extern fun hash_symbol (sym: symbol_t):<> uint = "hash_symbol"
extern fun eq_symbol_symbol (sym1: symbol_t, sym2: symbol_t):<> bool = "eq_symbol_symbol"

%{$

ats_void_type print_symbol (symbol_t sym) {
  char *ptr ; int len ;
  ptr = sym.ptr ; len = sym.len ;
  while (len > 0) { fputc (*ptr, stdout) ; --len ; ++ptr ; }
  return ;
} /* print_symbol */

symbol_t symbol_make_strint (ats_ptr_type str, ats_size_type len) {
  symbol_t sym ;
  sym.ptr = (char*)str ; sym.len = len ;
  return sym ;
}

symbol_t symbol_make_dnaseg
  (ats_ptr_type dna, ats_int_type off, ats_int_type len) {
  symbol_t sym ;
  sym.ptr = ((char*)dna)+off-1 ; sym.len = len ;
  return sym ;
}

ats_uint_type hash_symbol (symbol_t sym) {
  char *ptr ; int len ;
  unsigned int hash_val ;
  ptr = sym.ptr ; len = sym.len ;
  hash_val = 31415926 ;
  while (len > 0) {hash_val = ((hash_val << 5) + hash_val) + *ptr ; ++ptr ; --len ; }
  return hash_val ;
}

ats_bool_type eq_symbol_symbol (symbol_t sym1, symbol_t sym2) {
  int len1, len2 ;
  len1 = sym1.len ; len2 = sym2.len ;
  if (len1 != len2) return ats_false_bool ;
  if (!strncmp(sym1.ptr, sym2.ptr, len1)) return ats_true_bool ;
  return ats_false_bool ;
}

%}

(* ****** ****** *)

typedef symflt = @(symbol_t, float)

fn compare_symflt_symflt // [>=]
  (x1: &symflt, x2: &symflt):<> Sgn = compare_float_float (x2.1, x1.1)
// end of [compare_symflt_symflt]

viewtypedef frqlst = List_vt symflt

// print and free
fun print_free_frqlst
  (kfs: frqlst): void = begin case+ kfs of
  | ~list_vt_cons (kf, kfs) => begin print_symbol (kf.0);
       printf (" %.3f\n", @(double_of kf.1)); print_free_frqlst (kfs)
    end // end of [FRQLSTcons]
  | ~list_vt_nil () => ()
end // end of [print_free_frqlst]

(* ****** ****** *)

staload H = "hashtable.dats"

(* ****** ****** *)

typedef symtbl = $H.hashtbl_t (symbol_t, ref int)

// the gain seems to be around 6-8%
implement $H.hash_key<symbol_t> (sym, _) = hash_symbol (sym)
implement $H.equal_key_key<symbol_t> (sym1, sym2, _) = eq_symbol_symbol (sym1, sym2)

(* ****** ****** *)

extern fun symtbl_add (tbl: symtbl, sym: symbol_t): void = "symtbl_add"

implement symtbl_add (tbl, sym) = let
  val ans = $H.hashtbl_search<symbol_t, ref int> (tbl, sym)
in
  case+ ans of
  | ~Some_vt (cnt) => !cnt := !cnt + 1
  | ~None_vt () => let
      val cnt = ref_make_elt<int> (1)
      val ans = $H.hashtbl_insert_err<symbol_t, ref int> (tbl, sym, cnt)
    in
      case+ ans of ~Some_vt _ => () | ~None_vt () => ()
    end
end // end of [symtbl_add]

extern fun dna_count {n,k:nat | k <= n}
  (dna: dna_t, tbl: symtbl, n: size_t n, k: size_t k) : void = "dna_count"

(* ****** ****** *)

fn write_frequencies {n,k:nat | k <= n}
  (dna: dna_t, tbl: symtbl, n: size_t n, k: size_t k): void = let
  val () = $H.hashtbl_clear<symbol_t, ref int> (tbl)
  val () = dna_count (dna, tbl, n, k)
  var total: int = 0; viewdef V1 = int @ total
  var !p_clo = @lam
   (pf: !V1 | k: symbol_t, cnt: &ref int): void =<clo>
   $effmask_ref (total := total + !cnt)
  // end of [f1]
  val () = $H.hashtbl_foreach_clo {V1} (view@ total | tbl, !p_clo)
  val ftotal = float_of total
  var frqs: frqlst = list_vt_nil (); viewdef V2 = frqlst @ frqs
  var !p_clo = @lam
    (pf: !V2 | k: symbol_t, cnt: &ref int): void =<clo> let
    val f = 100 * $effmask_ref (float_of !cnt) / ftotal; val kf = @(k, f) in
    frqs := list_vt_cons (kf, frqs)
  end // end of [f2]
  val () = $H.hashtbl_foreach_clo {V2} (view@ frqs | tbl, !p_clo)
  val () = list_vt_quicksort (frqs, lam (x1, x2) => compare_symflt_symflt (x1, x2))
in
  print_free_frqlst (frqs)
end // end of [write_frequencies]

(* ****** ****** *)

fn write_count {n,k:nat}
  (dna: dna_t, tbl: symtbl, n: size_t n, seq: string k): void = let
  val k = string1_length seq
  val () = assert (k <= n)
  val () = $H.hashtbl_clear<symbol_t, ref int> (tbl)
  val () = dna_count (dna, tbl, n, k)
  val sym = symbol_make_strint (seq, k)
  val cntopt = $H.hashtbl_search<symbol_t, ref int> (tbl, sym)
  val cnt = case+ cntopt of ~Some_vt cnt => !cnt | ~None_vt () => 0
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
} /* end of [__getline] */

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

%}

(* ****** ****** *)

fun is_three (s: string): bool =
  if strncmp (s, ">THREE", 6) = 0 then true else false
// end of [is_three]

(* ****** ****** *)

extern fun dna_of_string (s: string): dna_t = "dna_of_string"

%{$

ats_ptr_type dna_of_string (ats_string_type s) { return s ; }

%}

(* ****** ****** *)

implement main (argc, argv) = let
  fun dna_three_get (n: &size_t? >> size_t n): #[n:nat] string n = let
    val s = getline (); val is3 = is_three (s)
  in
    if is3 then getrest (n) else dna_three_get (n)
  end // end of [dna_three_get]

  val () = gc_chunk_count_limit_max_set (~1) // no max
  var n: size_t // uninitialized
  val dna_three = dna_three_get (n)
  val () = assert (n >= 2)
(*
  val () = (prerr "main: n = "; prerr n; prerr_newline ())
*)
  val dna = dna_of_string dna_three

  fn hash (sym: symbol_t):<cloref> uint = hash_symbol (sym)
  fn eq (sym1: symbol_t, sym2: symbol_t):<cloref> bool = eq_symbol_symbol (sym1, sym2)
  // val tbl = $H.hashtbl_make_hint<symbol_t, ref int> (hash, eq, 98317)
  val tbl = $H.hashtbl_make_hint<symbol_t, ref int> (hash, eq, 196613)
in
  write_frequencies (dna, tbl, n, 1) ; print_newline () ;
  write_frequencies (dna, tbl, n, 2) ; print_newline () ;
  write_count (dna, tbl, n, "GGT") ;
  write_count (dna, tbl, n, "GGTA") ;
  write_count (dna, tbl, n, "GGTATT") ;
  write_count (dna, tbl, n, "GGTATTTTAATT") ;
  write_count (dna, tbl, n, "GGTATTTTAATTTATAGT") ;
end (* end of [main] *)

(* ****** ****** *)

%{$

ats_void_type dna_count
  (ats_ptr_type dna, ats_ptr_type tbl, ats_size_type n, ats_size_type k) {
  symbol_t sym ; char *ptr ; int nk ; 
  ptr = (char*)dna ; nk = n - k ; while (nk >= 0) {
    sym.ptr = ptr ; sym.len = k ; symtbl_add (tbl, sym) ; ptr += 1 ; nk -= 1 ;
  }
  return ;
}

%}

(* ****** ****** *)

(* end of [k-nucleotide1.dats] *)
