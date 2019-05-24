(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -O3 k-nucleotide4.dats -o k-nucleotide4 -D_ATS_GCATS
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats"
staload "libc/SATS/string.sats"
staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload H = "libats/SATS/hashtable_linprb.sats"
staload _(*anon*) = "libats/DATS/hashtable_linprb.dats"

(* ****** ****** *)

%{^
typedef char *symbol_t ;
%} // end of [%{^]

(* ****** ****** *)

abstype dna_t // boxed type
abst@ype symbol_t = $extype "symbol_t"

(* ****** ****** *)

typedef keyitm = @(symbol_t, int)

implement
$H.keyitem_isnot_null<keyitm> (ki) = let
  prval () = __assert (ki) where {
    extern praxi __assert (x: !($H.Opt keyitm) >> keyitm):<> void
  } // end of [prval]
  val i = ki.1
  val res = (i <> 0)
  val [b:bool] res = bool1_of_bool (res)
  prval () = __assert (ki) where {
    extern praxi __assert (x: &keyitm >> opt (keyitm, b)):<> void
  } // end of [prval]
in
  res
end // end of [keyitem_isnot_null]

(* ****** ****** *)

%{^

ats_void_type print_symbol
  (symbol_t sym, ats_size_type len) {
  while (len > 0) { fputc (*sym, stdout) ; --len ; ++sym ; }
  return ;
} // end of [print_symbol]

%} // end of [%{^]

extern fun print_symbol
  (sym: symbol_t, len: size_t): void = "print_symbol"
// end of [print_symbol]

(* ****** ****** *)

%{^

size_t the_symlen = 0 ;
ats_size_type symlen_get () { return the_symlen ; }
ats_void_type symlen_set
  (ats_size_type len) { the_symlen = len ; return ; }
// end of [symlen_set]

%} // end of [%{^]
extern fun symlen_get ():<> size_t = "symlen_get"
extern fun symlen_set (len: size_t):<> void = "symlen_set"

(* ****** ****** *)

%{^

// a commonly used simple hash function

static // inline
ats_ulint_type hash_symbol_len (
  symbol_t sym, ats_size_type len
) {
  unsigned long int hash_val = 0UL ;
  while (len >= 4) {
    hash_val += hash_val * 33 ;
    hash_val += sym[0] << 24 ;
    hash_val += sym[1] << 16 ;
    hash_val += sym[2] <<  8 ;
    hash_val += sym[3] ;
    sym += 4 ; len -= 4 ;
  } // end of [while]
  if (len >= 2) {
    hash_val = hash_val * 33 + (sym[0] << 8) + sym[1] ;
    sym += 2 ; len -= 2 ;
  } // end of [if]
  if (len >= 1) {
    hash_val = hash_val * 33 + sym[0] ;
  } // end of [while]
  return hash_val ;
} // end of [hash_symbol_len]

%} // end of [%{^]

extern fun hash_symbol_len
  (sym: symbol_t, len: size_t):<> ulint = "hash_symbol_len"
// end of [hash_symbol]

(* ****** ****** *)

implement $H.hash_key<symbol_t>
  (x, _) = hash_symbol_len (x, symlen_get ())
// end of [implement]

implement
$H.equal_key_key<symbol_t> (x1, x2, _) = let
  extern castfn __cast (x: symbol_t):<> string
  val x1 = __cast x1 and x2 = __cast x2
  val k = symlen_get ()
  val k = size1_of_size (k)
in
  strncmp (x1, x2, k) = 0
end // end of [implement]

(* ****** ****** *)

viewtypedef symtbl (l:addr) = $H.HASHTBLptr (symbol_t, int, l)

(* ****** ****** *)

extern fun succ_symbol (x: symbol_t): symbol_t = "mac#atspre_psucc"

fun dna_count {n,k:pos | k <= n} {l:agz}
  (tbl: !symtbl l, dna: dna_t, n: size_t n, k: size_t k): void = let
  val () = symlen_set (k)
  val () = $H.hashtbl_clear (tbl)
  var n: size_t = n
  var sym: symbol_t =
    __cast (dna) where { extern castfn __cast (x: dna_t): symbol_t }
  // end of [var]
in
  while (n >= k) let
    val [l_itm:addr] p_itm = $H.hashtbl_search_ref<symbol_t,int> (tbl, sym)
    val () = if p_itm <> null then let
      prval (fpf, pf) = __assert () where {
        extern praxi __assert (): (int@l_itm -<prf> void, int@l_itm)
      } // end of [prval]
      val () = !p_itm := !p_itm + 1
      prval () = fpf (pf)
    in
      // nothing
    end else let
      var res: int
      val ans = $H.hashtbl_insert<symbol_t,int> (tbl, sym, 1, res)
      prval () = opt_clear (res)
    in
      // nothing
    end // end of [val]
  in
    n := n - 1; sym := succ_symbol sym
  end // end of [while]
end // end of [dna_count]

(* ****** ****** *)

typedef symflt = @(symbol_t, float)

fn compare_symflt_symflt // [>=]
  (x1: &symflt, x2: &symflt):<> Sgn = compare_float_float (x2.1, x1.1)
// end of [compare_symflt_symflt]

viewtypedef frqlst = List_vt symflt

(* ****** ****** *)

// print and free
fun print_free_frqlst
  (kfs: frqlst, len: size_t): void = begin case+ kfs of
  | ~list_vt_cons (kf, kfs) => begin print_symbol (kf.0, len);
       printf (" %.3f\n", @(double_of kf.1)); print_free_frqlst (kfs, len)
    end // end of [FRQLSTcons]
  | ~list_vt_nil () => ()
end // end of [print_free_frqlst]

fn write_frequencies {n,k:pos | k <= n} {l:agz}
  (tbl: !symtbl l, dna: dna_t, n: size_t n, k: size_t k): void = let
  val () = dna_count (tbl, dna, n, k)
  var total: int = 0
  var !p_clo = @lam (pf: !int@total | k: symbol_t, i: &int): void =<clo>
    (total := total + i)
  val () = $H.hashtbl_foreach_vclo {int@total} (view@ total | tbl, !p_clo)
  val ftotal = float_of total
  var frqs: frqlst = list_vt_nil ()
  var !p_clo = @lam
    (pf: !frqlst @ frqs | k: symbol_t, cnt: &int): void =<clo> let 
    val f = (float_of 100) * float_of cnt / ftotal; val kf = @(k, f) in
    frqs := list_vt_cons (kf, frqs)
  end // end of [f]
  val () = $H.hashtbl_foreach_vclo {frqlst@frqs} (view@ frqs | tbl, !p_clo)
  val () = list_vt_quicksort (frqs, compare_symflt_symflt)
in
  print_free_frqlst (frqs, symlen_get ())
end // end of [write_frequencies]

(* ****** ****** *)

fn write_count {n,k:pos} {l:agz}
  (tbl: !symtbl l, dna: dna_t, n: size_t n, seq: string k): void = let
  val k = string1_length seq
  val () = assert (k <= n)
  val () = dna_count (tbl, dna, n, k)
  var res : int
  val ans = $H.hashtbl_search
    (tbl, __cast seq, res) where { extern castfn __cast (x: string): symbol_t }
  // end of [ans]
  val () = if ans then let
    prval () = opt_unsome {int} (res) in (*none*)
  end else let
    prval () = opt_unnone {int} (res) in res := 0
  end : void // end of [val]
in
  printf ("%d\t%s\n", @(res, seq))
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

%} // end of [%{^]

(* ****** ****** *)

fun is_three (s: string): bool =
  if strncmp (s, ">THREE", 6) = 0 then true else false
// end of [is_three]

(* ****** ****** *)

implement main (argc, argv) = let
  fun dna_three_get
    (n: &size_t? >> size_t n): #[n:nat] string n = let
    val s = getline (); val is3 = is_three (s)
  in
    if is3 then getrest (n) else dna_three_get (n)
  end // end of [dna_three_get]
  var n: size_t // uninitialized
  val dna_three = dna_three_get (n)
  val () = assert (n >= 2)
(*
  val () = (prerr "main: n = "; prerr n; prerr_newline ())
*)
  val dna3 =
    dna_of_string dna_three where {
    extern castfn dna_of_string (str: string): dna_t
  }
  val eqfn = $extval ($H.eqfn symbol_t, "0")
  val fhash = $extval ($H.hash symbol_t, "0")
  val tbl = $H.hashtbl_make_hint (fhash, eqfn, 196613)
in
  write_frequencies (tbl, dna3, n, 1) ; print_newline () ;
  write_frequencies (tbl, dna3, n, 2) ; print_newline () ;
  write_count (tbl, dna3, n, "GGT") ;
  write_count (tbl, dna3, n, "GGTA") ;
  write_count (tbl, dna3, n, "GGTATT") ;
  write_count (tbl, dna3, n, "GGTATTTTAATT") ;
  write_count (tbl, dna3, n, "GGTATTTTAATTTATAGT") ;
  $H.hashtbl_free (tbl) ; // hashtable containing only nonlinear items
end (* end of [main] *)

(* ****** ****** *)

(* end of [k-nucleotide4.dats] *)
