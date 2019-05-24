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

(* ****** ****** *)

// The hashtable implementation is based on linear-probing
// #include "symtbl.dats"

(* ****** ****** *)

%{^
// #include "symtbl.hats"
typedef ats_ptr_type ats_string_type ;
typedef struct { int beg ; int len ; } symbol_t ;
typedef struct { symbol_t sym ; int cnt ; } tblent_t ;
%} // end of [%{^]

(* ****** ****** *)

// staload "symtbl.sats"
abstype dna_t // boxed type
abst@ype symbol_t = $extype "symbol_t"
abstype symtbl_t // boxed type

extern fun print_symbol (dna: dna_t, sym: symbol_t): void
extern fun symtbl_make (dna: dna_t, size: Nat) : symtbl_t
extern fun symtbl_clear (tbl: symtbl_t) : void = "symtbl_clear"
extern fun symtbl_search (tbl: symtbl_t, name: string) : int
  = "symtbl_search"
extern fun symtbl_insert (tbl: symtbl_t, sym: symbol_t, cnt: int) : void
  = "symtbl_insert"
extern fun symtbl_fold{a:viewt@ype}
  (tbl: symtbl_t, f: !(symbol_t, int, &a) -<cloptr1> void, res: &a) : void
extern fun symtbl_dna (tbl: symtbl_t): dna_t

(* ****** ****** *)

abst@ype
tblent_t =
$extype "tblent_t"
typedef tblent = tblent_t

viewtypedef
symtbl (
  sz:int, n:int, l:addr
) = @{
  dna= dna_t
, ptr= ptr l
, view_arr= @[tblent][sz] @ l
, view_arr_gc= free_gc_v (tblent?, sz, l)
, size= int sz
, nitm= int n
} // end of [symtbl]

viewtypedef symtbl0 = symtbl (0, 0, null)
viewtypedef symtbl =
  [sz,n:nat | sz > 0] [l:addr] symtbl (sz, n, l)
assume symtbl_t =
  [l_tbl: addr] (vbox (symtbl @ l_tbl) | ptr l_tbl)

(* ****** ****** *)

extern fun fprint_symbol {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, dna: dna_t, sym: symbol_t): void
  = "fprint_symbol"

%{

ats_void_type fprint_symbol
  (ats_ptr_type out, ats_ptr_type dna, symbol_t sym) {
  char *s ; int i ;

  s = (char*)dna + sym.beg - 1 ; i = 0 ;

  while (i < sym.len) {
    fputc ( *s, (FILE*)out) ; ++i ; ++s ;
  }

  return ;

}

%}

implement print_symbol (dna, sym) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_symbol (file_mode_lte_w_w | !ptr_stdout, dna, sym);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_symbol]

(* ****** ****** *)

#define i2u uint1_of_int1
extern fun hash_string_33 (s: string):<> uInt = "hash_string_33"
extern fun hash_symbol_33 (dna: dna_t, sym: symbol_t):<> uInt = "hash_symbol_33"

%{

// a commonly used simple hash function

ats_uint_type hash_string_33 (ats_ptr_type s0) {
  unsigned int hash_val ; unsigned char *s ; int c ;
  hash_val = 314159 ;

  s = (unsigned char*)s0 ;
  while (1) {
    c = *s ;
    if (!c) return hash_val ;
    hash_val = ((hash_val << 5) + hash_val) + c ;
    s += 1 ;
  }
}

ats_uint_type hash_symbol_33 (ats_ptr_type dna, symbol_t sym) {

  unsigned int hash_val, n ; unsigned char *s ;
  hash_val = 314159 ;

  n = sym.len ;
  s = (unsigned char*)dna + sym.beg - 1 ;

  while (n > 0) {
    hash_val = ((hash_val << 5) + hash_val) + *s ;
    ++s ; --n ;
  }
/*
  fprintf (stdout, "has_symbol_33: \n") ;
  fprintf (stdout, "  sym = ") ;
  fprint_symbol (stdout, dna, sym) ;
  fprintf (stdout, "\n  hash_val = %u\n", hash_val) ;
*/
  return hash_val ;
}

%}

(* ****** ****** *)

extern
fun tblent_array_make
  {sz: nat} (sz: int sz)
  :<> [l:addr] (
  free_gc_v (tblent?, sz, l), array_v (tblent, sz, l) | ptr l
) = "tblent_array_make"

%{^

ats_ptr_type
tblent_array_make (ats_int_type sz) {
  return ats_calloc_gc (sz, sizeof(tblent_t)) ;
}

%}

(* ****** ****** *)

implement
symtbl_make
  (dna, sz) = let
//
val sz = max (sz, 1)
val (pf_tbl_gc, pf_tbl | p_tbl) = ptr_alloc_tsz {symtbl0} (sizeof<symtbl0>)
val (pf_arr_gc, pf_arr | p_arr) = tblent_array_make (sz)
//
val () = begin
  p_tbl->dna := dna;
  p_tbl->ptr := p_arr;
  p_tbl->view_arr := pf_arr;
  p_tbl->view_arr_gc := pf_arr_gc;
  p_tbl->size := sz;
  p_tbl->nitm := 0
end // end of [val]
//
prval () = free_gc_elim {symtbl0?} (pf_tbl_gc)
val (pfbox | ()) = vbox_make_view_ptr (pf_tbl | p_tbl)
//
in
  (pfbox | p_tbl)
end // symtbl_make

(* ****** ****** *)

extern fun tblent_array_clear {sz:nat} {l:addr}
  (pf: !array_v (tblent, sz, l) | p: ptr l, sz: int sz):<> void
  = "tblent_array_clear"

%{

ats_void_type
tblent_array_clear (ats_ptr_type p, ats_int_type sz) {
  memset (p, 0, sz * sizeof(tblent_t)) ;
}

%}

implement
symtbl_clear (tbl) = let
//
val (vbox pf_tbl | p_tbl) = tbl
//
in

tblent_array_clear (p_tbl->view_arr |  p_tbl->ptr, p_tbl->size);
p_tbl->nitm := 0
//
end // end of [symtbl_clear]

(* ****** ****** *)
//
// HX: linear probing
//
extern fun symtbl_search_probe {sz,i:nat | i < sz} {l:addr}
  (pf: !array_v(tblent, sz, l) |
  dna: dna_t, p: ptr l, sz: int sz, name: string, i: int i):<> int
  = "symtbl_search_probe"

%{

ats_int_type symtbl_search_probe
  (ats_string_type dna,
   ats_ptr_type p,
   ats_int_type sz,
   ats_string_type name,
   ats_int_type i) {

  tblent_t *ent ; int beg ;

  ent = ((tblent_t *)p) + i ;

  while (1) {
    beg = (ent->sym).beg ;
    if (beg == 0) return 0 ; // the entry is unoccupied
    if (strncmp (((char*)dna)+beg-1, (char*)name, (ent->sym).len) == 0) {
      return ent->cnt ;
    }
    ++i ; if (i >= sz) { i = 0 ; ent = (tblent_t *)p ; } else ++ent ;
  }
}

%}

implement symtbl_search (tbl, name) = let

val hash_val = hash_string_33 name
val (vbox pf_tbl | p_tbl) = tbl
val i = hash_val uimod p_tbl->size

in

symtbl_search_probe (
  p_tbl->view_arr | p_tbl->dna, p_tbl->ptr, p_tbl->size, name, i
)

end

(* ****** ****** *)

extern fun symtbl_insert_probe {sz,i:nat | i < sz} {l:addr}
  (pf: !array_v (tblent, sz, l) |
   dna: dna_t, p: ptr l, sz: int sz, sym: symbol_t, cnt: int, i: int i):<> bool
  = "symtbl_insert_probe"

%{

ats_bool_type symtbl_insert_probe
  (ats_ptr_type dna,
   ats_ptr_type p, ats_int_type sz,
   symbol_t sym, ats_int_type cnt,
   ats_int_type i) {

  tblent_t *ent ;
/*
  printf ("symtbl_insert_probe: sz = %i\n", sz) ;
*/

  ent = ((tblent_t *)p) + i ;
  while (1) {
    if (!(ent->sym).beg) { // the entry is not occupied
      ent->sym = sym ;
      if (cnt > 0) ent->cnt = cnt ; else ent->cnt = 1 ;
      return 1 ;
    }
/*
    printf ("symtbl_insert_probe: i = %i\n", i) ;
    fprint_symbol (stdout, dna, ent->sym) ; printf ("\n") ;
    fprint_symbol (stdout, dna, sym) ; printf ("\n") ;
*/
    // linear probing
    if (strncmp (dna+(ent->sym).beg-1, dna+sym.beg-1, sym.len) == 0) {
      if (cnt > 0) ent->cnt = cnt ; else ent->cnt += 1 ;
      return 0 ;
    }
    ++i ; if (i >= sz) { i = 0 ; ent = (tblent_t *)p ; } else ++ent ;
  }
}

%}

(* ****** ****** *)

extern fun symtbl_resize_move {sz:nat} {l,l_new:addr}
  (pf: !array_v(tblent, sz, l),
   pf_new: !array_v(tblent, sz+sz, l_new) |
   dna: dna_t, p: ptr l, p_new: ptr l_new, sz: int sz):<> void
  = "symtbl_resize_move"

%{

ats_void_type symtbl_resize_move
  (ats_ptr_type dna, ats_ptr_type p, ats_ptr_type p_new, ats_int_type sz) {

  int i, sz2, h ;
  tblent_t *ent ;

  i = 0 ; sz2 = sz + sz ; ent = (tblent_t *)p ;
/*
  printf ("symtbl_resize_move: sz2 = %i\n", sz2) ;
*/
  while (i < sz) {
    if (!(ent->sym).beg) { ++i ; ++ent ; continue ; }
    h = hash_symbol_33 (dna, ent->sym) % sz2 ;
    symtbl_insert_probe (dna, p_new, sz2, ent->sym, ent->cnt, h) ;
    ++i ; ++ent ;
  }

  return ;
}

%}

fn symtbl_resize (tbl: symtbl_t):<!ref> void = let

val (vbox pf_tbl | p_tbl) = tbl
val p_arr = p_tbl->ptr
prval pf_arr = p_tbl->view_arr
prval pf_arr_gc = p_tbl->view_arr_gc
val sz = p_tbl->size
val (pf_arr_gc_new, pf_arr_new | p_arr_new) = tblent_array_make (sz + sz)

in

symtbl_resize_move (pf_arr, pf_arr_new | p_tbl->dna, p_arr, p_arr_new, sz);
array_ptr_free {tblent?} (pf_arr_gc, pf_arr | p_arr);
p_tbl->ptr := p_arr_new;
p_tbl->view_arr := pf_arr_new;
p_tbl->view_arr_gc := pf_arr_gc_new;
p_tbl->size := sz + sz;

end // end of [symtbl_resize]

fun symtbl_resize_if (tbl: symtbl_t): void = let
  val nitm = let val (vbox pf_tbl | p_tbl) = tbl in p_tbl->nitm end
  val size = let val (vbox pf_tbl | p_tbl) = tbl in p_tbl->size end
in
  if (2 * nitm > size) then symtbl_resize (tbl)
end // end of [symtbl_resize]

(* ****** ****** *)

implement symtbl_insert (tbl, sym, cnt) = let
val () = symtbl_resize_if (tbl)
val (vbox pf_tbl | p_tbl) = tbl
val hash_val = hash_symbol_33 (p_tbl->dna, sym)
val i = hash_val uimod p_tbl->size
val is_new = symtbl_insert_probe
  (p_tbl->view_arr | p_tbl->dna, p_tbl->ptr, p_tbl->size, sym, cnt, i)
in

if is_new then p_tbl->nitm := 1 + p_tbl->nitm else ()

end // end of [symtbl_insert]

(* ****** ****** *)

extern fun tblent_array_fold {a:viewt@ype} {sz: nat} {l:addr}
  (pf: !array_v (tblent, sz, l) |
   p: ptr l, sz: int sz, f: !(symbol_t, int, &a) -<cloptr1> void, res: &a)
  :<> void
  = "tblent_array_fold"

%{

ats_void_type tblent_array_fold
  (ats_ptr_type p, ats_int_type sz, ats_clo_ptr_type f, ats_ptr_type res) {

  int i ; tblent_t *ent ;

  i = 0 ; ent = (tblent_t *)p ;
  while (i < sz) {
    if (!(ent->sym).beg) { ++i ; ++ent ; continue ; }
    ((ats_void_type (*)(ats_clo_ptr_type, symbol_t, ats_int_type, ats_ptr_type))(ats_closure_fun(f)))(f, ent->sym, ent->cnt, res) ;
    ++i ; ++ent ;
  }
}

%}

implement symtbl_fold {a} (tbl, f, res) = let

val (vbox pf_tbl | p_tbl) = tbl

in

tblent_array_fold {a}
  (p_tbl->view_arr | p_tbl->ptr, p_tbl->size, f, res)

end // end of [symtbl_insert]

(* ****** ****** *)

implement symtbl_dna (tbl) = begin
  let val (vbox pf_tbl | p_tbl) = tbl in p_tbl->dna end
end

(* ****** ****** *)

(* end of [symtbl.dats] *)


(* ****** ****** *)

extern fun dna_count {n,k:nat | k <= n}
  (tbl: symtbl_t, n: int n, k: int k) : symtbl_t = "dna_count"

// a linear datatype
dataviewtype frqlst = FRQLSTnil | FRQLSTcons of (symbol_t, float, frqlst)

// linear append
fun frqlst_append
  (xs0: &frqlst >> frqlst, ys: frqlst): void = begin case xs0 of
  | FRQLSTcons (k, f, !xs) => (frqlst_append (!xs, ys); fold@ xs0)
  | ~FRQLSTnil () => (xs0 := ys)
end // end of [frqlst_append]

// quick sort
fun qsort (xs: frqlst): frqlst = begin case+ xs of
  | FRQLSTcons (!k1_r, !f1_r, !xs1_r) => let
      val k1 = !k1_r and f1 = !f1_r and xs1 = !xs1_r
    in
      partition (
        view@ (!k1_r), view@ (!f1_r), view@ (!xs1_r)
      | xs, xs1_r, k1, f1, xs1, FRQLSTnil (), FRQLSTnil ()
      ) // end of [partition]
    end
  | FRQLSTnil () => (fold@ xs; xs)
end // end of [qsort]

and partition {l00,l01,l1:addr}
  (pf00: symbol_t @ l00, pf01: float @ l01, pf1: frqlst? @ l1 |
   node: FRQLSTcons_unfold (l00, l01, l1), node1: ptr l1,
   k0: symbol_t, f0: float, xs: frqlst, l: frqlst, r: frqlst)
  : frqlst = begin case+ xs of
  | FRQLSTcons (k1, f1, !xs1_r) =>
    let val xs1 = !xs1_r in
      if compare (f1, f0) >= 0 then begin
        !xs1_r := l; fold@ xs;
        partition (pf00, pf01, pf1 | node, node1, k0, f0, xs1, xs, r)
      end else begin
        !xs1_r := r; fold@ xs;
        partition (pf00, pf01, pf1 | node, node1, k0, f0, xs1, l, xs)
      end
    end
  | ~FRQLSTnil () =>
    let var l = qsort l and r = qsort r in
      !node1 := r; fold@ node; frqlst_append (l, node); l
    end
end // end of [partition]

// print and free
fun print_frqlst
  (dna: dna_t, kfs: frqlst): void = begin case+ kfs of
  | ~FRQLSTcons (k, f, kfs) => begin
      print_symbol (dna, k); printf (" %.3f\n", @(double_of f));
      print_frqlst (dna, kfs)
    end
  | ~FRQLSTnil () => ()
end // end of [print_frqlst]

fn write_frequencies {n,k:nat | k <= n}
  (tbl: symtbl_t, n: int n, k: int k): void = let
  val tbl = dna_count (tbl, n, k)
  var total: int = (0: int)
  fn f (k: symbol_t, cnt: int, res: &int):<cloptr> void = (res := res + cnt)
  val () = symtbl_fold {int} (tbl, f, total)
  val ftotal = float_of total
  var frqs: frqlst = FRQLSTnil ()
  fn f (k: symbol_t, cnt: int, res: &frqlst):<cloptr> void =
    let val fval = (float_of 100) * float_of cnt / ftotal in
      res := FRQLSTcons (k, fval, res)
    end
  val () = symtbl_fold {frqlst} (tbl, f, frqs)
in
  print_frqlst (symtbl_dna tbl, qsort frqs)
end // end of [write_frequencies]

(* ****** ****** *)

fn write_count {n,k:nat}
  (tbl: symtbl_t, n: int n, seq: string k): void = let
  val k = string1_length seq; val k = int1_of_size1 k
  val () = assert (k <= n)
  val tbl = dna_count (tbl, n, k)
  val cnt = symtbl_search (tbl, seq)
in
  printf ("%d\t%s\n", @(cnt, seq))
end // end of [write_count]

(* ****** ****** *)

typedef string_int = [n:nat] (string n, int n)

extern fun getline (): string
extern fun getrest (): string_int

dataviewtype charlst (int) =
  | charlst_nil (0)
  | {n:nat} charlst_cons (n+1) of (char, charlst n)

#define nil charlst_nil
#define cons charlst_cons
#define :: charlst_cons

extern fun charlst_is_nil {n:nat} (cs: &charlst n): bool (n == 0) =
  "charlst_is_nil"

implement charlst_is_nil (cs) = case+ cs of
  | nil () => (fold@ cs; true) | cons (c, !cs_r) => (fold@ cs; false)

extern fun
charlst_uncons {n:pos} (cs: &charlst n >> charlst (n-1)): char =
  "charlst_uncons"

implement charlst_uncons (cs) =
  let val ~(c :: cs_r) = cs in cs := cs_r; c end

extern fun
string_make_charlst_int {n:nat} (cs: charlst n, n: int n): string n =
  "string_make_charlst_int"

#define i2c char_of_int

implement getline () = let
  fun loop {n:nat} (cs: charlst n, n: int n): string =
    let val i = getchar () in
      if i >= 0 then let
        val c = i2c i
      in
        if c <> '\n' then loop (charlst_cons (c, cs), n+1)
        else string_make_charlst_int (cs, n)
      end else begin
        string_make_charlst_int (cs, n)
      end
   end // end of [loop]
in
  loop (charlst_nil (), 0)
end // end of [getline]

implement getrest () = let
  fun loop {n:nat} (cs: charlst n, n: int n): string_int =
    let val i = getchar () in
      if i >= 0 then let
        val c = i2c i
      in
        if c <> '\n' then
          loop (charlst_cons (char_toupper c, cs), n+1)
        else loop (cs, n)
      end else begin
        @(string_make_charlst_int (cs, n), n)
      end
    end // end of [let]
in
  loop (charlst_nil (), 0)
end // end of [getrest]

(* ****** ****** *)

extern
castfn dna_of_string (s: string): dna_t
extern fun is_three (s: string): bool = "is_three"

%{$

ats_bool_type
is_three (
  ats_ptr_type s0
) {
  char *s = (char*) s0 ;
//
  if ( *s != '>') return ats_false_bool ; ++s ;
  if ( *s != 'T') return ats_false_bool ; ++s ;
  if ( *s != 'H') return ats_false_bool ; ++s ;
  if ( *s != 'R') return ats_false_bool ; ++s ;
  if ( *s != 'E') return ats_false_bool ; ++s ;
  if ( *s != 'E') return ats_false_bool ;
//
  return ats_true_bool ;
} // end of [is_three]

%} // end of [%{$]

implement main (argc, argv) = let
//
  fun dna_three_get (): string_int = let
    val s = getline ()
    val () = assert (s <> "")
    val is3 = is_three (s)
(*
    val () = string_free (s) where {
      extern fun string_free (s: string): void = "ATS_FREE"
    } // end of [val]
*)
  in
    if is3 then getrest () else dna_three_get ()
  end // end of [dna_three_get]
//
  val () = gc_chunk_count_limit_max_set (~1) // no max
//
  val (dna_three, n) = dna_three_get ()
  val dna_three = dna_of_string dna_three
  val dna_table = symtbl_make (dna_three, 0x40000)
  val () = assert (n >= 2)
//
in
//
write_frequencies (dna_table, n, 1) ;
print_newline () ;
//
write_frequencies (dna_table, n, 2) ;
print_newline () ;
//
write_count (dna_table, n, "GGT") ;
write_count (dna_table, n, "GGTA") ;
write_count (dna_table, n, "GGTATT") ;
write_count (dna_table, n, "GGTATTTTAATT") ;
write_count (dna_table, n, "GGTATTTTAATTTATAGT") ;
//
end // end of [main]

(* ****** ****** *)

%{$

ats_ptr_type
dna_count (
  ats_ptr_type tbl, ats_int_type n, ats_int_type k
) {
  symbol_t sym ; int i, nk = n - k ;

  symtbl_clear (tbl) ;
  i = 0 ; 
  while (i <= nk) {
    ++i ; sym.beg = i ; sym.len= k ;
    symtbl_insert (tbl, sym, 0) ;
  }
  return tbl ;
} // end of [dna_count]

ats_ptr_type
string_make_charlst_int (
  ats_ptr_type cs, const ats_int_type n
) {
  char *s0, *s;
  s0 = ats_malloc_gc(n+1) ;
  s = s0 + n ; *s = '\0' ; --s ;
  while (!charlst_is_nil(&cs)) { *s = charlst_uncons(&cs) ; --s ; }
  return s0 ;
} // end of [string_make_charlst_int]

%} // end of [%{$]

(* ****** ****** *)

(* end of [k-nucleotide.dats] *)
