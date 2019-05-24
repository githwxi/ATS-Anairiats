// Time: August 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

// The hashtable implementation is based on linear-probing

(* ****** ****** *)

%{^
//
// #include "symtbl.hats"
//
typedef ats_ptr_type ats_string_type ;
typedef struct { int beg ; int len ; } symbol_t ;
typedef struct { symbol_t sym ; int cnt ; } tblent_t ;
//
%}

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
extern fun symtbl_fold {a:viewt@ype}
  (tbl: symtbl_t, f: !(symbol_t, int, &a) -<cloptr1> void, res: &a) : void
extern fun symtbl_dna (tbl: symtbl_t): dna_t

(* ****** ****** *)

abst@ype tblent_t = $extype "tblent_t"
typedef tblent = tblent_t

viewtypedef symtbl (sz:int, n:int, l:addr) = @{
  dna= dna_t
, ptr= ptr l
, view_arr= @[tblent][sz] @ l
, view_arr_gc= free_gc_v (tblent?, sz, l)
, size= int sz
, nitm= int n
}

viewtypedef symtbl0 = symtbl (0, 0, null)
viewtypedef symtbl = [sz,n:nat | sz > 0] [l:addr] symtbl (sz, n, l)
assume symtbl_t = [l_tbl: addr] (vbox (symtbl @ l_tbl) | ptr l_tbl)

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
    fputc (*s, (FILE*)out) ; ++i ; ++s ;
  }

  return ;

}

%}

implement print_symbol (dna, sym) =
  let
     val (pf_stdout | ptr_stdout) = stdout_get ()
  in
     fprint_symbol (file_mode_lte_w_w | !ptr_stdout, dna, sym);
     stdout_view_set (pf_stdout | (*none*))
  end

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
tblent_array_make
  (ats_int_type sz) {
  return ats_calloc_gc (sz, sizeof(tblent_t)) ;
} // end of [tblent_array_make]

%}

(* ****** ****** *)

implement
symtbl_make (dna, sz) = let
val sz = max (sz, 1)
val (pf_tbl_gc, pf_tbl | p_tbl) = ptr_alloc_tsz {symtbl0} (sizeof<symtbl0>)
val (pf_arr_gc, pf_arr | p_arr) = tblent_array_make (sz)

val () = begin
  p_tbl->dna := dna;
  p_tbl->ptr := p_arr;
  p_tbl->view_arr := pf_arr;
  p_tbl->view_arr_gc := pf_arr_gc;
  p_tbl->size := sz;
  p_tbl->nitm := 0
end // end of [val]

prval () = free_gc_elim {symtbl0?} (pf_tbl_gc)
val (pfbox | ()) = vbox_make_view_ptr (pf_tbl | p_tbl)

in
  (pfbox | p_tbl)
end // symtbl_make

(* ****** ****** *)

extern
fun tblent_array_clear
  {sz:nat} {l:addr} (
  pf: !array_v (tblent, sz, l) | p: ptr l, sz: int sz
) :<> void = "tblent_array_clear"

%{

ats_void_type
tblent_array_clear (ats_ptr_type p, ats_int_type sz) {
  memset (p, 0, sz * sizeof(tblent_t)) ;
}

%}

implement symtbl_clear (tbl) = let

val (vbox pf_tbl | p_tbl) = tbl

in

tblent_array_clear (p_tbl->view_arr |  p_tbl->ptr, p_tbl->size);
p_tbl->nitm := 0

end

//

(* ****** ****** *)
//
//  HX: linear probing
//
extern
fun symtbl_search_probe
  {sz,i:nat | i < sz} {l:addr} (
  pf: !array_v(tblent, sz, l) 
| dna: dna_t, p: ptr l, sz: int sz, name: string, i: int i
):<> int = "symtbl_search_probe"

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
  } // end of [while]
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

extern
fun symtbl_insert_probe
  {sz,i:nat | i < sz} {l:addr} (
  pf: !array_v (tblent, sz, l)
| dna: dna_t, p: ptr l, sz: int sz, sym: symbol_t, cnt: int, i: int i
) :<> bool = "symtbl_insert_probe"

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
  } // end of [while]
}

%}

(* ****** ****** *)

extern
fun symtbl_resize_move
  {sz:nat} {l,l_new:addr} (
  pf: !array_v(tblent_t, sz, l),
  pf_new: !array_v(tblent_t, sz+sz, l_new)
| dna: dna_t, p: ptr l, p_new: ptr l_new, sz: int sz
) :<> void = "symtbl_resize_move"

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
