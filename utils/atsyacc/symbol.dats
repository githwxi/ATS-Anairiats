(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "grammar.sats"

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

staload H = "LIB/hashtable.dats"
staload S = "LIB/funset_avltree.dats"

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

%{^

typedef FILE ats_FILE_viewtype ;

%}

(* ****** ****** *)

#define NONASSOC	0
#define LEFTASSOC 	1
#define RIGHTASSOC 	2

(* ****** ****** *)

#define TERM_INDEX_MAX1 65536
#assert (TERM_INDEX_MAX1 == (1 << 16))

(* ****** ****** *)

local

typedef symbol = '{
  symbol_name= string
, symbol_index= int
// nonassoc: 0; leftassoc: 1; rightassoc: 2;
, symbol_assoc= int
, symbol_nullable= bool
, symbol_frstset= symbolsetref
, symbol_fllwset= symbolsetref
, symbol_rulerhslst= rulerhslst
} // end of [symbol]
 
assume symbol_t = symbol

val the_term_index = ref_make_elt<int> (0)
val the_nonterm_index = ref_make_elt<int> (TERM_INDEX_MAX1)

val the_symtbl =
  $H.hashtbl_make<string, symbol_t> (hash, eq) where {
  fn hash (x: string):<cloref> uint = uint_of_ulint (string_hash_33 x)
  fn eq (x1: string, x2: string):<cloref> bool = (x1 = x2)
} // end of [val]

fn symbol_make_name_index
  (name: string, index: int): symbol_t = '{
  symbol_name= name
, symbol_index= index
, symbol_assoc= ~1 // default
, symbol_nullable= false // default
, symbol_frstset= _symbolset_nil // default; it is to be computed
, symbol_fllwset= _symbolset_nil // default; it is to be computed
, symbol_rulerhslst= list_nil ()
} where {
  // this is used as a place holder
  val _symbolset_nil = $extval (symbolsetref, "(ats_ptr_type)0")
} // end of [symbol_make_name_index]

in // in of [local]

//

implement symbol_name_get (x) = x.symbol_name
implement symbol_index_get (x) = x.symbol_index

//

implement symbol_find_name (name) =
  $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
// end of [symbol_find_name]

implement name_is_new (name) = let
  val ans = $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
in
  case+ ans of ~None_vt () => true | ~Some_vt _ => false
end // end of [name_is_new]

implement symbol_make_name (knd, name) = let
  val ans = $H.hashtbl_search<string,symbol_t> (the_symtbl, name)
in
  case+ ans of
  | ~Some_vt sym => sym | ~None_vt () => symbol_make_newname (knd, name)
  // end of [case]
end // end of [symbol_make_name]

//

extern fun the_term_index_get (): int
extern fun the_term_index_getinc (): int

implement the_term_index_get () = !the_term_index

implement the_term_index_getinc () = let
  val n = !the_term_index
  val () = !the_term_index := n + 1
  val () = if (n >= TERM_INDEX_MAX1) then begin
    prerr "exit(ATSYACC): there are too many terminals!"; prerr_newline ();
    exit {void} (1)
  end // end of [val]
in
  n
end // end of [the_term_index_getinc]

extern fun the_nonterm_index_get (): int
extern fun the_nonterm_index_getinc (): int

implement the_nonterm_index_get () = !the_nonterm_index
implement the_nonterm_index_getinc () = let
  val n = !the_nonterm_index; val () = !the_nonterm_index := n+1 in n
end // end of [the_nonterm_index_getinc]

//  

implement symbol_make_newname (knd, name) = sym where {
(*
  val () = begin
    print "symbol_make_newname: name = "; print name; print_newline ()
  end // end of [val]
*)
  val index = (case+ knd of
    | SYMKINDterm () => the_term_index_getinc ()
    | SYMKINDnonterm () => the_nonterm_index_getinc ()
  ) : int
(*
  val () = begin
    print "symbol_make_newname: index = "; print index; print_newline ()
  end // end of [val]
*)
  val sym = symbol_make_name_index (name, index)
  val ans = begin
    $H.hashtbl_insert_err<string,symbol_t> (the_symtbl, name, sym)
  end // end of [val]
  val () = case+ ans of
    | ~None_vt () => () | ~Some_vt _ => begin
        prerr "Internal Error: symbol_make_newname"; prerr_newline ();
        exit (1)
      end // end of [Some_vt]
  // end of [val]
} // end of [symbol_make_newname]

//

implement the_end_symbol =
  symbol_make_newname (SYMKINDterm, "$end")

implement symbol_is_end (x) = begin
  x.symbol_index = the_end_symbol.symbol_index
end // end of [symbol_is_end]

implement the_accept_symbol =
  symbol_make_newname (SYMKINDnonterm, "$accept")

//

implement eq_symbol_symbol (x1, x2) =
  (x1.symbol_index = x2.symbol_index)
implement neq_symbol_symbol (x1, x2) =
  (x1.symbol_index <> x2.symbol_index)

implement compare_symbol_symbol (x1, x2) =
  compare (x1.symbol_index, x2.symbol_index)

(* ****** ****** *)

implement fprint_symbol (pf_mod | out, x) = let
  val () = fprint1_string (pf_mod | out, x.symbol_name)
(*  
  val () = fprintf (pf_mod | out, "(%i)", @(x.symbol_index))
*)
in
  // empty
end // end of [fprint_symbol]

implement print_symbol (x) = print_mac (fprint_symbol, x)
implement prerr_symbol (x) = prerr_mac (fprint_symbol, x)

(* ****** ****** *)

implement symbol_is_term (x) =
  if x.symbol_index < TERM_INDEX_MAX1 then true else false

implement symbol_is_nonterm (x) =
  if x.symbol_index >= TERM_INDEX_MAX1 then true else false

(* ****** ****** *)

implement symbol_term_total_get () =
  the_term_index_get ()

implement symbol_nonterm_total_get () =
  (the_nonterm_index_get () - TERM_INDEX_MAX1)

(* ****** ****** *)

extern typedef "symbol_t" = symbol

(* ****** ****** *)

//
// this function must be called before the following one:
// [the_nullfrstfllw_table_gen]
//

extern fun the_allsym_initialize (): void = "atsyacc_the_allsym_initialize"

implement the_allsym_initialize () = () where {
  val n = symbol_term_total_get ()
  val () = the_bitvecsz_set (n) where {
    extern fun the_bitvecsz_set (n: int): void = "atsyacc_the_bitvecsz_set"
  }
  val () = the_alltermarr_alloc (n) where { extern fun
    the_alltermarr_alloc (n: int): void = "atsyacc_the_alltermarr_alloc"
  } // end of [val]
  var !p_clo = @lam
    (pf: !unit_v | _: string, x: &symbol_t): void => begin case+ 0 of
    | _ when symbol_is_term x => let
        val () = the_alltermarr_set (x) where { extern fun
          the_alltermarr_set (x: symbol_t): void = "atsyacc_the_alltermarr_set"
        } // end of [val]
        val x_frstset = symbolset_sing x and x_fllwset = symbolset_nil ()
      in
        symbol_frstset_set (x, x_frstset); symbol_fllwset_set (x, x_fllwset)
      end // end of [_ when ...]
    | _ => let
        val x_frstset = symbolset_nil () and x_fllwset = symbolset_nil ()
      in
        symbol_frstset_set (x, x_frstset); symbol_fllwset_set (x, x_fllwset)
      end // end of [_]
  end // end of [var]
  prval pf = unit_v ()
  val () = begin
    $H.hashtbl_foreach_clo<string,symbol_t> {unit_v} (pf | the_symtbl, !p_clo)
  end // end of [val]
  prval unit_v () = pf
} // end of [symbol_term_total_get]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

%{$

ats_int_type
atsyacc_symbol_assoc_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_assoc ;
}

ats_void_type
atsyacc_symbol_assoc_set
  (ats_ptr_type sym, ats_int_type assoc) {
  ((symbol_t)sym)->atslab_symbol_assoc = assoc ;
  return ;
}

/* ****** ****** */

ats_bool_type
atsyacc_symbol_nullable_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_nullable ;
}

ats_void_type
atsyacc_symbol_nullable_set
  (ats_ptr_type sym, ats_bool_type nullable) {
  ((symbol_t)sym)->atslab_symbol_nullable = nullable ;
  return ;
}

/* ****** ****** */

ats_ptr_type // symbolset
atsyacc_symbol_frstset_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_frstset ;
}

ats_void_type
atsyacc_symbol_frstset_set
  (ats_ptr_type sym, ats_ptr_type frstset) {
  ((symbol_t)sym)->atslab_symbol_frstset = frstset ;
  return ;
}

/* ****** ****** */

ats_ptr_type // symbolset
atsyacc_symbol_fllwset_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_fllwset ;
}

ats_void_type
atsyacc_symbol_fllwset_set
  (ats_ptr_type sym, ats_ptr_type fllwset) {
  ((symbol_t)sym)->atslab_symbol_fllwset = fllwset ;
  return ;
}

/* ****** ****** */

ats_ptr_type // symbolset
atsyacc_symbol_rulerhslst_get (ats_ptr_type sym) {
  return ((symbol_t)sym)->atslab_symbol_rulerhslst ;
}

ats_void_type
atsyacc_symbol_rulerhslst_set
  (ats_ptr_type sym, ats_ptr_type rulerhslst) {
  ((symbol_t)sym)->atslab_symbol_rulerhslst = rulerhslst ;
  return ;
}

/* ****** ****** */

//
// this part is needed for the implementation of the function
// [the_alltermarr_make] implemented in [atsyacc_main]
//

// this array holds all terminals
static ats_ptr_type the_alltermarr = 0 ;

ats_void_type
atsyacc_the_alltermarr_alloc (ats_int_type n) {
  the_alltermarr = ATS_MALLOC (n * sizeof (symbol_t)) ;
  return ;
} /* atsyacc_the_alltermarr_alloc */

ats_ptr_type
atsyacc_the_alltermarr_get (ats_int_type ind) {
  ats_ptr_type sym ;
  sym = ((symbol_t*)the_alltermarr)[ind] ; return sym ;
} /* atsyacc_the_alltermarr_get */

ats_void_type
atsyacc_the_alltermarr_set (ats_ptr_type sym) {
  int ind ;
  ind = atsyacc_symbol_index_get (sym) ; 
  ((symbol_t*)the_alltermarr)[ind] = sym ; return ;
} /* atsyacc_the_alltermarr_set */

%}

(* ****** ****** *)

(* end of [symbol.dats] *)
