(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

abstype HASHTBLref (key: t@ype, itm: viewt@ype)

staload H = "libats/SATS/hashtable_chain.sats"

(* ****** ****** *)

extern
castfn HASHTBLref_encode
  {key:t@ype;itm:viewt@ype}
  {l:agz} (x: $H.HASHTBLptr (key, itm, l)): HASHTBLref (key, itm)
// end of [HASHTBLref_encode]

extern
castfn HASHTBLref_decode
  {key:t@ype;itm:viewt@ype} (x: HASHTBLref (key, itm)) : [l:agz] (
  $H.HASHTBLptr (key, itm, l) -<lin,prf> void | $H.HASHTBLptr (key, itm, l)
) // end of [HASHTBLref_decode]

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"
staload _(*anon*) = "libats/DATS/hashtable_chain.dats"

(* ****** ****** *)

local

assume symbol_t = '{
  symbol_name= string, symbol_index= int
} // end of [symbol_t]

val the_symtbl
  : HASHTBLref (string, symbol_t) = let
  val hash = lam (x: string): ulint =<cloref> string_hash_33 (x)
  val eqfn = lam (x1: string, x2: string): bool =<cloref> (x1 = x2)
  val x = $H.hashtbl_make {string,symbol_t} (hash, eqfn)
in
  HASHTBLref_encode (x)
end // end of [val]

val the_symcnt = ref_make_elt<int> (0)

in // in of [local]

fn symbol_make_name_index
  (name: string, index: int): symbol_t = '{
  symbol_name= name
, symbol_index= index
} // end of [symbol_make_name_index]

implement
symbol_make_name (name: string) = let
  var res: symbol_t?
  val (fpf_x | x) = HASHTBLref_decode (the_symtbl)
  val ans = $H.hashtbl_search (x, name, res)
  prval () = fpf_x (x)
in
  if ans then let
    prval () = opt_unsome {symbol_t} (res) in res
  end else let
    prval () = opt_unnone {symbol_t} (res)
    val n = !the_symcnt; val () = !the_symcnt := n+1
    val sym = symbol_make_name_index (name, n)
    val (fpf_x | x) = HASHTBLref_decode (the_symtbl)    
    val () = $H.hashtbl_insert<string,symbol_t> (x, name, sym)
    prval () = fpf_x (x)  
  in
    sym
  end // end of [if]
end // end of [symbol_make]

implement symbol_get_name (x) = x.symbol_name

//

implement fprint_symbol (out, x) = fprint (out, x.symbol_name)

(*

implement fprint_symbol (out, x) =
  fprintf (out, "%s(%i)", @(x.symbol_name, x.symbol_index))

*)

implement print_symbol (x) = fprint_symbol (stdout_ref, x)
implement prerr_symbol (x) = fprint_symbol (stderr_ref, x)

//

implement eq_symbol_symbol
  (x1, x2) = x1.symbol_index = x2.symbol_index
// end of [eq_symbol_symbol]

implement neq_symbol_symbol
  (x1, x2) = x1.symbol_index <> x2.symbol_index
// end of [eq_symbol_symbol]

implement compare_symbol_symbol (x1, x2) =
  compare (x1.symbol_index, x2.symbol_index)
// end of [eq_symbol_symbol]

end // end of [local]

(* ****** ****** *)

implement symbol_BOOL = symbol_make_name "bool"
implement symbol_INT = symbol_make_name "int"
implement symbol_STRING = symbol_make_name "string"
implement symbol_UNIT = symbol_make_name "unit"

(* ****** ****** *)

implement symbol_PLUS = symbol_make_name "+"
implement symbol_MINUS = symbol_make_name "-"
implement symbol_TIMES = symbol_make_name "*"
implement symbol_SLASH = symbol_make_name "/"
implement symbol_UMINUS = symbol_make_name "~"

implement symbol_GT = symbol_make_name ">"
implement symbol_GTE = symbol_make_name ">="
implement symbol_LT = symbol_make_name "<"
implement symbol_LTE = symbol_make_name "<="
implement symbol_EQ = symbol_make_name "="
implement symbol_NEQ = symbol_make_name "<>"

implement symbol_PRINT = symbol_make_name "print"
implement symbol_PRINT_INT = symbol_make_name "print_int"

(* ****** ****** *)

local

staload M = "libats/SATS/funmap_avltree.sats"
staload _(*M*) = "libats/DATS/funmap_avltree.dats"
assume symenv_t (a:t@ype) = $M.map (symbol_t, a)
typedef key = symbol_t
fn{} cmp (k1:key, k2:key):<cloref> Sgn = compare (k1, k2)

in // in of [local]

implement{a}
symenv_make_nil () = $M.funmap_make_nil ()

(*
fun{key,itm:t@ype}
funmap_search (
  m: map (key, itm), k0: key, cmp: cmp key, res: &itm? >> opt (itm, b)
) :<> #[b:bool] bool b
// end of [funmap_search]
*)
implement{a}
symenv_lookup (env, k0) = let
  var res: a?
  val ans =
    $M.funmap_search<key,a> (env, k0, cmp, res)
  // end of [val]
in
  if ans then let
    prval () = opt_unsome {a} (res) in Some_vt (res)
  end else let
    prval () = opt_unnone {a} (res) in None_vt ()
  end // end of [if]
end // end of [symenv_lookup]

(*
fun{key,itm:t@ype} funmap_insert (
  m: &map (key, itm), k0: key, x0: itm, cmp: cmp key
) :<> bool(*[k0] alreay exists in [m]*) // end of [funmap_insert]
*)
implement{a}
symenv_insert (env, k, i) = env where {
  var env = env
  val ans(*discarded*) = $M.funmap_insert<key,a> (env, k, i, cmp)
} // end of [symenv_insert]

end // end of [local]

(* ****** ****** *)

(* end of [symbol.dats] *)
