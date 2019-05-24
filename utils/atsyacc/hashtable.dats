(*
**
** A hashtable implementation
** where buckets are represented as linked lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

typedef hash (key: t@ype) = (key) -<cloref> uint
typedef eq (key: t@ype) = (key, key) -<cloref> bool

abstype hashtbl_t (key:t@ype, itm:viewt@ype+)

(* ****** ****** *)

extern fun{key:t@ype}
  equal_key_key (x1: key, x2: key, eq: eq key):<> bool

implement{key} equal_key_key (x1, x2, eq) = eq (x1, x2)

(* ****** ****** *)

extern fun{key:t@ype}
  hash_key (x: key, hash: hash key):<> uint

implement{key} hash_key (x, hash) = hash (x)

(* ****** ****** *)

extern fun hashtbl_size
  {key:t@ype;itm:viewt@ype} (tbl: hashtbl_t (key, itm)): Nat

extern fun hashtbl_total
  {key:t@ype;itm:viewt@ype} (tbl: hashtbl_t (key, itm)): Nat

extern fun{key:t@ype;itm:viewt@ype}
  hashtbl_make (hash: hash key, eq: eq key): hashtbl_t (key, itm)

extern fun{key:t@ype;itm:viewt@ype}
  hashtbl_make_hint (hash: hash key, eq: eq key, hint: Nat): hashtbl_t (key, itm)

extern fun{key:t@ype;itm:t@ype}
  hashtbl_search (tbl: hashtbl_t (key, itm), k0: key): Option_vt itm

extern fun{key:t@ype;itm:viewt@ype}
  hashtbl_insert_err (tbl: hashtbl_t (key, itm), k: key, i: itm): Option_vt itm

extern fun{key:t@ype;itm:viewt@ype}
  hashtbl_remove_err (tbl: hashtbl_t (key, itm), k0: key): Option_vt itm

extern fun{key:t@ype;itm:t@ype}
  hashtbl_clear (tbl: hashtbl_t (key, itm)): void

extern fun{} hashtbl_free_err
  {key:t@ype;itm:viewt@ype} (tbl: hashtbl_t (key, itm)): int

extern fun{} hashtbl_free_exn
  {key:t@ype;itm:viewt@ype} (tbl: hashtbl_t (key, itm)): void

(* ****** ****** *)

extern fun{key:t@ype;itm:viewt@ype} hashtbl_foreach_clo {v:view}
  (pf: !v | tbl: hashtbl_t (key, itm), f: &(!v | key, &itm) -<clo1> void): void

extern fun{key:t@ype;itm:viewt@ype} hashtbl_foreach_cloref {v:view}
  (pf: !v | tbl: hashtbl_t (key, itm), f: !(!v | key, &itm) -<cloref1> void): void

(* ****** ****** *)

dataviewtype chain (key:t@ype, itm:viewt@ype+, int) =
  | {n:nat} CHAINcons (key, itm, n+1) of (key, itm, chain (key, itm, n))
  | CHAINnil (key, itm, 0)

viewtypedef chain (key:t@ype,itm:viewt@ype) = [n:nat] chain (key, itm, n)
viewtypedef chain0 = chain (void, void, 0)

(* ****** ****** *)

stadef chainsz = sizeof (chain0)
extern typedef "chain0" = chain0

(* ****** ****** *)

#define nil CHAINnil; #define cons CHAINcons

(* ****** ****** *)

fun{key:t@ype;itm:t@ype} chain_free {n:nat} .<n>.
  (kis: chain (key, itm, n)):<> void = begin case+ kis of
  | ~cons (_(*key*), _(*itm*), kis) => chain_free (kis) | ~nil () => ()
end // end of [chain_free]

(* ****** ****** *)

fun{key:t@ype;itm:t@ype} chain_search {n:nat} .<n>.
  (kis: !chain (key,itm,n), k0: key, eq: eq key):<> Option_vt itm =
  case+ kis of
  | cons (k, i, !kis1) => let
      val keq = equal_key_key (k0, k, eq)
    in
      if keq then (fold@ kis; Some_vt i) else let
        val ans = chain_search (!kis1, k0, eq)
      in
        fold@ kis; ans
      end // end of [if]
    end // end of [cons]
  | nil () => (fold@ kis; None_vt ())
// end of [chain_search]

fn{key:t@ype;itm:viewt@ype} chain_insert {n:nat}
  (kis: &chain (key,itm,n) >> chain (key,itm,n+1), k: key, i: itm):<> void =
  kis := cons (k, i, kis)
// end of [chain_insert]

stadef b2i = int_of_bool
fun{key:t@ype;itm:viewt@ype} chain_remove {n:nat} .<n>.
  (kis: &chain (key,itm,n) >> chain (key,itm,n-b2i b), k0: key, eq: eq key)
  :<> #[b:bool | b2i b <= n] option_vt (itm, b) = begin case+ kis of
  | cons (k, !i, !kis1) => let
      val keq = equal_key_key (k0, k, eq)
    in
      if keq then let
        val i = !i and kis1 = !kis1
      in
        free@ {key,itm} {n} (kis); kis := kis1; Some_vt i
      end else let
        val ans = chain_remove<key,itm> {n-1} (!kis1, k0, eq)
      in
        fold@ kis; ans
      end // end of [if]
    end // end of [cons]
  | nil () => let
      prval () = fold@ kis in None_vt ()
    end // end of [nil]
end // end of [chain_remove]

fun{key:t@ype;itm:viewt@ype}
  chain_foreach_clo {v:view} {n:nat} {f:eff} .<n>. (
    pf: !v | kis: !chain (key, itm, n), f: &(!v | key, &itm) -<clo,f> void
  ) :<f> void = begin case+ kis of
  | cons (k, !i, !kis1) => begin
      f (pf | k, !i); chain_foreach_clo (pf | !kis1, f); fold@ kis
    end // end of [cons]
  | nil () => fold@ kis
end // end of [chain_foreach_clo]

(* ****** ****** *)

dataview hashtbl_v
  (key:t@ype, itm:viewt@ype+, int(*sz*), int(*tot*), addr, addr) =
  | {sz,tot,n:nat} {l_beg,l_end:addr}
    hashtbl_v_cons (key, itm, sz+1, tot+n, l_beg, l_end) of
      (chain (key, itm, n) @ l_beg, hashtbl_v (key, itm, sz, tot, l_beg+chainsz, l_end))
  | {l:addr} hashtbl_v_nil (key, itm, 0, 0, l, l)

extern prfun // proof is omitted
  hashtbl_v_split {key:t@ype;itm:viewt@ype}
  {sz,sz1,tot:nat | sz1 <= sz} {l_beg,l_end:addr} {ofs:int} (
    pf_mul: MUL (sz1, sizeof(chain0), ofs)
  , pf_tbl: hashtbl_v (key, itm, sz, tot, l_beg, l_end)
  ) :<> [tot1:nat | tot1 <= tot] @(
    hashtbl_v (key, itm, sz1, tot1, l_beg, l_beg+ofs)
  , hashtbl_v (key, itm, sz-sz1, tot-tot1, l_beg+ofs, l_end)
  ) // end of [hashtbl_split]

extern prfun // proof is omitted
  hashtbl_v_unsplit {key:t@ype;itm:viewt@ype}
  {sz1,sz2,tot1,tot2:nat} {l_beg,l_mid,l_end:addr} (
    pf1: hashtbl_v (key, itm, sz1, tot1, l_beg, l_mid)
  , pf2: hashtbl_v (key, itm, sz2, tot2, l_mid, l_end)
  ) :<prf> hashtbl_v (
      key, itm, sz1+sz2, tot1+tot2, l_beg, l_end
    ) // end of [hashtbl_v_unsplit]

(* ****** ****** *)

fn{} hashtbl_split {key:t@ype;itm:viewt@ype}
  {sz,sz1,tot:nat | sz1 <= sz} {l_beg,l_end:addr} (
    pf_tbl: hashtbl_v (key, itm, sz, tot, l_beg, l_end)
  | p_beg: ptr l_beg, sz1: size_t sz1
  ) :<> [tot1:nat | tot1 <= tot] [l_mid:addr] @(
      hashtbl_v (key, itm, sz1, tot1, l_beg, l_mid)
    , hashtbl_v (key, itm, sz-sz1, tot-tot1, l_mid, l_end)
    | ptr l_mid
    ) = let
  val (pf_mul | ofs) = mul2_size1_size1 (sz1, sizeof<chain0>)
  prval (pf1_tbl, pf2_tbl) = hashtbl_v_split {key,itm} (pf_mul, pf_tbl)
in
  (pf1_tbl, pf2_tbl | p_beg + ofs)
end // end of [hashtbl_split]

(* ****** ****** *)

fn{key:t@ype;itm:t@ype} hashtbl_ptr_search_off
  {sz,off,tot:nat | off < sz} {l_beg,l_end:addr} (
    pf: !hashtbl_v (key, itm, sz, tot, l_beg, l_end)
  | p_beg: ptr l_beg, k0: key, eq: eq key, off: size_t off
  ) :<> Option_vt itm = let
  val (pf1, pf2 | p_mid) =
    hashtbl_split<> {..} {sz,off,tot} (pf | p_beg, off)
  prval hashtbl_v_cons (pf21, pf22) = pf2
  val ans = chain_search (!p_mid, k0, eq)
  prval pf2 = hashtbl_v_cons (pf21, pf22)
  prval () = pf := hashtbl_v_unsplit (pf1, pf2)
in
  ans
end // end of [hashtbl_ptr_search_off]

(* ****** ****** *)

fn{key:t@ype;itm:viewt@ype} hashtbl_ptr_insert_off
  {sz,off,tot:nat | off < sz} {l_beg,l_end:addr} (
    pf: !hashtbl_v (key, itm, sz, tot, l_beg, l_end)
          >> hashtbl_v (key, itm, sz, tot+1, l_beg, l_end)
  | p_beg: ptr l_beg, k: key, i: itm, off: size_t off
  ) :<> void = let
  val (pf1, pf2 | p_mid) =
    hashtbl_split<> {..} {sz,off,tot} (pf | p_beg, off)
  prval hashtbl_v_cons (pf21, pf22) = pf2
  val ans = chain_insert (!p_mid, k, i)
  prval pf2 = hashtbl_v_cons (pf21, pf22)
  prval () = pf := hashtbl_v_unsplit (pf1, pf2)
in
  // empty
end // end of [hashtbl_ptr_insert_off]

(* ****** ****** *)

fn{key:t@ype;itm:viewt@ype} hashtbl_ptr_remove_off
  {sz,off,tot:nat | off < sz} {l_beg,l_end:addr} (
    pf: !hashtbl_v (key, itm, sz, tot, l_beg, l_end)
          >> hashtbl_v (key, itm, sz, tot-b2i b, l_beg, l_end)
  | p_beg: ptr l_beg, k0: key, eq: eq key, off: size_t off
  ) :<> #[b:bool | b2i b <= tot] option_vt (itm, b) = let
  val (pf1, pf2 | p_mid) =
    hashtbl_split<> {..} {sz,off,tot} (pf | p_beg, off)
  prval hashtbl_v_cons (pf21, pf22) = pf2
  val ans = chain_remove (!p_mid, k0, eq)
  prval pf2 = hashtbl_v_cons (pf21, pf22)
  prval () = pf := hashtbl_v_unsplit (pf1, pf2)
in
  ans
end // end of [hashtbl_ptr_remove_off]

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
  hashtbl_ptr_insert_chain
  {sz:pos;tot,n:nat} {l_beg,l_end:addr} .<n>. (
    pf: !hashtbl_v (key, itm, sz, tot, l_beg, l_end)
          >> hashtbl_v (key, itm, sz, tot+n, l_beg, l_end)
  | sz: int sz
  , p_beg: ptr l_beg
  , kis: chain (key, itm, n)
  , hash: hash key
  ) :<> void = begin case+ kis of
  | ~cons (k, i, kis) => let
      // insertion must be done in the reverse order!
      val () = hashtbl_ptr_insert_chain (pf | sz, p_beg, kis, hash)
      val h = hash_key (k, hash)
      val h = uint1_of_uint (h)
      val [off:int] off = h mod sz; val off = size1_of_int1 off
      val (pf1, pf2 | p_mid) =
        hashtbl_split<> {..} {sz,off,tot+n-1} (pf | p_beg, off)
      prval hashtbl_v_cons (pf21, pf22) = pf2
      val () = chain_insert (!p_mid, k, i)
      prval pf2 = hashtbl_v_cons (pf21, pf22)
      prval () = pf := hashtbl_v_unsplit (pf1, pf2)
    in
      // empty
    end // end of [cons]
  | ~nil () => ()
end // end of [hashtbl_ptr_insert_chain]

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
  hashtbl_ptr_relocate
  {sz1:nat;sz2:pos;tot1,tot2:nat} .<sz1>.
  {l1_beg,l2_beg,l1_end,l2_end:addr} (
    pf1: !hashtbl_v (key, itm, sz1, tot1, l1_beg, l1_end)
          >> hashtbl_v (key, itm, sz1, 0(*tot*), l1_beg, l1_end)
  , pf2: !hashtbl_v (key, itm, sz2, tot2, l2_beg, l2_end)
          >> hashtbl_v (key, itm, sz2, tot1+tot2, l2_beg, l2_end)
  | sz1: int sz1, sz2: int sz2, p1_beg: ptr l1_beg, p2_beg: ptr l2_beg
  , hash: hash key
  ) :<> void = begin
  if sz1 > 0 then let
    prval hashtbl_v_cons (pf11, pf12) = pf1
    val kis = !p1_beg; val () = !p1_beg := nil ()
    val () = hashtbl_ptr_insert_chain (pf2 | sz2, p2_beg, kis, hash)
    val () = hashtbl_ptr_relocate
      (pf12, pf2 | sz1-1, sz2, p1_beg+sizeof<chain0>, p2_beg, hash)
    prval () = pf1 := hashtbl_v_cons (pf11, pf12)
  in
    // empty
  end else let
    prval hashtbl_v_nil () = pf1; prval () = pf1 := hashtbl_v_nil ()
  in
    // empty
  end // end of [if]
end // end of [hashtbl_ptr_relocate]

(* ****** ****** *)

fun{key:t@ype;itm:t@ype}
  hashtbl_ptr_clear
    {sz:nat;tot:nat} {l_beg,l_end:addr} .<sz>. (
    pf: !hashtbl_v (key, itm, sz, tot, l_beg, l_end)
          >> hashtbl_v (key, itm, sz, 0(*tot*), l_beg, l_end)
  | sz: int sz, p_beg: ptr l_beg
  ) :<> void = begin
  if sz > 0 then let
    prval hashtbl_v_cons (pf1, pf2) = pf
    val () = chain_free (!p_beg); val () = !p_beg := nil ()
    val () = hashtbl_ptr_clear<key,itm> (pf2 | sz-1, p_beg+sizeof<chain0>)
    prval () = pf := hashtbl_v_cons (pf1, pf2)
  in
    // empty
  end else let
    prval hashtbl_v_nil () = pf; prval () = pf := hashtbl_v_nil ()
  in
    // empty
  end // end of [if]
end // end of [hashtbl_ptr_clear]

(* ****** ****** *)

extern fun hashtbl_ptr_make
  {key:t@ype;itm:viewt@ype} {sz:pos} (sz: int sz)
  :<> [l_beg,l_end:addr] @(
    free_gc_v l_beg
  , hashtbl_v (key, itm, sz, 0(*tot*), l_beg, l_end)
  | ptr l_beg
  ) // end of [hashtbl_ptr_make]
  = "hashtbl_ptr_make"

extern fun hashtbl_ptr_free
  {key:t@ype;itm:viewt@ype} {sz:pos} {l_beg,l_end:addr} (
    pf_gc: free_gc_v l_beg
  , pf_tbl: hashtbl_v (key, itm, sz, 0(*tot*), l_beg, l_end)
  | p_beg: ptr l_beg
  ) :<> void
  = "hashtbl_ptr_free"

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
  hashtbl_ptr_foreach_clo {v:view}
    {sz,tot:nat} {l_beg,l_end:addr} {f:eff} .<sz>. (
    pf: !v, pf_tbl: !hashtbl_v (key, itm, sz, tot, l_beg, l_end)
  | sz: int sz, p_beg: ptr l_beg, f: &(!v | key, &itm) -<clo,f> void
  ) :<f> void = begin
  if sz > 0 then let
    prval hashtbl_v_cons (pf1_tbl, pf2_tbl) = pf_tbl
    val () = chain_foreach_clo (pf | !p_beg, f)
    val () = // segfault during typechecking if {v} is not provided!!!
      hashtbl_ptr_foreach_clo<key,itm> {v}
        (pf, pf2_tbl | sz-1, p_beg+sizeof<chain0>, f)
    prval () = pf_tbl := hashtbl_v_cons (pf1_tbl, pf2_tbl)
  in
    // empty
  end // end of [if]
end // end of [hashtbl_ptr_foreach_clo]

(* ****** ****** *)

dataviewtype hashtbl_vt (key:t@ype,itm:viewt@ype) =
  | {sz:pos;tot:nat} {l_beg,l_end:addr}
    hashtbl_vt_some (key, itm) of (
      free_gc_v (l_beg)
    , hashtbl_v (key, itm, sz, tot, l_beg, l_end)
    | int sz, int tot, ptr l_beg, hash key, eq key
    ) // end of [hashtbl_vt_some]
  | hashtbl_vt_none (key, itm) of ()

(* ****** ****** *)

assume hashtbl_t
  (key:t@ype, itm:viewt@ype) = ref (hashtbl_vt (key, itm))

(* ****** ****** *)

implement hashtbl_size (tbl) = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
in
  case+ !p_tbl of
  | hashtbl_vt_some (_, _ | sz, _, _, _, _) => (fold@ !p_tbl; sz)
  | hashtbl_vt_none () => (fold@ !p_tbl; 0)
end // end of [hashtbl_size]

(* ****** ****** *)

implement hashtbl_total (tbl) = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
in
  case+ !p_tbl of
  | hashtbl_vt_some (_, _ | _, tot, _, _, _) => (fold@ !p_tbl; tot)
  | hashtbl_vt_none () => (fold@ !p_tbl; 0)
end // end of [hashtbl_total]

(* ****** ****** *)

implement{key,itm} hashtbl_search (tbl, k0) = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
in
  case+ !p_tbl of
  | hashtbl_vt_some (_, !pf | sz, _, p_beg, hash, eq) => let
      val h = hash_key (k0, hash)
      val h = uint1_of_uint (h)
      val off = h mod sz; val off = size1_of_int1 off
      val ans = hashtbl_ptr_search_off (!pf | p_beg, k0, eq, off)
    in
      fold@ !p_tbl; ans
    end // end of [hashtbl_vt_some]
  | hashtbl_vt_none () => (fold@ !p_tbl; None_vt ())
end // end of [hashtbl_search]

(* ****** ****** *)

fn{key:t@ype;itm:viewt@ype}
  hashtbl_resize {sz_new:pos} (
    tbl: hashtbl_t (key, itm), sz_new: int sz_new
  ) : void = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
in
  case+ !p_tbl of
  | hashtbl_vt_some (!pf_gc, !pf | !sz, _(*tot*), !p, hash, eq) => let
      prval pf1_gc = !pf_gc and pf1 = !pf; val p1 = !p
      val (pf2_gc, pf2 | p2) = hashtbl_ptr_make (sz_new)
      val () = hashtbl_ptr_relocate (pf1, pf2 | !sz, sz_new, !p, p2, hash)
      val () = hashtbl_ptr_free (pf1_gc, pf1 | p1)
    in
      !pf_gc := pf2_gc; !pf := pf2; !sz := sz_new; !p := p2; fold@ !p_tbl
    end
  | hashtbl_vt_none () => (fold@ !p_tbl)
end // end of [hashtbl_resize]

(* ****** ****** *)

#define HASHTABLE_DOUBLE_THRESHOLD 5.0
#assert (HASHTABLE_DOUBLE_THRESHOLD > 2.0)
#define HASHTABLE_HALF_THRESHOLD 0.5
#assert (HASHTABLE_HALF_THRESHOLD < 1.0)

fn{key:t@ype;itm:viewt@ype}
  hashtbl_resize_double (tbl: hashtbl_t (key, itm)): void = let
  val sz = hashtbl_size (tbl)
in
  if sz > 0 then hashtbl_resize (tbl, sz + sz) else ()
end // end of [hashtbl_resize_double]

fn{key:t@ype;itm:viewt@ype}
  hashtbl_resize_half (tbl: hashtbl_t (key, itm)): void = let
  val sz = hashtbl_size (tbl)
in
  if sz >= 2 then hashtbl_resize (tbl, sz / 2) else ()
end // end of [hashtbl_resize_half]

(* ****** ****** *)

implement{key,itm} hashtbl_insert_err (tbl, k, i) = let
  var ratio: double = 0.0
  val ans = let
    val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
  in
    case+ !p_tbl of
    | hashtbl_vt_some (_, !pf | sz, !tot, p_beg, hash, eq) => let
        val tot1 = !tot + 1
        val () = ratio := double_of_int (tot1) / sz
        val h = hash_key (k, hash)
        val h = uint1_of_uint (h)
        val off = h mod sz; val off = size1_of_int1 off
        val () = hashtbl_ptr_insert_off<key,itm> (!pf | p_beg, k, i, off)
      in
        !tot := !tot + 1; fold@ !p_tbl; None_vt ()
      end // end of [hashtbl_vt_some]
    | hashtbl_vt_none () => (fold@ !p_tbl; Some_vt i)
  end : Option_vt itm // end of [val]
  val () = begin
    if ratio >= HASHTABLE_DOUBLE_THRESHOLD then hashtbl_resize_double (tbl)
  end // end of [val]
in
  ans
end // end of [hashtbl_insert_err]

(* ****** ****** *)

implement{key,itm} hashtbl_remove_err (tbl, k0) = let
  var ratio: double = 1.0
  val ans = let
    val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
  in
    case+ !p_tbl of
    | hashtbl_vt_some (_, !pf | sz, !tot, p_beg, hash, eq) => let
        val h = hash_key (k0, hash)
        val h = uint1_of_uint (h)
        val off = h mod sz; val off = size1_of_int1 (off)
        val ans = hashtbl_ptr_remove_off<key,itm> (!pf | p_beg, k0, eq, off)
        val () = case+ ans of
          | Some_vt _ => let
              val tot1 = !tot - 1
              val () = ratio := double_of_int (tot1) / sz
            in
              fold@ ans; !tot := tot1; fold@ !p_tbl
            end // end of [Some_vt]
          | None_vt _ => (fold@ ans; fold@ !p_tbl)
      in
        ans
      end // end of [hashtbl_vt_some]
    | hashtbl_vt_none () => (fold@ !p_tbl; None_vt ())
  end : Option_vt itm // end of [val]
  val () = if ratio <= HASHTABLE_HALF_THRESHOLD then hashtbl_resize_half (tbl)
in
  ans
end // end of [hashtbl_remove_err]

(* ****** ****** *)

(*
// some prime numbers
53, 97, 193, 389, 769, 1543, 3079, 6151, 12289, 24593, 49157, 98317, 196613, 393241, 786433, 1572869, 3145739, 6291469, 12582917, 25165843, 50331653, 100663319, 201326611, 402653189, 805306457, 1610612741
*)

#define HASHTABLE_SIZE_HINT 97

implement{key,itm} hashtbl_make (hash, eq) = begin
  hashtbl_make_hint<key,itm> (hash, eq, 0)
end // end of [hashtbl_make]

implement{key,itm} hashtbl_make_hint (hash, eq, hint) = let
  val sz = (if hint > 0 then hint else HASHTABLE_SIZE_HINT): Pos
  val (pf_gc, pf | p_beg) = hashtbl_ptr_make (sz)
  val tbl = hashtbl_vt_some (pf_gc, pf | sz, 0, p_beg, hash, eq)
in
  ref_make_elt<hashtbl_vt(key,itm)> (tbl)
end // end of [hashtbl_make_hint]

(* ****** ****** *)

implement{key,itm} hashtbl_clear (tbl) = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
in
  case+ !p_tbl of
  | hashtbl_vt_some
      (!pf_gc, !pf | sz, !tot, p_beg, _, _) => let
      val () = hashtbl_ptr_clear (!pf | sz, p_beg)
    in
      !tot := 0; fold@ !p_tbl
    end // end of [hashtbl_vt_some]
  | hashtbl_vt_none () => fold@ !p_tbl
end // end of [hashtbl_clear]

(* ****** ****** *)

#define HashtblFreeError1 1 // freeing a nonempty hashtable
#define HashtblFreeError2 2 // freeing an already freed hashtable

implement{} hashtbl_free_err (tbl) = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
  var err: int = 0
  val () = case+ !p_tbl of
    | hashtbl_vt_some {..} {sz,tot}
        (!pf_gc, !pf | sz, tot, p_beg, _, _) => begin
        if tot = 0 then let
          val () = hashtbl_ptr_free (!pf_gc, !pf | p_beg)
        in
          free@ {..} {sz,tot} !p_tbl; !p_tbl := hashtbl_vt_none ()
        end else begin
          fold@ !p_tbl; err := HashtblFreeError1
        end // end of [if]
      end // end of [hashtbl_vt_some]
    | hashtbl_vt_none () => (fold@ !p_tbl; err := HashtblFreeError2)
  // end of [val]
in
  err // error code
end // end of [hashtbl_free_err]

exception HashtblFreeException of int

implement{} hashtbl_free_exn (tbl) = let
  val err = hashtbl_free_err (tbl)
in
  if err > 0 then $raise HashtblFreeException (err) else ()
end // end of [hashtbl]

(* ****** ****** *)

implement{key,itm}
  hashtbl_foreach_clo {v} (pf0 | tbl, f) = let
  val (vbox pf_tbl | p_tbl) = ref_get_view_ptr (tbl)
in
  case+ !p_tbl of
  | hashtbl_vt_some (_, !pf | sz, _, p_beg, _, _) => let
      val () = $effmask_ref begin
        hashtbl_ptr_foreach_clo {v} (pf0, !pf | sz, p_beg, f)
      end
    in
      fold@ !p_tbl
    end // end of [cons]
  | hashtbl_vt_none () => fold@ !p_tbl
end // end of [hashtbl_foreach_clo]

(* ****** ****** *)

implement{key,itm}
  hashtbl_foreach_cloref {v} (pf0 | tbl, f) = let
  typedef clo_type = (!v | key, &itm) -<clo1> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  val () = $effmask_ref (hashtbl_foreach_clo<key,itm> {v} (pf0 | tbl, !p_f))
in
  // empty
end // end of [hashtbl_foreach_cloref]

(* ****** ****** *)

%{$

// shortcuts? yes. worth it? probably.

// static inline
ats_ptr_type
hashtbl_ptr_make (ats_int_type sz) {
  ats_ptr_type p ;
  /* zeroing the allocated memory is mandatory! */
  p = ATS_CALLOC(sz, sizeof(chain0)) ;
  return p ;
} /* end of [hashtbl_ptr_make] */

// static inline
ats_void_type
hashtbl_ptr_free (ats_ptr_type p) { ATS_FREE(p) ; return ; }
/* end of [hashtbl_ptr_free] */

%}

(* ****** ****** *)

(* end of [hashtable.dats] *)
