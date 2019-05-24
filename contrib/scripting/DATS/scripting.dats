(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
*)

(* ****** ****** *)

(*
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2011
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time
#define ATS_DYNLOADFLAG 1 // for dynloading at run-time

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"
staload _(*anon*) = "libats/DATS/linqueue_lst.dats"

(* ****** ****** *)
//
staload UN = "prelude/SATS/unsafe.sats"
//
staload FCNTL = "libc/SATS/fcntl.sats"
staload STDIO = "libc/SATS/stdio.sats"
//
(* ****** ****** *)

staload RE = "libats/SATS/regexp.sats"
staload HASH = "libats/SATS/hashtable_chain.sats"

(* ****** ****** *)

staload "contrib/scripting/SATS/scripting.sats"

(* ****** ****** *)

#define i2sz size1_of_int1

(* ****** ****** *)

implement strptrlst_free (xs) =
  case+ xs of
  | ~list_vt_cons (x, xs) => let
      val () = strptr_free (x) in strptrlst_free (xs)
    end // end of [list_vt_cons]
  | ~list_vt_nil () => ()
// end of [strptrlst_free]

(* ****** ****** *)

implement
strptr_make_segment (str, i, j) =
  if i >= 0 then
    strptr_of_strbuf (string_make_substring (str, (i2sz)i, i2sz(j-i)))
  else strptr_null () // end of [if]
// end of [strptr_make_segment]

(* ****** ****** *)

implement
fprint_segment (out, str, i, j) = let
//
extern fun stradd
  (str: string, i: int): string = "atspre_padd_int"
extern fun fwrite
  (str: string, n: size_t, out: FILEref): void = "atslib_fwrite_byte_exn"
//
in
  fwrite (stradd (str, i), i2sz (j-i), out)
end // end of [fprint_segment]

(* ****** ****** *)

implement
string_split_string_list
  (str, pat) = let
  val re = $RE.regexp_compile (pat)
  val p_re = $RE.ptr_of_REGEXPptr (re)
in
  if p_re > null then let
    val res = $RE.regexp_split_string_list (re, str)
    val () = $RE.regexp_free (re)
  in
    res
  end else let
    val _ptr = $RE.regexp_free_null (re)
(*
    val pat = $UN.castvwtp1 {string} (pat)
    val () = prerrf (
      "exit(ATS): [pcre_comiple] failed: pattern = %s\n", @(pat)
    ) // end of [val]
*)
  in
    list_vt_nil () // HX: indication of error
  end (* end of [if] *)
end // end of [string_split_string_list]

(* ****** ****** *)

(*
fun string_replace_substring
  {n:nat} {i,ln:nat | i + ln <= n} {k:nat} (
  src: string n, n: int n, i: int i, ln: int ln
, sub: string k, k: int k
) : strptr1 = "atsctrb_string_replace_substring"
*)

%{
ats_ptr_type
atsctrb_string_replace_substring (
  ats_ptr_type src
, ats_int_type n
, ats_int_type i
, ats_int_type ln
, ats_ptr_type sub
, ats_int_type k
) {
  ats_ptr_type dst ;
//
  dst = ATS_MALLOC (n - ln + k + 1) ;
//
  memcpy (dst, src, i) ;
  memcpy (dst+i, sub, k) ;
  strcpy (dst+(i+k), src+(i+ln)) ;
//
  return dst ;
} // end of [atsctrb_string_replace_substring]
%} // end of [%{]

(* ****** ****** *)

local
//
val hash = lam (x: string) =<cloref> string_hash_33 (x)
val eqfn = lam (x1: string, x2: string) =<cloref> (x1 = x2)
//
in // in of [local]

implement
strhashmap_make {itm} () = let
  val tbl = $HASH.hashtbl_make {string,itm} (hash, eqfn)
  extern castfn __cast {l:addr} // the view is given to GC
    (x: $HASH.HASHTBLptr (string, itm, l)): STRHASHMAPref (itm)
  // end of [extern]
in
  __cast (tbl)
end // end of [strhashmap]

implement{itm}
strhashmap_search (tbl, k) = let
  var res: itm?
  viewtypedef ptbl = $HASH.HASHTBLptr1 (string, itm)
  val (fpf_ptbl | ptbl) = __cast (tbl) where {
    extern castfn __cast (tbl: STRHASHMAPref itm):<> (ptbl -<lin,prf> void | ptbl)
  } // end of [val]
  val ans = $HASH.hashtbl_search (ptbl, k, res)
  prval () = fpf_ptbl (ptbl)
in
  if ans then let
    prval () = opt_unsome {itm} (res) in Some_vt (res)
  end else let
    prval () = opt_unnone {itm} (res) in None_vt ()
  end (* end of [if] *)
end // end of [strhashmap_search]

implement{itm}
strhashmap_insert (tbl, k, i) = let
  viewtypedef ptbl = $HASH.HASHTBLptr1 (string, itm)
  val (fpf_ptbl | ptbl) = __cast (tbl) where {
    extern castfn __cast (tbl: STRHASHMAPref itm):<> (ptbl -<lin,prf> void | ptbl)
  } // end of [val]
  val () = $HASH.hashtbl_insert (ptbl, k, i)
  prval () = fpf_ptbl (ptbl)
in
  // nothing
end // end of [strhashmap_insert]

implement{itm}
strhashmap_remove (tbl, k0) = let
  var res: itm?
  viewtypedef ptbl = $HASH.HASHTBLptr1 (string, itm)
  val (fpf_ptbl | ptbl) = __cast (tbl) where {
    extern castfn __cast (tbl: STRHASHMAPref itm):<> (ptbl -<lin,prf> void | ptbl)
  } // end of [val]
  val ans = $HASH.hashtbl_remove (ptbl, k0, res)
  prval () = fpf_ptbl (ptbl)
in
  if ans then let
    prval () = opt_unsome {itm} (res) in Some_vt (res)
  end else let
    prval () = opt_unnone {itm} (res) in None_vt ()
  end (* end of [if] *)
end // end of [strhashmap_remove]

end // end of [local]

(* ****** ****** *)

local

staload Q = "libats/SATS/linqueue_lst.sats"

in // in of [local]

implement{itm}
strhashmap_foreach_vclo
  {v} (pf | tbl, f) = () where {
  viewtypedef ptbl = $HASH.HASHTBLptr1 (string, itm)
  val (fpf_ptbl | ptbl) = __cast (tbl) where {
    extern castfn __cast (tbl: STRHASHMAPref itm):<> (ptbl -<lin,prf> void | ptbl)
  } // end of [val]
  val () = $HASH.hashtbl_foreach_vclo<string,itm> {v} (pf | ptbl, f)
  prval () = fpf_ptbl (ptbl)
} // end of [strhashmap_foreach_vclo]

implement{itm}
strhashmap_listize (tbl) = let
//
  typedef T = (string, itm)
  var q: $Q.QUEUE1 (T)
  val () = $Q.queue_initialize {T} (q)
  viewdef V = $Q.QUEUE1 (T) @ q
  var !p_clo = @lam (pf: !V | k: string, i: &itm): void =<clo> $Q.queue_insert (q, (k, i))
//
  val () = strhashmap_foreach_vclo {V} (view@ q | tbl, !p_clo)
//
in
  $Q.queue_uninitialize (q)
end // end of [strhashmap_listize]

end // end of [local]

(* ****** ****** *)

local

staload Q = "libats/SATS/linqueue_lst.sats"

in // in of [local]

implement
fstringize (fil) = let
  viewtypedef VT (n:int) = $Q.QUEUE (char, n)
  fun loop {n:nat} (
    fil: FILEref, q: &VT (n) >> VT (n), n: int n
  ) : #[n:nat] int n = let
    val i = $STDIO.fgetc0_err (fil)
  in
    if i >= 0 then let
      val () = $Q.queue_insert (q, (char_of_int)i)
    in
      loop (fil, q, n+1)
    end else n
  end // end of [loop]
  var q: VT (0)
  val () = $Q.queue_initialize {char} (q)
  val n = loop (fil, q, 0)
  val cs = $Q.queue_uninitialize (q)
  val res = string_make_list_int ($UN.castvwtp1(cs), n)
  val () = list_vt_free (cs)
in
  strptr_of_strbuf (res)
end // end of [fstringize]

end // end of [local]

(* ****** ****** *)

implement
fsubst_pat_string
  (inp, out, pat, sub) = let
  val str0 = fstringize (inp)
in
//
if strptr_isnot_null (str0) then let
//
  val strlst =
    string_split_string_list ($UN.castvwtp1(str0), pat)
   // end of [val]
  val () = strptr_free (str0)
  fun loop (
    out: FILEref, sub: string, i: int, res: List_vt (strptr1)
  ) : void = let
    // nothing
  in
    case+ res of
    | ~list_vt_cons (fst, res) => let
        val () = if i > 0 then fprint_string (out, sub)
        val () = fprint_strptr (out, fst); val () = strptr_free (fst)
      in
        loop (out, sub, i+1, res)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  end // end of [loop]
  val () = loop (out, sub, 0, strlst)
in
  0 (*succ*)
end else let
  val () = strptr_free (str0)
in
  1 (*fail*)
end // end of [if]
//
end // end of [fsubst_pat_string]

(* ****** ****** *)

(* end of [scripting.dats] *)
