(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May 2008

(* ****** ****** *)

staload "ats_charlst.sats"

(* ****** ****** *)

implement
charlst_free (cs) = begin case+ cs of
  | ~CHARLSTcons (c, cs) => charlst_free cs | ~CHARLSTnil () => ()
end // end of [charlst_free]

(* ****** ****** *)

implement
charlst_length (cs) = aux (cs, 0) where {
  fun aux {i,j:nat}
    (cs: !charlst_vt i, j: int j)
    : int (i+j) = begin case+ cs of
    | CHARLSTcons (_, !cs1) => begin
        let val n = aux (!cs1, j+1) in fold@ (cs); n end
      end // end of [CHARLSTcons]
    | CHARLSTnil () => (fold@ (cs); j)
  end // end of [aux]
} // end of [charlst_length]

(* ****** ****** *)

implement
charlst_add_string {m,n}
  (cs, str) = loop (str, 0, cs) where {
  fun loop {m,i:nat | i <= n} .<n-i>.
    (str: string n, i: size_t i, cs: charlst_vt m)
    : charlst_vt (m+n-i) =
    if string_isnot_atend (str, i) then
      loop (str, i+1, CHARLSTcons (str[i], cs))
    else cs
  // end of [loop]
} // end of [charlst_add_string]

(* ****** ****** *)

implement
string_make_charlst_rev (cs) = begin
  string_make_charlst_rev_int (cs, charlst_length cs)
end // end of [string_make_charlst_rev]

(* ****** ****** *)

extern
fun charlst_is_nil {n:nat}
  (cs: !charlst_vt n): bool (n == 0) = "atsopt_charlst_is_nil"
// end of [fun charlst_is_nil]

implement
charlst_is_nil (cs) = case+ cs of
  | CHARLSTcons _ => (fold@ cs; false) | CHARLSTnil _ => (fold@ cs; true)
// end of [charlst_is_nil]

(* ****** ****** *)

extern
fun charlst_uncons {n:pos}
  (cs: &charlst_vt n >> charlst_vt (n-1)): char = "atsopt_charlst_uncons"
// end of [fun charlst_uncons]

implement
charlst_uncons (cs) =
  let val+ ~CHARLSTcons (c, cs_r) = cs in cs := cs_r; c end
// end of [charlst_uncons]

(* ****** ****** *)

%{^

ATSextfun()
ats_bool_type atsopt_charlst_is_nil (ats_ref_type) ;
ATSextfun()
ats_char_type atsopt_charlst_uncons (ats_ref_type) ;

ats_ptr_type
string_make_charlst_rev_int (
  ats_ptr_type cs, ats_int_type n
) {
  char *s;
  s = ATS_MALLOC (n+1) ; s += n ; *s = '\000' ;
  while (!atsopt_charlst_is_nil(cs)) { *--s = atsopt_charlst_uncons(&cs) ; }
  return s ;
} // end of [string_make_charlst_rev_int]

%} // end of [%{^]

(* ****** ****** *)

(* end of [ats_charlst.dats] *)
