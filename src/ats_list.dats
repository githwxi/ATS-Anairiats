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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
// Time: (month?) 2007

(* ****** ****** *)

extern fun fun_coerce_arg_v_vt_res
  {arg:viewt@ype} {v:view} {vt:viewtype} {f:eff} {res:viewt@ype}
  (f: arg -<f> res):<0> (!v | arg, !vt) -<f> res
  = "atspre_fun_coerce"

(* ****** ****** *)

staload "ats_list.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

implement
list_is_cons (xs) =
  case+ xs of list_cons _ => true | list_nil _ => false
// end of [list_is_cons]

(* ****** ****** *)

(*
** HX: tail-recursive implementation
*)
implement
list_append
  {a} (xs, ys) = let
  fun aux {n1,n2:nat} .<n1>. (
      xs: list (a, n1)
    , ys: list (a, n2)
    , res: &(List a)? >> list (a, n1+n2)
    ) :<> void = begin case+ xs of
    | x :: xs => let
        val () = (res := cons {a} {0} (x, ?)); val+ cons (_, !p) = res
      in
        aux (xs, ys, !p); fold@ res
      end // end of [::]
    | nil () => (res := ys) // end of [nil]
  end // end of [aux]
  var res: List a // uninitialized
in
  aux (xs, ys, res); res
end // end of [list_append]

(* ****** ****** *)

implement
list_extend (xs, x) = begin
  list_append (xs, list_cons (x, list_nil ()))
end // end of [list_extend]

(* ****** ****** *)

implement
list_foreach_main (pf | xs, f, env) = begin case+ xs of
  | cons (x, xs) => (f (pf | x, env); list_foreach_main (pf | xs, f, env))
  | nil () => ()
end // end of [list_foreach_main]

implement
list_foreach_fun (xs, f) = begin case+ xs of
  | cons (x, xs) => (f x; list_foreach_fun (xs, f)) | nil () => ()
end // end of [list_foreach_fun]

implement
list_foreach_cloptr (xs, f) = begin case+ xs of
  | cons (x, xs) => (f x; list_foreach_cloptr (xs, f)) | nil () => ()
end // end of [list_foreach_cloptr]

(* ****** ****** *)

implement
list_length {a} (xs) = let
  fun loop {i,j:nat} .<i>.
    (xs: list (a, i), j: int j):<> int (i+j) =
    case+ xs of  _ :: xs => loop (xs, succ j) | nil () => j
  // end of [loop]
in
  loop (xs, 0)
end // end of [list_length]

(* ****** ****** *)

(*
** HX: tail-recursive implementation
*)
implement
list_map_main
  {a,b} {v} {vt} {n} {f:eff} (pf | xs, f, env) = let
  fun aux {n:nat} .<n>. (
      pf: !v
    | xs: list (a, n)
    , f: (!v | a, !vt) -<f> b
    , res: &(List b)? >> list (b, n)
    , env: !vt
  ) :<f> void = begin case+ xs of
    | x :: xs => let
        val y = f (pf | x, env)
        val+ () = (res := cons {b} {0} (y, ?)); val+ cons (_, !p) = res
      in
        aux (pf | xs, f, !p, env); fold@ res
      end // end of [::]
    | nil () => (res := nil ()) // end of [nil]
  end // end of [aux]
  var res: List b // uninitialized
in
  aux (pf | xs, f, res, env); res
end // end of [list_map_main]

implement
list_map_fun {a,b} {n} {f:eff} (xs, f) = let
  val f = fun_coerce_arg_v_vt_res {a} {unit_v} {Ptr} {f} {b} (f)
  prval pf = unit_v ()
  var ptr0 = null
  val ans = list_map_main {a,b} {unit_v} {Ptr} (pf | xs, f, ptr0)
  prval unit_v () = pf
in
  ans
end // end of [list_map_fun]

implement
list_map_cloptr
  {a,b} {n} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> b
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> b = f (x)
  prval pf = unit_v ()
  val ans = list_map_main {a,b} {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ans
end // end of [list_map_cloptr]

(* ****** ****** *)

implement
list_revapp (xs, ys) = case+ xs of
  | x :: xs => list_revapp (xs, x :: ys) | nil () => ys
// end of [list_revapp]

implement list_reverse (xs) = list_revapp (xs, nil ())

implement
list_reverse_list_vt {a} {n} (xs) = let
  extern castfn __cast (xs: list (a, n)):<> list_vt (a, n)
in
  __cast (list_reverse (xs)) // HX-2010-10-31: cutting a corner!
end // end of [list_reverse_list_vt]

(* ****** ****** *)

implement
list_length_compare
  (xs1, xs2) = case+ xs1 of
  | _ :: xs1 => begin case+ xs2 of
    | _ :: xs2 => list_length_compare (xs1, xs2) | nil () => 1
    end // end of [::]
  | nil () => begin
      case+ xs2 of _ :: _ => ~1 | nil () => 0
    end // end of [nil]
// end of [list_length_compare]

(* ****** ****** *)

(*
** HX: tail-recursive implementation
*)
implement
list_vt_append {a} (xs0, ys0) = let
//
fun loop {n1,n2:nat} .<n1>.
  (xs0: &list_vt (a, n1) >> list_vt (a, n1+n2), ys0: list_vt (a, n2))
  :<> void = begin case+ xs0 of
  | list_vt_cons (_, !xs) => (loop (!xs, ys0); fold@ xs0)
  | list_vt_nil () => (xs0 := ys0)
end // end of [loop]
//
var xs0 = xs0
//
in
  loop (xs0, ys0); xs0
end // end of [list_vt_append]

(* ****** ****** *)

(*
** HX: tail-recursive implementation
*)
implement
list_vt_prefix {a} (xs, i) = let
//
fun loop {n,i:nat | i <= n} .<i>. (
    xs: &list_vt (a, n) >> list_vt (a, n-i)
  , i: int i
  , res: &(List_vt a)? >> list_vt (a, i)
  ) :<> void = begin
  if i > 0 then let
    val () = res := xs
    val+ list_vt_cons (_, !xs_nxt) = res; val () = xs := !xs_nxt
  in
    loop (xs, i-1, !xs_nxt); fold@ {a} (res)
  end else begin
    res := list_vt_nil {a} ()
  end
end // end of [loop]
//
var res: List_vt a // uninitialized
//
in
  loop (xs, i, res); res
end // end of [list_vt_prefix]

(* ****** ****** *)

implement
list_vt_revapp
  (xs, ys) = case+ xs of
  | ~list_vt_cons (x, xs) => list_vt_revapp (xs, list_vt_cons (x, ys))
  | ~list_vt_nil () => ys
// end of [list_vt_revapp]

implement
list_vt_reverse (xs) = list_vt_revapp (xs, list_vt_nil ())

(* ****** ****** *)

implement
list_vt_revapp_list
  (xs, ys) = case+ xs of
  | ~list_vt_cons (x, xs) => list_vt_revapp_list (xs, list_cons (x, ys))
  | ~list_vt_nil () => ys
// end of [list_vt_revapp_list]

implement
list_vt_reverse_list (xs) = list_vt_revapp_list (xs, list_nil ())

(* ****** ****** *)

(*
** HX: tail-recursive implementation
*)
implement{a}
list_vt_copy (xs) = let
  fun aux {n:nat} .<n>.
    (xs: !list_vt (a, n), res: &(List_vt a)? >> list_vt (a, n))
    :<> void = begin case+ xs of
    | list_vt_cons (x, !xs_nxt) => let
        val () = res := list_vt_cons {a} {0} (x, ?)
        val+ list_vt_cons (_, !res_nxt) = res
      in
        aux (!xs_nxt, !res_nxt); fold@ xs; fold@ res
      end // end of [list_vt_cons]
    | list_vt_nil () => begin
        res := list_vt_nil (); fold@ xs
      end // end of [list_vt_nil]
  end // end of [aux]
  var res: (List_vt a)? // uninitialized
in
  aux (xs, res); res
end // end of [list_vt_copy]

implement
list_vt_copy__boxed {a} (xs) = list_vt_copy<a> (xs)

(* ****** ****** *)

(* tail-recursive implementation *)
implement{a} list_vt_free (xs) = begin
  case+ xs of
  | ~list_vt_cons (_, xs) => list_vt_free xs
  | ~list_vt_nil () => ()
end // end of [list_vt_free]

implement
list_vt_free__boxed {a} (xs) = list_vt_free<a> (xs)

(* ****** ****** *)

implement{a}
list_vt_length (xs) = let
  fun aux {i,j:nat} .<i>.
    (xs: !list_vt (a, i), j: int j):<> int (i+j) =
    case+ xs of
    | list_vt_cons (_, !xs1) => begin
        let val n = aux (!xs1, j + 1) in fold@ xs; n end
      end
    | list_vt_nil () => (fold@ xs; j)
  // end of [aux]
in
  aux (xs, 0)
end // end of [list_vt_length]

implement
list_vt_length__boxed {a} (xs) = list_vt_length<a> (xs)

(* ****** ****** *)

implement
fprintlst {a} {m} (
  pf | out, xs, sep, fprint
) = let
  fun aux (
    out: &FILE m, xs: List a, i: int
  ) :<cloref1> void =
    case+ xs of
    | list_cons (x, xs) => let
        val () = if i > 0 then
          fprint1_string (pf | out, sep)
        // end of [val]
        val () = fprint (pf | out, x)
      in
         aux (out, xs, i+1)
      end // end of [list_cons]
    | list_nil () => () // end of [list_nil]
  // end of [aux]
in
  aux (out, xs, 0)
end // end of [fprintlst]

(* ****** ****** *)

(* end of [ats_list.dats] *)
