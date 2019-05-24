(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

#include "prelude/params.hats"

#if VERBOSE_PRELUDE #then

#print "Loading [basic_sta.sats] starts!\n"

#endif

(* ****** ****** *)

(* some integer constants *)

#define power_2_4 0x10
#define power_2_5 0x20
#define power_2_6 0x40
#define power_2_7 0x80
#define power_2_8 0x100
#define power_2_10 0x400
#define power_2_15 0x8000
#define power_2_16 0x10000
#define power_2_20 0x100000
#define power_2_31 0x80000000
#define power_2_32 0x100000000
#define power_2_63 0x8000000000000000
#define power_2_64 0x10000000000000000

(* ****** ****** *)

// some unindexed types

(* ****** ****** *)

abst@ype bool_t0ype = $extype "ats_bool_type"
abst@ype byte_t0ype = $extype "ats_byte_type" // sizeof (byte) = 1

(* ****** ****** *)

abst@ype char_t0ype = $extype "ats_char_type"
abst@ype schar_t0ype = $extype "ats_schar_type"
abst@ype uchar_t0ype = $extype "ats_uchar_type"

(* ****** ****** *)

abstype clo_t0ype // ats_clo_type

(* ****** ****** *)

abst@ype double_t0ype = $extype "ats_double_type"

(* ****** ****** *)

absviewtype exception_viewtype // boxed type

(* ****** ****** *)

abst@ype int_t0ype = $extype "ats_int_type"
abst@ype uint_t0ype = $extype "ats_uint_type"

abst@ype int_short_t0ype = $extype "ats_sint_type"
abst@ype uint_short_t0ype = $extype "ats_usint_type"

abst@ype int_short_short_t0ype = $extype "ats_sint_type"
abst@ype uint_short_short_t0ype = $extype "ats_ussint_type"

abst@ype int_long_t0ype = $extype "ats_lint_type"
abst@ype uint_long_t0ype = $extype "ats_ulint_type"

abst@ype int_long_long_t0ype = $extype "ats_llint_type"
abst@ype uint_long_long_t0ype = $extype "ats_ullint_type"

abst@ype intmax_t0ype = $extype "ats_intmax_type"
abst@ype uintmax_t0ype = $extype "ats_uintmax_type"

// integer types guaranteed to be of one word size
abstype intptr_type // ats_intptr_type
abstype uintptr_type // ats_uintptr_type

// integer types with fixed size
abst@ype int8_t0ype = $extype "ats_int8_type"
abst@ype uint8_t0ype = $extype "ats_uint8_type"

abst@ype int16_t0ype = $extype "ats_int16_type"
abst@ype uint16_t0ype = $extype "ats_uint16_type"

abst@ype int32_t0ype = $extype "ats_int32_type"
abst@ype uint32_t0ype = $extype "ats_uint32_type"

abst@ype int64_t0ype = $extype "ats_int64_type"
abst@ype uint64_t0ype = $extype "ats_uint64_type"

// integer types for sizes
abst@ype size_t0ype = $extype "ats_size_type"
abst@ype ssize_t0ype = $extype "ats_ssize_type"
abst@ype ptrdiff_t0ype = $extype "ats_ptrdiff_type"

(* ****** ****** *)

abstype ptr_type

(* ****** ****** *)

abstype string_type // boxed type

(* ****** ****** *)

abst@ype void_t0ype = $extype "ats_void_type" // sizeof (void) = 0

(* ****** ****** *)

// some built-in static constants for integer operations

sta neg_int_int : int -> int (* integer negation *)
stadef ~ = neg_int_int

sta add_int_int_int : (int, int) -> int (* addition *)
stadef + = add_int_int_int

sta sub_int_int_int: (int, int) -> int (* subtraction *)
stadef - = sub_int_int_int

sta nsub_int_int_int: (int, int) -> int (* subtraction on nats *)
stadef nsub = nsub_int_int_int

sta mul_int_int_int : (int, int) -> int (* multiplication *)
stadef * = mul_int_int_int

sta div_int_int_int : (int, int) -> int (* division *)
stadef / = div_int_int_int

sta mod_int_int_int : (int, int) -> int (* modulo operation *)
stadef mod = mod_int_int_int

sta abs_int_int : int -> int
stadef abs = abs_int_int

sta max_int_int_int : (int, int) -> int
stadef max = max_int_int_int

sta min_int_int_int : (int, int) -> int
stadef min = min_int_int_int

sta int_of_bool : bool -> int and bool_of_int : int -> bool
sta int_of_char : char -> int and char_of_int : int -> char

(* ****** ****** *)

// The built-in boolean constants

sta true_bool : bool and false_bool : bool
stadef true = true_bool and false = false_bool

// some built-in static constants for boolean operations

sta neg_bool_bool : bool -> bool (* boolean negation *)
stadef ~ = neg_bool_bool

sta mul_bool_bool_bool : (bool, bool) -> bool (* conjunction *)
stadef && = mul_bool_bool_bool

sta add_bool_bool_bool : (bool, bool) -> bool (* disjunction *)
stadef || = add_bool_bool_bool

sta gt_bool_bool_bool : (bool, bool) -> bool
stadef > = gt_bool_bool_bool

sta gte_bool_bool_bool : (bool, bool) -> bool
stadef >= = gte_bool_bool_bool

sta lt_bool_bool_bool : (bool, bool) -> bool
stadef < = lt_bool_bool_bool

sta lte_bool_bool_bool : (bool, bool) -> bool
stadef <= = lte_bool_bool_bool

sta eq_bool_bool_bool : (bool, bool) -> bool
stadef == = eq_bool_bool_bool

sta neq_bool_bool_bool : (bool, bool) -> bool
stadef <> = neq_bool_bool_bool

(* ****** ****** *)

// some built-in static constants for char comparisons

sta sub_char_char_int : (char, char) -> int
stadef - = sub_char_char_int

sta gt_char_char_bool : (char, char) -> bool
stadef > = gt_char_char_bool

sta gte_char_char_bool : (char, char) -> bool
stadef >= = gte_char_char_bool

sta lt_char_char_bool : (char, char) -> bool
stadef < = lt_char_char_bool

sta lte_char_char_bool : (char, char) -> bool
stadef <= = lte_char_char_bool

sta eq_char_char_bool : (char, char) -> bool
stadef == = eq_char_char_bool

sta neq_char_char_bool : (char, char) -> bool
stadef <> = neq_char_char_bool

(* ****** ****** *)

// some built-in static constants for integer comparisons

sta gt_int_int_bool : (int, int) -> bool
stadef > = gt_int_int_bool

sta gte_int_int_bool : (int, int) -> bool
stadef >= = gte_int_int_bool

sta lt_int_int_bool : (int, int) -> bool
stadef < = lt_int_int_bool

sta lte_int_int_bool : (int, int) -> bool
stadef <= = lte_int_int_bool

sta eq_int_int_bool : (int, int) -> bool
stadef == = eq_int_int_bool

sta neq_int_int_bool : (int, int) -> bool
stadef <> = neq_int_int_bool

// some built-in static constants for pointer arithmetic

sta null_addr : addr
stadef null = null_addr

sta add_addr_int_addr : (addr, int) -> addr
stadef + = add_addr_int_addr

sta sub_addr_int_addr : (addr, int) -> addr
stadef - = sub_addr_int_addr

sta sub_addr_addr_int : (addr, addr) -> int
stadef - = sub_addr_addr_int

sta gt_addr_addr_bool : (addr, addr) -> bool
stadef > = gt_addr_addr_bool

sta gte_addr_addr_bool : (addr, addr) -> bool
stadef >= = gte_addr_addr_bool

sta lt_addr_addr_bool : (addr, addr) -> bool
stadef < = lt_addr_addr_bool

sta lte_addr_addr_bool : (addr, addr) -> bool
stadef <= = lte_addr_addr_bool

sta eq_addr_addr_bool : (addr, addr) -> bool
stadef == = eq_addr_addr_bool

sta neq_addr_addr_bool : (addr, addr) -> bool
stadef <> = neq_addr_addr_bool

(*

// some built-in static constants for rationals
// not yet supported and may never be supported

sta ~ : rat -> rat (* rational negation *)
sta + : (rat, rat) -> rat (* addition *)
and - : (rat, rat) -> rat (* subtraction *)
and * : (rat, rat) -> rat (* multiplication *)
and / : (rat, int) -> rat (* division *)
and / : (rat, rat) -> rat (* division *)

sta > : (rat, rat) -> bool
sta > : (rat, int) -> bool
and >= : (rat, rat) -> bool
and < : (rat, rat) -> bool
and <= : (rat, rat) -> bool
and <> : (rat, rat) -> bool
and == : (rat, rat) -> bool

*)

(* ****** ****** *)

// an empty viewtype
viewtypedef none_viewt0ype = [a:viewt@ype | false] a

(* ****** ****** *)

// an empty viewtype
viewtypedef bottom_viewt0ype_uni = {a:viewt@ype} a
viewtypedef bottom_viewt0ype_exi = [a:viewt@ype | false] a

// some built-in type/viewtype/prop/view constructors

absview at_viewt0ype_addr_view (viewt@ype+, addr)
stadef @ = at_viewt0ype_addr_view

(* ****** ****** *)

abstype ref_viewt0ype_type (viewt@ype) // boxed type
stadef ref = ref_viewt0ype_type

abstype refconst_t0ype_type (t@ype) // boxed type
stadef refconst = refconst_t0ype_type

(* ****** ****** *)

// for taking out a component in a record
abst@ype without_viewt0ype_t0ype (viewt@ype)
stadef without = without_viewt0ype_t0ype

// sta vbox_view_prop : view -> prop
absprop vbox_view_prop (view)
stadef vbox = vbox_view_prop

(* ****** ****** *)

abst@ype value_t0ype_int_t0ype (a:t@ype+, i:int) =
  union (i) { value= a }
stadef value = value_t0ype_int_t0ype
typedef Value (a:t@ype) =
  [i:int | 0 <= i; i <= 1] value (a, i)

absviewt@ype
value_viewt0ype_int_viewt0ype (a:viewt@ype+, i:int) =
  union (i) { value= a }
stadef value_vt = value_viewt0ype_int_viewt0ype
viewtypedef Value_t (a:viewt@ype) =
  [i:int | 0 <= i; i <= 1] value_vt (a, i)

(* ****** ****** *)

(*

// not yet supported and may never be supported

datasort stamp = (* abstract *)

// sta vfrac : (stamp, view, rat) -> view
absview vfrac (stamp, view, rat)

// sta vtfrac : (stamp, viewtype, rat) -> viewtype
absviewtype vtfrac (stamp, viewtype, rat)

*)

(* ****** ****** *)

// build-in dependent type constructors

abstype
array0_viewt0ype_type (elt:viewt@ype)

abstype
array_viewt0ype_int_type (elt:viewt@ype, sz:int)

abstype
matrix0_viewt0ype_type (elt:viewt@ype)

abstype
matrix_viewt0ype_int_int_type (elt:viewt@ype, nrow:int, ncol:int)

(* ****** ****** *)

abst@ype bool_bool_t0ype (bool) = $extype "ats_bool_type"

abst@ype char_char_t0ype (char) = $extype "ats_char_type"

abst@ype int_int_t0ype (int) = $extype "ats_int_type"
abst@ype uint_int_t0ype (int) = $extype "ats_uint_type"

abst@ype lint_int_t0ype (int) = int_long_t0ype
abst@ype ulint_int_t0ype (int) = uint_long_t0ype

abst@ype llint_int_t0ype (int) = int_long_long_t0ype
abst@ype ullint_int_t0ype (int) = uint_long_long_t0ype

abst@ype size_int_t0ype (i:int) = $extype "ats_size_type"
abst@ype ssize_int_t0ype (i:int) = $extype "ats_ssize_type"

abst@ype ptrdiff_int_t0ype (i:int) = $extype "ats_ptrdiff_type"

(* ****** ****** *)

abstype ptr_addr_type (addr)

(* ****** ****** *)

abstype string_int_type (int)
abstype stropt_int_type (int)
abst@ype strbuf_int_int_t0ype (max: int, len: int) (* variable size *)
absviewtype strptr_addr_viewtype (addr) // for linear strings

(* ****** ****** *)

// The following definitions are needed in the ATS constraint solver

// absolute value function relation

stadef abs_int_int_bool (x: int, v: int): bool =
  (x >= 0 && x == v) || (x <= 0 && ~x == v)

stadef abs_r = abs_int_int_bool

//

stadef btw_int_int_int_bool (x: int, y: int, z:int): bool =
  (x <= y && y < z)

// subtraction relation on natural numbers

stadef nsub_int_int_int_bool (x: int, y: int, v: int): bool =
  (x >= y && v == x - y) || (x <= y && v == 0)

stadef nsub_r = nsub_int_int_int_bool

// maximum function relation

stadef max_int_int_int_bool (x: int, y: int, v: int): bool =
  (x >= y && x == v) || (x <= y && y == v)

stadef max_r = max_int_int_int_bool

// minimum function relation

stadef min_int_int_int_bool (x: int, y: int, v: int): bool =
  (x >= y && y == v) || (x <= y && x == v)

stadef min_r = min_int_int_int_bool

// sign function relation

stadef sgn_int_int_bool (x: int, v: int): bool =
  (x > 0 && v == 1) || (x == 0 && v == 0) || (x < 0 && v == ~1)

stadef sgn_r = sgn_int_int_bool

// division relation

stadef ndiv_int_int_int_bool (x: int, y:int, q: int): bool =
  (q * y <= x && x < q * y + y)

stadef ndiv_r = ndiv_int_int_int_bool

stadef div_int_int_int_bool (x: int, y: int, q: int) =
  (x >= 0 && y > 0 && ndiv_int_int_int_bool (x, y, q)) ||
  (x >= 0 && y < 0 && ndiv_int_int_int_bool (x, ~y, q)) ||
  (x <= 0 && y > 0 && ndiv_int_int_int_bool (~x, y, q)) ||
  (x <= 0 && y < 0 && ndiv_int_int_int_bool (~x, ~y, q))

stadef div_r = div_int_int_int_bool

(* ****** ****** *)

sta sizeof_viewt0ype_int : viewt@ype -> int
stadef sizeof = sizeof_viewt0ype_int

stadef sizeof_viewt0ype_int_bool (a:int, n:int) = n >= 0
stadef sizeof_r = sizeof_viewt0ype_int_bool

(* ****** ****** *)

// introduce some short names

stadef array0 = array0_viewt0ype_type // with dynamic size
stadef array = array_viewt0ype_int_type // without dynamic size
stadef matrix0 = matrix0_viewt0ype_type // with dynamic size
stadef matrix = matrix_viewt0ype_int_int_type // without dynamic size

(* this order is significant! *)
stadef bool = bool_bool_t0ype
stadef bool = bool_t0ype

stadef byte = byte_t0ype

(* ****** ****** *)

(* this order is significant! *)
stadef char = char_char_t0ype
stadef char = char_t0ype

stadef schar = schar_t0ype
stadef uchar = uchar_t0ype

(* ****** ****** *)

stadef double = double_t0ype

stadef exn = exception_viewtype

(* ****** ****** *)

(* this order is significant! *)
stadef int = int_int_t0ype
stadef int = int_t0ype

(* this order is significant! *)
stadef uint = uint_int_t0ype
stadef uint = uint_t0ype

(* this order is significant! *)
stadef size_t = size_int_t0ype
stadef size_t = size_t0ype

stadef ssize_t = ssize_int_t0ype
stadef ssize_t = ssize_t0ype

stadef ptrdiff_t = ptrdiff_int_t0ype
stadef ptrdiff_t = ptrdiff_t0ype

(* ****** ****** *)

stadef ptr = ptr_addr_type
stadef ptr = ptr_type

(* ****** ****** *)

stadef strbuf = strbuf_int_int_t0ype
stadef strbuf (bsz:int) = [len:int] strbuf (bsz, len)

stadef string = string_int_type
stadef string = string_type
stadef stropt = stropt_int_type
stadef strptr = strptr_addr_viewtype // for linear strings
stadef strptr0 = [l:addr] strptr (l)
stadef strptr1 = [l:addr | l > null] strptr (l)

(* ****** ****** *)

stadef void = void_t0ype

(* ****** ****** *)

datatype unit = unit

typedef Bool = [b:bool] bool b
typedef Char = [c:char] char c

typedef Int = [i:int] int i
typedef intLt (n:int) = [i:int | i < n] int i
typedef intLte (n:int) = [i:int | i <= n] int i
typedef intGt (n:int) = [i:int | i > n] int i
typedef intGte (n:int) = [i:int | i >= n] int i
typedef intBtw (lb:int, ub:int) = [i: int | lb <= i; i < ub] int i

typedef Nat = [n:int | n >= 0] int n
typedef natLt (n:int) = [i:int | 0 <=i; i < n] int i
typedef natLte (n:int) = [i:int | 0<= i; i <= n] int i

typedef Pos = intGt 0
typedef Neg = intLt 0

typedef Ptr = [l:addr] ptr l
typedef Ptr1 = [l:addr | l > null] ptr l

typedef Sgn = [i:int | ~1 <= i; i <= 1] int i

typedef String = [n:int | n >= 0] string n
typedef Stropt = [n:int] stropt n

typedef uInt = [n:int | n >=0] uint n

typedef sizeof_t (a:viewt@ype) =
  size_int_t0ype (sizeof_viewt0ype_int a)

typedef sizeLt (n: int) = [i:int | 0 <= i; i < n] size_t (i)
typedef sizeLte (n: int) = [i:int | 0 <= i; i <= n] size_t (i)
typedef ssizeBtw (lb:int, ub:int) = [i: int | lb <= i; i < ub] ssize_t i

(* ****** ****** *)

// for memory deallocation (with/without GC)

absview free_gc_addr_view (l:addr)
absview free_ngc_addr_view (l:addr)

stadef free_gc_v = free_gc_addr_view
stadef free_ngc_v = free_ngc_addr_view

//

absview free_gc_viewt0ype_addr_view (a:viewt@ype+, l:addr)
absview free_ngc_viewt0ype_addr_view (a:viewt@ype+, l:addr)

stadef free_gc_v = free_gc_viewt0ype_addr_view
stadef free_ngc_v = free_ngc_viewt0ype_addr_view

//

absview free_gc_viewt0ype_addr_int_view (a:viewt@ype+, n:int, l:addr)
absview free_ngc_viewt0ype_addr_int_view (a:viewt@ype+, n:int, l: addr)

stadef free_gc_v = free_gc_viewt0ype_addr_int_view
stadef free_ngc_v = free_ngc_viewt0ype_addr_int_view

//

absview
freebyte_gc_int_addr_view (n:int, l:addr)
stadef freebyte_gc_v = freebyte_gc_int_addr_view
absview
freebyte_ngc_int_addr_view (n:int, l:addr)
stadef freebyte_ngc_v = freebyte_ngc_int_addr_view

(* ****** ****** *)
//
// values of viewtype [junkptr] need to be freed by calling [free];
// note that the viewtype [junkptr] may be just defined as follows:
// [a:viewt@ype; l:addr] (free_gc_v (a, l), a? @ l | ptr l)
//
absviewtype junkptr_viewtype
stadef junkptr = junkptr_viewtype

(* ****** ****** *)
//
// This definition should not be changed!
//
viewtypedef
arrayptrsize_viewt0ype_int_viewt0ype (a: viewt@ype, n:int) =
  [l:addr | l <> null] (free_gc_v (a?, n, l), @[a][n] @ l | ptr l, int n)

stadef arrpsz = arrayptrsize_viewt0ype_int_viewt0ype

(* ****** ****** *)

// closure, closure pointer and closure reference
absviewt@ype clo_viewt0ype_viewt0ype (viewt@ype+ (*fun*))
stadef clo = clo_viewt0ype_viewt0ype

absviewtype cloptr_viewt0ype_viewtype (viewt@ype+ (*fun*))
stadef cloptr = cloptr_viewt0ype_viewtype

abstype cloref_t0ype_type (t@ype)
stadef cloref = cloref_t0ype_type

(* ****** ****** *)

// for print-format strings
abstype printf_c_types_type (types) // boxed type
stadef printf_c = printf_c_types_type

(* ****** ****** *)

datasort file_mode =
  | file_mode_r (* read *)
  | file_mode_w (* write *)
  | file_mode_rw (* read and write *)

stadef r = file_mode_r ()
stadef w = file_mode_w ()
stadef rw = file_mode_rw ()

// [ats_FILE_viewtype] is defined in [libc/CATS/stdio.cats]
absviewt@ype
FILE_viewt0ype (file_mode) = $extype "ats_FILE_viewtype"
stadef FILE = FILE_viewt0ype

// [FILEref_type] is [ref (FILE m)] for some [m]
abstype FILEref_type; stadef FILEref = FILEref_type

(* ****** ****** *)

// some common datatypes

dataviewtype
box_viewt0ype_viewtype (a:viewt@ype+) = box (a) of a

stadef box = box_viewt0ype_viewtype

// [list_t0ype_int_type] is covariant
datatype // t@ype+: covariant
list_t0ype_int_type (a:t@ype+, int) =
  | {n:int | n >= 0}
      list_cons (a, n+1) of (a, list_t0ype_int_type (a, n))
  | list_nil (a, 0)

stadef list = list_t0ype_int_type
typedef List (a:t@ype) = [n:int | n >= 0] list (a, n)

// [option_t0ype_bool_type] is covariant
datatype  // t@ype+: covariant
option_t0ype_bool_type (a:t@ype+, bool) =
  | None (a, false) | Some (a, true) of a

stadef option = option_t0ype_bool_type
typedef Option (a:t@ype) = [b:bool] option (a, b)

(* ****** ****** *)

// some common dataviewtypes

// [list_viewt0ype_int_viewtype] is covariant
dataviewtype // viewt@ype+: covariant
list_viewt0ype_int_viewtype (a:viewt@ype+, int) =
  | {n:int | n >= 0}
      list_vt_cons (a, n+1) of (a, list_viewt0ype_int_viewtype (a, n))
  | list_vt_nil (a, 0)

stadef list_vt = list_viewt0ype_int_viewtype
viewtypedef List_vt (a:viewt@ype) = [n:int | n >= 0] list_vt (a, n)

// [option_viewt0ype_bool_viewtype] is covariant
dataviewtype option_viewt0ype_bool_viewtype (a:viewt@ype+, bool) =
  | None_vt (a, false) | Some_vt (a, true) of a

stadef option_vt = option_viewt0ype_bool_viewtype
viewtypedef Option_vt (a:viewt@ype) = [b:bool] option_vt (a, b)

(* ****** ****** *)

// some useful props and views

dataview option_view_int_view (a:view+, bool) =
  | None_v (a, false) | Some_v (a, true) of a

stadef option_v = option_view_int_view

//

dataprop unit_p = unit_p
dataview unit_v = unit_v

//

// subview relation that only allows *reading*
absprop vsubr_p (v1:view+, v2: view-) // v2 -<prf> [v:iew] @(v1, v)
stadef <= (v1:view, v2:view) = vsubr_p (v1, v2)

// subview relation that allows *reading* and *writing*
absprop vsubw_p (v1:view, v2: view) // v2 -<prf> @(v1, v1 -<lin,prf> v2)

(* ****** ****** *)

absviewt@ype crypt_viewt0ype_viewt0ype (a:viewt@ype) = a
stadef crypt = crypt_viewt0ype_viewt0ype

(* ****** ****** *)

// [lazy T] : supspended computation with a value of type T
abstype lazy_t0ype_type (t@ype+) // boxed type
stadef lazy = lazy_t0ype_type

// [lazy_vt VT] : supspended computation with a linear value of viewtype VT
absviewtype lazy_viewt0ype_viewtype (viewt@ype+) // boxed linear type
stadef lazy_vt = lazy_viewt0ype_viewtype

(* ****** ****** *)

// lazy streams
datatype stream_con (a:t@ype+) =
  | stream_nil (a) | stream_cons (a) of (a, stream a)

where stream (a:t@ype) = lazy (stream_con a)

// lazy linear streams
dataviewtype stream_vt_con (a:viewt@ype+) =
  | stream_vt_nil (a) | stream_vt_cons (a) of (a, stream_vt a)

where stream_vt (a:viewt@ype) = lazy_vt (stream_vt_con a)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [basic_sta.sats] finishes!\n"

#endif

(* end of [basics_sta.sats] *)
