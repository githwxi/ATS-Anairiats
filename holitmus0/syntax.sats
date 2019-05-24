(*
**
** HOLITMUS: a proof checker for higher-order logic
**
** Originally implemented in OCaml
**    by Chad Brown (cebrown AT mathgate DOT info)
** Time: March/September, 2008
**
** Translated to ATS
**    by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

datatype stp =
  | STPbas of string
  | STPprp of ()
  | STParr of (stp, stp)

fun fprint_stp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, stp: stp): void

fun print_stp (x: stp): void
fun prerr_stp (x: stp): void

(* ****** ****** *)

datatype trm (int) =
  | {n:nat} TRMnam (n) of string
  | {n,i:nat | i < n} TRMdbi (n) of int i
  | {n:pos} TRMlam (n-1) of (stp, trm n)
  | {n:nat} TRMapp (n) of (trm n, trm n)
  | {n:pos} TRMall (n-1) of (stp, trm n)
  | {n:nat} TRMimp (n) of (trm n, trm n)
  | {n:nat} TRMany (n) of stp

typedef trm = [n:nat] trm n

fun fprint_trm {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, trm: trm): void

fun print_trm (x: trm): void
fun prerr_trm (x: trm): void

(* ****** ****** *)

datatype pftrm (int) =
  | {n:nat} PFTRMcon (n) of string
  | {n,i:nat | i < n} PFTRMdbi (n) of int i
  | {n:pos} PFTRMtlam (n-1) of (stp, pftrm n)
  | {n:pos} PFTRMplam (n-1) of (trm n, pftrm n)
  | {n:nat} PFTRMtapp (n) of (pftrm n, trm n)
  | {n:nat} PFTRMpapp (n) of (pftrm n, pftrm n)
  | {n:nat} PFTRMxi (n) of pftrm n

typedef pftrm = [n:nat] pftrm n

fun fprint_pftrm {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, pftrm: pftrm): void

fun print_pftrm (x: pftrm): void
fun prerr_pftrm (x: pftrm): void

(* ****** ****** *)

fun prop_false {n:nat} (): trm n and prop_true {n:nat} (): trm n

fun eq_stp_stp (_: stp, _: stp): bool
overload = with eq_stp_stp

fun eq_trm_trm {n:nat} (_: trm n, _: trm n): bool
overload = with eq_trm_trm

(* ****** ****** *)

(* end of [syntax.sats] *)
