(*
**
** Some utility functions for handling the syntax of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Guillaume Bruneri (guillaume.bruneri AT gmail DOT com)
**
** Time: Start Time, 2011
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload Lab = "ats_label.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

fun tostring_label (x: $Lab.label_t): string
overload tostring with tostring_label

(* ****** ****** *)

local

staload "ats_parser.sats"

in // in of [local]

fun parse_from_string_yyres
  (tok: yybeg, str: string): yyres
// end of [parse_from_string_yyres]

fun parse_from_string_i0de (inp: string): $Syn.i0de
fun parse_from_string_s0rtid (inp: string): $Syn.i0de
fun parse_from_string_si0de (inp: string): $Syn.i0de
fun parse_from_string_di0de (inp: string): $Syn.i0de
fun parse_from_string_s0exp (inp: string): $Syn.s0exp
fun parse_from_string_d0exp (inp: string): $Syn.d0exp
fun parse_from_string_d0ecseq_dyn (inp: string): $Syn.d0eclst

end // end of [local]

(* ****** ****** *)

(* end of [atsyndef_util.sats] *)
