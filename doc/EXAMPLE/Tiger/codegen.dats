(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

#if MARCH == "SPIM" #then
#print "MARCH == SPIM\n"
#include "codegen_spim.dats"
#endif

(* ****** ****** *)

#if MARCH == "x86_32" #then
#print "MARCH == x86_32\n"
#include "codegen_x86_32.dats"
#endif

(* ****** ****** *)

fun instrlst_add_stmlst
  (frm: frame, res: &instrlst_vt, stms: stmlst): void =
  case+ stms of
  | list_cons (stm, stms) => let
      val () = instrlst_add_stm (frm, res, stm) in
      instrlst_add_stmlst (frm, res, stms)
    end // end of [list_cons]
  | list_nil () => ()
// end of [instrlst_add_stmlst]

(* ****** ****** *)

implement
codegen_stm (frm, stm) = let
  var res: instrlst_vt = list_vt_nil ()
  val () = instrlst_add_stm (frm, res, stm)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen]

implement
codegen_stmlst (frm, stms) = let
  var res: instrlst_vt = list_vt_nil ()
  val () = instrlst_add_stmlst (frm, res, stms)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen_stmlst]

(* ****** ****** *)

implement
codegen_proc (frm, stms) = let
  var res: instrlst_vt = list_vt_nil ()
  val () = $F.procEntryExit1_entr (frm, res)
  val () = instrlst_add_stmlst (frm, res, stms)
  val () = $F.procEntryExit1_exit (frm, res)
  val () = $F.procEntryExit2 (frm, res)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)
in
  res
end // end of [codegen_proc]

(* ****** ****** *)

(* end of [codegen.dats] *)
