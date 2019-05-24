(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software, Inc.
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
//
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: August, 2011
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "atsdoc_translate.sats"

(* ****** ****** *)
//
dynload "atsdoc_translate.dats"
dynload "atsdoc_translate_error.dats"
dynload "atsdoc_translate_item.dats"
//
(* ****** ****** *)
//
dynload "libatsdoc/dynloadall.dats" // HX: for libatsdoc.o
//
(* ****** ****** *)

datatype comarg = COMARGkey of (int, string)
vtypedef comarglst_vt (n: int) = list_vt (comarg, n)

(* ****** ****** *)

extern
fun comarg_parse (s: string):<> comarg
extern
fun comarglst_parse {n:nat}
  (argc: int n, argv: &(@[string][n])):<> list_vt (comarg, n)
// end of [comarglst_parse]

(* ****** ****** *)

implement
comarg_parse (s) = let
  fun loop {n,i:nat | i <= n} .<n-i>.
    (s: string n, n: int n, i: int i):<> comarg = 
    if i < n then begin
      if (s[i] <> '-') then COMARGkey (i, s) else loop (s, n, i+1)
    end else begin
      COMARGkey (n, s) (* loop exists *)
    end // end of [if]
  // end of [loop]
  val s = string1_of_string s
  val n = string_length s; val n = int1_of_size1 n
in
  loop (s, n, 0)
end // end of [comarg_parse]

implement
comarglst_parse
  {n} (argc, argv) = let
//
vtypedef
arglst(n: int) = list_vt (comarg, n)
//
fun
loop
{i:nat | i <= n}{l:addr} .<n-i>.
(
  pf0: arglst(0)@l
| argv: &(@[string][n]), i: int i, p: ptr l
) :<cloref> (arglst (n-i) @ l | void) =
(
//
if
i < argc
then let
  val+~list_vt_nil () = !p
  val x = comarg_parse (argv.[i])
  val () = !p := list_vt_cons (x, list_vt_nil ())
  val+ list_vt_cons (_, !lst) = !p
  val (pf | ()) = loop (view@ (!lst) | argv, i+1, lst)
in
  fold@(!p); (pf0 | ())
end // end of [then]
else (pf0 | ()) // end of [else]
//
) (* end of [loop] *)
//
var lst0 = list_vt_nil{comarg}()
val (pf | ()) = loop (view@ lst0 | argv, 0, &lst0) // tail-call
prval ((*void*)) = view@ lst0 := pf
//
in
  lst0
end // end of [comarglst_parse]

(* ****** ****** *)

fn comarg_warning
  (str: string) = {
  val () = prerr "waring(ATSDOC)"
  val () = prerr ": unrecognized command line argument ["
  val () = prerr str
  val () = prerr "] is ignored."
  val () = prerr_newline ()
} // end of [comarg_warning]

(* ****** ****** *)

datatype
waitkind =
  | WTKnone of ()
  | WTKinput of () // -i ...
  | WTKoutcode of () // --outcode ... // data
  | WTKoutdata of () // --outdata ... // code
  | WTKprefix of () // --prefix
// end of [waitkind]

typedef
cmdstate = @{
  comarg0= comarg
//
, waitkind= waitkind
//
, ninputfile= int // number of processed input files
//
} // end of [cmdstate]

(* ****** ****** *)

fn isWTKinput
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WTKinput () => true | _ => false
// end of [isWTKinput]

fn isWTKoutcode
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WTKoutcode () => true | _ => false
// end of [isWTKoutcode]

fn isWTKoutdata
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WTKoutdata () => true | _ => false
// end of [isWTKoutdata]

fn isWTKprefix
  (state: cmdstate): bool =
  case+ state.waitkind of
  | WTKprefix () => true | _ => false
// end of [isWTKprefix]

(* ****** ****** *)

datatype outchan =
  | OUTCHANptr of FILEref | OUTCHANref of FILEref
// end of [OUTCHAN]

fun outchan_get_fileref
  (x: outchan): FILEref = (
  case+ x of
  | OUTCHANref (filr) => filr | OUTCHANptr (filp) => filp
) // end of [outchan_get_fileref]

fun outchan_close
  (x: outchan): void =
  case+ x of
  | OUTCHANptr (filp) => fclose0_exn (filp)
  | OUTCHANref (filr) => ()
// end of [outchan_close]

(* ****** ****** *)

local
//
val stdoutchan = OUTCHANref (stdout_ref)
val the_outcode = ref<outchan> (stdoutchan)
val the_outdata = ref<outchan> (stdoutchan)
//
in (* in-of-local *)

fun outcode_get
  (): outchan = !the_outcode
fun outcode_set
  (_new: outchan): void = let
  val _old = !the_outcode
  val () = !the_outcode := _new
in
  outchan_close (_old)
end  // end of [outcode_set]

fun outdata_get
  (): outchan = !the_outdata
fun outdata_set
  (_new: outchan): void = let
  val _old = !the_outdata
  val () = !the_outdata := _new
in
  outchan_close (_old)
end  // end of [outdata_set]

end // end of [local]

(* ****** ****** *)

fun
outcode_set_filename
  (path: string): void = let
  val (pfopt | filp) = fopen_err (path, file_mode_w)
in
//
if filp > null then let
  prval
  Some_v (pffil) = pfopt
  val filp = __cast (pffil | filp) where {
    extern castfn __cast {m:fm} {l:addr} (pf: FILE (m) @ l | p: ptr l): FILEref 
  } // end of [val]
in
  outcode_set (OUTCHANptr (filp))
end else let
  prval None_v () = pfopt in outcode_set (OUTCHANref (stderr_ref))
end // end of [if]
//
end // end of [outcode_set_filename]

(* ****** ****** *)

fun
outdata_set_filename
  (path: string): void = let
  val (pfopt | filp) = fopen_err (path, file_mode_w)
in
//
if filp > null then let
  prval Some_v (pffil) = pfopt
  val filp = __cast (pffil | filp) where {
    extern castfn __cast {m:fm} {l:addr} (pf: FILE (m) @ l | p: ptr l): FILEref 
  } // end of [val]
in
  outdata_set (OUTCHANptr (filp))
end else let
  prval None_v () = pfopt in outdata_set (OUTCHANref (stderr_ref))
end // end of [if]
//
end // end of [outdata_set_filename]

(* ****** ****** *)

local

val argv0 = ref<string> ("")

in (* in-of-local *)

fn argv0_get (): string = !argv0
fn argv0_set (cmd: string): void = !argv0 := cmd

end // end of [local]

(* ****** ****** *)

fn atsdoc_usage (): void = {
  val cmd = argv0_get () // [argv0] is already set
  val () = printf ("usage: %s <command> ... <command>\n\n", @(cmd))
  val () = printf ("where each <command> is of one of the following forms:\n\n", @())
  val () = printf ("  -i filenames (for taking input from <filenames>)\n", @())
  val () = printf ("  --input filenames (for taking input from <filenames>)\n", @())
  val () = printf ("  -oc filename (outputing texting code to <filename>)\n", @())
  val () = printf ("  --outcode filename (outputing texting code to <filename>)\n", @())
  val () = printf ("  -od filename (outputing texting data to <filename>)\n", @())
  val () = printf ("  --outdata filename (outputing texting data to <filename>)\n", @())
  val () = printf ("  -h (for printing out the usage)\n", @())
  val () = printf ("  --help (for printing out the usage)\n", @())
  val () = printf ("\n", @())
} // end of [atsdoc_usage]

(* ****** ****** *)

fn*
process_cmdline
  {i:nat} .<i,0>. (
  state: &cmdstate, arglst: comarglst_vt (i)
) :<fun1> void = let
(*
  val () = prerrf ("process_cmdline: enter\n")
*)
in
//
case+ arglst of
| ~list_vt_cons (arg, arglst) => (
    process_cmdline2 (state, arg, arglst)
  ) // endof [list_vt_cons]
| ~list_vt_nil ()
    when state.ninputfile = 0 => let
//
    val outdata = outdata_get ()
    val filr = outchan_get_fileref (outdata)
    val () = trans_top_from_stdin (filr)
//
    val outcode = outcode_get ()
    val filr = outchan_get_fileref (outcode)
    val () = fprint_the_tranitmlst (filr, "STDIN")
//
  in
    // nothing
  end // end of [list_vt_nil when ...]
| ~list_vt_nil () => ()
//
end // end of [process_cmdline]

and
process_cmdline2
  {i:nat} .<i,2>. (
  state: &cmdstate
, arg: comarg, arglst: comarglst_vt (i)
) :<fun1> void = let
in
//
case+ arg of
| _ when isWTKinput (state) => let
//
// HX: the [WTKinput] state stays unchanged
//
    val nif = state.ninputfile
  in
    case+ arg of
    | COMARGkey (1, key) when nif > 0 =>
        process_cmdline2_COMARGkey1 (state, arglst, key)
    | COMARGkey (2, key) when nif > 0 =>
        process_cmdline2_COMARGkey2 (state, arglst, key)
    | COMARGkey (_, basename) => let
        val () = state.ninputfile := state.ninputfile + 1
        val outdata = outdata_get ()
        val filr = outchan_get_fileref (outdata)
        val () = trans_top_from_basename (filr, basename)
        val outcode = outcode_get ()
        val filr = outchan_get_fileref (outcode)
        val () = fprint_the_tranitmlst (filr, basename)
      in
        process_cmdline (state, arglst)
      end (* end of [_] *)
  end // end of [_ when isWTKinput]
//
| _ when isWTKoutcode (state) => let
    val () = state.waitkind := WTKnone ()
    val COMARGkey (_, basename) = arg
    val () = outcode_set_filename (basename)
  in
    process_cmdline (state, arglst)
  end // end of [_ when isWTKoutcode]
| _ when isWTKoutdata (state) => let
    val () = state.waitkind := WTKnone ()
    val COMARGkey (_, basename) = arg
    val () = outdata_set_filename (basename)
  in
    process_cmdline (state, arglst)
  end // end of [_ when isWTKoutdata]
//
| _ when isWTKprefix (state) => let
    val () = state.waitkind := WTKnone ()
    val COMARGkey (_, prfx) = arg
    val () = funres_set_prfx (prfx) // HX: prefix for return names
  in
    process_cmdline (state, arglst)
  end // end of [_ when isWTKoutdata]
//
| COMARGkey (1, key) =>
    process_cmdline2_COMARGkey1 (state, arglst, key)
| COMARGkey (2, key) =>
    process_cmdline2_COMARGkey2 (state, arglst, key)
| COMARGkey (_, key) => let
    val () = state.waitkind := WTKnone ()
    val () = comarg_warning (key)
  in
    process_cmdline (state, arglst)
  end
//
end // end of [process_cmdline2]

and
process_cmdline2_COMARGkey1
  {i:nat} .<i,1>. (
  state: &cmdstate
, arglst: comarglst_vt (i)
, key: string
) :<fun1> void = let
  val () = state.waitkind := WTKnone ()
  val () = (case+ key of
    | "-i" => {
        val () = state.ninputfile := 0
        val () = state.waitkind := WTKinput ()
      }
    | "-oc" => {
        val () = state.ninputfile := 0
        val () = state.waitkind := WTKoutcode ()
      }
    | "-od" => {
        val () = state.ninputfile := 0
        val () = state.waitkind := WTKoutdata ()
      }
    | "-h" => {
        val () = state.waitkind := WTKnone ()
        val () = state.ninputfile := state.ninputfile + 1 // HX: cutting a corner!
        val () = atsdoc_usage () // print out usage
      }
(*
    | "-v" => atsdoc_version (stdout_ref)
*)
    | _ => comarg_warning (key)
  ) : void // end of [val]
in
  process_cmdline (state, arglst)
end // end of [process_cmdline2_COMARGkey1]

and
process_cmdline2_COMARGkey2
  {i:nat} .<i,1>. (
  state: &cmdstate
, arglst: comarglst_vt (i)
, key: string
) :<fun1> void = let
  val () = state.waitkind := WTKnone ()
  val () = (case+ key of
    | "--input" => {
        val () = state.ninputfile := 0
        val () = state.waitkind := WTKinput
      }
    | "--outcode" => {
        val () = state.waitkind := WTKoutcode ()
      }
    | "--outdata" => {
        val () = state.waitkind := WTKoutdata ()
      }
    | "--prefix" => {
        val () = state.waitkind := WTKprefix ()
      }
    | "--help" => {
        val () = state.waitkind := WTKnone ()
        val () = state.ninputfile := state.ninputfile + 1 // HX: cutting a corner!
        val () = atsdoc_usage () // print out usage
      }
(*
    | "--version" => atsdoc_version (stdout_ref)
*)
    | _ => comarg_warning (key)
  ) : void // end of [val]
in
  process_cmdline (state, arglst)
end // end of [process_cmdline2_COMARGkey2]

(* ****** ****** *)

implement
main(argc, argv) = {
(*
//
val () =
println!
  ("Hello from [atsdoc]!")
//
*)
//
val () = argv0_set (argv.[0])
//
val
arglst =
  comarglst_parse (argc, argv)
//
val+~list_vt_cons (arg0, arglst) = arglst
//
var
state = @{
  comarg0 = arg0
//
, waitkind= WTKnone ()
//
, ninputfile= (0)
//
} : cmdstate
//
val () =
  process_cmdline (state, arglst)
//
val () = outchan_close (outcode_get ())
val () = outchan_close (outdata_get ())
//
} (* end of [main] *)

(* ****** ****** *)

(* end of [atsdoc_main.dats] *)
