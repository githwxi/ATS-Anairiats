(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "error.sats"
staload "types.sats"
staload "absyn.sats"
staload "parser.sats"
staload "tychecker.sats"
staload INT0 = "interp0.sats"
staload TL = "templab.sats"
staload TR = "irtree.sats"
staload F = "frame.sats"
staload TRAN = "translate.sats"
staload CA = "canonical.sats"
staload INT1 = "interp1.sats"

staload "assem.sats"
staload "codegen.sats"

staload "fgraph.sats"
staload "igraph.sats"
staload "regalloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

dynload "error.dats"
dynload "stamp.dats"
dynload "symbol.dats"
dynload "types.dats"
dynload "absyn.dats"

dynload "fixity.dats"
dynload "parser.dats"

dynload "PARCOMB/posloc.dats"
dynload "PARCOMB/tokenize.dats"
dynload "PARCOMB/parcomb.dats"

dynload "tychecker.dats"

dynload "interp0.dats"

dynload "templab.dats"

dynload "irtree.dats"

dynload "frame.dats"

dynload "translate.dats"

dynload "canonical.dats"

dynload "interp1.dats"

dynload "assem.dats"

dynload "codegen.dats"

dynload "fgnode.dats"
dynload "tempset.dats"

dynload "fgraph.dats"
dynload "igraph.dats"

dynload "liveness.dats"
dynload "regalloc.dats"

(* ****** ****** *)

fn compusage (cmd: string) = begin
  printf ("%s --help: print out usage\n", @(cmd));
(*
  printf ("%s --test: test a set of selected examples\n", @(cmd));
*)
  printf ("%s <file>: compile the given <file>\n", @(cmd));
  printf ("%s : compile the program read from the stdin\n", @(cmd));
end // end of [compusage]

(* ****** ****** *)

(*

fn comptest () = let
  val dirname = "Examples/TestCases"
  fn test (filename: string) = try let
    val exp = parse_from_file (filename)
    val () = printf
      ("The file [%s] is parsed successfully.", @(filename))
    val () = print_newline ()
    val ty = transProg (exp)
    val () = begin
      print "ty = "; print_ty (ty); print_newline ()
    end // end of [val]
(*
    val vlu = $INT0.interp0Prog (exp)
    val () = begin
      print "vlu = "; $INT0.print_value (vlu); print_newline ()
    end // end of [val]
*)
  in
    printf (
      "The file [%s] passed the test.\n", @(filename)
    ) // end of [printf]
  end with
    | ~FatalError _ => begin prerrf
        ("The file [%s] failed the test.\n", @(filename))     
      end
  // end of [test]
  val NFILE = 48 // [test49.tig] contains error
  val () = loop (1) where {
    fun loop (i: int): void =
      if i <= NFILE then let
        val filename = sprintf ("%s/test%i.tig", @(dirname, i))
        val () = test (filename)
      in
        loop (i + 1)
      end // end of [if]
    // end of [loop]
  } // end of [val]
  val ()  = test (dirname + "/merge.tig")
  val ()  = test (dirname + "/queens.tig")
in
  // empty
end // end of [comptest]

*)

(* ****** ****** *)

fun fprint_stmlst (out: FILEref, ss: $TR.stmlst): void =
  case+ ss of
  | list_cons (s, ss) => begin
      $TR.fprint_stm (out, s); fprint_newline (out); fprint_stmlst (out, ss)
    end // end of [list_cons]
  | list_nil () => fprint_newline (out)
// end of [fprint_stmlst]

fn print_stmlst (ss: $TR.stmlst): void = fprint_stmlst (stdout_ref, ss)

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

fn emit_proc (
    knd: int, frm: $F.frame_t, inss: instrlst
  ) : void = () where {
  val frmsz = $F.frame_size_get (frm)
  val lab_frm = $F.frame_name_get (frm)
  val nam_frm = $TL.label_name_get (lab_frm)
  val () = print ("\t.text\n")
  val () = if knd > 0 // [tiger_main] is global
    then printf (".globl %s\n", @(nam_frm))
  // end of [val]
#if MARCH == "x86_32" #then
  val () = printf ("\t.type\t%s, @function\n", @(nam_frm))
#endif  // MARCH == "x86_32"
  val () = printf ("%s:\n", @(nam_frm))
#if MARCH == "x86_32" #then
  // this style requires a feature like ".set"
  val () = printf ("\t.set\t.%s_framesize, %i\n", @(nam_frm, frmsz))
#endif // MARCH == "x86_32"
  val () = $F.procEntryExit1_entr_emit (stdout_ref, frm)
  fun loop (inss: instrlst): void = case+ inss of
    | list_cons (ins, inss) => let
(*
        val () = (print_instr (ins); print_newline ())
*)
        val () = case+ ins of
          | INSTRoper (asm, _, _, _)
              when string_is_empty asm => ()
            // [INSTRoper ("", _, _, _)
          | INSTRoper _ => let
              val asm = regalloc_insfmt (ins) in printf ("\t%s\n", @(asm))
            end // end of [INSTRoper]
          | INSTRlabel (asm, _) => printf ("%s\n", @(asm))
          | INSTRmove (_, src, dst) => let
              val src = regassgn_find src and dst = regassgn_find dst in
              if $TL.eq_temp_temp (src, dst) then () else let
                val asm = regalloc_insfmt (ins) in printf ("\t%s\n", @(asm))
              end // end of [if]
            end (* end of [INSTRmove] *)
      in
        loop inss
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
  val () = loop (inss)
#if (MARCH == "x86_32") #then
  val () = printf ("\t.size\t%s, .-%s\n", @(nam_frm, nam_frm))
#endif // MARCH == "x86_32"
} // end of [emit_proc]

(* ****** ****** *)

fn emit_char (c: char): void =
  case+ 0 of
  | _ when char_isprint c => print_char c
  | _ when (c = '\n') => print_string "\\n"
  | _ when (c = '\t') => print_string "\\t"
  | _ => let
      val _0 = int_of_char '0'
      val d = uint1_of_char c
      val d2 = int_of (d \mod_uint_uint 8U)
      val c2 = char_of_int (_0 + d2)
      val d = d / 8U
      val d1 = int_of (d \mod_uint_uint 8U)
      val c1 = char_of_int (_0 + d1)
      val d = d / 8U
      val d0 = int_of (d)
      val c0 = char_of_int (_0 + d0)
    in
      print_char '\\'; print_char c0; print_char c1; print_char c2
    end // end of [_]
// end of [emit_char]

(* ****** ****** *)

fn emit_string_def
  (def: string): void = () where {
  val () = print_char '"'
  val () = loop (def, 0) where {
    val def = string1_of_string def
    fun loop {n,i:nat | i <= n}
      (str: string n, i: size_t i): void =
      if string_isnot_atend (str, i)
        then (emit_char str[i]; loop (str, i+1))
      // end of [if]
    // end of [loop]
  } // end of [val]
  val () = print_char '"'
} // end of [emit_string]

#if (MARCH == "SPIM") #then
fn emit_string
  (lab: $TL.label_t, def: string): void = () where {
  val () = print ("\t.data\n")
  val () = $TL.print_label (lab)
  val () = print ":\n"
  val () = print "\t.asciiz\t"
  val () = emit_string_def (def)
  val () = print "\n"
} // end of [emit_string]
#endif // MARCH == "SPIM"

#if (MARCH == "x86_32") #then
fn emit_string
  (lab: $TL.label_t, def: string): void = () where {
  val () = print "."
  val () = $TL.print_label (lab)
  val () = print ":\n"
  val () = print "\t.string\t"
  val () = emit_string_def (def)
  val () = print "\n"
} // end of [emit_string]
#endif // MARCH == "x86_32"

(* ****** ****** *)

implement main (argc, argv) = let
  val () = case+ argc of
    | _ when argc >= 2 => begin case+ argv.[1] of
      | "--help" => (
          compusage (argv.[0]); exit {void} (0)
        ) // end [--help]
(*
      | "--test" => (comptest (); exit {void} (0))
*)
      | _ => () // continue
      end // end of [_ when ...]
    | _ => ()
  // end of [val]
  val prog_exp = case+ argc of
    | 1 => parse_from_stdin ()
    | _ (* argc >= 2 *) =>> parse_from_file (argv.[1])
  // end of [val]
(*
  val () = begin
    print "prog_exp = "; print_exp (prog_exp); print_newline ()
  end // end of [val]
*)
  val prog_ty = transProg (prog_exp)
(*
  val () = begin
    print "prog_ty = "; print_ty (prog_ty); print_newline ()
  end // end of [val]
*)
(*
  val prog_vlu = $INT0.interp0Prog (prog_exp)
  val () = begin
    print "prog_vlu = "; $INT0.print_value (prog_vlu); print_newline ()
  end // end of [val]
*)

  val prog_e1xp = $TRAN.transProg1 (prog_exp)
(*
  val () = begin
    print "prog_e1xp = "; $TRAN.print_e1xp prog_e1xp; print_newline ()
  end // end of [val]
*)
  val prog_stm = $TRAN.unNx (prog_e1xp)
(*
  val () = begin
    print "prog_stm = "; $TR.print_stm prog_stm; print_newline ()
  end // end of [val]
*)  
  val theFraglst = list_reverse ($F.frame_theFraglst_get ())
  
  datatype f1rag =
    | F1RAGproc of ($F.frame_t, $TR.stmlst) | F1RAGstring of ($TL.label_t, string)
  // end of [f1rag]
  viewtypedef f1raglst_vt = List_vt f1rag

  val theF1raglst = loop (theFraglst, list_vt_nil) where {
    fun loop (xs: $F.fraglst_vt, res: f1raglst_vt): f1raglst_vt = case+ xs of
      | ~list_vt_cons (x, xs) => let
          val f1rag = case+ x of
          | $F.FRAGproc (frm, stm) => let
(*
              val () = $TR.prerr_stm (stm)
*)
              val stms = $CA.linearize stm
              val (lab_done, blks) = $CA.blocklst_gen (stms)
              val stms = $CA.trace_schedule (lab_done, blks)
              val lab_frm = $F.frame_name_get (frm)
(*
              val () = $INT1.the_labmap_frame_stmlst_insert (lab_frm, frm, stms)
              val () = begin
                prerr "FRAGproc: "; $TL.prerr_label lab_frm; prerr_string ":\n";
                fprint_stmlst (stderr_ref, stms)
              end // end of [val]
*)
            in
              F1RAGproc (frm, stms)
            end // end of [FRAGproc]
          | $F.FRAGstring (lab, str) => let
(*
              val () = $INT1.the_labmap_string_insert (lab, str)
              val () = begin
                prerr "FRAGstring: "; $TL.prerr_label lab; prerr_string ": ";
                prerr_string str; prerr_newline ()
              end // end of [val]
*)
            in
              F1RAGstring (lab, str)
            end // end of [val]
        in
          loop (xs, list_vt_cons (f1rag, res))
        end // end of [list_cons]
      | ~list_vt_nil () => list_vt_reverse res
    // end of [loop]
  } // end of [val]

  val prog_stms = $CA.linearize prog_stm
  val (lab_done, prog_blks) = $CA.blocklst_gen (prog_stms)
  val prog_stms = $CA.trace_schedule (lab_done, prog_blks)
(*
  val () = fprint_stmlst (stderr_ref, prog_stms)
  val () = $INT1.interp1Prog (prog_stms)
*)
//
  val () = loop (theF1raglst) where {
    fun loop (xs: f1raglst_vt): void = case+ xs of
      | ~list_vt_cons (x, xs) => let
          val () = case+ x of
            | F1RAGproc (frm, stms) => let
(*
                val lab_frm = $F.frame_name_get (frm)
                val () = begin
                  prerr "F1RAGproc: "; $TL.prerr_label lab_frm; prerr_string ":\n"
                end // end of [val]
*)
                val inss = codegen_proc (frm, stms)
                val inss = instrlst_regalloc (frm, inss)
                val () = emit_proc (0(*local*), frm, inss)
              in
                // empty
              end // end of [val]
            | F1RAGstring (label, str) => emit_string (label, str)
          // end of [val]
        in
          loop (xs)
        end // end of [list_cons]
      | ~list_vt_nil () => ()
    // end of [loop]
  } // end of [val]
//
  val prog_frm = $F.theTopFrame
  val prog_inss = codegen_proc (prog_frm, prog_stms)
  // val () = prerr_instrlst (prog_inss)
  val prog_inss = instrlst_regalloc (prog_frm, prog_inss)
  val () = emit_proc (1(*global*), prog_frm, prog_inss)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [tigerats_main.dats] *)
