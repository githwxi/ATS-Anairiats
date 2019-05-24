(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

staload "irtree.sats"

(* ****** ****** *)

fn fprint_binop (out: FILEref, binop: binop) = case+ binop of
  | PLUS _ => fprint_string (out, "+")
  | MINUS _ => fprint_string (out, "-")
  | MUL _ => fprint_string (out, "*")
  | DIV _ => fprint_string (out, "/")
(*
  | AND _ => fprint_string (out, "&")
  | OR _ => fprint_string (out, "|")
  | LSHIFT _ => fprint_string (out, "lsl")
  | RSHIFT _ => fprint_string (out, "lsr")
  | ARSHIFT _ => fprint_string (out, "asr")
  | XOR _ => fprint_string (out, "xor")
*)
// end of [fprint_binop]

(* ****** ****** *)

fn fprint_relop (out: FILEref, relop: relop) = case+ relop of
  | EQ _ => fprint_string (out, "=")
  | NEQ _ => fprint_string (out, "<>")
  | GT _ => fprint_string (out, "GT")
  | GE _ => fprint_string (out, "GTE")
  | LT _ => fprint_string (out, "LT")
  | LE _ => fprint_string (out, "LE")
(*
  | UGT _ => fprint_string (out, "UGT")
  | UGE _ => fprint_string (out, "UGE")
  | ULT _ => fprint_string (out, "ULT")
  | ULE _ => fprint_string (out, "ULE")
*)
// end of [fprint_relop]

(* ****** ****** *)

fn fprint_explst
  (out: FILEref, es: explst) = let
  fun loop
    (out: FILEref, es: explst, i: int): void =
    case+ es of
    | list_cons (e, es) => let
        val () = if i > 0 then fprint_string (out, ", ")
      in
        fprint_exp (out, e); loop (out, es, i+1)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
in
  loop (out, es, 0)
end // end of [fprint_explst]

implement fprint_exp (out, exp) = let
  macdef prstr (str) = fprint_string (out, ,(str))
in
  case+ exp of
  | EXPconst i => begin
      prstr "EXPconst("; fprint_int (out, i); prstr ")"
    end // end of [EXPconst]
  | EXPname (lab) => begin
      prstr "EXPname("; $TL.fprint_label (out, lab); prstr ")"
    end // end of [EXPname]
  | EXPtemp (tmp) => begin
      prstr "EXPtemp("; $TL.fprint_temp (out, tmp); prstr ")"
    end // end of [EXPtemp]
  | EXPbinop (binop, e1, e2) => begin
      prstr "EXPbinop(";
      fprint_binop (out, binop);
      prstr "; ";
      fprint_exp (out, e1); prstr ", "; fprint_exp (out, e2);
      prstr ")"
    end // end of [EXPbinop]
  | EXPmem e => begin
      prstr "EXPmem("; fprint_exp (out, e); prstr ")"
    end // end of [EXPmem]
  | EXPcall (e_fun, es_arg) => begin
      prstr "EXPcall(";
      fprint_exp (out, e_fun);
      prstr "; ";
      fprint_explst (out, es_arg);
      prstr ")"
    end // end of [EXPcall]
  | EXPeseq (s, e) => begin
      prstr "EXPeseq(";
      fprint_stm (out, s); prstr "; "; fprint_exp (out, e);
      prstr ")"
    end // end of [EXPeseq]
end // end of [fprint_exp]

implement print_exp (exp) = fprint_exp (stdout_ref, exp)
implement prerr_exp (exp) = fprint_exp (stderr_ref, exp)

(* ****** ****** *)

implement fprint_stm (out, stm) = let
  macdef prstr (str) = fprint_string (out, ,(str))
in
  case+ stm of
  | STMmove (e1, e2) => begin
      prstr "STMmove(";
      fprint_exp (out, e1); prstr ", "; fprint_exp (out, e2);
      prstr ")"
    end // end of [STMmove]
  | STMexp e => begin
      prstr "STMexp("; fprint_exp (out, e); prstr ")"
    end // end of [STMexp]
  | STMjump (e, labs) => begin
      prstr "STMjump(";
      fprint_exp (out, e); prstr "; "; prstr "...";
      prstr ")"
    end // end of [STMjump]
  | STMcjump (relop, e1, e2, tlab, flab) => begin
      prstr "STMcjump(";
      fprint_relop (out, relop);
      prstr "; ";
      fprint_exp (out, e1);
      prstr ", ";      
      fprint_exp (out, e2);
      prstr "; ";
      $TL.fprint_label (out, tlab);
      prstr " : ";
      $TL.fprint_label (out, flab);
      prstr ")"
    end // end of [STMcjump]
  | STMseq (s1, s2) => begin
      prstr "STMseq(";
      fprint_stm (out, s1); prstr "; "; fprint_stm (out, s2);
      prstr ")"
    end // end of [STMseq]
  | STMlabel lab => begin
      prstr "STMlabel("; $TL.fprint_label (out, lab); prstr ")"
    end // end of [STMlabel]
  | STMusedef _ => begin
      prstr "STMusedef("; prstr "..."; prstr ")"
    end // end of [STMusedef]
end (* end of [fprint_stm] *)

implement print_stm (stm) = fprint_stm (stdout_ref, stm)
implement prerr_stm (stm) = fprint_stm (stderr_ref, stm)

(* ****** ****** *)

implement exp_const_0 = EXPconst 0
implement exp_const_1 = EXPconst 1

implement stm_nop = STMexp (exp_const_0)

(* ****** ****** *)

implement binop_is_additive (binop) =
  case+ binop of
  | PLUS _ => true | MINUS _ => true | _ => false
// end of [binop_is_additive]

implement binop_is_multiplicative (binop) =
  case+ binop of
  | MUL _ => true | DIV _ => true | _ => false
// end of [binop_is_multiplicative]

(* ****** ****** *)

implement relop_negate (relop) = case+ relop of
  | EQ () => NEQ ()
  | NEQ () => EQ ()
  | GT () => LE ()
  | GE () => LT ()
  | LT () => GE ()
  | LE () => GT ()
// end of [relop_negate]

(* ****** ****** *)

(* end of [irtree.dats] *)
