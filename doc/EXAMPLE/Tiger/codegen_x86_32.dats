(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

// this one does instruction selection for x86-32 arch.

(* ****** ****** *)

staload Err = "error.sats"

staload TL = "templab.sats"
typedef temp = $TL.temp_t
typedef templst = $TL.templst
viewtypedef templst_vt = List_vt (temp)

(* ****** ****** *)

staload AS = "assem.sats"

(* ****** ****** *)

staload F = "frame.sats"
typedef frame = $F.frame_t

(* ****** ****** *)

staload "irtree.sats"

(* ****** ****** *)

staload "codegen.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

viewtypedef instrlst_vt = $AS.instrlst_vt

(* ****** ****** *)

#define p2s string_of_strptr

(* ****** ****** *)

(*
// it is impractical to achieve decent instruction selection
// by a manual approach; some kind of tool is clearly needed.
*)

fn instrlst_add_stm
  (frm: frame, res: &instrlst_vt, stm: stm): void = let
  typedef instr = $AS.instr
  fn emit (res: &instrlst_vt, ins: instr): void =
    res := list_vt_cons (ins, res)
  // end of [emit]

  // AT&T-style of syntax is used for the assembly code
  fun auxstm (res: &instrlst_vt, stm: stm): void = let
(*
    val () = begin
      prerr "auxstm: stm = "; prerr_stm stm; prerr_newline ()
    end // end of [val]
*)
  in
    case+ stm of
    | STMseq (stm1, stm2) => () where {
        val () = auxstm (res, stm1); val () = auxstm (res, stm2)
      } // end of [STMseq]
    | STMjump (e, labs) => begin case+ e of
      | EXPname lab => let
          val asm = "jmp ." + $TL.label_name_get lab
          val src = '[] and dst = '[]; val jump = Some '[lab]
        in
          emit (res, $AS.INSTRoper (asm, src, dst, jump))
        end // end of [EXPname]
      | _ => let
          val s0 = auxexp (res, e)
          val asm = "jmp `s0"
          val src = '[s0] and dst = '[]; val jump = Some labs
        in
          emit (res, $AS.INSTRoper (asm, src, dst, jump))
        end // end of [_]
      end (* end of [STMjump] *)
    | STMcjump (relop, e1, e2, tlab, flab) => () where {
        val opcode = (case+ relop of
          | EQ  _ => "je"
          | NEQ _ => "jne"
          | GT  _ => "jg"
          | GE  _ => "jge"
          | LT  _ => "jl"
          | LE  _ => "jle"
        ) : string // end of [val]
        val s0 = auxexp (res, e1)
        val () = case+ e2 of
          | EXPconst i2 => emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val asm = p2s (sprintf ("cmpl $%i, `s0", @(i2)))
              val src = '[s0] and dst = '[]; val jump = None ()
            } // end of [val]
          | _ => () where {
              val s1 = auxexp (res, e2); val () = emit
                (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                val asm = "cmpl `s1, `s0"
                val src = '[s0, s1] and dst = '[]; val jump = None ()
              } // end of [val]
            } (* end of [_] *)
        // end of [val]
        val () = emit
          (res, $AS.INSTRoper (asm, src, dst, jump)) where {
          val tname = $TL.label_name_get tlab
          val asm = p2s (sprintf ("%s .%s", @(opcode, tname)))
          val src = '[] and dst = '[]; val jump = Some '[tlab, flab]
        } // end of [val]
      } (* end of [STMcjump] *)
    | STMmove (EXPmem (e1), e2) => begin case+ e1 of
        | EXPbinop (binop, e1_base, EXPconst ofs)
            when binop_is_additive binop => () where {
            var ofs: int = ofs
            val () = case+ binop of
              | PLUS () => () | _ (*MINUS*) => (ofs := ~ofs)
            // end of [val]
            val s0 = auxexp (res, e1_base)
            val () = case+ e2 of
              | EXPconst i2 => () where {
                  val () = emit
                    (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                    val asm = p2s (sprintf ("movl $%i, %i(`s0)", @(i2, ofs)))
                    val src = '[s0] and dst = '[]; val jump= None ()
                  } // end of [val]
                } (* end of [EXPconst] *)
              | EXPname lab2 => () where {
                  val () = emit
                    (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                    val name = $TL.label_name_get (lab2)
                    val asm = p2s (sprintf ("movl $.%s, %i(`s0)", @(name, ofs)))
                    val src = '[s0] and dst = '[]; val jump= None ()
                  } // end of [val]              
                } (* end of [EXPname] *)
              | _ => () where {
                  val s1 = auxexp (res, e2)
                  val () = emit
                    (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                    val asm = p2s (sprintf ("movl `s1, %i(`s0)", @(ofs)))
                    val src = '[s0, s1] and dst = '[]; val jump= None ()
                  } // end of [val]
                } (* end of [_] *)
            // end of [val]
          } // end of [EXPbinop (_(*additive*), _, EXPconst)]
        | _ => () where {
            val s0 = auxexp (res, e1)
            val () = case+ e2 of
              | EXPconst i2 => () where {
                  val () = emit
                    (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                    val asm = p2s (sprintf ("movl $%i, 0(`s0)", @(i2)))
                    val src = '[s0] and dst = '[]; val jump = None ()
                  } // end of [val]
                } (* end of [EXPconst] *)
              | EXPname lab2 => () where {
                  val () = emit
                    (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                    val name = $TL.label_name_get (lab2)
                    val asm = p2s (sprintf ("movl $.%s, 0(`s0)", @(name)))
                    val src = '[s0] and dst = '[]; val jump = None ()
                  } // end of [val]
                } (* end of [EXPname] *)
              | _ => () where {
                  val s1 = auxexp (res, e2)
                  val () = emit
                    (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                    val asm = "movl `s1, 0(`s0)"
                    val src = '[s0, s1] and dst = '[]; val jump = None ()
                  } // end of [val]
                } (* end of [_] *)
            // end of [val]
          } (* end of [_] *)
        (* end of [case ... of ...] *)
      end (* end of [STMmove (EXPmem, _)] *)
    | STMmove (EXPtemp t1, e2) => () where {
        val () = case+ e2 of
          | EXPconst i2 => () where {
              val () = emit
                (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                val asm = p2s (sprintf ("movl $%i, `d0", @(i2)))
                val src = '[] and dst = '[t1]; val jump = None ()
              } // end of [val]
            } (* end of [EXPconst] *)
          | EXPname lab2 => () where {
              val () = emit
                (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                val name = $TL.label_name_get (lab2)
                val asm = p2s (sprintf ("movl $.%s, `d0", @(name)))
                val src = '[] and dst = '[t1]; val jump = None ()
              } // end of [val]          
            } (* end of [EXPname] *)
          | _ => () where {
              val s0 = auxexp (res, e2); val () = emit
                (res, $AS.INSTRmove (asm, src, dst)) where {
                val asm = "movl `s0, `d0"; val src = s0 and dst = t1
              } // end of [val]
            } (* end of [_] *)
        // end of [val]
      } (* end of [STMmove (EXPtemp, _)] *)
    | STMlabel lab => () where {
        val name = $TL.label_name_get lab
        val asm = p2s (sprintf (".%s:", @(name)))
        val () = emit (res, $AS.INSTRlabel (asm, lab))
      } // end of [STMlabel]
    | STMexp e => begin
        let val _(*tmp*) = auxexp (res, e) in () end
      end // end of [STMexp]
    | STMusedef (uselst, deflst) => () where {
        val asm = "" // this instruction is not emitted
        val src = uselst and dst = deflst
        val jump = None ()
        val () = emit (res, $AS.INSTRoper (asm, src, dst, jump))
      } // end of [STMusedef]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": auxstm: stm = "; prerr_stm stm; prerr_newline ();
        exit {void} (1)
      end // end of [_]
  end // end of [auxstm]

  and auxexp (res: &instrlst_vt, exp: exp)
    : temp (* [temp] must not be special! *) = let
(*
    val () = begin
      prerr "auxexp: exp = "; prerr_exp exp; prerr_newline ()
    end // end of [val]
*)
  in
    case+ exp of
//
    | EXPconst i => d0 where {
        val d0 = $TL.temp_make_new ()
        val asm = p2s (sprintf ("movl $%i, `d0", @(i)))
        val src = '[] and dst = '[d0]; val jump = None ()
        val () = emit (res, $AS.INSTRoper (asm, src, dst, jump))
      } (* end of [EXPconst] *)
//
    | EXPname lab => d0 where {
        val d0 = $TL.temp_make_new ()
        val name = $TL.label_name_get (lab)
        val asm = p2s (sprintf ("movl $.%s, `d0", @(name)))
        val src = '[] and dst = '[d0]; val jump = None ()
        val () = emit (res, $AS.INSTRoper (asm, src, dst, jump))
      } (* end of [EXPconst] *)
//
(*
    | EXPtemp tmp => if
        $TL.temp_is_special (tmp) then let
        val d0 = $TL.temp_make_new (); val () = emit
          (res, $AS.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = tmp and dst = d0
        } // end of [val]
      in
        d0 // [d0] is not special
      end else begin
        tmp // [tmp] is not special
      end // end of [EMPtemp]
*)
    | EXPtemp tmp => tmp
//
    | EXPbinop (binop, e1, e2)
        when binop_is_additive binop => d0 where {
        val opcode = (case+ binop of
          | PLUS _ => "addl" | MINUS _ => "subl" | _ => "notaddsub"
        ) : string // end of [val]
        val d0 = $TL.temp_make_new ()
        val () = case+ e2 of
        | EXPconst i2 => () where {
            val s0 = auxexp (res, e1)
            val () = emit
              (res, $AS.INSTRmove (asm, src, dst)) where {
              val asm = "movl `s0, `d0"; val src = s0  and dst = d0
            } // end of [val]
            val () = emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val asm = p2s (sprintf ("%s $%i, `d0", @(opcode, i2)))
              val src = '[d0] and dst = '[d0]; val jump = None ()
            } // end of [val]
          } (* end of [EXPcons] *)
        | _ => () where {
            val s0 = auxexp (res, e1)
            val s1 = auxexp (res, e2)
            val () = emit
              (res, $AS.INSTRmove (asm, src, dst)) where {
              val asm = "movl `s0, `d0"; val src = s0 and dst = d0
            } // end of [val]
            val () = emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val asm = opcode + " `s1, `d0"
              val src = '[d0, s1] and dst = '[d0]; val jump = None ()
            } // end of [val]
          } (* end of [_] *)
        // end of [val]
      } (* end of [val] *)
//
    | EXPbinop (MUL (), e1, e2) => d0 where {
        val d0 = $TL.temp_make_new ()
        val s0 = auxexp (res, e1); val s1 = auxexp (res, e2)
        (*
        ** NOTE: there is no need to save a named register like EAX as
        ** it is assumed that such a register is not to be used directly
        ** without being defined first.
        *)
        val () = emit
          (res, $AS.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = s0 and dst = $F.EAX
        } // end of [val]
        // NOTE: one-operand style of [imull] is used here
        val () = emit
          (res, $AS.INSTRoper (asm, src, dst, jump)) where {
          val asm = "imull `s1"
          val src = '[$F.EAX, s1] and dst = '[$F.EAX, $F.EDX]
          val jump = None ()
        } // end of [val]
        val () = emit
          (res, $AS.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = $F.EAX and dst = d0
        } // end of [val]
     } (* end of [EXPbinop (MUL, _, _)] *)
//
    | EXPbinop (DIV (), e1, e2) => d0 where {
        val d0 = $TL.temp_make_new ()
        val s0 = auxexp (res, e1); val s1 = auxexp (res, e2)
        val () = emit
          (res, $AS.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = s0 and dst = $F.EAX
        } // end of [val]
        val () = emit // converting EAX to EDX:EAX
          (res, $AS.INSTRoper (asm, src, dst, jump)) where {
          val asm = "cltd"; val src = '[$F.EAX] and dst = '[$F.EDX]
          val jump = None ()
        } // end of [val]
        val () = emit
          (res, $AS.INSTRoper (asm, src, dst, jump)) where {
          val asm = "idivl `s2"
          val src = '[$F.EAX, $F.EDX, s1] and dst = '[$F.EAX, $F.EDX]
          val jump = None ()
        } // end of [val]
        val () = emit
          (res, $AS.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = $F.EAX and dst = d0
        } // end of [val]
      } (* end of [EXPbinop (DIV, _, _)] *)
//
    | EXPmem (e) => d0 where {
        val d0 = $TL.temp_make_new ()
        val () = case+ e of
        | EXPbinop (binop, e_base, EXPconst ofs)
            when binop_is_additive binop => () where {
            var ofs: int = ofs
            val () = case+ binop of
              | PLUS () => () | _ (*MUNUS*) => (ofs := ~ofs)
            val s0 = auxexp (res, e_base)
            val () = emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val asm = p2s (sprintf ("movl %i(`s0), `d0", @(ofs)))
              val src = '[s0] and dst = '[d0]; val jump = None ()
            } // end of [val]
          } (* end of [EXPbinop _(*additive*), _, EXPconst)] *)
        | _ => () where {
            val s0 = auxexp (res, e)
            val () = emit
              (res, $AS.INSTRoper (asm, src, dst, jump)) where {
              val asm = "movl (`s0), `d0"
              val src = '[s0] and dst = '[d0]; val jump = None ()
            } // end of [val]
          } (* end of [_] *)
        // end of [val]
      } (* end of [EXPmem] *)
//
    | EXPcall (e_fun, es_arg) => d0 where {
        val d0 = $TL.temp_make_new ()
        val calldefs =
          $F.theFunargReglst + $F.theCallersavedReglst // EAX, ECX, EDX
        // end of [val]
        val nargsz = (case+ e_fun of
          | EXPname lab_fun => nargsz where {
              val @(nargsz, fars) = auxarglst (res, es_arg)
              val () = emit
                (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                val name = $TL.label_name_get (lab_fun)
                val asm = p2s (sprintf ("call %s", @(name)))
                val src = fars and dst = calldefs; val jump = None ()
              } // end of [val]
            } (* end of [_] *)
          | _ => nargsz where {
              val s_fun = auxexp (res, e_fun)
              val @(nargsz, fars) = auxarglst (res, es_arg)
              val () = emit
                (res, $AS.INSTRoper (asm, src, dst, jump)) where {
                val asm = "call `s0"
                val src = list_cons (s_fun, fars) and dst = calldefs
                val jump = None ()
              } // end of [val]
            } (* end of [_] *)
          // end of [case]
        ) : int (*nargsz*) // end of [val]
        val () = emit
          (res, $AS.INSTRoper (asm, src, dst, jump)) where {
          val asm = p2s (sprintf ("addl $%i, `s0", @(nargsz)))
          val s0 = $F.SP; val src = '[s0] and dst = '[s0]; val jump = None ()
        } // end of [val]
        val () = emit
          (res, $AS.INSTRmove (asm, src, dst)) where {
          val asm = "movl `s0, `d0"; val src = $F.RV and dst = d0
        } // end of [val]
      } (* end of [EXPcall] *)
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": auxexp: exp = "; prerr_exp exp; prerr_newline ();
        exit {temp} (1)
      end // end of [_]
  end // end of [auxexp]
  
  and auxarglst // moving args into places
    (res: &instrlst_vt, es: explst): (int(*nargsz*), templst) = let
    val narg = list_length (es)
    val nargsz = narg * $F.WORDSIZE
    val rev_fars = loop
      ($F.theFunargReglst, narg, list_vt_nil) where {
      fun loop (
          fars: templst, n: int, rev_fars: templst_vt
        ) : templst_vt =
        if n > 0 then begin case+ fars of
          | list_cons (far, fars) => let
              val rev_fars = list_vt_cons (far, rev_fars)
            in
              loop (fars, n-1, rev_fars)
            end // end of [list_cons]
          | list_nil () => rev_fars
        end else begin
          rev_fars  // no more arguments and loop exits
        end // end of [if]
      // end of [loop]
    } // end of [val]
    val fars = list_of_list_vt (list_vt_reverse rev_fars)
    val () = emit
      (res, $AS.INSTRoper (asm, src, dst, jump)) where {
      val asm = p2s (sprintf ("subl $%i, `s0", @(nargsz)))
      val s0 = $F.SP; val src = '[s0] and dst = '[s0]; val jump = None ()
    } // end of [val]
    val () = loop (res, es, fars, 0(*ofs*)) where {
      fun loop
        (res: &instrlst_vt, es: explst, fars: templst, ofs: int): void =
        case+ es of
        | list_cons (e, es) => let
            val s0 = auxexp (res, e) in
            case+ fars of
            | list_cons (far, fars) => let
                val () = emit
                  (res, $AS.INSTRmove (asm, src, dst)) where {
                  val asm = "movl `s0, `d0"; val src = s0 and dst = far
                } // end of [val]
              in
                loop (res, es, fars, ofs + $F.WORDSIZE)
              end // end of [list_cons]
            | list_nil () => let
                val () = emit
                  (res, $AS.INSTRoper (asm, src, dst, jump)) where  {
                  val asm = p2s (sprintf ("movl `s0, %i(`s1)", @(ofs)))
                  val src = '[s0, $F.SP] and dst = '[]; val jump = None ()
                } // end of [val]
              in
                loop (res, es, fars, ofs + $F.WORDSIZE)
              end // end of [val]
          end // end of [list_cons]
        | list_nil () => ()
      // end of [loop]
    } // end of [val]
  in
    @(nargsz, fars)
  end // end of [auxarglst]
in
  auxstm (res, stm)
end // end of [instrlst_add_stm]

(* ****** ****** *)

(* end of [codegen_x86_32.dats] *)
