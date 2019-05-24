(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload Err = "error.sats"

(* ****** ****** *)

staload "frame.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

//
// this part is architechture-independent; it can be shared if needed
//

local

val theFraglst = ref_make_elt<fraglst> (list_nil)

in // in of [loca]

implement frame_theFraglst_get () = !theFraglst

implement frame_theFraglst_add (frag) =
  !theFraglst := list_cons (frag, !theFraglst)
// end of [frame_theFraglst_add]

implement frame_theFraglst_reset () = !theFraglst := list_nil ()
// end of [frame_theFraglst_reset]

end // end of [local]

(* ****** ****** *)

staload TL = "templab.sats"

typedef temp = $TL.temp_t
typedef label = $TL.label_t

(* ****** ****** *)

staload AS = "assem.sats"
staload TR = "irtree.sats"

typedef instr = $AS.instr

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

local

datatype access =
  | InFrame of int | InReg of temp
// end of [access]

assume access_t = access

typedef frame = '{
  frame_name= label
, frame_argofs= int // the difference between SP and 1st arg
, frame_arglst= accesslst
, frame_nlocvar= int // number of local variables in the frame
} // end of [frame]

assume frame_t = frame

in // end of [in]

fn fprint_access (out: FILEref, acc: access_t): void =
  case+ acc of
  | InFrame ofs => begin
      fprint_string (out, "InFrame("); fprint_int (out, ofs); fprint_string (out, ")")
    end // end of [InFrame]
  | InReg tmp => begin
      fprint_string (out, "InReg("); $TL.fprint_temp (out, tmp); fprint_string (out, ")")
    end // end of [InReg]
// end of [fprint_access]

fn prerr_access (acc: access_t): void = fprint_access (stderr_ref, acc)

(* ****** ****** *)

implement access_is_inreg (acc) = case+ acc of InReg _ => true | _ => false
implement access_is_inframe (acc) = case+ acc of InFrame _ => true | _ => false

implement exp_make_access (e_off, acc) = case+ acc of
  | InFrame (k) => begin
      $TR.EXPmem ($TR.EXPbinop ($TR.PLUS, e_off, $TR.EXPconst k))
    end // end of [InFrame]
  | InReg tmp => $TR.EXPtemp tmp
// end of [exp_make_access]

(* ****** ****** *)

local

#include "params.hats"

in

implement WORDSIZE = (WORDSIZE_TARGET / 8)

end // end of [local]

(* ****** ****** *)

implement theTopFrame = let
  val lab0 = $TL.tiger_main in
  frame_make_new (lab0, 0(*argofs*), list_nil (*arglst*))
end // end of [theTopFrame]

(* ****** ****** *)

implement frame_make_new (lab, ofs0, arglst) = '{
  frame_name= lab
, frame_argofs= ofs0
, frame_arglst= arglst
, frame_nlocvar= 0
} where {
  fun aux
    (xs: List bool, ofs: int): accesslst = case+ xs of
    | list_cons (x, xs) => let
        val acc = (
          if x(*escaped*) then InFrame (ofs) else begin
            let val tmp = $TL.temp_make_new () in InReg (tmp) end
          end // end of [if]
        ) : access
(*
        val () = begin
          prerr "frame_make_new: aux: ofs = "; prerr ofs; prerr_newline ();
          prerr "frame_make_new: aux: acc = "; prerr_access acc; prerr_newline ();
        end // end of [val]
*)
        // [ofs] is increased regardless [acc] is InFrame or InReg
        val accs = aux (xs, ofs + WORDSIZE) // stack grows downward
      in
        list_cons (acc, accs)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux]
 val arglst = aux (arglst, ofs0)
} // end of [frame_make_new]

implement frame_name_get (f) = f.frame_name
implement frame_argofs_get (f) = f.frame_argofs
implement frame_arglst_get (f) = f.frame_arglst

extern fun frame_nlocvar_set (f: frame, n: int): void
  = "tigerats_frame_nlocvar_set"

implement frame_size_get (f) = ~f.frame_nlocvar

implement frame_alloc_local
  (frame, isEscaped) = case+ 0 of
  | _ when isEscaped => let
      val n = frame.frame_nlocvar
      val n_new = n - WORDSIZE // downward!
      val () = frame_nlocvar_set (frame, n_new) 
    in
      InFrame (n_new)
    end // end of [_ when ...]
  | _ (* not escaped *) => let
      val tmp = $TL.temp_make_new () in InReg (tmp)
    end // end of [_]
// end of [frame_alloc_local]

extern typedef "frame_t" = frame

(* ****** ****** *)

#define p2s string_of_strptr

implement
instr_make_mem_read (acc, tmp) = case+ acc of
  | InFrame (ofs) => 
     $AS.INSTRoper (asm, src, dst, jump) where {
#if (MARCH == "SPIM") #then
      val asm = p2s (sprintf ("lw `d0, %i(`s0)", @(ofs)))
#endif // MARCH == "SPIM"
#if (MARCH == "x86_32") #then
      val asm = p2s (sprintf ("movl %i(`s0), `d0", @(ofs)))
#endif // MARCH == "x86_32"
      val src = '[FP] and dst = '[tmp]; val jump = None ()
    } // end of [INSTRoper]
  | InReg _ => begin
      prerr "INTERNAL ERROR: instr_make_mem_read: acc = InReg (...)";
      $Err.abort {instr} (1)
    end // end of [InReg]
// end of [instr_make_mem_read]

implement
instr_make_mem_write (acc, tmp) = case+ acc of
  | InFrame (ofs) => 
     $AS.INSTRoper (asm, src, dst, jump) where {
#if (MARCH == "SPIM") #then
      val asm = p2s (sprintf ("sw `s1, %i(`s0)", @(ofs)))
#endif // MARCH == "SPIM"
#if (MARCH == "x86_32") #then
      val asm = p2s (sprintf ("movl `s1, %i(`s0)", @(ofs)))
#endif // MARCH == "x86_32"
      val src = '[FP, tmp] and dst = '[]; val jump = None ()
    } // end of [INSTRoper]
  | InReg _ => begin
      prerr "INTERNAL ERROR: instr_make_mem_write: acc = InReg (...)";
      $Err.abort {instr} (1)
    end // end of [InReg]
// end of [instr_make_mem_write]

(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

#if (MARCH == "SPIM") #then

// tmp0 (*SP*) -> r29
// tmp1 (*FP*) -> r30
// tmp2 (*RV*) -> r2 (* or r3 *)
// tmp3 (*RA*) -> r31

#define REGISTER_0 0
#define REGISTER_SP 1
#define REGISTER_FP 2
#define REGISTER_RV 3
#define REGISTER_RV2 4
#define REGISTER_RA 5 // it is callee saved

val temp_r0 = $TL.temp_make_fixed (REGISTER_0)

implement ZERO = temp_r0

val temp_SP = $TL.temp_make_fixed (REGISTER_SP)
val temp_FP = $TL.temp_make_fixed (REGISTER_FP)
val temp_RV = $TL.temp_make_fixed (REGISTER_RV)
val temp_RV2 = $TL.temp_make_fixed (REGISTER_RV2)

implement SP = temp_SP
implement FP = temp_FP
implement RV = temp_RV

val temp_r2 = temp_RV
val temp_r3 = temp_RV2

implement theSpecialReglst = '[
  temp_r0, temp_SP, temp_FP
] // end of [theSpecialReglst]

val temp_r4 = $TL.temp_make_fixed (10)
val temp_r5 = $TL.temp_make_fixed (11)
val temp_r6 = $TL.temp_make_fixed (12)
val temp_r7 = $TL.temp_make_fixed (13)

implement theFunargReglst = '[
  temp_r4, temp_r5, temp_r6, temp_r7
] // end of [theFunargReglst]

val temp_r8 = $TL.temp_make_fixed (20)
val temp_r9 = $TL.temp_make_fixed (21)
val temp_r10 = $TL.temp_make_fixed (22)
val temp_r11 = $TL.temp_make_fixed (23)
val temp_r12 = $TL.temp_make_fixed (24)
val temp_r13 = $TL.temp_make_fixed (25)
val temp_r14 = $TL.temp_make_fixed (26)
val temp_r15 = $TL.temp_make_fixed (27)
val temp_r24 = $TL.temp_make_fixed (28)
val temp_r25 = $TL.temp_make_fixed (29)

implement theCallersavedReglst = '[
  temp_r8, temp_r9, temp_r10, temp_r11
, temp_r12, temp_r13, temp_r14, temp_r15
, temp_r24, temp_r25
] // end of [theCallersavedReglst]

val temp_r16 = $TL.temp_make_fixed (40)
val temp_r17 = $TL.temp_make_fixed (41)
val temp_r18 = $TL.temp_make_fixed (42)
val temp_r19 = $TL.temp_make_fixed (43)
val temp_r20 = $TL.temp_make_fixed (44)
val temp_r21 = $TL.temp_make_fixed (45)
val temp_r22 = $TL.temp_make_fixed (46)
val temp_r23 = $TL.temp_make_fixed (47)
val temp_r31 = $TL.temp_make_fixed (REGISTER_RA)

implement RA = temp_r31
implement exp_RA = $TR.EXPtemp RA

implement theCalleesavedReglst = '[
  temp_r16, temp_r17, temp_r18, temp_r19
, temp_r20, temp_r21, temp_r22, temp_r23
, temp_r31(*RA*)
] // end of [theCalleesavedReglst]

implement theGeneralReglst = '[
(*
  temp_r0 // zero reigster
  temp_r1 // [at] register; reserved for assembler
*)
  temp_r2
(*
, temp_r3 // not used
*)
, temp_r4
, temp_r5
, temp_r6
, temp_r7
, temp_r8
, temp_r9
, temp_r10
, temp_r11
, temp_r12
, temp_r13
, temp_r14
, temp_r15
, temp_r16
, temp_r17
, temp_r18
, temp_r19
, temp_r20
, temp_r21
, temp_r22
, temp_r23
, temp_r24
, temp_r25
(*
, temp_r26 // reserved for OS kernel
, temp_r27 // reserved for OS kernel
, temp_r28 // poiner to global area
, temp_r29 // SP
, temp_r30 // FP
*)
, temp_r31(*RA*)
] // end of [theGeneralReglst]

(* ****** ****** *)

#endif // end of [MARCH == "SPIM"]

(* ****** ****** *)

#if (MARCH == "x86_32") #then

implement theFunargReglst = '[]

// tmp0 (*SP*) -> esp
// tmp1 (*FP*) -> ebp
// tmp2 (*RV*) -> eax
// tmp3 (*RA*) -> eip

#define REGISTER_SP 0
#define REGISTER_FP 1
#define REGISTER_RV 2 // tmp2 (*RV*) -> %eax

val temp_SP = $TL.temp_make_fixed (REGISTER_SP)
val temp_FP = $TL.temp_make_fixed (REGISTER_FP)
val temp_RV = $TL.temp_make_fixed (REGISTER_RV)

implement SP = temp_SP
implement FP = temp_FP
implement RV = temp_RV

// [RV] is [EAX] on x86-32
implement theSpecialReglst = '[temp_SP, temp_FP]

val temp_eax = temp_RV
val temp_esp = temp_SP
val temp_ebp = temp_FP

implement EAX = temp_eax
implement ESP = temp_esp
implement EBP = temp_ebp

#define REGISTER_ECX 11
#define REGISTER_EDX 12

val temp_ecx = $TL.temp_make_fixed (REGISTER_ECX)
val temp_edx = $TL.temp_make_fixed (REGISTER_EDX)

implement ECX = temp_ecx
implement EDX = temp_edx

implement theCallersavedReglst = '[
  temp_eax, temp_ecx, temp_edx
] // end of [theCallersavedReglst]

#define REGISTER_EBX 20
#define REGISTER_ESI 21
#define REGISTER_EDI 22

val temp_ebx = $TL.temp_make_fixed (REGISTER_EBX)
val temp_esi = $TL.temp_make_fixed (REGISTER_ESI)
val temp_edi = $TL.temp_make_fixed (REGISTER_EDI)

implement EBX = temp_ebx
implement ESI = temp_esi
implement EDI = temp_edi

implement theCalleesavedReglst = '[
  temp_ebx, temp_esi, temp_edi
] // end of [theCalleesavedReglst]

implement theGeneralReglst = '[
  temp_eax
, temp_ebx
, temp_ecx
, temp_edx
, temp_esi
, temp_edi
] // end of [theGeneralReglst]

(* ****** ****** *)

#endif // end of [MARCH == "x86_32"]

(* ****** ****** *)

local

staload H = "LIB/hashtable.dats"

typedef key = $TL.temp_t and itm = string

val _hash_temp = lam (tmp: key): ulint =<cloref> $TL.hash_temp (tmp)

val _eq_temp = lam
  (tmp1: key, tmp2: key): bool =<cloref> $TL.eq_temp_temp (tmp1, tmp2)
// end of [_eq_temp]

val theRegNameTbl = $H.hashtbl_make_hint<key,itm> (_hash_temp, _eq_temp, 32)

fn regname_insert (tmp: $TL.temp_t, name: string): void = let
  val ans = $H.hashtbl_insert_err<key,itm> (theRegNameTbl, tmp, name)
in
  case+ ans of ~Some_vt _ => () | ~None_vt _ => ()
end // end of [regname_insert]

#if (MARCH == "SPIM") #then

val () = regname_insert (temp_r0, "$zero")
//
val () = regname_insert (SP, "$sp") // r29
val () = regname_insert (FP, "$fp") // r30
// for return values
val () = regname_insert (temp_r2, "$v0")
val () = regname_insert (temp_r3, "$v1")
// for passing funargs
val () = regname_insert (temp_r4, "$a0")
val () = regname_insert (temp_r5, "$a1")
val () = regname_insert (temp_r6, "$a2")
val () = regname_insert (temp_r7, "$a3")
// caller saved
val () = regname_insert (temp_r8, "$t0")
val () = regname_insert (temp_r9, "$t1")
val () = regname_insert (temp_r10, "$t2")
val () = regname_insert (temp_r11, "$t3")
val () = regname_insert (temp_r12, "$t4")
val () = regname_insert (temp_r13, "$t5")
val () = regname_insert (temp_r14, "$t6")
val () = regname_insert (temp_r15, "$t7")
// callee saved
val () = regname_insert (temp_r16, "$s0")
val () = regname_insert (temp_r17, "$s1")
val () = regname_insert (temp_r18, "$s2")
val () = regname_insert (temp_r19, "$s3")
val () = regname_insert (temp_r20, "$s4")
val () = regname_insert (temp_r21, "$s5")
val () = regname_insert (temp_r22, "$s6")
val () = regname_insert (temp_r23, "$s7")
// caller saved
val () = regname_insert (temp_r24, "$t8")
val () = regname_insert (temp_r25, "$t9")
//
val () = regname_insert (temp_r31, "$ra") // r31

#endif

#if (MARCH == "x86_32") #then

val () = regname_insert (SP, "%esp")
val () = regname_insert (FP, "%ebp")
val () = regname_insert (EAX, "%eax")
val () = regname_insert (EBX, "%ebx")
val () = regname_insert (ECX, "%ecx")
val () = regname_insert (EDX, "%edx")
val () = regname_insert (ESI, "%esi")
val () = regname_insert (EDI, "%edi")

#endif

in // in of [local]

implement register_name_get (tmp) = let
  val ans = $H.hashtbl_search<key,itm> (theRegNameTbl, tmp)
in
  case+ ans of ~Some_vt name => name | ~None_vt () => "tmp?"
end // end of [register_name_get]

end // end of [local]

(* ****** ****** *)

#if (MARCH == "SPIM") #then

(* ****** ****** *)

implement procEntryExit1_entr (frm, inss) = ()

implement procEntryExit1_entr_emit (out, frm) = let
// for saving the FP on the stack
  val () = fprintf (out, "\taddi $sp, $sp, -%i\n", @(WORDSIZE))
  val () = fprintf (out, "\tsw $fp, 0($sp)\n", @())
  val () = fprintf (out, "\tmove $fp, $sp\n", @())
  val frmsz = frame_size_get (frm)
(*
  val () = begin
    prerr "procEntryExit1_entr: frmsz = "; prerr frmsz; prerr_newline ()
  end // end of [val]
*)
  val () = if frmsz > 0 then
    fprintf (out, "\taddi $sp, $sp, -%i\n", @(frmsz))
  // end of [val]
in
  // empty
end // end of [procEntryExit1_entr_emit]

implement procEntryExit1_exit (frm, inss) = let
  viewtypedef instrlst_vt = $AS.instrlst_vt
  val () = () where {
    val asm = "move `d0, `s0"
    val src = '[FP] and dst = '[SP]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
// for restoring the FP from the stack
  val () = () where {
    val asm = "lw `d0, 0(`s0)"
    val src = '[SP] and dst = '[FP]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
  val () = () where {
    val asm = p2s (sprintf ("addi `d0, `s0, %i", @(WORDSIZE)))
    val src = '[SP] and dst = '[SP]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
in
  // empty
end // end of [procEntryExit1_exit]

(* ****** ****** *)

implement procEntryExit2 (_(*frm*), inss) =
  inss := list_vt_cons (ins, inss) where {
  val asm = "jr $ra"
  val src = theCalleesavedReglst and dst = '[]; val jump = None ()
  val ins = $AS.INSTRoper (asm, src, dst, jump)
} // end of [procEntryExit2]

(* ****** ****** *)

#endif // end of [MARCH = "SPIM"]

(* ****** ****** *)

#if (MARCH == "x86_32") #then

(* ****** ****** *)

implement procEntryExit1_entr (frm, inss) = let
(*
  val () = () where {
    val asm = "pushl `s0"
    val src = '[FP] and dst = '[]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
  val () = () where {
    val asm = "movl `s0, `d0"
    val src = '[SP] and dst = '[FP]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
//
  val () = () where {
    val lab = frame_name_get (frm)
    val nam = $TL.label_name_get (lab)
    val asm = sprintf ("subl $.%s_framesize, `s0", @(nam))
    val src = '[SP] and dst = '[SP]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
*)
in
  // empty
end // end of [procEntryExit1_entr]

implement procEntryExit1_entr_emit (out, frm) = let
  val () = fprintf (out, "\tpushl %%ebp\n", @())
  val () = fprintf (out, "\tmovl %%esp, %%ebp\n", @())
  val frmsz = frame_size_get (frm)
  val () = if frmsz > 0 then let
    val lab = frame_name_get (frm)
    val nam = $TL.label_name_get (lab)
    val () = fprintf (out, "\tsubl $.%s_framesize, %%esp\n", @(nam))
  in
    // empty
  end // end of [val]
in
  // empty
end // end of [procEntryExit_entr_emit]

implement procEntryExit1_exit (frm, inss) = let
  viewtypedef instrlst_vt = $AS.instrlst_vt
  val () = () where {
    val asm = "leave"
    val src = '[FP] and dst = '[SP]; val jump = None ()
    val ins = $AS.INSTRoper (asm, src, dst, jump)
    val () = inss := list_vt_cons (ins, inss)
  } // end of [val]
in
  // empty
end // end of [procEntryExit1_exit]

(* ****** ****** *)

implement procEntryExit2 (_(*frm*), inss) =
  inss := list_vt_cons (ins, inss) where {
  val asm = "ret"
  val src = theCalleesavedReglst and dst = '[]; val jump = None ()
  val ins = $AS.INSTRoper (asm, src, dst, jump)
} // end of [procEntryExit2]

(* ****** ****** *)

#endif // end of [MARCH = "x86_32"]

(* ****** ****** *)

implement exp_FP = $TR.EXPtemp (temp_FP)
implement exp_SP = $TR.EXPtemp (temp_SP)
implement exp_RV = $TR.EXPtemp (temp_RV)

(* ****** ****** *)

%{$

#define NBIT_PER_BYTE 8

ats_void_type
tigerats_frame_nlocvar_set
  (ats_ptr_type frame, ats_int_type n) {
  ((frame_t)frame)->atslab_frame_nlocvar = n ; return ;
} // end of [tigerats_frame_nlocvar_set]

%}

(* ****** ****** *)

(* end of [frame.dats] *)
