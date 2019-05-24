(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

(*
**
** This interpreter is primarily for testing if the tree
** instructions obtained after the canonicalization phase
** work properly.
**
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload Sym = "symbol.sats"

staload TL = "templab.sats"
typedef temp = $TL.temp_t
typedef label = $TL.label_t

overload = with $TL.eq_label_label

(* ****** ****** *)

staload TR = "irtree.sats"
typedef stmlst = $TR.stmlst

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/array0.dats"
staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

datatype v1al =
  | V1ALint of int | V1ALlab of label | V1ALstr of string
// end of [v1al]

val v1al_int_0 = V1ALint 0

(* ****** ****** *)

datatype v2al =
  | V2ALcod of ($F.frame_t, stmlst)
  | V2ALpre of (List v1al -<cloref1> v1al)
  | V2ALstr of string

(* ****** ****** *)

staload M = "LIB/funmap_avltree.dats"

typedef tmpmap = $M.map_t ($TL.temp_t, v1al)

(* ****** ****** *)

local

val _cmp_tmp = lam
  (x1: temp, x2: temp): Sgn
  =<cloref> $TL.compare_temp_temp (x1, x2)
// end of [val]

in // in of [local]

fn tmpmap_empty () = $M.funmap_empty<> {temp, v1al} ()

fn tmpmap_search (env: tmpmap, tmp: temp): v1al = let
  val ans = begin
    $M.funmap_search<temp,v1al> (env, tmp, _cmp_tmp)
  end // end of [val]
in
  case+ ans of ~Some_vt v1al => v1al | ~None_vt () => v1al_int_0
end // end of [the_tmpmap_search]

fn tmpmap_insert
  (env: &tmpmap, tmp: temp, v1al: v1al): void = begin
  env := $M.funmap_insert<temp,v1al> (env, tmp, v1al, _cmp_tmp)
end // end of [the_tempmap_search]

end // end of [local]

(* ****** ****** *)

local

val _cmp_lab = lam
  (x1: label, x2: label): Sgn
  =<cloref> $TL.compare_label_label (x1, x2)
// end of [val]

typedef labmap = $M.map_t ($TL.label_t, v2al)

val the_labmap_ref = let
  val map = $M.funmap_empty<> {label, v2al} ()
in
  ref_make_elt<labmap> (map)
end (* end of [the_labmap_ref] *)

in // in of [local]

fn the_labmap_search (lab: label): v2al = let
  val ans = begin
    $M.funmap_search<label,v2al> (!the_labmap_ref, lab, _cmp_lab)
  end // end of [val]
in
  case+ ans of
  | ~Some_vt fv => fv | ~None_vt () => begin
      prerr "INTERNAL ERROR";
      prerr ": the_labmap_search: unfound label ["; $TL.prerr_label lab;
      prerr "]"; prerr_newline ();
      exit {v2al} (1)
    end // end of [None_vt]
end // end of [the_labmap_search]

fn the_labmap_insert (lab: label, v2al: v2al): void = begin
  !the_labmap_ref := $M.funmap_insert (!the_labmap_ref, lab, v2al, _cmp_lab)
end // end of [the_labmap_insert]

end // end of [local]

(* ****** ****** *)

//
// a string may be static (V1ALlab) and dynamic (V1ALstr)
//

fn string_of_v1al (v: v1al): string = case- v of
  | V1ALlab lab => let
      val- V2ALstr str = the_labmap_search (lab) in str
    end // end of [V1ALlab]
  | V1ALstr str => str // [str] is dynamically generated
// end of [string_of_v1al]

(* ****** ****** *)

val () = the_labmap_insert (
  $TL.tiger_print, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v, _) = vs
    val str = string_of_v1al (v)
  in
    print_string str; v1al_int_0
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_print_int, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v, _) = vs; val- V1ALint i = v in
    print_int i; v1al_int_0
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_flush, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val () = fflush_exn (stdout_ref) in v1al_int_0
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_getchar, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val i = getchar (); val c = char_of_int i
    val sbp = string_make_char (1, c)
    val s = string1_of_strbuf (sbp)
  in
    V1ALstr (s)
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_concat, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v1, vs) = vs
    val- list_cons (v2, vs) = vs
    val str1 = string_of_v1al (v1)
    val str2 = string_of_v1al (v2)
  in
    V1ALstr (str1 + str2)
  end // end of [val]
} // end of [val]

(* ****** ****** *)

val () = the_labmap_insert (
  $TL.tiger_chr, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v, vs) = vs
    val- V1ALint i = v
    val c = char_of_int (i)
    val sbp = string_make_char (1, c)
    val str = string1_of_strbuf (sbp)
  in
    V1ALstr (str)
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_ord, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v, vs) = vs
    val str = string_of_v1al (v)
    val str = string1_of_string str
    val () = assert (string_isnot_atend (str, 0))
    val c = str[0]
    val i = int_of_char c
  in
    V1ALint (i)
  end // end of [val]
} // end of [val]

(* ****** ****** *)

val () = the_labmap_insert (
  $TL.tiger_eq_string_string, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v1, vs) = vs
    val- list_cons (v2, vs) = vs
    val str1 = string_of_v1al (v1)
    val str2 = string_of_v1al (v2)
  in
    if str1 = str2 then V1ALint (1) else V1ALint (0)
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_neq_string_string, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v1, vs) = vs
    val- list_cons (v2, vs) = vs
    val str1 = string_of_v1al (v1)
    val str2 = string_of_v1al (v2)
  in
    if str1 <> str2 then V1ALint (1) else V1ALint (0)
  end // end of [val]
} // end of [val]

(* ****** ****** *)

val WSZ = $F.WORDSIZE

extern fun the_memory_get (i: int): v1al
extern fun the_memory_set (i: int, v: v1al): void

extern fun the_stack_push (v: v1al): void
extern fun the_stackptr_get (): int
extern fun the_stackptr_set (i: int): void

local

#define HEAPSIZE 0xF0000
#define STACKSIZE 0x10000

#define MEMORYSIZE 0x100000 // stack + heap
#assert (MEMORYSIZE = STACKSIZE + HEAPSIZE)

val the_heapptr = ref_make_elt<int> (STACKSIZE)

val the_stackptr = ref_make_elt<int> (STACKSIZE)

val the_memory = array0_make_elt<v1al> (MEMORYSIZE, v1al_int_0)

in // in of [local]

implement the_memory_get (i) = the_memory[i]
implement the_memory_set (i, v) =  the_memory[i] := v

implement the_stack_push (v) = let
  val i = !the_stackptr - 1 in
  !the_stackptr := i; the_memory[i] := v
end // end of [the_stack_push]

implement the_stackptr_get () = !the_stackptr
implement the_stackptr_set (i) = !the_stackptr := i

val () = the_labmap_insert (
  $TL.tiger_array_alloc, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v, _) = vs; val- V1ALint i = v
    val n = !the_heapptr; val () = !the_heapptr := n+i
    in V1ALint (n * WSZ)
  end // end of [val]
} // end of [val]

val () = the_labmap_insert (
  $TL.tiger_array_make_elt, V2ALpre f_pre
) where {
  val f_pre = lam
    (vs: List v1al): v1al =<cloref1> let
    val- list_cons (v_size, vs) = vs
    val- list_cons (v_init, vs) = vs
    val- V1ALint i_size = v_size
    val n = !the_heapptr
    val () = !the_heapptr := n+i_size
    val () = loop (v_init, n+i_size, n) where {
      fun loop (v_init: v1al, ni_size: int, ni: int): void =
        if ni_size > ni then begin
          the_memory[ni] := v_init; loop (v_init, ni_size, ni+1)
        end // end of [if]
    } // end of [val]
  in
    V1ALint (n * WSZ)
  end // end of [val]
} // end of [val]

end // end of [local]

(* ****** ****** *)

fun stmlst_label_find
  (stms: stmlst, lab: label): stmlst = begin
  case+ stms of
  | list_cons (stm, stms) => begin case+ stm of
    | $TR.STMlabel lab1 when lab = lab1 => stms
    | _ => stmlst_label_find (stms, lab)
    end // end of [list_cons]
  | list_nil () => begin
      prerr "INTERNAL ERROR";
      prerr ": stmlst_label_find: unfound label: [";
      $TL.prerr_label lab;
      prerr "]"; prerr_newline ();
      exit {stmlst} (1)
    end // end of [list_nil]
end // end of [stmlst_label_find]

(* ****** ****** *)

#define l2l list_of_list_vt

(* ****** ****** *)

#define FRAMESIZE 256 // it is fixed for simplicity

extern fun interp1Exp (env: tmpmap, exp: $TR.exp): v1al
extern fun interp1Stmlst
  (s0tms: stmlst, env: &tmpmap, stms: stmlst): void

implement interp1Exp (env, exp) = let
  fn err {a:t@ype} (exp: $TR.exp): a = begin
    prerr "INTERNAL ERROR";
    prerr ": interp1Exp: exp = "; $TR.prerr_exp exp;
    prerr_newline ();
    exit {a} (1)
  end // end of [interp1Exp]
(*
  val () = begin
    prerr "interp1Exp: exp = "; $TR.prerr_exp exp; prerr_newline ()
  end // end of [val]
*)
in
  case+ exp of
  | $TR.EXPconst int => V1ALint int
  | $TR.EXPname lab => V1ALlab lab
  | $TR.EXPtemp tmp => tmpmap_search (env, tmp)
  | $TR.EXPbinop (oper, e1, e2) => let
      val- V1ALint i1 = interp1Exp (env, e1)
      val- V1ALint i2 = interp1Exp (env, e2)
    in
      case+ oper of
      | $TR.PLUS _ => V1ALint (i1 + i2)
      | $TR.MINUS _ => V1ALint (i1 - i2)
      | $TR.MUL _ => V1ALint (i1 * i2)
      | $TR.DIV _ => V1ALint (i1 / i2)
(*
      | _ => err {v1al} (exp)
*)
    end // end of [EXPbinop]
  | $TR.EXPmem e_ind => let
      val- V1ALint ind =
        interp1Exp (env, e_ind) in the_memory_get (ind / WSZ)
    end // end of [EXPmem]
  | $TR.EXPcall (e_fun, es_arg) => let
      val v_fun = interp1Exp (env, e_fun)
      val vs_arg_rev = loop (env, es_arg, list_nil) where {
        fun loop (
            env: tmpmap
          , es: $TR.explst
          , vs: List v1al
          ) : List v1al = case+ es of
          | list_cons (e, es) => let
              val v = interp1Exp (env, e) in
              loop (env, es, list_cons (v, vs))
            end // end of [list_cons]
          | list_nil () => vs
        // end of [loop]
      } // end of [val]
      val- V1ALlab lab = v_fun
      val v2al = the_labmap_search (lab)
    in
      case+ v2al of
      | V2ALcod (frm, stms) => let
          // push arguments onto the stack
          val () = loop (vs_arg_rev) where {
            fun loop (vs: List v1al): void = case+ vs of
              | list_cons (v, vs) => (the_stack_push v; loop vs)
              | list_nil () => ()
            // end of [loop]
          } // end of [val]
          var env_new = tmpmap_empty () // so no need for saving [env]!
          val () = loop (env_new, fars, vs_arg) where {
            val fars = $F.theFunargReglst
            val vs_arg = l2l (list_reverse vs_arg_rev)
            fun loop // passing some arguments in registers
              (env: &tmpmap, fars: List temp, vs: List v1al): void =
              case+ (fars, vs) of
              | (list_cons (far, fars), list_cons (v, vs)) => (
                  tmpmap_insert (env, far, v); loop (env, fars, vs)
                ) // end of [list_cons, list_cons]
              | (_, _) => ()
            // end of [loop]
          } // end of [val]
          // callee starts
          val i_sp = the_stackptr_get ()
          val ofs0 = $F.frame_argofs_get frm
          val () = tmpmap_insert (env_new, $F.FP, V1ALint (i_sp * WSZ - ofs0)) // FP update
          val () = the_stackptr_set (i_sp - FRAMESIZE)
          val () = interp1Stmlst (stms, env_new, stms)
          val () = the_stackptr_set (i_sp)
          // callee finishes
        in
          tmpmap_search (env_new, $F.RV) // fetch the return value
        end // end of [F1UNcod]
      | V2ALpre f_pre => let
          val vs_arg = l2l (list_reverse vs_arg_rev) in f_pre vs_arg
        end // end of [V2ALpre]
      | V2ALstr str => V1ALstr str
    end // end of [EXPcall]
  | _ => err (exp)
end // end of [interp1Exp]

implement interp1Stmlst (s0tms, env, stms) = let
  fn err {a:t@ype} (stm: $TR.stm): a = begin
    prerr "INTERNAL ERROR";
    prerr ": interp1Stmlst: stm = "; $TR.prerr_stm stm;
    prerr_newline ();
    exit {a} (1)
  end // end of [err]
(*
  val () = case+ stms of
    | list_cons (stm, _) => begin
        prerr "interp1Stmlst: stm = "; $TR.prerr_stm stm; prerr_newline ()
      end // end of [list_cons]
    | list_nil () => ()
  // end of [val]
*)
in
  case+ stms of
  | list_cons (stm, stms) => (case+ stm of
    | $TR.STMmove ($TR.EXPtemp tmp1, e2) => let
        val v2 = interp1Exp (env, e2); val () = tmpmap_insert (env, tmp1, v2)
      in
        interp1Stmlst (s0tms, env, stms)
      end // end of [$TR.STMmove]
    | $TR.STMmove ($TR.EXPmem e1_ind, e2) => let
        val- V1ALint ind1 = interp1Exp (env, e1_ind)
(*
        val () = begin
          prerr "interp1Stmlst: STMmove: ind1 = "; prerr_int ind1; prerr_newline ()
        end // end of [interp1Stmlst]
*)
        val v2 = interp1Exp (env, e2)
        val () = the_memory_set (ind1 / WSZ, v2) in interp1Stmlst (s0tms, env, stms)
      end // end of [val]
    | $TR.STMexp e => let
        val _(*v*) = interp1Exp (env, e) in interp1Stmlst (s0tms, env, stms)
      end // end of [STMexp]
    | $TR.STMjump (e, _) => let
        val- V1ALlab lab = interp1Exp (env, e)
        val stms_new = stmlst_label_find (s0tms, lab) in
        interp1Stmlst (s0tms, env, stms_new)
      end // end of [STMjump]
    | $TR.STMcjump (relop, e1, e2, tlab, flab) => let
        val- V1ALint i1 = interp1Exp (env, e1)
        val- V1ALint i2 = interp1Exp (env, e2)
        val test = (case+ relop of
          | $TR.EQ => (i1 = i2)
          | $TR.NEQ => (i1 <> i2)
          | $TR.LT => (i1 < i2)
          | $TR.LE => (i1 <= i2)
          | $TR.GT => (i1 > i2)
          | $TR.GE => (i1 >= i2)
(*
          | _ => err {bool} (stm)
*)
        ) : bool // end of [val]
      in
        if test then let
          val stms_new = stmlst_label_find (s0tms, tlab)
        in
          interp1Stmlst (s0tms, env, stms_new)
        end else begin
          interp1Stmlst (s0tms, env, stms) // it is a fall-through
        end // end of [if]
      end // end of [STMcjump]
    | $TR.STMlabel _ => interp1Stmlst (s0tms, env, stms)
    | _ => err (stm)
    ) // end of [list_cons]
  | list_nil () => ()
end // end of [interp1Stmlst]

(* ****** ****** *)

staload "interp1.sats"

implement the_labmap_string_insert
  (lab, str) = the_labmap_insert (lab, V2ALstr str)

implement the_labmap_frame_stmlst_insert
  (lab, frm, stms) = the_labmap_insert (lab, V2ALcod (frm, stms))

#define FRAMESIZE_TOP 1024

implement interp1Prog (stms) = let
// (*
  val () = begin
    prerr "WORDSIZE = "; prerr WSZ; prerr_newline ()
  end // end of [val]
// *)
  var env = tmpmap_empty ()
  val i_sp = the_stackptr_get ()
  val f_sp = i_sp * WSZ
  val () = the_stackptr_set (i_sp - FRAMESIZE_TOP)
  val () = tmpmap_insert (env, $F.FP, V1ALint f_sp) in
  interp1Stmlst (stms, env, stms)
end // end of [val]

(* ****** ****** *)

(* end of [interp1.dats] *)
