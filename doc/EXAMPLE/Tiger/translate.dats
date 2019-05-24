(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

staload TL = "templab.sats"

typedef label = $TL.label_t

staload TR = "irtree.sats"

(* ****** ****** *)

staload "translate.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

implement unEx (e1xp) = case+ e1xp of
  | Ex exp => exp
  | Nx stm => $TR.EXPeseq (stm, $TR.exp_const_0)
  | Cx fstm => let
      val res = $TL.temp_make_new ()
      val exp_res = $TR.EXPtemp res
      val tlab = $TL.label_make_new ()
      val flab = $TL.label_make_new ()
      val stm1 = $TR.STMmove (exp_res, $TR.exp_const_1)
      val stm2 = fstm (tlab, flab)
      val stm3 = $TR.STMlabel flab
      val stm4 = $TR.STMmove (exp_res, $TR.exp_const_0)
      val stm5 = $TR.STMlabel tlab
      macdef seq (x1, x2) = $TR.STMseq (,(x1), ,(x2))
      val stm = seq (stm1, seq (stm2, seq (stm3, seq (stm4, stm5))))
    in
      $TR.EXPeseq (stm, exp_res)
    end // end of [Cx]
// end of [unEx]

(* ****** ****** *)

implement unNx (e1xp) = case+ e1xp of
  | Nx stm => stm
  | Ex exp => $TR.STMexp exp
  | Cx fstm => let
      val lab = $TL.label_make_new () in
      $TR.STMseq (fstm (lab, lab), $TR.STMlabel lab)
    end // end of [Nx]
// end of [unNx]

(* ****** ****** *)

implement unCx (e1xp) = case+ e1xp of
  | Cx fstm => fstm
  | Ex exp => begin case+ exp of
    | $TR.EXPconst i when i = 0 =>
        lam (tlab, flab) => $TR.STMjump ($TR.EXPname flab, '[flab])
      // end of [EXPconst 0]
    | $TR.EXPconst i (* i <> 0 *) =>
        lam (tlab, flab) => $TR.STMjump ($TR.EXPname tlab, '[tlab])
      // end of [EXPconst _]
    | _ => lam (tlab, flab) => 
        $TR.STMcjump ($TR.NEQ, exp, $TR.exp_const_0, tlab, flab)
      // end of [_]
    end // end of [Ex]
  | Nx _ => begin
      prerr "exit(TIGER)";
      prerr ": INTERAL ERROR: unCx"; prerr_newline ();
      exit (1)
    end // end of [Nx]
// end of [unCx]

(* ****** ****** *)

implement fprint_e1xp (out, e1xp) = $TR.fprint_exp (out, unEx e1xp)
implement print_e1xp (e1xp) = fprint_e1xp (stdout_ref, e1xp)
implement prerr_e1xp (e1xp) = fprint_e1xp (stderr_ref, e1xp)

(* ****** ****** *)

staload S = "stamp.sats"
staload F = "frame.sats"

datatype level =
  | LEVELtop of $F.frame_t
  | LEVELsub of (
      $S.stamp_t, $F.frame_t, level (*parent*)
    ) // end of [SUB]

typedef levelopt = Option level

extern fun level_frame_get (lev: level): $F.frame_t

implement level_frame_get (lev) = case+ lev of
  | LEVELtop frm => frm | LEVELsub (_(*stamp*), frm, _(*parent*)) => frm
// end of [level_frame_get]

extern fun eq_level_level (l1: level, l2: level): bool
overload = with eq_level_level

implement eq_level_level (l1, l2) = case+ (l1, l2) of
  | (LEVELtop _, LEVELtop _) => true
  | (LEVELsub (stamp1, _, _), LEVELsub (stamp2, _, _)) =>
      if $S.eq_stamp_stamp (stamp1, stamp2) then true else false
    // end of [LEVELsub _, LEVELsub _]
  | (_, _) => false
// end of [eq_level_level]

(* ****** ****** *)

staload "types.sats"
staload "absyn.sats"

staload Sym = "symbol.sats"

local

staload M = "LIB/funmap_avltree.dats"

val _cmp = lam (x1: sym, x2: sym): Sgn
  =<cloref> $Sym.compare_symbol_symbol (x1, x2)
// end of [val]

in // in of [local]

datatype vfent =
  | VFENTfun of (label, level)
  | VFENTvar of (level, $F.access_t)

typedef env = $M.map_t (sym, vfent)

extern fun env_empty (): env
implement env_empty () = $M.funmap_empty<> ()

extern fun env_insert
  (env: env, sym: sym, ent: vfent): env
implement env_insert (env, sym, ent) =
  $M.funmap_insert<sym,vfent> (env, sym, ent, _cmp)
// end of [tymap_insert]

extern fun env_search (env: env, sym: sym): vfent
implement env_search (env, sym) = let
  val ans = $M.funmap_search<sym,vfent> (env, sym, _cmp)
in
  case+ ans of
  | ~Some_vt ent => ent | ~None_vt () => begin
      prerr "INTERNAL ERROR";
      prerr ": env_search: unrecognized symbol [";
      $Sym.prerr_symbol sym;
      prerr "]";
      prerr_newline ();
      exit {vfent} (1)
    end // end of [None_vt]
  // end of [case]
end // end of [env_search]

end // end of [local]
  
(* ****** ****** *)

fun frame_stalnk_get (f) = let
  val xs = $F.frame_arglst_get (f)
in
  case+ xs of
  | list_cons _ => list_last (xs)
  | list_nil () => begin
      prerr "INTERNAL ERROR";
      prerr ": frame_stalnk_get: arglst is empty";
      prerr_newline ();
      exit (1)
    end // end of [list_nil]
  // end of [case]
end // end of [frame_stalnk_get]

fn frame_baseptr_compute
  (lev0: level, lev: level): $TR.exp = let
(*
  val frm0 = level_frame_get lev0
  val lab0 = $F.frame_name_get (frm0)
  val () = begin
    prerr "frame_baseptr_compute: lab0 = "; $TL.prerr_label lab0; prerr_newline ()
  end // end of [val]
  val frm = level_frame_get lev
  val lab = $F.frame_name_get (frm)
  val () = begin
    prerr "frame_baseptr_compute: lab = "; $TL.prerr_label lab; prerr_newline ()
  end // end of [val]
*)
  fun loop (
      lev0: level, lev: level, e_fp: $TR.exp
    ) : $TR.exp =
    if lev0 = lev then e_fp else begin case+ lev of
      | LEVELsub (_, frm, lev_p) => let
          val stalnk = frame_stalnk_get (frm)
          val e_fp = $F.exp_make_access (e_fp, stalnk)
        in
          loop (lev0, lev_p, e_fp)
        end // end of [LEVELsub]
      | LEVELtop _ => begin
          prerr "INTERNAL ERROR: stalnk_compute: lev = LEVELtop";
          prerr_newline ();
          exit (1)
        end // end of [LEVELtop]
    end // end of [if]
  // end of [loop]
in
  loop (lev0, lev, $F.exp_FP)
end // end of [stalnk_compute]

fn exp_make_level_access
  (lev0: level, lev: level, acc: $F.access_t): $TR.exp = let
  val e_fp = frame_baseptr_compute (lev0, lev)
in
  $F.exp_make_access (e_fp, acc)
end // end of [exp_make_access]

(* ****** ****** *)

extern fun transVar1 (lev: level, env: env, x: v1ar): e1xp
extern fun transExp1 (lev: level, env: env, e: exp): e1xp

typedef stmlst = List ($TR.stm)
extern fun transDec1 (lev: level, env: &env, d: dec, stms: &stmlst): void

(* ****** ****** *)

#define :: list_cons
overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

implement transVar1 (lev0, env, x0) = let
(*
  val () = begin
    prerr "transVar1: x0 = "; prerr_v1ar x0; prerr_newline ()
  end // end of [val]
*)
in
  case+ x0.v1ar_node of
  | SimpleVar sym => Ex (te) where {
(*
      val () = begin
        prerr "transVar1: SimpleVar: sym = ";
        $Sym.prerr_symbol sym; prerr_newline ()
      end // end of [val]
*)
      val ent = env_search (env, sym)
      val te = (case+ ent of
        | VFENTvar (fp_lev, acc) => exp_make_level_access (fp_lev, lev0, acc)
        | _ => begin
            prerr "INTERNAL ERROR";
            prerr ": tranVar1: unrecognized symbol [";
            $Sym.prerr_symbol sym;
            prerr "]";
            prerr_newline ();
            exit (1)
          end // end of [val]
      ) : $TR.exp
    } // end of [SimpleVar]
  | FieldVar (x_rec, lab) => let
      val e_rec = transVar1 (lev0, env, x_rec)
      val ofs = loop (lts, lab, 0(*ofs*)) where {
        val lts = (case+ x_rec.v1ar_ty of
          | TYrec (_(*stamp*), lts) => lts | _ => begin
              prerr "INTERNAL ERROR";
              prerr ": transVar1: FieldVar: not a record type";
              prerr_newline ();
              exit {labtylst} (1)
            end // end of [_]
        ) : labtylst // end of [val]
        fun loop (lts: labtylst, lab: sym, ofs: int): int =
          case+ lts of
          | LABTYLSTcons (lab1, _(*ty*), lts) => begin
              if lab = lab1 then ofs else loop (lts, lab, ofs + $F.WORDSIZE)
            end // end of [LABTYLSTcons]
          | LABTYLSTnil () => ofs
        // end of [loop]
      } // end of [val]
      val te_rec = unEx e_rec
      val te_addr = $TR.EXPbinop ($TR.PLUS, te_rec, $TR.EXPconst ofs)
    in
      Ex ($TR.EXPmem te_addr)
    end // end of [FieldVar]
  | SubscriptVar (x_arr, e_ind) => let
      val e_arr = transVar1 (lev0, env, x_arr)
      val e_ind = transExp1 (lev0, env, e_ind)
      val te_arr = unEx e_arr
      val te_ind = unEx e_ind
      val te_ofs = $TR.EXPbinop ($TR.MUL, te_ind, $TR.EXPconst $F.WORDSIZE)
      val te_addr = $TR.EXPbinop ($TR.PLUS, te_arr, te_ofs)
    in
      Ex ($TR.EXPmem te_addr)
    end // end of [SubscriptVar]
end // end of [transVar1]

(* ****** ****** *)

fn transExp1_SeqExp
  (lev0: level, env: env, es: explst): e1xp = seq0 (es) where {
  fun seq0 (es: explst)
    :<cloref1> e1xp = case+ es of
    | list_cons (e, es) => seq1 (e, es)
    | list_nil () => Ex ($TR.EXPconst 0)
  // end of [seq0]
  and seq1 (e0: exp, es: explst)
    :<cloref1> e1xp = begin case+ es of
    | list_cons (e1, es) => Ex (seq2 (e0, e1, es))
    | list_nil () => transExp1 (lev0, env, e0)
  end // end of [seq1]
  and seq2 (e0: exp, e1: exp, es: explst)
    :<cloref1> $TR.exp = begin case+ es of
    | list_cons (e2, es) => let
        val e0 = transExp1 (lev0, env, e0) in
        $TR.EXPeseq (unNx e0, seq2 (e1, e2, es))
      end // end of [list_cons]
    | list_nil () => let
        val e0 = transExp1 (lev0, env, e0)
        val e1 = transExp1 (lev0, env, e1) in $TR.EXPeseq (unNx e0, unEx e1)
      end // end of [list_nil]
   end // end of [seq2]
} // end of [SeqExp]

(* ****** ****** *)

fun seq_stm_stmlst_rev
  (stm0: $TR.stm, stms: stmlst): $TR.stm = case+ stms of
  | list_cons (stm1, stms) =>
      seq_stm_stmlst_rev ($TR.STMseq (stm1, stm0), stms)
  | list_nil () => stm0
// end of [seq_stm_stmlst_rev]

fn eseq_stmlst_rev_exp (stms: stmlst, exp: $TR.exp): $TR.exp = begin
  case+ stms of
  | list_cons (stm, stms) => let
      val stm = seq_stm_stmlst_rev (stm, stms) in $TR.EXPeseq (stm, exp)
    end // end of [list_cons]
  | list_nil () => exp
end // end of [eseq_stmlst_rev_exp]

(* ****** ****** *)

local

viewtypedef lablst_vt = List_vt (label)

val theBreaklabLst = ref_make_elt<lablst_vt> (list_vt_nil)
val theContinuelabLst = ref_make_elt<lablst_vt> (list_vt_nil)

in // in of [local]

fn theBreaklabLst_push (lab: label): void = let
  val (pfbox | p) = ref_get_view_ptr (theBreaklabLst)
  prval vbox pf = pfbox
in
  !p := list_vt_cons (lab, !p)
end // end of [theBreaklabLst]

fn theBreaklabLst_pop (): void = let
  val (pfbox | p) = ref_get_view_ptr (theBreaklabLst)
  prval vbox pf = pfbox
in
  case+ !p of
  | ~list_vt_cons (_, xs) => (!p := xs ) | _ => ()
end // end of [theBreaklabLst]

fn loop_breaklab_get (): label = let
  val (pfbox | p) = ref_get_view_ptr (theBreaklabLst)
  prval vbox pf = pfbox
in
  case+ !p of
  | list_vt_cons (x, _) => let val x = x in fold@ !p; x end
  | _ => $effmask_all begin
      prerr "INTERNAL ERROR";
      prerr ": loop_breaklab_get: [theBreaklabLst] is empty";
      prerr_newline ();
      exit {label} (1)
    end // end of [val]
end // end of [loop_breaklab_get]

//

fn theContinuelabLst_push (lab: label): void = let
  val (pfbox | p) = ref_get_view_ptr (theContinuelabLst)
  prval vbox pf = pfbox
in
  !p := list_vt_cons (lab, !p)
end // end of [theBreaklabLst]

fn theContinuelabLst_pop (): void = let
  val (pfbox | p) = ref_get_view_ptr (theContinuelabLst)
  prval vbox pf = pfbox
in
  case+ !p of ~list_vt_cons (_, xs) => (!p := xs ) | _ => ()
end // end of [theContinuelabLst]

fn loop_continuelab_get (): label = let
  val (pfbox | p) = ref_get_view_ptr (theContinuelabLst)
  prval vbox pf = pfbox
in
  case+ !p of
  | list_vt_cons (x, _) => let val x = x in fold@ !p; x end
  | _ => $effmask_all begin
      prerr "INTERNAL ERROR";
      prerr ": loop_continuelab_get: [theContinuelabLst] is empty";
      prerr_newline ();
      exit {label} (1)
    end // end of [val]
end // end of [loop_continuelab_get]

end // end of [local]

(* ****** ****** *)

fn expbinop_plus_make
  (e1: $TR.exp, e2: $TR.exp): $TR.exp =
  case+ e1 of
  | $TR.EXPconst i1 => begin case+ e2 of
      | $TR.EXPconst i2 => $TR.EXPconst (i1 + i2)
      | _ => $TR.EXPbinop ($TR.PLUS, e2, e1)
    end // end of [EXPconst]
  | _ => $TR.EXPbinop ($TR.PLUS, e1, e2)
// end of [expbinop_plus_make]

fn expbinop_minus_make
  (e1: $TR.exp, e2: $TR.exp): $TR.exp =
  case+ e1 of
  | $TR.EXPconst i1 => begin case+ e2 of
      | $TR.EXPconst i2 => $TR.EXPconst (i1 - i2)
      | _ => $TR.EXPbinop ($TR.MINUS, e1, e2)
    end // end of [EXPconst]
  | _ => $TR.EXPbinop ($TR.MINUS, e1, e2)
// end of [expbinop_minus_make]

(* ****** ****** *)

implement transExp1 (lev0, env, e0) = let
(*
  val () = begin
    prerr "transExp1: e0 = "; prerr_exp (e0); prerr_newline ()
  end // end of [val]
*)
in
  case+ e0.exp_node of
  | VarExp x => transVar1 (lev0, env, x)
  | NilExp _ => Ex ($TR.EXPconst 0)
  | IntExp int => Ex ($TR.EXPconst int)
  | StringExp str => let
      val lab = $TL.label_make_str_new ()
      val frag = $F.FRAGstring (lab, str)
      val () = $F.frame_theFraglst_add (frag)
    in
      Ex ($TR.EXPname lab)
    end // end of [StringExp]
  | CallExp (f(*sym*), es_arg) =>  Ex (te_call) where {
(*
      val () = begin
        prerr "transExp1: CallExp: f = "; $Sym.prerr_symbol f; prerr_newline ()
      end // end of [val]
*)
      val ent = env_search (env, f)
      val (f_lab, f_lev) = (case+ ent of
        | VFENTfun (lab, lev) => @(lab, lev) | _ => begin
            prerr "INTERNAL ERROR";
            prerr ": transExp1: CallExp: illegal function entry: f = ";
            $Sym.prerr_symbol f;
            prerr_newline ();
            exit {(label, level)} (1)
          end // end of [_]
      ) : (label, level)
      val ofp_lev = (case+ f_lev of
        | LEVELtop _ => None | LEVELsub (_, _, lev) => Some lev
      ) : levelopt // end of [val]
      val te_fun = $TR.EXPname (f_lab)
      val tes_arg = loop (es_arg) where {
        fun loop (es: explst):<cloref1> $TR.explst = case+ es of
          | list_cons (e, es) => let
              val e = transExp1 (lev0, env, e) in unEx e :: loop es
            end // end of [list_cons]
          | list_nil () => begin case+ ofp_lev of
            | Some fp_lev => let
                val te_fp = frame_baseptr_compute (fp_lev, lev0)
              in
                list_cons (te_fp, list_nil ()) // a static link is passed
              end // end of [Some]
            | None () => list_nil () // there is no static link to be passed
            end // end of [list_nil]
        // end of [loop]
      } // end of [val]
      val te_call = $TR.EXPcall (te_fun, tes_arg)
    } // end of [CallExp]
  | OpExp (a1, oper, a2) => let
      val e1 = transExp1 (lev0, env, a1)
      val e2 = transExp1 (lev0, env, a2)
    in
      case+ oper of
      | PlusOp _ =>
          Ex (expbinop_plus_make (unEx e1, unEx e2))
      | MinusOp _ =>
          Ex (expbinop_minus_make (unEx e1, unEx e2))
      | TimesOp _ =>
          Ex ($TR.EXPbinop ($TR.MUL, unEx e1, unEx e2))
      | DivideOp _ =>
          Ex ($TR.EXPbinop ($TR.DIV, unEx e1, unEx e2))
      | EqOp _ => let
          val ty1 = a1.exp_ty
          val te1 = unEx e1 and te2 = unEx e2 in
          case+ ty1 of
          | TYbase name when name = $Sym.symbol_INT => Cx  (
              lam (tl, fl) => $TR.STMcjump ($TR.EQ, te1, te2, tl, fl)
            ) // end of [TYbase INT]
          | TYbase name when name = $Sym.symbol_STRING => let
              val te_fun = $TR.EXPname $TL.tiger_eq_string_string
            in
              Ex ($TR.EXPcall (te_fun, '[te1, te2]))
            end // end of [TYbase STRING]
          | _ => Cx  ( // handling records
              lam (tl, fl) => $TR.STMcjump ($TR.EQ, te1, te2, tl, fl)
            ) // end of [_]
        end // end of [EqOp]
      | NeqOp _ => let
          val ty1 = a1.exp_ty
          val te1 = unEx e1 and te2 = unEx e2 in
          case+ ty1 of
          | TYbase name when name = $Sym.symbol_INT => Cx  (
              lam (tl, fl) => $TR.STMcjump ($TR.NEQ, te1, te2, tl, fl)
            ) // end of [TYbase INT]
          | TYbase name when name = $Sym.symbol_STRING => let
              val te_fun = $TR.EXPname $TL.tiger_neq_string_string
            in
              Ex ($TR.EXPcall (te_fun, '[te1, te2]))
            end // end of [TYbase STRING]
          | _ => Cx  ( // handling records
              lam (tl, fl) => $TR.STMcjump ($TR.NEQ, te1, te2, tl, fl)
            ) // end of [_]
        end // end of [NeqOp]
      | GtOp _ => let
          val te1 = unEx e1 and te2 = unEx e2 in
          Cx  (lam (tl, fl) => $TR.STMcjump ($TR.GT, te1, te2, tl, fl))
        end // end of [GtOp]
      | GeOp _ => let
          val te1 = unEx e1 and te2 = unEx e2 in
          Cx  (lam (tl, fl) => $TR.STMcjump ($TR.GE, te1, te2, tl, fl))
        end // end of [GeOp]
      | LtOp _ => let
          val te1 = unEx e1 and te2 = unEx e2 in
          Cx  (lam (tl, fl) => $TR.STMcjump ($TR.LT, te1, te2, tl, fl))
        end // end of [LtOp]
      | LeOp _ => let
          val te1 = unEx e1 and te2 = unEx e2 in
          Cx  (lam (tl, fl) => $TR.STMcjump ($TR.LE, te1, te2, tl, fl))
        end // end of [LeOp]
      | AndOp _ => let
          val lab = $TL.label_make_new ()
          val fstm1 = unCx e1 and fstm2 = unCx e2
          val stm_lab = $TR.STMlabel lab
        in
          Cx (lam (tl, fl) => 
                $TR.STMseq (fstm1 (lab, fl), $TR.STMseq (stm_lab, fstm2 (tl, fl)))
          ) // end of [Cx]
        end // end of [AndOp]
      | OrOp _ => let
          val lab = $TL.label_make_new ()
          val fstm1 = unCx e1 and fstm2 = unCx e2
          val stm_lab = $TR.STMlabel lab
        in
          Cx (lam (tl, fl) => 
                $TR.STMseq (fstm1 (tl, lab), $TR.STMseq (stm_lab, fstm2 (tl, fl)))
          ) // end of [Cx]
        end // end of [OrOp]
    end // end of [OpExp]
  | RecordExp (fes, _(*typ*)) => let
      val n = list_length (fes)
      val te_size = $TR.EXPconst (n)
      val tmp = $TL.temp_make_new ()
      val te_tmp = $TR.EXPtemp (tmp)
      val te_alloc = $TR.EXPname $TL.tiger_array_alloc
      val te_arrptr = $TR.EXPcall (te_alloc, '[te_size])
      val stm0 = $TR.STMmove (te_tmp, te_arrptr)
      fun aux (fes: fieldexplst, ofs: int, stms: stmlst):<cloref1> stmlst =
        case+ fes of
        | list_cons (fe, fes) => let
            val e = transExp1 (lev0, env, fe.fieldexp_exp)
            val te_addr = $TR.EXPbinop ($TR.PLUS, te_tmp, $TR.EXPconst ofs)
            val stm = $TR.STMmove ($TR.EXPmem te_addr, unEx e)
          in
            aux (fes, ofs + $F.WORDSIZE, list_cons (stm, stms))
          end // end of [list_cons]
        | list_nil () => stms
      // end of [aux]
      val stms = aux (fes, 0(*ofs*), list_nil ())
      val stm = case+ stms of
        | list_cons (stm, stms) =>
            $TR.STMseq (stm0, seq_stm_stmlst_rev (stm, stms))
        | list_nil () => stm0
      // end of [stm]
    in
      Ex ($TR.EXPeseq (stm, te_tmp))
    end // end of [RecordExp]
  | SeqExp (es) => transExp1_SeqExp (lev0, env, es)
  | AssignExp (x1, e2) => let
      val e1 = transVar1 (lev0, env, x1)
      val e2 = transExp1 (lev0, env, e2)
    in
      Nx ($TR.STMmove (unEx e1, unEx e2))
    end // end of [AssignExp]
  | IfExp (e1, e2, oe3) => let
      macdef seq (x1, x2) = $TR.STMseq (,(x1), ,(x2))
      val tlab = $TL.label_make_new ()
      val flab = $TL.label_make_new ()
      val e1 = transExp1 (lev0, env, e1)
      val fstm = unCx e1
      val stm1 = fstm (tlab, flab)
    in
      case+ oe3 of
      | Some e3 => let
          val tmp = $TL.temp_make_new ()
          val te_tmp = $TR.EXPtemp (tmp)
          val lab = $TL.label_make_new ()
          val te_lab = $TR.EXPname lab
          val stm2 = $TR.STMlabel (tlab)
          val e2 = transExp1 (lev0, env, e2)
          val stm3 = $TR.STMmove (te_tmp, unEx e2)
          val stm4 = $TR.STMjump (te_lab, '[lab])
          val stm5 = $TR.STMlabel (flab)
          val e3 = transExp1 (lev0, env, e3)
          val stm6 = $TR.STMmove (te_tmp, unEx e3)
          val stm7 = $TR.STMlabel (lab)
          val stm = seq (
            stm1, seq (stm2, seq (stm3, seq (stm4, seq (stm5, seq (stm6, stm7)))))
          ) // end of [val]
        in
          Ex ($TR.EXPeseq (stm, te_tmp))
        end // end of [Some]
      | None () => let
          val stm2 = $TR.STMlabel (tlab)
          val e2 = transExp1 (lev0, env, e2)
          val stm3 = unNx e2
          val stm4 = $TR.STMlabel (flab)
        in
          Nx (seq (stm1, seq (stm2, seq (stm3, stm4))))
        end // end of [None]
    end (* end of [IfExp] *)
  | WhileExp (e_test, e_body) => let
      macdef seq (x1, x2) = $TR.STMseq (,(x1), ,(x2))
      val lab_test = $TL.label_make_new ()
      val lab_loop = $TL.label_make_new ()
      val lab_done = $TL.label_make_new ()
      val () = theBreaklabLst_push (lab_done)
      val () = theContinuelabLst_push (lab_test)
      val e_test = transExp1 (lev0, env, e_test)
      val fstm = unCx (e_test)
      val e_body = transExp1 (lev0, env, e_body)
      val stm1 = $TR.STMlabel lab_test
      val stm2 = fstm (lab_loop, lab_done)
      val stm3 = $TR.STMlabel lab_loop
      val stm4 = unNx (e_body)
      val stm5 = $TR.STMjump ($TR.EXPname lab_test, '[lab_test])
      val stm6 = $TR.STMlabel lab_done
      val stm = seq (
        stm1, seq (stm2, seq (stm3, seq (stm4, seq (stm5, stm6))))
      ) // end of [seq]
      val () = theBreaklabLst_pop () and () = theContinuelabLst_pop ()
    in
      Nx stm
    end // end of [WhileExp]
  | ForExp (ind, isEscaped, e_lo, e_hi, e_body) => let
      macdef seq (x1, x2) = $TR.STMseq (,(x1), ,(x2))
      val e_lo = transExp1 (lev0, env, e_lo)
      val te_lo = unEx e_lo
      val e_hi = transExp1 (lev0, env, e_hi)
      val te_hi = unEx e_hi
      val frm0 = level_frame_get (lev0)
      val acc_ind = $F.frame_alloc_local (frm0, !isEscaped)
      val env = env_insert (env, ind, VFENTvar (lev0, acc_ind))
      val te_ind = exp_make_level_access (lev0, lev0, acc_ind)
      val stm11 = $TR.STMmove (te_ind, te_lo)
      val tmp_lmt = $TL.temp_make_new ()
      val te_lmt = $TR.EXPtemp (tmp_lmt)
      val stm12 = $TR.STMmove (te_lmt, te_hi)
      val stm1 = $TR.STMseq (stm11, stm12)
      val lab_loop = $TL.label_make_new ()
      val lab_test = $TL.label_make_new ()
      val lab_incr = $TL.label_make_new ()
      val lab_done = $TL.label_make_new ()
      val () = theBreaklabLst_push (lab_done)
      val () = theContinuelabLst_push (lab_test)      
      val stm2 = $TR.STMcjump ($TR.LE, te_ind, te_lmt, lab_loop, lab_done)
      val stm3 = $TR.STMlabel lab_loop
      val e_body = transExp1 (lev0, env, e_body)
      val stm4 = unNx (e_body)
      val stm51 = $TR.STMlabel lab_test
      val stm52 = $TR.STMcjump ($TR.LT, te_ind, te_lmt, lab_incr, lab_done)
      val stm5 = $TR.STMseq (stm51, stm52)
      val stm61 = $TR.STMlabel lab_incr
      val te_ind1 = $TR.EXPbinop ($TR.PLUS, te_ind, $TR.exp_const_1)
      val stm62 = $TR.STMmove (te_ind, te_ind1)
      val stm6 = $TR.STMseq (stm61, stm62)
      val stm7 = $TR.STMjump ($TR.EXPname lab_loop, '[lab_loop])
      val stm8 = $TR.STMlabel (lab_done)
      val stm = seq (
        stm1, seq (stm2, seq (stm3, seq (stm4, seq (stm5, seq (stm6, seq (stm7, stm8))))))
      ) // end of [val]
      val () = theBreaklabLst_pop () and () = theContinuelabLst_pop ()
    in
      Nx (stm)
    end // end of [ForExp]
  | BreakExp () => let
      val blab = loop_breaklab_get ()
    in
      Nx ($TR.STMjump ($TR.EXPname blab, '[blab]))
    end // end of [BreakExp]
  | ContinueExp () => let
      val clab = loop_continuelab_get ()
    in
      Nx ($TR.STMjump ($TR.EXPname clab, '[clab]))
    end // end of [BreakExp]
  | LetExp (ds, e_body) => let
      var env_r: env = env
      var stms: stmlst = list_nil ()
      val () = loop (lev0, env_r, ds, stms) where {
        fun loop (
            lev0: level, env_r: &env, ds: declst, stms: &stmlst
          ) : void = case+ ds of
          | list_cons (d, ds) => let
              val () = transDec1
                (lev0, env_r, d, stms) in
              loop (lev0, env_r, ds, stms)
            end // end of [list_cons]
          | list_nil () => ()
        // end of [loop]
      } // end of [val]
      val e_body = transExp1 (lev0, env_r, e_body)
    in
      Ex (eseq_stmlst_rev_exp (stms, unEx e_body))
    end // end of [LetExp]
  | ArrayExp (_(*typ*), e_size, e_init) => let
      val e_size = transExp1 (lev0, env, e_size)
      val e_init = transExp1 (lev0, env, e_init)
      val arg1 = unEx e_size; val arg2 = unEx e_init
    in
      Ex ($TR.EXPcall ($TR.EXPname $TL.tiger_array_make_elt, '[arg1, arg2]))
    end // end of [ArrayExp]
end // end of [transExp1]

(* ****** ****** *)

fn funarglst_move
  (accs: $F.accesslst, ofs0: int): $TR.stm = let
  viewtypedef res_vt = List_vt ($TR.stm)
  fun loop1 (
      fars: $TL.templst
    , accs: $F.accesslst
    , ofs: int
    , res: &res_vt
    ) : void =
    case+ accs of
    | list_cons (acc, accs) => begin case+ fars of
      | list_cons (far, fars) => let
          val e_fp = $TR.EXPtemp $F.FP
          val e_acc = $F.exp_make_access (e_fp, acc)
          val e_far = $TR.EXPtemp far
          val () = res := list_vt_cons ($TR.STMmove (e_acc, e_far), res)
        in
          loop1 (fars, accs, ofs + $F.WORDSIZE, res)
        end // end of [list_cons]
      | list_nil () => loop2 (acc, accs, ofs, res) // the rest of the
        // arguments are passed in the stack frame
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop1]

  and loop2 (
      acc: $F.access_t
    , accs: $F.accesslst
    , ofs: int
    , res: &res_vt
    ) : void = let
    val () = if $F.access_is_inreg acc then let
      val e_fp = $TR.EXPtemp $F.FP
      val e_acc = $F.exp_make_access (e_fp, acc)
      val e_far = 
        $TR.EXPmem ($TR.EXPbinop ($TR.PLUS, e_fp, $TR.EXPconst ofs))
      val () = res := list_vt_cons ($TR.STMmove (e_acc, e_far), res)
    in
      // empty
    end else begin
      // [acc] is allocated in the stack frame and no move is needed
    end // end of [if]
  in
    case+ accs of
    | list_cons (acc, accs) => loop2 (acc, accs, ofs + $F.WORDSIZE, res)
    | list_nil () => ()
  end // end of [loop2]

  var res: res_vt = list_vt_nil ()
  val () = loop1 ($F.theFunargReglst, accs, ofs0, res)
in
  case+ res of
    | ~list_vt_cons (stm, stms) => loop (stms, stm) where {
        fun loop (stms: List_vt ($TR.stm), stm: $TR.stm): $TR.stm =
          case+ stms of
          | ~list_vt_cons (stm1, stms1) => loop (stms1, $TR.STMseq (stm1, stm))
          | ~list_vt_nil () => stm
        // end of [loop]
      }
    | ~list_vt_nil () => $TR.stm_nop
  // end of [val]  
end // end of [funarglst_move]

(* ****** ****** *)

fn calleesaved_save ()
  : @($TR.stm, $TL.templst_vt) = let
  fun aux (tmps: $TL.templst): @($TR.stm, $TL.templst_vt) =
    case+ tmps of
    | list_cons (tmp, tmps) => let
        val tmp_new = $TL.temp_make_new ()
        val stm = $TR.STMmove ($TR.EXPtemp tmp_new, $TR.EXPtemp tmp)
        val res = aux (tmps)
      in
        ($TR.STMseq (stm, res.0), list_vt_cons (tmp_new, res.1))
      end // end of [list_cons]
    | list_nil () => @($TR.stm_nop, list_vt_nil)
  // end of [aux]
in
  aux ($F.theCalleesavedReglst)
end // end of [calleesave_save]

fn calleesaved_restore
  (tmps_new: $TL.templst_vt): $TR.stm = let
  fun aux
    (tmps_new: $TL.templst_vt, tmps: $TL.templst): $TR.stm =
    case+ tmps_new of
    | ~list_vt_cons (tmp_new, tmps_new) => begin case+ tmps of
      | list_cons (tmp, tmps) => let
          val stm_fst = $TR.STMmove ($TR.EXPtemp tmp, $TR.EXPtemp tmp_new)
          val stm_rst = aux (tmps_new, tmps)
        in
          $TR.STMseq (stm_fst, stm_rst)
        end // end of [list_cons]
      | list_nil () => aux (tmps_new, tmps)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => $TR.stm_nop
  // end of [aux]
in
  aux (tmps_new, $F.theCalleesavedReglst)
end // end of [calleesaved_restore]

(* ****** ****** *)

fn transFundec1_fst
  (lev0: level, env: &env, fd: fundec): level = let
(*
  val () = begin
    prerr "transFundec1: fd_name = ";
    $Sym.prerr_symbol fd.fundec_name; prerr_newline ()
  end // end of [val]
*)
  val lab_frm = $TL.label_make_fun_new (fd.fundec_name)
  val arglst = fd.fundec_arglst
  val esclst = aux (arglst) where {
    fun aux (fts: fieldtyplst): List bool = case+ fts of
      | list_cons (ft, fts) => let
          val rb = ft.fieldtyp_escape in list_cons (!rb, aux fts)
        end // end of [list_cons]
      | list_nil () => list_nil ()
    // end of [aux]
  } // end of [val]
  val esclst = list_extend (esclst, true(*stalnk*))
  val esclst = list_of_list_vt (esclst)
  var ofs0: int = 0
#if MARCH  = "x86_32"
  val () = ofs0 := ofs0 + $F.WORDSIZE // [call] pushes EIP onto the stack
#endif
//
  val () = ofs0 := ofs0 + $F.WORDSIZE // [FP] is to be pushed onto the stack
//
  val frm = $F.frame_make_new (lab_frm, ofs0, esclst)
  val acclst = $F.frame_arglst_get (frm)
  val stamp = $S.stamp_make ()
  val lev1 = LEVELsub (stamp, frm, lev0)
  val () = env :=
    env_insert (env, fd.fundec_name, VFENTfun (lab_frm, lev1))
in
  lev1
end // end of [transFundec1_fst]

fn transFundec1_snd
  (env: env, fd: fundec, lev1: level): void = let
  val arglst = fd.fundec_arglst
  val frm = level_frame_get (lev1)
  val argofs = $F.frame_argofs_get (frm)
  val acclst = $F.frame_arglst_get (frm)
  val env = loop (lev1, env, arglst, acclst) where {
    fun loop (
        lev1: level
      , env: env
      , fts: fieldtyplst
      , accs: $F.accesslst
      ) : env = begin case+ (fts, accs) of
      | (list_cons (ft, fts), list_cons (acc, accs)) => let
          val ent = VFENTvar (lev1, acc)
          val env = env_insert
            (env, ft.fieldtyp_lab, ent) in loop (lev1, env, fts, accs)
        end // end of [list_cons, list_cons]
      | (_, _) => env
    end // end of [loop]
  } // end of [env]
  val res_calleesaved_save = calleesaved_save ()
  val stm_save = res_calleesaved_save.0
  val stm_restore = calleesaved_restore (res_calleesaved_save.1)
  // there is no point in saving calleesaved into callersaved
  val stm_usedef = $TR.STMusedef ('[], $F.theCallersavedReglst)
  val stm_argmov = funarglst_move (acclst, argofs)
  val e_body = transExp1 (lev1, env, fd.fundec_body)
  val stm = $TR.STMmove ($F.exp_RV, unEx e_body)
  val stm = $TR.STMseq (stm, stm_restore)
  val stm = $TR.STMseq (stm_argmov, stm)
  val stm = $TR.STMseq (stm_usedef, stm)
  val stm = $TR.STMseq (stm_save, stm)
in
  $F.frame_theFraglst_add ($F.FRAGproc (frm, stm))
end // end of [transFundec1_snd]

(* ****** ****** *)

implement transDec1 (lev0, env, d0, stms) = let
(*
  val () = begin
    prerr "transDec1: e0 = "; prerr_dec (d); prerr_newline ()
  end // end of [val]
*)
in
  case+ d0.dec_node of
  | VarDec (sym, isEscaped, _(*typopt*), e_init) => let
      val e_init = transExp1 (lev0, env, e_init)
      val frm0 = level_frame_get (lev0)
      val acc = $F.frame_alloc_local (frm0, !isEscaped)
      val env_new = env_insert (env, sym, VFENTvar (lev0, acc))
      val te = exp_make_level_access (lev0, lev0, acc)
      val stm = $TR.STMmove (te, unEx e_init)
      val () = stms := list_cons (stm, stms)
    in
      env := env_new
    end // end of [VarDec]
  | FunctionDec fds => aux2 (env, fds, levs) where {
      // extending the environment
      fun aux1 (lev0: level, env: &env, fds: fundeclst): List level =
        case+ fds of
        | list_cons (fd, fds) => let
            val lev1 = transFundec1_fst (lev0, env, fd)
            val levs = aux1 (lev0, env, fds) in list_cons (lev1, levs)
          end // end of [list_cons]
        | list_nil () => list_nil ()
      // end of [aux1]
      val levs = aux1 (lev0, env, fds)
      // compiling the definition
      fun aux2 (env: env, fds: fundeclst, levs: List level): void =
        case+ fds of
        | list_cons (fd, fds) => let
            val- list_cons (lev1, levs) = levs
            val () = transFundec1_snd (env, fd, lev1) in
            aux2 (env, fds, levs)
          end // end of [list_cons]
        | list_nil () => ()
      // end of [loop]
    } // end of [FunctionDec]
  | TypeDec _ => () // ignore type declarations
end // end of [transDec]

(* ****** ****** *)

implement transProg1 (e_prog) = let
  val frm0 = $F.theTopFrame
  val lev0 = LEVELtop frm0 and env = env_empty ()

  val ent = VFENTfun ($TL.tiger_chr, lev0)
  val env = env_insert (env, $Sym.symbol_CHR, ent)

  val ent = VFENTfun ($TL.tiger_flush, lev0)
  val env = env_insert (env, $Sym.symbol_FLUSH, ent)

  val ent = VFENTfun ($TL.tiger_getchar, lev0)
  val env = env_insert (env, $Sym.symbol_GETCHAR, ent)

  val ent = VFENTfun ($TL.tiger_ord, lev0)
  val env = env_insert (env, $Sym.symbol_ORD, ent)

  val ent = VFENTfun ($TL.tiger_print, lev0)
  val env = env_insert (env, $Sym.symbol_PRINT, ent)

  val ent = VFENTfun ($TL.tiger_print_int, lev0)
  val env = env_insert (env, $Sym.symbol_PRINT_INT, ent)

  val ent = VFENTfun ($TL.tiger_size, lev0)
  val env = env_insert (env, $Sym.symbol_SIZE, ent)

  val ent = VFENTfun ($TL.tiger_substring, lev0)
  val env = env_insert (env, $Sym.symbol_SUBSTRING, ent)

  val ent = VFENTfun ($TL.tiger_concat, lev0)
  val env = env_insert (env, $Sym.symbol_CONCAT, ent)

  val ent = VFENTfun ($TL.tiger_not, lev0)
  val env = env_insert (env, $Sym.symbol_NOT, ent)

  val ent = VFENTfun ($TL.tiger_exit, lev0)
  val env = env_insert (env, $Sym.symbol_EXIT, ent)
//
  val res_calleesaved_save = calleesaved_save ()
  val stm_save = res_calleesaved_save.0
  val stm_restore = calleesaved_restore (res_calleesaved_save.1)
  val stm_usedef = $TR.STMusedef ('[], $F.theCallersavedReglst)
  val e_prog = transExp1 (lev0, env, e_prog)
  val stm = $TR.STMmove ($F.exp_RV, unEx e_prog)
  val stm = $TR.STMseq (stm, stm_restore)
  val stm = $TR.STMseq (stm_usedef, stm)
  val stm = $TR.STMseq (stm_save, stm)
in
  Ex ($TR.EXPeseq (stm, $F.exp_RV))
end // end of [transProg1]

(* ****** ****** *)

(* end of [translate.dats] *)
