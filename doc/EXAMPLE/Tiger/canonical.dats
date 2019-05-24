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

typedef label = $TL.label_t

(* ****** ****** *)

staload "irtree.sats"

(* ****** ****** *)

staload "canonical.sats"

(* ****** ****** *)

fun expIsPure (exp: exp): bool = case+ exp of
  | EXPconst _ => true
  | EXPname _ => true
  | EXPbinop (_, e1, e2) =>
      if expIsPure e1 then expIsPure e2 else false
  | _ => false
// end of [expIsPure]

fun expIsRead (exp: exp): bool = case+ exp of
  | EXPtemp _ => true
  | EXPconst _ => true
  | EXPname _ => true
  | EXPbinop (_, e1, e2) => begin
      if expIsRead e1 then expIsRead e2 else false
    end // end of [EXPbinop]
  | EXPmem e => expIsRead e
(*
    // this not needed:
  | EXPeseq (s1, e2) => begin
      if stmIsRead s1 then expIsRead e2 else false
    end // end of [EXPeseq]
*)
  | _ => false
// end of [expIsRead]

and stmIsRead (stm: stm): bool = case+ stm of
  | STMexp exp => expIsRead exp
  | STMseq (stm1, stm2) => begin
      if stmIsRead stm1 then stmIsRead stm2 else false
    end // end of [STMseq]
  | _ => false
// end of [stmIsPure]

fn isCommutable
  (stm: stm, exp: exp)
  : bool = begin case+ (stm, exp) of
  | (_, _) when expIsPure exp => true
  | (_, _) when stmIsRead stm andalso expIsRead exp => true
  | (_, _) => false
end // end of [isCommutable]

fn seqSimplify
  (stm1: stm, stm2: stm): stm = begin
  case+ (stm1, stm2) of
  | (_, _) when stmIsRead stm1 => stm2
  | (_, _) when stmIsRead stm2 => stm1
  | (_, _) => STMseq (stm1, stm2)
end // end of [seqSimplify]

(* ****** ****** *)

fn exp_temp_make (): exp = EXPtemp ($TL.temp_make_new ())

(* ****** ****** *)

fun doStm (s0: stm): stm = let
(*
  val () = begin
    prerr "doStm: s0 = "; prerr_stm s0; prerr_newline ()
  end // end of [val]
*)
in
  case+ s0 of
  | STMexp (e) => let
      val (s, e) = doExp e in seqSimplify (s, STMexp e)
    end // end of [STMexp]
  | STMlabel _ => s0
  | STMseq (s1, s2) => let
      val s1 = doStm s1; val s2 = doStm s2 in seqSimplify (s1, s2)
    end // end of [STMseq]
  | STMjump (e, labs) => let
      val (s, e) = doExp e in STMjump (e, labs)
    end // end of [STMjump]
  | STMcjump (oper, e1, e2, tl, fl) => let
      val (s1, e1) = doExp (e1); val (s2, e2) = doExp (e2)
      val s = seqSimplify (s1, s2) 
    in
      seqSimplify (s, STMcjump (oper, e1, e2, tl, fl))
    end // end of [STMcjump]
  | STMmove (e1 as EXPtemp _, EXPcall (e_fun, es_arg)) => let
      val (s1, e_fun) = doExp e_fun; val (s2, es_arg) = doExplst es_arg
      val s = seqSimplify (s1, s2); val e2 = EXPcall (e_fun, es_arg)
    in
      seqSimplify (s, STMmove (e1, e2))
    end // end of [STMmove (EXPtemp, EXPcall)]
  | STMmove (e1, e2) => let
      val (s1, e1) = doExp (e1); val (s2, e2) = doExp (e2)
      val s = seqSimplify (s1, s2) 
    in
      seqSimplify (s, STMmove (e1, e2))
    end // end of [STMmove (_, _)]
  | STMusedef _ => s0
end // end of [doStm]

and doExp (e0: exp): @(stm, exp) = let
(*
  val () = begin
    prerr "doExp: e0 = "; prerr_exp e0; prerr_newline ()
  end // end of [val]
*)
in
  case+ e0 of
  | EXPbinop (oper, e1, e2) => let
      val (s1, e1) = doExp (e1); val (s2, e2) = doExp (e2)
      val s = seqSimplify (s1, s2)
    in
      (s, EXPbinop (oper, e1, e2))
    end // end of [EXPbinop]
  | EXPmem e => let
      val (s, e) = doExp (e) in (s, EXPmem e)
    end // end f [EXPmem]
  | EXPeseq (s1, e) => let
      val s1 = doStm (s1)
      val (s2, e) = doExp e in (seqSimplify (s1, s2), e)
    end // end of [EXPeseq]
  | EXPcall (e_fun, es_arg) => let
      val e_tmp = exp_temp_make ()
      val (s1, e_fun) = doExp (e_fun); val (s2, es_arg) = doExplst (es_arg)
      val s = seqSimplify (s1, s2)
      val e0 = EXPcall (e_fun, es_arg)
    in
      (seqSimplify (s, STMmove (e_tmp, e0)), e_tmp)
    end // end of [EXPcall]
  | _ (* EXPconst, EXPtemp, EXPname *) => (stm_nop, e0)
end // end of [doExp]

and doExplst (es: explst): @(stm, explst) = case+ es of
  | list_cons (e1, es1) => let
      val (s1, e1) = doExp (e1); val (s2, es1) = doExplst (es1)
    in
      case+ 0 of
      | _ when isCommutable (s2, e1) => let
          val s = seqSimplify (s1, s2) in (s, list_cons (e1, es1))
        end // end of [_ when ...]
      | _ => let
          val e_tmp = exp_temp_make (); val s_tmp = STMmove (e_tmp, e1)
          val s1 = seqSimplify (s1, s_tmp); val s = seqSimplify (s1, s2)
        in
          (s, list_cons (e_tmp, es1))
        end // end of [_]
      end (* end of [list_cons] *)
  | list_nil () => (stm_nop, list_nil ())
// end of [doExplst]

(* ****** ****** *)

implement linearize (s0) = aux (doStm s0, list_nil ()) where {
  fun aux (s0: stm, res: stmlst): stmlst = case+ s0 of
    | STMseq (s1, s2) => aux (s1, aux (s2, res)) | _ => list_cons (s0, res)
} // end of [linearize]

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

#define l2l list_of_list_vt

(* ****** ****** *)

fn block_make
  (lab: label, ss: stmlst, s: stm): block = '{
  block_lab= lab, block_init= ss, block_last= s
} // end of [block_make]

implement blocklst_gen (ss0) = let
  val lab_done = $TL.label_make_new ()

  fun f1 (ss0: stmlst, blks: blocklst)
    :<cloref1> blocklst = begin case+ ss0 of
    | list_cons (s, ss) => begin case+ s of
      | STMlabel lab => f2 (ss, lab, list_nil, blks) | _ => let
          val lab = $TL.label_make_new () in f2 (ss0, lab, list_nil (), blks)
        end // end of [_]
      end (* end of [list_cons] *)
    | list_nil () => l2l (list_reverse blks)
  end // end of [f1]
  
  and f2 (
      ss0: stmlst
    , lab: label
    , res: stmlst
    , blks: blocklst
    ) :<cloref1> blocklst = begin case+ ss0 of
    | list_cons (s, ss) => begin case+ s of
      | STMjump _ => let
          val res_rev = l2l (list_reverse res)
          val blk = block_make (lab, res_rev, s)
          val blks = list_cons (blk, blks)
        in
          f1 (ss, blks)
        end // end of [STMjump]
      | STMcjump _ => let
          val res_rev = l2l (list_reverse res)
          val blk = block_make (lab, res_rev, s)
          val blks = list_cons (blk, blks)
        in
          f1 (ss, blks)
        end // end of [STMcjump]
      | STMlabel lab1 => let
          val res_rev = l2l (list_reverse res)
          val stm_jump = STMjump (EXPname lab1, '[lab1])
          val blk = block_make (lab, res_rev, stm_jump)          
          val blks = list_cons (blk, blks)
        in
          f2 (ss, lab1, list_nil (), blks)
        end // end of [STMlabel]
      | _ => f2 (ss, lab, list_cons (s, res), blks)
      end (* end of [list_cons] *)
    | list_nil () => let
        val res_rev = l2l (list_reverse res)
        val stm_jump = STMjump (EXPname lab_done, '[lab_done])
        val blk = block_make (lab, res_rev, stm_jump)
        val blks = list_cons (blk, blks)
      in
        l2l (list_reverse blks)
      end // end of [list_nil]
  end // end of [f2]
in
  (lab_done, f1 (ss0, list_nil ()))
end // end of [blocklst_gen]

(* ****** ****** *)

staload M = "LIB/linmap_randbst.dats"

viewtypedef blockmap = $M.map_vt (label, block)

local

val _cmp = lam (x1: label, x2: label)
  : Sgn =<cloref> $TL.compare_label_label (x1, x2)
// end of [val]

in

extern fun blockmap_empty (): blockmap

extern fun blockmap_insert
  (map: &blockmap, lab: label, blk: block): void

extern fun blockmap_remove
  (map: &blockmap, lab: label): Option_vt (block)

implement blockmap_empty () = $M.linmap_empty<> ()

implement blockmap_insert (map, lab, blk) = let
  val ans = $M.linmap_insert<label,block> (map, lab, blk, _cmp) in
  case+ ans of ~Some_vt _ => () | ~None_vt _ => ()
end // end of [blockmap_insert]

implement blockmap_remove (map, lab) =
  $M.linmap_remove<label,block> (map, lab, _cmp)
// end of [blockmap_remove]

end // end of [local]

(* ****** ****** *)

fun trace_gen
  (map: &blockmap, blk: block): stmlst = let
  val blk_lab = blk.block_lab
  val stm_lab = STMlabel blk_lab
  val blk_init = blk.block_init
  val blk_last = blk.block_last
in
  case blk_last of
  | STMjump (EXPname lab1, _) => let
      val ans = blockmap_remove (map, lab1)
    in
      case+ ans of
      | ~Some_vt (blk1) => let
          val ss = trace_gen (map, blk1) in
          list_cons (stm_lab, list_append (blk_init, ss))
        end // end of [Some_vt]
      | ~None_vt () => let
          val blks = list_extend (blk_init, blk_last)
          val blks = list_of_list_vt (blks)
        in
          list_cons (stm_lab, blks)
        end // end of [None_vt]
    end // end of [STMjump]
  | STMcjump (relop, e1, e2, tlab, flab) => let
      val relop = relop_negate (relop)
      val tlab = flab and flab = tlab
      val blk_last = STMcjump (relop, e1, e2, tlab, flab)
      val ans = blockmap_remove (map, flab) in
      case+ ans of
      | ~Some_vt (blk1) => let
          val ss = trace_gen (map, blk1)
          val ss = list_cons (blk_last, ss) in
          list_cons (stm_lab, list_append (blk_init, ss))
        end // end of [Some_vt]
      | ~None_vt () => let
          val stm_jump = STMjump (EXPname flab, '[flab]) in
          list_cons (
            stm_lab, list_append (blk_init, '[blk_last, stm_jump])
          ) // end of [list_cons]
        end // end of [None_vt]
    end // end of [STMcjump]
  | _ => let
      val blks = list_extend (blk_init, blk_last)
      val blks = list_of_list_vt (blks)
    in
      list_cons (stm_lab, blks)
    end // end of [_]
end // end of [trace_gen]

(* ****** ****** *)

typedef trace = stmlst
typedef tracelst = List trace

implement trace_schedule (lab_done, blks) = let
  fun aux (
      map: &blockmap
    , blks: blocklst
    , trcs: tracelst
    ) :<cloref1> stmlst =
    case+ blks of
    | list_nil () => loop (trcs, '[stm_lab]) where {
        val stm_lab = STMlabel (lab_done)
        fun loop (trcs: tracelst, res: stmlst): stmlst =
          case+ trcs of
          | list_cons (trc, trcs) => loop (trcs, list_append (trc, res))
          | list_nil () => res
        // end of [loop]
      } // end of [list_nil]
    | list_cons (blk, blks) => let
        val ans = blockmap_remove (map, blk.block_lab)
      in
        case+ ans of
        | ~Some_vt _ => let
            val trc = trace_gen (map, blk) in
            aux (map, blks, list_cons (trc, trcs))
          end // end of [Some_vt]
        | ~None_vt () => aux (map, blks, trcs)
      end // end of [list_cons]
  // end of [aux]
  var map = blockmap_empty ()
  val () = loop (map, blks) where {
    fun loop (map: &blockmap, blks: blocklst): void = case+ blks of
      | list_cons (blk, blks) => let
          val () = blockmap_insert (map, blk.block_lab, blk)
        in
          loop (map, blks)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop]
  } // end of [val]
  val res = aux (map, blks, list_nil ())
(*
  val () = let
    val size = $M.linmap_size (map) in
    prerr "size (0) = "; prerr size; print_newline ()
  end // end of [val]
*)
in
  $M.linmap_free (map); res  
end // end of [trace_schedule]

(* ****** ****** *)

(* end of [canonical.dats] *)
