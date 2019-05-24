(*
** VSTTE 2012 Verification Competition
**
** Problem 2
**
** HX: All is done.
** See REDUCTION, VT1, VT2 and VT3 for verification
** See reduction and reduction_cmplt for implementation
*)

(* ****** ****** *)

// [tm] for terms
datasort tm = S | K | App of (tm, tm)

// [ctx]
datasort ctx =
  | CTXhole // []
  | CTXapp1 of (ctx, tm)
  | CTXapp2 of (tm, ctx)
// end of [ctx]

(* ****** ****** *)
//
// ISVAL(t) means that [t] is a value
//
dataprop ISVAL (tm) =
  | ISVAL_K0 (K) of ()
  | ISVAL_S0 (S) of ()
  | {v:tm} ISVAL_K1 (App(K, v)) of ISVAL (v)
  | {v:tm} ISVAL_S1 (App(S, v)) of ISVAL (v)
  | {v1,v2:tm}
    ISVAL_S2 (App(App(S, v1), v2)) of (ISVAL (v1), ISVAL (v2))
// end of [ISVAL]

(* ****** ****** *)
//
// if App(s, t) is a value, then [s] is a value
//
prfn lemma_ISVAL_app1
  {s,t:tm}
  (pf: ISVAL (App (s, t))): ISVAL (s) =
  case+ pf of
  | ISVAL_K1 (pf1) => ISVAL_K0 ()
  | ISVAL_S1 (pf1) => ISVAL_S0 ()
  | ISVAL_S2 (pf1, pf2) => ISVAL_S1 (pf1)
  | _ =/=>> () // =/=>> means that the rest of cases are proven to be not accessible
// end of [lemma_isVAL_app1]

//
// if App(s, t) is a value, then [t] is a value
//
prfn lemma_ISVAL_app2
  {s,t:tm}
  (pf: ISVAL (App (s, t))): ISVAL (t) =
  case+ pf of
  | ISVAL_K1 (pf1) => pf1
  | ISVAL_S1 (pf1) => pf1
  | ISVAL_S2 (pf1, pf2) => pf2
  | _ =/=>> () // =/=>> means that the rest of cases are proven to be not accessible
// end of [lemma_isVAL_app2]

(* ****** ****** *)
//
// ISCBV(C) means that C is a call-by-value context
//
dataprop ISCBV (ctx) =
  | ISCBV_hole (CTXhole) of ()
  | {C:ctx} {t:tm} ISCBV_app1 (CTXapp1 (C, t)) of ISCBV (C)
  | {v:tm} {C:ctx} ISCBV_app2 (CTXapp2 (v, C)) of (ISVAL v, ISCBV (C))
// end of [ISCBV]

(* ****** ****** *)
//
// CTXFOLD(C, t1, t2) means that C[t1] = t2
//
dataprop
CTXFOLD (ctx, tm, tm) =
  | {t:tm} CTXFOLD_hole (CTXhole, t, t)
  | {C:ctx} {t:tm} {t1:tm} {t2:tm}
    CTXFOLD_app1 (CTXapp1 (C, t), t1, App (t2, t)) of CTXFOLD (C, t1, t2)
  | {t:tm} {C:ctx} {t1:tm} {t2:tm}
    CTXFOLD_app2 (CTXapp2 (t, C), t1, App (t, t2)) of (CTXFOLD (C, t1, t2))
// end of [CTXFOLD]

//
// CTXUNFOLD(t1, C, t2) means that t1 = C[t2]
//
propdef
CTXUNFOLD (t1:tm, C:ctx, t2:tm) = CTXFOLD (C:ctx, t2:tm, t1:tm)

(* ****** ****** *)

(*
** A bona-fide encoding of the 'reduction' relation:
** CRED (t1, t2) mean that t1 -> t2
*)
dataprop
CRED (t1:tm, t2:tm) =
  | {C:ctx} {v1,v2:tm}
    CRED_K (t1, t2) of (
      ISCBV C, ISVAL v1, ISVAL v2
    , CTXUNFOLD (t1, C, App (App (K, v1), v2)), CTXFOLD (C, v1, t2)
    ) // end of [CRED_K]
  | {C:ctx} {v1,v2,v3:tm}
    CRED_S (t1, t2) of (
      ISCBV C, ISVAL v1, ISVAL v2, ISVAL v3
    , CTXUNFOLD (t1, C, App (App (App (S, v1), v2), v3)), CTXFOLD (C, App (App (v1, v3), App (v2, v3)), t2)
    ) // end of [CRED_S]
// end of [CRED]

(* ****** ****** *)
//
// t1 -> t2 implies t1(t) -> t2(t)
//
prfn lemma_CRED_app1
  {t1,t2:tm} {t:tm} (
  pf: CRED (t1, t2)
): CRED (App (t1, t), App (t2, t)) = case+ pf of
  | CRED_K (pfcbv, pf1val, pf2val, pf_unfold, pf_fold) =>
      CRED_K (ISCBV_app1 (pfcbv), pf1val, pf2val, CTXFOLD_app1 pf_unfold, CTXFOLD_app1 pf_fold)
  | CRED_S (pfcbv, pf1val, pf2val, pf3val, pf_unfold, pf_fold) =>
      CRED_S (ISCBV_app1 (pfcbv), pf1val, pf2val, pf3val, CTXFOLD_app1 pf_unfold, CTXFOLD_app1 pf_fold)
// end of [lemma_CRED_app1]

//
// t1 -> t2 implies v(t1) -> v(t2)
//
prfn lemma_CRED_app2
  {v:tm} {t1,t2:tm} (
  pfval: ISVAL v, pf: CRED (t1, t2)
) : CRED (App (v, t1), App (v, t2)) = case+ pf of
  | CRED_K (pfcbv, pf1val, pf2val, pf_unfold, pf_fold) =>
      CRED_K (ISCBV_app2 (pfval, pfcbv), pf1val, pf2val, CTXFOLD_app2 (pf_unfold), CTXFOLD_app2 (pf_fold))
  | CRED_S (pfcbv, pf1val, pf2val, pf3val, pf_unfold, pf_fold) =>
      CRED_S (ISCBV_app2 (pfval, pfcbv), pf1val, pf2val, pf3val, CTXFOLD_app2 (pf_unfold), CTXFOLD_app2 (pf_fold))
// end of [lemma_CRED_app2]

(* ****** ****** *)
//
// [CRED] is rather inconvenient to use. So let us define the following [RED]
//
dataprop
RED (tm, tm) =
  | {v1,v2:tm}
    RED_K (App (App (K, v1), v2), v1) of (ISVAL v1, ISVAL v2)
  | {v1,v2,v3:tm}
    RED_S (
      App (App (App (S, v1), v2), v3)
    , App (App (v1, v3), App (v2, v3))
    ) of (ISVAL v1, ISVAL v2, ISVAL v3)
  | {t1,t2:tm} {t:tm}
    RED_app1 (App (t1, t), App (t2, t)) of RED (t1, t2)
  | {t:tm} {t1,t2:tm}
    RED_app2 (App (t, t1), App (t, t2)) of (ISVAL t, RED (t1, t2))
// end of [RED]

(* ****** ****** *)
//
// RED (t1, t2) implies CRED (t1, t2)
//
prfun
lemma_RED_CRED {t1,t2:tm} .<t1>.
  (pf: RED (t1, t2)): CRED (t1, t2) =
  case+ pf of
  | RED_K (pf1val, pf2val) =>
      CRED_K (ISCBV_hole, pf1val, pf2val, CTXFOLD_hole, CTXFOLD_hole)
  | RED_S (pf1val, pf2val, pf3val) =>
      CRED_S (ISCBV_hole, pf1val, pf2val, pf3val, CTXFOLD_hole, CTXFOLD_hole)
  | RED_app1 (pf1) => lemma_CRED_app1 (lemma_RED_CRED (pf1))
  | RED_app2 (pf1val, pf2) => lemma_CRED_app2 (pf1val, lemma_RED_CRED (pf2))
// end of [lemma_RED_CRED]

//
// CRED (t1, t2) implies RED (t1, t2)
//
prfun
lemma_CRED_RED {t1,t2:tm} .<t1>.
  (pf: CRED (t1, t2)): RED (t1, t2) =
  case+ pf of
  | CRED_K (pfcbv, pf1val, pf2val, pf_unfold, pf_fold) => (
    case+ pf_unfold of
    | CTXFOLD_hole () => let
        prval CTXFOLD_hole () = pf_fold in RED_K (pf1val, pf2val)
      end // end of [hole]
    | CTXFOLD_app1 (pf_unfold) => let
        prval ISCBV_app1 (pfcbv) = pfcbv
        prval CTXFOLD_app1 (pf_fold) = pf_fold
      in
        RED_app1 (lemma_CRED_RED (CRED_K (pfcbv, pf1val, pf2val, pf_unfold, pf_fold)))
      end // end of [CTXFOLD_app1]
    | CTXFOLD_app2 (pf_unfold) => let
        prval ISCBV_app2 (pfval, pfcbv) = pfcbv
        prval CTXFOLD_app2 (pf_fold) = pf_fold
      in
        RED_app2 (pfval, lemma_CRED_RED (CRED_K (pfcbv, pf1val, pf2val, pf_unfold, pf_fold)))
      end // end of [CTXFOLD_app2]
    )
  | CRED_S (pfcbv, pf1val, pf2val, pf3val, pf_unfold, pf_fold) => (
    case+ pf_unfold of
    | CTXFOLD_hole () => let
        prval CTXFOLD_hole () = pf_fold in RED_S (pf1val, pf2val, pf3val)
      end // end of [hole]
    | CTXFOLD_app1 (pf_unfold) => let
        prval ISCBV_app1 (pfcbv) = pfcbv
        prval CTXFOLD_app1 (pf_fold) = pf_fold
      in
        RED_app1 (lemma_CRED_RED (CRED_S (pfcbv, pf1val, pf2val, pf3val, pf_unfold, pf_fold)))
      end // end of [CTXFOLD_app1]
    | CTXFOLD_app2 (pf_unfold) => let
        prval ISCBV_app2 (pfval, pfcbv) = pfcbv
        prval CTXFOLD_app2 (pf_fold) = pf_fold
      in
        RED_app2 (pfval, lemma_CRED_RED (CRED_S (pfcbv, pf1val, pf2val, pf3val, pf_unfold, pf_fold)))
      end // end of [CTXFOLD_app2]
    )
// end of [lemma_CRED_RED]

(* ****** ****** *)
//
// from now on, [CRED] is retired; instead, [RED] will be used to encode the one-step call-by-value
// evaluation
//
(* ****** ****** *)
//
// REDM (t1, t2, n) means that [t1] evaluates to [t2] in [n] steps.
//
dataprop
REDM (tm, tm, int) =
  | {t:tm} REDM0 (t, t, 0) of ()
  | {t0:tm} {t1:tm} {t2:tm} {n:nat}
    REDM1 (t0, t2, n+1) of (RED (t0, t1), REDM (t1, t2, n))
// end of [REDM]
//
// REDM is overloaded: REDM (t1, t2) means that there exists [n] such that REDM (t1, t2, n) holds
//
propdef REDM (t1:tm, t2:tm) = [n:nat] REDM (t1, t2, n)

(* ****** ****** *)
//
// REDM (t1, t2, n) implies REDM (t1(t), t2(t), n)
//
prfun
lemma_REDM_app1
  {t1,t2:tm} {t:tm} {n:nat} .<n>. (
  pf: REDM (t1, t2, n)
) : REDM (App (t1, t), App (t2, t), n) = case+ pf of
  | REDM0 () => REDM0 ()
  | REDM1 (pf1, pf2) => let
      prval pf1 = RED_app1 (pf1)
      prval pf2 = lemma_REDM_app1 (pf2)
    in
      REDM1 (pf1, pf2)
    end // end of [REDM1]
// end of [lemma_REDM1_app1]
//
// REDM (t1, t2, n) implies REDM (v(t1), v(t2) n)
//
prfun
lemma_REDM_app2
  {t1,t2:tm} {t:tm} {n:nat} .<n>. (
  pfval: ISVAL t, pf: REDM (t1, t2, n)
) : REDM (App (t, t1), App (t, t2), n) = case+ pf of
  | REDM0 () => REDM0 ()
  | REDM1 (pf1, pf2) => let
      prval pf1 = RED_app2 (pfval, pf1)
      prval pf2 = lemma_REDM_app2 (pfval, pf2)
    in
      REDM1 (pf1, pf2)
    end // end of [REDM1]
// end of [lemma_REDM1_app2]

(* ****** ****** *)
//
// REDM (t1, t2, n) and RED (t2, t3) implies REDM (t1, t3, n+1)
//
prfun
lemma_REDM_RED {t1,t2,t3:tm} {n:nat} .<n>.
  (pf1: REDM (t1, t2, n), pf2: RED (t2, t3)): REDM (t1, t3, n+1) =
  case+ pf1 of
  | REDM0 () => REDM1 (pf2, REDM0 ())
  | REDM1 (pf11, pf12) => REDM1 (pf11, lemma_REDM_RED (pf12, pf2))
// end of [lemma_REDM_RED]
//
// REDM (t1, t2, n1) and REDM (t2, t3, n2) implies REDM (t1, t3, n1+n2)
//
prfun
lemma_REDM_REDM {t1,t2,t3:tm} {n1,n2:nat} .<n1>.
  (pf1: REDM (t1, t2, n1), pf2: REDM (t2, t3, n2)): REDM (t1, t3, n1+n2) =
  case+ pf1 of
  | REDM0 () => pf2
  | REDM1 (pf11, pf12) => REDM1 (pf11, lemma_REDM_REDM (pf12, pf2))
// end of [lemma_REDM_REDM]

(* ****** ****** *)
//
// NRED(s) means that [s] cannot be reduced; that is, s->t for any t
// leads to a contradiction
//
propdef NRED (s:tm) = {t:tm} RED (s, t) -> [false] void

(* ****** ****** *)
//
// a value cannot be reduced; that is ISVAL(s) and RED(s, t)
// leads to a contradiction
//
prfun
lemma_ISVAL_RED_false
  {s:tm} {t:tm} .<s>. (
  pfval: ISVAL (s), pfred: RED (s, t)
) : [false] void =
  case+ pfred of
  | RED_K (_, _) => (
    case+ pfval of
    | ISVAL_K0 _ =/=> false
    | ISVAL_S0 _ =/=> false
    | ISVAL_K1 _ =/=> false
    | ISVAL_S1 _ =/=> false
    | ISVAL_S2 _ =/=> false
  )
  | RED_S (_, _, _) => (
    case+ pfval of
    | ISVAL_K0 _ =/=> false
    | ISVAL_S0 _ =/=> false
    | ISVAL_K1 _ =/=> false
    | ISVAL_S1 _ =/=> false
    | ISVAL_S2 _ =/=> false
  )
  | RED_app1 (pfred) => let
      prval pfval = lemma_ISVAL_app1 (pfval) in lemma_ISVAL_RED_false (pfval, pfred)
    end
  | RED_app2 (_, pfred) => let
      prval pfval = lemma_ISVAL_app2 (pfval) in lemma_ISVAL_RED_false (pfval, pfred)
    end
// end of [lemma_ISVAL_RED_false]

(* ****** ****** *)
//
// REDUCTION (t, v) means that
// [t] evaluates to a value [v] in many steps.
//
propdef REDUCTION (t:tm, v:tm) = (REDM (t, v), ISVAL (v))

(* ****** ****** *)
//
// datatype for run-time values representing terms
//
datatype TM (tm) =
  | K (K) of ()
  | S (S) of ()
  | {t1,t2:tm}
    App (App (t1, t2)) of (TM t1, TM t2)
// end of [TM]

(* ****** ****** *)
//
// the functions [reduction] means that given any term t,
// its return is a term v such that v is a value and REDM (t, v) holds.
// this function is to be implemented later:
//
extern
fun reduction {t:tm} (t: TM (t)): [v:tm] (REDUCTION (t, v) | TM (v))

(* ****** ****** *)

(*
** Verification Tasks
** 1. Prove that if reduction (t) returns t' then t -> t' and t' -/-> (40 points)
** // HX: fully completed
*)
prfn VT1 {t,t':tm} (
  pf: REDUCTION (t, t')
) : (REDM (t, t'), NRED (t')) = let // t reduces to t' and t' cannot be reduced further
  prval (pf1, pf2) = pf
  prfn fpf {t'':tm} (pfred: RED (t', t'')): [false] void = lemma_ISVAL_RED_false (pf2, pfred)
in
  (pf1, fpf)
end // end of [VT1]

(* ****** ****** *)
(*
** Verification Tasks
** 2. Prove that the function 'reduction'
**    terminates on any term which does not contains S
** // HX: fully completed
*)

//
// Sfree(t) means that [t] does not contain [S]
//
dataprop
Sfree (tm) =
  | Sfree_K (K) of ()
  | {t1,t2:tm}
    Sfree_app (App (t1, t2)) of (Sfree t1, Sfree t2)
// end of [Sfree]

//
// KNF(t) means that [t] is a normal form containing only K
//
dataprop KNF (tm) =
  | KNF_K (K) of ()
  | {t:tm} KNF_app (App (K, t)) of KNF (t)
// end of [KNF]

//
// each KNF is a value
//
prfun lemma_KNF_ISVAL
  {t:tm} .<t>. (pf: KNF (t)): ISVAL (t) =
  case+ pf of
  | KNF_K () => ISVAL_K0 ()
  | KNF_app (pf) => ISVAL_K1 (lemma_KNF_ISVAL (pf))
// end of [lemma_KNF_ISVAL]

//
// VT2_ means that for every term [s] containing no S, there exists
// a term [t] such that [s] reduces to [t] in many steps and [t] is a KNF.
//
prfun VT2_ {s:tm} .<s>. (
  pf: Sfree s
) : [t:tm] (REDM (s, t), KNF (t)) =
  case+ pf of
  | Sfree_K () => (REDM0 (), KNF_K ())
  | Sfree_app (pf1, pf2) => let
      prval (pf1redm, pf1knf) = VT2_ (pf1)
      prval (pf2redm, pf2knf) = VT2_ (pf2)
      prval pf1redm = lemma_REDM_app1 (pf1redm)
      prval pf1val = lemma_KNF_ISVAL (pf1knf)
      prval pf2redm = lemma_REDM_app2 (pf1val, pf2redm)
      prval pf12redm = lemma_REDM_REDM (pf1redm, pf2redm)
    in
      case+ pf1knf of
      | KNF_K () => (pf12redm, KNF_app (pf2knf))
      | KNF_app (pf1knf) => let
          prval pf1val = lemma_KNF_ISVAL (pf1knf)
          prval pfred = RED_K (pf1val, lemma_KNF_ISVAL (pf2knf))
        in
          (lemma_REDM_RED (pf12redm, pfred), pf1knf)
        end
    end // end of [Sfree]
// end of [VT2_]

//
// VT2: for every S-free term [s], there is a [t] such that REDUCTION (s, t) holds.
//
prfn VT2
  {s:tm} (
  pf: Sfree s
) : [t:tm] REDUCTION (s, t) = let
  prval (pfredm, pfknf) = VT2_ (pf)
in
  (pfredm, lemma_KNF_ISVAL (pfknf))
end // end of [VT2]

(* ****** ****** *)

dataprop KS (int, tm) =
  | KS0 (0, K) of ()
  | {n:nat} {t:tm}
    KS1 (n+1, App (t, K)) of KS (n, t)
// end of [KS]

(* ****** ****** *)

(*
** Verification Tasks
** 3. Consider the meta-language function ks defined by ... (25 points)
** // HX: fully completed
*)

prfun
VT3_1
  {n:nat | n mod 2 == 0}
  {t:tm} .<n>.
  (pf: KS (n, t)): REDM (t, K) =
  sif n > 0 then let
    prval KS1 (pf1) = pf
    prval pf1res = VT3_2 (pf1) // ks(n-1) => KK
    prval pf1res = lemma_REDM_app1 (pf1res) // => ks(n) => (KK)K
    stadef KKK = App (App (K, K), K)
    prval pf_KKK_K = RED_K (ISVAL_K0, ISVAL_K0)
  in
    lemma_REDM_RED (pf1res, pf_KKK_K)
  end else let // n == 0
    prval KS0 () = pf in REDM0 ()
  end // end of [sif]
// end of [VT3_1]

and
VT3_2
  {n:nat | n mod 2 == 1} .<n>.
  {t:tm}
  (pf: KS (n, t)): REDM (t, App (K, K)) =
  sif n > 1 then let
    prval KS1 (pf1) = pf
    prval pf1res = VT3_1 (pf1) // ks(n-1) => K
  in
    lemma_REDM_app1 (pf1res) // => ks(n) => KK
  end else let
    prval KS1 (KS0 ()) = pf in REDM0 ()
  end // end of [sif]
// end of [VT3_2]

(* ****** ****** *)

dataprop
EVAL (tm, tm, int) =
//
  | EVAL0_K (K, K, 0) of ()
  | EVAL0_S (S, S, 0) of ()
//
  | {t1,t2:tm} {v1,v2:tm} {n1,n2:nat}
    EVAL1_app (
      App (t1, t2), App (v1, v2), n1+n2
    ) of (
      EVAL (t1, v1, n1), EVAL (t2, v2, n2), ISVAL (App(v1, v2))
    ) // end of [EVAL1_app]
//
  | {t1,t2:tm} {v1,v2:tm} {n1,n2:nat}
    EVAL1_app_K (
      App (t1, t2), v1, n1+n2+1
    ) of (
      EVAL (t1, App (K, v1), n1), EVAL (t2, v2, n2)
    ) // end of [EVAL1_app_K]
//
  | {t1,t2:tm} {v11,v12,v2:tm} {n1,n2:nat} {v:tm} {n:nat}
    EVAL1_app_S (
      App (t1, t2), v, n1+n2+1+n
    ) of (
      EVAL (t1, App (App (S, v11), v12), n1)
    , EVAL (t2, v2, n2)
    , EVAL (App (App (v11, v2), App (v12, v2)), v, n)
    ) // end of [EVAL1_app_S]
// end of [EVAL]

propdef EVAL (s:tm, v:tm) = [n:nat] EVAL (s, v, n)

(* ****** ****** *)
//
// EVAL (s, v, n) implies REDM (s, v, n) and ISVAL (v)
//
prfun
lemma_EVAL_REDMVAL
  {s,v:tm} {n:nat} .<n,s>.
  (pf: EVAL (s, v, n)): (REDM (s, v, n), ISVAL v) =
  case+ pf of
  | EVAL0_K () => (REDM0 (), ISVAL_K0)
  | EVAL0_S () => (REDM0 (), ISVAL_S0)
  | EVAL1_app (pf1, pf2, pfval) => let
      prval (pf1redm, pf1val) = lemma_EVAL_REDMVAL (pf1)
      prval (pf2redm, pf2val) = lemma_EVAL_REDMVAL (pf2)
      prval pf1redm = lemma_REDM_app1 (pf1redm)
      prval pf2redm = lemma_REDM_app2 (pf1val, pf2redm)
      prval pf12redm = lemma_REDM_REDM (pf1redm, pf2redm)
    in
      (pf12redm, pfval)
    end
  | EVAL1_app_K (pf1, pf2) => let
      prval (pf1redm, pf1val) = lemma_EVAL_REDMVAL (pf1)
      prval (pf2redm, pf2val) = lemma_EVAL_REDMVAL (pf2)
      prval pf1redm = lemma_REDM_app1 (pf1redm)
      prval pf2redm = lemma_REDM_app2 (pf1val, pf2redm)
      prval pf12redm = lemma_REDM_REDM (pf1redm, pf2redm)
      prval pf1val_1 = lemma_ISVAL_app2 pf1val
      prval pfred = RED_K (pf1val_1, pf2val)
    in
      (lemma_REDM_RED (pf12redm, pfred), pf1val_1)
    end // end of [EVAL1_app_K]
  | EVAL1_app_S (pf1, pf2, pf3) => let
      prval (pf1redm, pf1val) = lemma_EVAL_REDMVAL (pf1)
      prval (pf2redm, pf2val) = lemma_EVAL_REDMVAL (pf2)
      prval pf1redm = lemma_REDM_app1 (pf1redm)
      prval pf2redm = lemma_REDM_app2 (pf1val, pf2redm)
      prval pf12redm = lemma_REDM_REDM (pf1redm, pf2redm)
      prval pf1val_1 = lemma_ISVAL_app1 pf1val
      prval pf1val_1_2 = lemma_ISVAL_app2 pf1val_1
      prval pf1val_2 = lemma_ISVAL_app2 pf1val
      prval pfred = RED_S (pf1val_1_2, pf1val_2, pf2val)
      prval (pf3redm, pf3val) = lemma_EVAL_REDMVAL (pf3)
    in
      (lemma_REDM_REDM (lemma_REDM_RED (pf12redm, pfred), pf3redm), pf3val)
    end // end of [EVAL1_app_S]
// end of [lemma_EVAL_REDMVAL]

prfn
lemma_EVAL_ISVAL
  {s,v:tm} {n:nat}
  (pf: EVAL (s, v, n)): ISVAL v = let
  prval (_, pfval) = lemma_EVAL_REDMVAL (pf) in pfval
end // end of [lemma_EVAL_ISVAL]

(* ****** ****** *)
//
// K(v1)(v2) cannot be a value (it is redex!)
//
prfn
lemma_ISVAL_Kvv_false {v1,v2:tm}
  (pf: ISVAL (App (App (K, v1), v2))): [false] void =
  case+ pf of
  | ISVAL_K0 _ => ()
  | ISVAL_S0 _ => ()
  | ISVAL_K1 _ => ()
  | ISVAL_S1 _ => ()
  | ISVAL_S2 _ => ()
// end of [lemma_ISVAL_Kvv_false]

//
// App(App (App(v1, v2), v3), v4) cannot be a value
//
prfn
lemma_ISVAL_app3_false {v1,v2,v3,v4:tm}
  (pf: ISVAL (App (App (App (v1, v2), v3), v4))): [false] void =
  case+ pf of
  | ISVAL_K0 _ => ()
  | ISVAL_S0 _ => ()
  | ISVAL_K1 _ => ()
  | ISVAL_S1 _ => ()
  | ISVAL_S2 _ => ()
// end of [lemma_ISVAL_app3_false]

(* ****** ****** *)

fun eval
  {s:tm} (s: TM s)
  : [v:tm] (EVAL (s, v) | TM v) =
  case+ s of
  | K () => (EVAL0_K | s)
  | S () => (EVAL0_S | s)
  | App (s1, s2) => let
      val (pf1ev | v1) = eval (s1)
      prval pf1val = lemma_EVAL_ISVAL (pf1ev) // [v1] is a value
      val (pf2ev | v2) = eval (s2)
      prval pf2val = lemma_EVAL_ISVAL (pf2ev) // [v2] is a value
    in
      case v1 of
      | App (K(), v11) => (EVAL1_app_K (pf1ev, pf2ev) | v11)
      | App (App (S(), v11), v12) => let
          val (pf3ev | v) = eval (App (App (v11, v2), App (v12, v2)))
        in
          (EVAL1_app_S (pf1ev, pf2ev, pf3ev) | v)
        end
      | K () =>
          (EVAL1_app (pf1ev, pf2ev, ISVAL_K1 (pf2val)) | App (v1, v2))
      | S () =>
          (EVAL1_app (pf1ev, pf2ev, ISVAL_S1 (pf2val)) | App (v1, v2))
      | App (S(), v11) => let
          prval pfval = ISVAL_S2 (lemma_ISVAL_app2 (pf1val), pf2val)
        in
          (EVAL1_app (pf1ev, pf2ev, pfval) | App (v1, v2))
        end // end of [APP (S, _)]
//
// HX: =/=> means that the pattern is proven to be not accessible
//
      | App (App (K(), _), _) =/=> lemma_ISVAL_Kvv_false (pf1val)
      | App (App (App (_, _), _), _) =/=> lemma_ISVAL_app3_false (pf1val)
    end // end of [App]
// end of [eval]

(* ****** ****** *)
//
// The following function [reduction] takes a term t; if it terminates,
// it returns another term v paired with a proof showing that t and v are
// related according to the REDUCTION relation.
(*
extern
fun reduction {t:tm} (t: TM (t)): [v:tm] (REDUCTION (t, v) | TM (v))
*)
//
implement
reduction (t) = let
  val (pfev | v) = eval (t)
  prval (pfredm, pfval) = lemma_EVAL_REDMVAL (pfev)
in
  ((pfredm, pfval) | v)
end // [reduction]

(* ****** ****** *)

(*
** HX: given my understanding of your formulation of the problem, you do
** not ask for completeness to be proven, which is encoded by the following
** function: if REDUCTION (t, v) is defined, then reduction_cmplt is guaranteed
** to return v:
*)

extern
fun reduction_cmplt {t,v:tm} (pf: REDUCTION (t, v) | t: TM (t)):<> TM (v)

(*
** I implement [reduction_cmplt] as follows just in case you want it:
*)

(* ****** ****** *)

dataprop
EVALAPP (tm, tm, tm, int) =
  | {v1,v2:tm}
    EVALAPP0 (v1, v2, App (v1, v2), 0) of ISVAL (App (v1, v2))
  | {v1,v2:tm}
    EVALAPP1_K (App (K, v1), v2, v1, 1)
  | {v1,v2,v3:tm}{n:nat}{v:tm}
    EVALAPP1_S (App (App (S, v1), v2), v3, v, n+1) of EVAL (App (App (v1, v3), App (v2, v3)), v, n)
// end of [EVALAPP]

prfn
lemma_EVALAPP_K {v1,v2,v3:tm}{n:nat}
  (pf: EVALAPP (App (K, v1), v2, v3, n)): [n > 0] void =
  case+ pf of
  | EVALAPP1_K () => ()
  | EVALAPP0 (pfval) => lemma_ISVAL_Kvv_false (pfval)
// end of [lemma_EVALAPP_K]

prfn
lemma_EVALAPP_S {v1,v2,v3,v4:tm}{n:nat}
  (pf: EVALAPP (App (App (S, v1), v2), v3, v4, n)): [n > 0] void =
  case+ pf of
  | EVALAPP1_S _ => ()
  | EVALAPP0 (pfval) => lemma_ISVAL_app3_false (pfval)
// end of [lemma_EVALAPP_S]

(* ****** ****** *)

prfn
lemma_EVAL_unapp
  {s1,s2:tm} {v:tm} {n:nat} (
  pf: EVAL (App (s1, s2), v, n)
) : [v1,v2:tm;n1,n2,n3:nat | n1+n2+n3==n] (
  EVAL (s1, v1, n1)
, EVAL (s2, v2, n2)
, EVALAPP (v1, v2, v, n3)
)  =
  case+ pf of
  | EVAL1_app (pf1, pf2, pfval) => (pf1, pf2, EVALAPP0 (pfval))
  | EVAL1_app_K (pf1, pf2) => (pf1, pf2, EVALAPP1_K ())
  | EVAL1_app_S (pf1, pf2, pf3) => (pf1, pf2, EVALAPP1_S (pf3))
// end of [lemma_EVAL_unapp]

(* ****** ****** *)

fun eval_cmplt
  {s,v:tm} {n:nat} .<n,s>.
  (pf: EVAL (s, v, n) | s: TM s)
  :<> TM v = // this is a pure terminating function
  case+ s of
  | K () => let
     prval EVAL0_K () = pf in K ()
    end
  | S () => let
     prval EVAL0_S () = pf in S ()
    end
  | App (s1, s2) => let
      prval (pf1, pf2, pf3) = lemma_EVAL_unapp (pf)
      val v1 = eval_cmplt (pf1 | s1)
      prval pf1val = lemma_EVAL_ISVAL (pf1) // [v1] is a value
      val v2 = eval_cmplt (pf2 | s2)      
    in
      case+ v1 of
      | App (K(), v11) => let
          prval () = lemma_EVALAPP_K (pf3)
          prval EVALAPP1_K () = pf3 in v11
        end
      | App (App (S(), v11), v12) => let
          prval () = lemma_EVALAPP_S (pf3)
          prval EVALAPP1_S (pf3ev) = pf3
        in
          eval_cmplt (pf3ev | App (App (v11, v2), App (v12, v2)))
        end
      | K () => let
          prval EVALAPP0 _ = pf3 in App (v1, v2)
        end
      | S () => let
          prval EVALAPP0 _ = pf3 in App (v1, v2)
        end
      | App (S(), v11) => let
          prval EVALAPP0 _ = pf3 in App (v1, v2)
        end
//
      | App (App (K(), _), _) =/=> lemma_ISVAL_Kvv_false (pf1val)
      | App (App (App (_, _), _), _) =/=> lemma_ISVAL_app3_false (pf1val)
//
    end // end of [App]
// end of [eval_cmplt]

(* ****** ****** *)

extern
praxi // axiom
lemma_REDMVAL_EVAL
  {s,v:tm} {n:nat}
  (pf1: REDM (s, v, n), pf2: ISVAL v): EVAL (s, v, n)
// end of [lemma_REDMVAL_EVAL]

(* ****** ****** *)
//
// Please note that
// [lemma_REDMVAL_EVAL] is the only lemma not proven in this solution.
//
(* ****** ****** *)

(*
extern
fun reduction_cmplt {t,v:tm} (pf: REDUCTION (t, v) | t: TM (t)):<> TM (v)
*)
implement
reduction_cmplt (pf | t) = let
  prval pfev = lemma_REDMVAL_EVAL (pf.0, pf.1) in eval_cmplt (pfev | t)
end // end of [reduction_cmplt]

(* ****** ****** *)
//
// Because [reduction] and [reduction_cmplt] have the same erasure, we
// can argue that [reduction] is both sound and complete. Cheers!
// 
(* ****** ****** *)
//
// Yes, what is implemented here can be run. Give it a try if you like.
//
(* ****** ****** *)

fun print_term
  {t:tm} (t: TM t): void =
  case+ t of
  | K () => print ("K")
  | S () => print ("S")
  | App (t1, t2) => (
      print "("; print_term (t1); print ")"; print_term t2
    ) // end of [App]
// end of [print_term]

(* ****** ****** *)

implement
main () = () where {
  val I = App (App (S, K), K)
  val (pf | ans) = reduction (App (App (I, I), K))
  val () = (print "((I)I)K --> "; print_term ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem2.dats] *)
