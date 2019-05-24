// Some examples in the following paper:
// Implementing typeful program transformations
// by Chiyan Chen and Rui Shi and Hongwei Xi

// February 2007:
// It is ported to ATS/Geizella by Hongwei Xi

(* ****** ****** *)

infixr ->> ::

datasort ty = int | ->> of (ty, ty) | forall of (ty -> ty)
datasort env = nil | :: of (ty, env)

datatype VAR (env, ty) =
  | {G:env} {t:ty} VARone (t :: G, t)
  | {G:env} {t1,t2:ty} VARshi (t2 :: G, t1) of VAR (G, t1)

datatype EXP (env, ty) =
  | {G:env} {t:ty} EXPvar (G, t) of VAR (G, t)
  | {G:env} {t1,t2:ty} EXPlam (G, t1 ->> t2) of EXP (t1 :: G, t2)
  | {G:env} {t1,t2:ty} EXPapp (G, t2) of (EXP (G, t1 ->> t2), EXP (G, t1))
(*
  | {G:env} {f:ty->ty} EXPtlam (G, forall f) of ({t:ty} EXP (G, f t))
  | {G:env} {f:ty->ty;t:ty} EXPtapp (G, f t) of EXP (G, forall f)
*)

typedef SUB (G1:env, G2:env) = {t:ty} VAR(G1,t) -> EXP(G2,t)

// implementing some substitution functions

val idSub = (lam x => EXPvar x)
  : {G:env} SUB (G, G)

val shiSub = (lam x => EXPvar (VARshi x))
  : {G:env} {t:ty} SUB (G, t :: G)

fun subst {G1,G2:env} {t:ty}
  (sub: SUB(G1,G2)) (e: EXP(G1,t)): EXP(G2,t) = begin case+ e of
  | EXPvar x => sub (x)
  | EXPlam e => EXPlam (subst (subLam sub) e)
  | EXPapp (e1, e2) => EXPapp (subst sub e1, subst sub e2)
(*
  | EXPtlam {G1} {f} e => EXPtlam {G2} {f} (lam {t:ty} => subst sub (e {t}))
  | EXPtapp e => EXPtapp (subst sub e)
*)
end // end of [subst]

and subLam {G1,G2:env} {t:ty}
  (sub: SUB (G1,G2)): SUB (t::G1,t::G2) = begin
  lam v => case+ v of
    | VARone () => EXPvar (VARone)
    | VARshi x' => subst (shiSub {..} {..}) (sub x') 
end // end of [subLam]

fun subPre {G1,G2:env} {t:ty} (sub: SUB(G1, G2)) (e: EXP (G2, t))
  : SUB (t :: G1, G2) = begin
  lam x => case+ x of VARone () => e | VARshi x => sub x
end // end of [subPre]
  
fun subComp {G1,G2,G3:env} (sub1: SUB (G1,G2)) (sub2: SUB (G2,G3))
  : SUB (G1, G3) = begin
  lam x => subst sub2 (sub1 x)
end // end of [subComp]

// implementing the normalization function for simply typed lambda-calculus

fun nf {G:env} {t:ty} (e: EXP(G, t)): EXP (G, t) = begin
  case+ e of
  | EXPvar _ => e
  | EXPlam e => EXPlam (nf e)
  | EXPapp (e1, e2) => begin case+ nf e1 of
    | EXPlam e => nf (subst (subPre idSub e2) e)
    | e1 => EXPapp (e1, nf e2)
    end
(*
  | EXPtlam {G} {f} e => EXPtlam {G} {f} (lam {t:ty} => nf (e {t}))
  | EXPtapp e => EXPtapp (nf e)
*)
end // end of [nf]

// implementing a call-by-value evaluator for simply typed lambda-calculus

datatype VAL (ty) =
  | {G:env} {t1,t2:ty} VALclo (t1 ->> t2) of (ENV G, EXP (t1 :: G, t2))
  | {G:env} {f:ty->ty} VALtclo (forall f) of (ENV G, {t:ty} EXP (G, f t))

and ENV (env) =
  | ENVnil (nil)
  | {G:env} {t:ty} ENVcons (t :: G) of (VAL t, ENV G)

fun evalVar {G:env} {t:ty}
  (env: ENV G) (x: VAR (G, t)): VAL t = begin case+ x of
  | VARone () => let val ENVcons (v, _) = env in v end
  | VARshi x => let val ENVcons (_, env) = env in evalVar env x end
end // end of [evalVar]

fun eval {G:env} {t:ty}
  (env: ENV G) (e: EXP (G, t)): VAL t = begin case+ e of
  | EXPvar x => evalVar env x
  | EXPlam (e) => VALclo (env, e)
  | EXPapp (e1, e2) => let
      val VALclo (env', body) = eval env e1
      val v = eval env e2
    in
      eval (ENVcons (v, env')) body
    end
(*
  | EXPtlam {G} {f} e => VALtclo {G} {f} (env, e)
  | EXPtapp e => let
      val VALtclo (env, body) = eval env e
    in
      eval env (body {...})
    end
*)
end // end of [eval]

fun evaluate {t:ty} (e: EXP (nil, t)): VAL t = eval ENVnil e

// ------------------------ additional examples ------------------------

// the example of CPS transformation can be found in CPS.ats in the same
// directory

// the example of closure conversion can be found in ClosureConv.ats in
// the same directory

(* ****** ****** *)

(* end of [ITPT.dats] *)
