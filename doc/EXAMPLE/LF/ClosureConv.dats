//
//
// A typeful implementation of closure conversion
//
//

// January 2005:
// The code is written by Hongwei Xi

// February 2007:
// This code is ported to ATS/Geizella by Hongwei Xi

// March 3rd, 2008
// This code is ported to ATS/Anairiats by Hongwei Xi

(* ****** ****** *)

infixr ->> ::

datasort ty = int | ->> of (ty, ty)
datasort env = nil | :: of (ty, env)

datatype VAR (env, ty) =
  | {G:env} {t:ty} VARone (t :: G, t)
  | {G:env} {t1,t2:ty} VARshi (t2 :: G, t1) of VAR (G, t1)

datatype EXP (env, ty) =
  | {G:env} {t:ty} EXPvar (G, t) of VAR (G, t)
  | {G:env} {t1,t2:ty} EXPlam (G, t1 ->> t2) of EXP (t1 :: G, t2)
  | {G:env} {t1,t2:ty} EXPapp (G, t2) of (EXP (G, t1 ->> t2), EXP (G, t1))

typedef EXP0 (t: ty) = EXP (nil, t)

datatype EXP' (env, ty) =
  | {G:env} {t:ty} EXPvar' (G, t) of VAR (G, t)
  | {G1,G2:env} {t1,t2:ty}
      EXPclo' (G1, t1 ->> t2) of (EXP' (t1 :: G2, t2), ENV (G1, G2))
  | {G1:env} {t1,t2:ty} EXPapp' (G1, t2) of (EXP' (G1, t1 ->> t2), EXP' (G1, t1))

and ENV (env, env) =
  | {G:env} ENVnil (G, nil)
  | {G1,G2:env} {t:ty} ENVcons (G1, t :: G2) of (EXP' (G1, t), ENV (G1, G2))

typedef EXP0' (t:ty) = EXP' (nil, t)

fun EXPone' {G:env} {t:ty} (): EXP' (t :: G, t) = EXPvar' (VARone)

typedef SUB (G1:env, G2:env) = {t:ty} VAR(G1,t) -> EXP'(G2,t)

val nilSub =
  (lam x => case+ x of VARone _ =/=> () | VARshi _ =/=> ())
  : SUB (nil, nil)

val idSub = (lam x => EXPvar' x)
  : {G:env} SUB (G, G)

val shiSub = (lam x => EXPvar' (VARshi x))
  : {G:env} {t:ty} SUB (G, t :: G)

//

fun subst {G1,G2:env} {t:ty}
  (sub: SUB(G1,G2)) (e: EXP'(G1,t)): EXP'(G2,t) = begin
  case+ e of
  | EXPvar' x => sub (x)
  | EXPclo' (code, env) => EXPclo' (code, substEnv sub env)
  | EXPapp' (e1, e2) => EXPapp' (subst sub e1, subst sub e2)
end // end of [subst]

and subLam {G1,G2:env} {t:ty}
  (sub: SUB (G1,G2)): SUB (t::G1,t::G2) = begin
  lam x => case+ x of
    | VARone () => EXPvar' (VARone)
    | VARshi x' => subst (shiSub {..} {..}) (sub x')
end // end of [subLam]

and substEnv {G1,G2,G3:env}
  (sub: SUB(G1,G2)) (e: ENV(G1,G3)): ENV(G2,G3) = begin
  case+ e of
  | ENVnil () => ENVnil
  | ENVcons (e, env) => ENVcons (subst sub e, substEnv sub env)
end // end of [substEnv]

fun expShi {G:env} {t1,t2:ty} (e: EXP' (G, t1)): EXP' (t2 :: G, t1) =
  subst (shiSub {..} {..}) e

fun envShi {G1,G2:env} {t:ty}
  (env: ENV (G1, G2)): ENV (t :: G1, G2) = begin
  case+ env of
  | ENVnil () => ENVnil
  | ENVcons (e, env) => ENVcons (expShi e, envShi env)
end // end of [envShi]

fun envLam {G1,G2:env} {t:ty}
  (env: ENV (G1, G2)): ENV (t :: G1, t :: G2) =
  ENVcons (EXPone' (), envShi env)

fun cc {G1,G2:env} {t:ty}
  (sub: SUB (G1, G2), env: ENV (G2, G2), e: EXP (G1, t))
  : EXP' (G2, t) = begin case+ e of
  | EXPvar i => sub i
  | EXPlam e => EXPclo' (cc (subLam sub, envLam env, e), env)
  | EXPapp (e1, e2) => EXPapp' (cc (sub, env, e1), cc (sub, env, e2))
end // end of [cc]

fun cc0 {t:ty} (e: EXP0 (t)): EXP0' t = cc (nilSub, ENVnil, e)

//

// some simple examples:

fun EXPone {G:env} {t:ty} (): EXP (t :: G, t) =
  EXPvar (VARone)

fun EXPtwo {G:env} {t1,t2:ty} (): EXP (t1 :: t2 :: G, t2) =
  EXPvar (VARshi VARone)

fun EXPthree {G:env} {t1,t2,t3:ty} (): EXP (t1 :: t2 :: t3 :: G, t3) =
  EXPvar (VARshi (VARshi VARone))

// lam x. x
val ans1 = cc0 (EXPlam {nil} {int(),int()} (EXPone ()))

// lam x. lam y. y (x)
val ans2 = cc0 (EXPlam (EXPlam (EXPapp (EXPone (), EXPtwo ()))))

// lam x. lam y. lam z. z (x (y))
val ans3 = cc0 (EXPlam (EXPlam (EXPlam (EXPapp (EXPone (), EXPapp (EXPtwo (), EXPthree ()))))))

// lam x. lam y. x (y) (y)
val ans4 = cc0 (EXPlam (EXPlam (EXPapp (EXPapp (EXPtwo (), EXPone ()), EXPone ()))))

(* ****** ****** *)

(* end of [ClosureConv.dats] *)
