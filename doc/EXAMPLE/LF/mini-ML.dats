//
// An implementation of mini-ML that is proven to be correct
//

// January 2005:
// It is completed by Hongwei Xi.

// January 2007:
// It is ported to ATS/Geizella by Hongwei Xi.

// March 5th, 2008:
// It is verified by ATS/Anairiats (without any changes being made).

(* ****** ****** *)

datasort tp =
  | TPnat
  | TPfun of (tp, tp)
  | TPtup of (tp, tp)

dataparasort tm = 
  | TMzero
  | TMsucc of tm
  | TMlam of (tm -> tm)
  | TMapp of (tm, tm)
  | TMtup of (tm, tm)
  | TMfst of tm
  | TMsnd of tm
  | TMfix of (tm -> tm)
  | TMcase of (tm, tm, tm -> tm)

datasort ctx = CTXnil | CTXcons of (ctx, tm, tp)

dataprop ISVAL (tm, int) =
  | ISVALzero (TMzero, 0)
  | {e:tm} {n:nat} ISVALsucc (TMsucc e, n+1) of ISVAL (e, n)
  | {f: tm->tm} ISVALlam (TMlam f, 0)
  | {e1,e2:tm} {n1,n2:nat}
      ISVALtup (TMtup (e1, e2), n1+n2+1) of (ISVAL (e1, n1), ISVAL (e2, n2))

propdef ISVAL0 (e: tm) = [n:nat] ISVAL (e, n)

dataprop EVAL (tm, tm, int) =
  | EVALzero (TMzero, TMzero, 0)
  | {e,v:tm} {n:nat} EVALsucc (TMsucc e,TMsucc v, n+1) of EVAL (e, v, n)
  | {f:tm ->tm} EVALlam (TMlam f, TMlam f, 0)
  | {e1:tm; f1:tm->tm; e2,v2,v:tm} {n1,n2,n3:nat} 
      EVALapp(TMapp(e1,e2), v, n1+n2+n3+1) of
        (EVAL(e1, TMlam f1, n1), EVAL(e2, v2, n2), EVAL (f1 v2, v, n3))
  | {e1,v1,e2,v2:tm} {n1,n2:nat}
      EVALtup (TMtup (e1, e2), TMtup (v1, v2), n1+n2+1) of
        (EVAL (e1, v1, n1), EVAL (e2, v2, n2))
  | {e,v1,v2:tm} {n:nat}
      EVALfst (TMfst e, v1, n+1) of EVAL (e, TMtup (v1, v2), n)
  | {e,v1,v2:tm} {n:nat}
      EVALsnd (TMsnd e, v2, n+1) of EVAL (e, TMtup (v1, v2), n)
  | {f:tm->tm; v:tm} {n:nat}
      EVALfix (TMfix f, v, n+1) of EVAL (f (TMfix f), v, n)
  | {e0,e1:tm;f2:tm->tm;v:tm} {n1,n2:nat}
      EVALcase1 (TMcase (e0, e1, f2), v, n1+n2+1) of
        (EVAL (e0, TMzero, n1), EVAL (e1, v, n2))
  | {e0,e1:tm;f2:tm->tm;v0,v:tm} {n1,n2:nat}
      EVALcase2 (TMcase (e0, e1, f2), v, n1+n2+1) of
        (EVAL (e0, TMsucc v0, n1), EVAL (f2 v0, v, n2))

propdef EVAL0 (e1: tm, e2: tm) = [n:nat] EVAL (e1, e2, n)

//

prfun lemma0 {e1,e2:tm} {n:nat} .<n>.
  (pf: EVAL (e1, e2, n)): ISVAL0 (e2) = begin
  case+ pf of
  | EVALzero () => ISVALzero
  | EVALsucc pf => ISVALsucc (lemma0 pf)
  | EVALlam () => ISVALlam
  | EVALapp (_, _, pf) => lemma0 pf
  | EVALtup (pf1, pf2) => ISVALtup (lemma0 pf1, lemma0 pf2)
  | EVALfst (pf) => let prval ISVALtup (pf1, _) = lemma0 pf in pf1 end
  | EVALsnd (pf) => let prval ISVALtup (_, pf2) = lemma0 pf in pf2 end
  | EVALfix (pf) => lemma0 pf
  | EVALcase1 (_, pf) => lemma0 pf
  | EVALcase2 (_, pf) => lemma0 pf
end // end of [lemma0]

prfun lemma1 {e:tm} {n:nat} .<n>.
  (pf: ISVAL (e, n)): EVAL0 (e, e) = begin
  case+ pf of
  | ISVALzero () => EVALzero
  | ISVALsucc pf => EVALsucc (lemma1 pf)
  | ISVALlam () => EVALlam
  | ISVALtup (pf1, pf2) => EVALtup (lemma1 pf1, lemma1 pf2)
end // end of [lemma1]

prfn lemma2 {e:tm}
  (pf: ISVAL0 (TMsucc e)): ISVAL0 (e) =
  let prval ISVALsucc pf = pf in pf end

//

datatype IN (tm,tp,ctx) = 
  | {e:tm} {t:tp} {G:ctx} INone(e,t,CTXcons(G,e,t))
  | {e,e':tm} {t,t':tp} {G:ctx}
      INshi(e,t,CTXcons(G,e',t')) of IN(e,t,G)

datatype DER (ctx,tm,tp) = 
  | {G:ctx} {e:tm} {t:tp} DERvar (G,e,t) of IN (e,t,G)
  | {G:ctx} DERzero(G,TMzero,TPnat)
  | {G:ctx} {e:tm} DERsucc (G,TMsucc e,TPnat) of DER (G,e,TPnat)
  | {G:ctx} {f:tm->tm} {t1,t2:tp} 
      DERlam(G,TMlam f,TPfun(t1,t2)) of ({x:tm} (DER (CTXcons(G,x,t1), f x, t2)))
  | {G:ctx} {e1,e2:tm} {t1,t2:tp}
      DERapp(G,TMapp(e1,e2),t2) of (DER (G,e1,TPfun (t1,t2)),DER (G,e2,t1))
  | {G:ctx} {e1,e2:tm} {t1,t2:tp}
      DERtup(G, TMtup(e1,e2), TPtup (t1,t2)) of (DER (G, e1, t1), DER (G, e2, t2))
  | {G:ctx} {e:tm} {t1,t2:tp}
      DERfst(G, TMfst e, t1) of DER (G, e, TPtup (t1, t2))
  | {G:ctx} {e:tm} {t1,t2:tp}
      DERsnd(G, TMsnd e, t2) of DER (G, e, TPtup (t1, t2))
  | {G:ctx} {f:tm->tm} {t:tp}
      DERfix(G, TMfix f, t) of ({x:tm} (DER (CTXcons(G,x,t), f x, t)))
  | {G:ctx} {e0,e1:tm; f2:tm->tm} {t:tp}
      DERcase (G, TMcase (e0, e1, f2), t) of
        (DER (G, e0, TPnat), DER (G, e1, t), {x:tm} DER (CTXcons(G,x,TPnat), f2 x, t))

datatype ENV (ctx) =
  | ENVnil(CTXnil)
  | {G:ctx} {e:tm} {t:tp}
       ENVlamcons(CTXcons(G,e,t)) of (ISVAL0 e | ENV (G), VAL (e, t))
  | {G:ctx} {f:tm->tm} {t:tp}
       ENVfixcons(CTXcons(G,TMfix f,t)) of
         (ENV (G), {x:tm} (DER (CTXcons(G,x,t), f x, t)))

and VAL (tm, tp) =
  | VALzero (TMzero, TPnat)
  | {e:tm} VALsucc (TMsucc e, TPnat) of VAL (e, TPnat)
  | {G:ctx} {f:tm->tm} {t1,t2:tp}
      VALclo(TMlam f, TPfun (t1, t2)) of 
        (ENV(G), {x:tm} DER(CTXcons(G,x,t1), f x, t2))
  | {G:ctx} {e1,e2:tm} {t1,t2:tp}
      VALtup(TMtup(e1, e2), TPtup(t1, t2)) of (VAL (e1, t1), VAL (e2, t2))

//

(* need to check pattern matching always succeeds *)
fun eval {G:ctx} {e1:tm} {t1:tp}
   (env: ENV G, der: DER(G,e1,t1))
  : [e2:tm] (EVAL0 (e1,e2) | VAL (e2,t1)) = begin
  case+ der of
  | DERvar i => evalVar (env, i)
  | DERzero () => (EVALzero | VALzero)
  | DERsucc der =>
      let val (pf | v) = eval (env, der) in (EVALsucc pf | VALsucc v) end
  | DERlam (fder) => (EVALlam | VALclo (env, fder))
  | DERapp (der1, der2) => let
      val (pf1 | c1) = eval (env, der1)
      val (pf2 | v2) = eval (env, der2)
      val VALclo (env, fder) = c1
      val (pf | v) = eval (ENVlamcons (lemma0 pf2 | env, v2), fder {...})
    in
      (EVALapp (pf1, pf2, pf) | v)
    end
  | DERtup (der1, der2) => let
      val (pf1 | v1) = eval (env, der1)
      val (pf2 | v2) = eval (env, der2)
    in
      (EVALtup (pf1, pf2) | VALtup (v1, v2))
    end
  | DERfst (der) => let
      val+ (pf | VALtup (v1, _)) = eval (env, der)
    in
      (EVALfst pf | v1)
    end
  | DERsnd (der) => let
      val+ (pf | VALtup (_, v2)) = eval (env, der)
    in
      (EVALsnd pf | v2)
    end
  | DERfix {G} {f} {t} (fder) => let
      val (pf | v) = eval (ENVfixcons {G} {f} {t} (env, fder), fder {...})
    in
      (EVALfix pf | v)
    end
  | DERcase (der0, der1, fder2) => let
      val (pf0 | v0) = eval (env, der0)
    in
      case+ v0 of
      | VALzero () => let
          val (pf1 | v1) = eval (env, der1)
        in
          (EVALcase1 (pf0, pf1) | v1)
        end
      | VALsucc v0 => let
          val (pf2 | v2) =
            eval (ENVlamcons (lemma2 (lemma0 pf0) | env, v0), fder2 {...})
        in
          (EVALcase2 (pf0, pf2) | v2)
        end
    end
end // end of [eval]

and evalVar {G:ctx} {e1:tm} {t:tp}
  (env: ENV G, i: IN(e1,t,G))
  : [e2:tm] (EVAL0 (e1, e2) | VAL (e2, t)) = begin
  case+ i of
  | INone () => begin case+ env of
    | ENVlamcons (pf | _, v) => (lemma1 pf | v)
    | ENVfixcons {G} {f} {t} (env, fder) => let
          val (pf | v) = eval (ENVfixcons {G} {f} {t} (env, fder), fder)
        in
          (EVALfix pf | v)
         end
    end
  | INshi i => begin case+ env of
    | ENVlamcons (_ | env, _) => evalVar (env, i)
    | ENVfixcons (env, _) => evalVar (env, i)
  end
end // end [of evalVar]

typedef DER0 (e:tm, t:tp) = DER (CTXnil, e, t)

fun evaluate {e:tm} {t:tp}
  (der: DER0 (e,t)): [e':tm] (EVAL0 (e,e') | VAL(e',t)) = begin
  eval (ENVnil, der)
end // end of [evaluate]

(* ****** ****** *)

(* end of [miniML.dats] *)
