// A formalization of simply typed call-by-value lambda-calculus with
// products and fixed-points that makes use of an encoding that combines
// higher-order abstract syntax with first-order abstract syntax.

// May 2005:
// it is completed by Kevin Donnelly and Hongwei Xi

// January 2007:
// It is ported to ATS/Geizella by Hongwei Xi

// July 2008
// Ported to ATS/Anairiats by Hongwei Xi
// (* some cases are still missing *)

(* ****** ****** *)

datasort tm = TMunit
            | TMtup of (tm, tm)
            | TMfst of tm
            | TMsnd of tm
            | TMlam of (tm -> tm)
            | TMapp of (tm, tm)
            | TMfix of (tm -> tm)
// end of [datasort]

datasort tms = TMSnil | TMScons of (tm, tms)

datasort tp = TPfun of (tp,tp) | TPtup of (tp,tp) | TPunit

datasort ctx = CTXnil | CTXcons of (tm, tp, ctx)

dataprop INCTX (tm,tp,ctx,int) = 
  | {G:ctx} {t:tm} {T:tp} INCTXone(t,T,CTXcons(t,T,G),0)
  | {G:ctx} {t,t':tm} {T,T':tp} {n:nat}
      INCTXshi(t,T,CTXcons(t',T',G),n+1) of INCTX(t,T,G,n)

dataprop DER (ctx,tm,tp,int) =
  | {G:ctx} {t:tm} {T:tp} {n:nat} DERvar(G,t,T,0) of INCTX(t,T,G,n)

  | {G:ctx} DERunit(G,TMunit,TPunit,0)

  | {G:ctx} {t1,t2:tm} {T1,T2:tp} {n1,n2:nat}
      DERtup (G,TMtup(t1,t2), TPtup (T1,T2),n1+n2+1) of
        (DER (G,t1,T1,n1), DER (G,t2,T2,n2))

  | {G:ctx} {t:tm} {T1,T2:tp} {n:nat}
      DERfst (G, TMfst t, T1, n+1) of DER (G, t, TPtup (T1, T2), n)

  | {G:ctx} {t:tm} {T1,T2:tp} {n:nat}
      DERsnd (G, TMsnd t, T2, n+1) of DER (G, t, TPtup (T1, T2), n)

  | {G:ctx} {f:tm->tm} {T1,T2:tp} {n:nat}
      DERlam (G,TMlam f, TPfun(T1,T2), n+1) of
        ({x:tm} DER (CTXcons (x,T1,G), f x, T2, n))

  | {G:ctx} {t1,t2:tm} {T1,T2:tp} {n1,n2:nat}
      DERapp (G, TMapp(t1,t2), T2, n1+n2+1) of
        (DER (G, t1, TPfun(T1,T2),n1), DER(G,t2,T1,n2))

  | {G:ctx} {f:tm->tm} {T:tp} {n:nat}
      DERfix(G,TMfix f, T, n+1) of
        ({x:tm} DER (CTXcons (x,T,G), f x, T, n))

propdef DER0 (G:ctx,t:tm,T:tp) = [n:nat] DER (G, t, T, n)

dataprop IN (tm,tms,int) =
  | {t:tm} {ts:tms} INone(t,TMScons(t,ts),0)
  | {ts:tms} {t,t':tm} {n:nat} INshi(t, TMScons (t', ts),n+1) of IN(t, ts, n)

datatype TERM (tms,tm,int) =
  | {ts:tms} {t:tm} {T:tp} {n:nat} TERMvar (ts,t,n) of (IN (t,ts,n) | int n)

  | {ts:tms} TERMunit (ts, TMunit, 0)

  | {ts:tms} {t1,t2:tm} {n1,n2:nat}
      TERMtup (ts, TMtup(t1,t2), n1+n2+1) of (TERM (ts,t1,n1), TERM (ts,t2,n2))

  | {ts:tms} {t:tm} {n:nat} TERMfst (ts, TMfst t, n+1) of TERM (ts, t, n)

  | {ts:tms} {t:tm} {n:nat} TERMsnd (ts, TMsnd t, n+1) of TERM (ts, t, n)

  | {ts:tms} {f: tm->tm} {n:nat}
      TERMlam (ts, TMlam f, n+1) of ({x:tm} TERM(TMScons(x, ts), f x, n))

  | {ts:tms} {t,t':tm} {n1,n2:nat} 
      TERMapp (ts, TMapp(t,t'), n1+n2+1) of (TERM(ts,t,n1),TERM(ts,t',n2))

  | {ts:tms} {f:tm->tm} {n:nat}
      TERMfix (ts, TMfix f, n+1) of ({x:tm} TERM(TMScons(x, ts), f x, n))

typedef TERM0 (ts:tms,t:tm) = [n:nat] TERM(ts,t,n)

//

dataprop EVAL(tm,tm,int) =
  | EVALunit(TMunit,TMunit,0)

  | {t1,t2,v1,v2:tm} {n1,n2:nat}
      EVALtup (TMtup(t1,t2), TMtup (v1,v2), n1+n2+1) of (EVAL(t1,v1,n1),EVAL(t2,v2,n2))

  | {t,v1,v2:tm} {n:nat}
      EVALfst (TMfst t, v1, n+1) of EVAL (t, TMtup (v1, v2), n)

  | {t,v1,v2:tm} {n:nat}
      EVALsnd (TMsnd t, v2, n+1) of EVAL (t, TMtup (v1, v2), n)

  | {f:tm->tm} EVALlam(TMlam f, TMlam f, 0)

  | {t1,t2,t1':tm; f:tm->tm; v,v':tm} {m,n,p:nat}
      EVALapp(TMapp(t1,t2),v',m+n+p+1) of
        (EVAL(t1,TMlam f,m), EVAL(t2,v,n), EVAL(f v,v',p))

  | {f:tm->tm; v:tm} {n:nat}
      EVALfix(TMfix f, v, n+1) of (EVAL(f (TMfix f), v, n))

propdef EVAL0(t1:tm,t2:tm) = [n:nat] EVAL(t1,t2,n)

dataprop ISVAL(tm,int) =
  | ISVALunit(TMunit,0)
  | {t1,t2:tm} {n1,n2:nat}
       ISVALtup(TMtup(t1,t2), n1+n2+1) of (ISVAL(t1,n1),ISVAL(t2,n2))
  | {f: tm->tm} ISVALlam(TMlam f,0)

propdef ISVAL0(t:tm) = [n:nat] ISVAL(t,n)

//

prfun lemma00 {t,v:tm} {n:nat} .<n>. (pf: EVAL (t, v, n)): ISVAL0 v =
  case+ pf of
    | EVALunit () => ISVALunit()
    | EVALtup(pf1,pf2) => ISVALtup(lemma00 pf1, lemma00 pf2)
    | EVALfst pf => let prval ISVALtup (pf1, _) = lemma00 pf in pf1 end
    | EVALsnd pf => let prval ISVALtup (_, pf2) = lemma00 pf in pf2 end
    | EVALlam () => ISVALlam()
    | EVALapp (_, _, pf3) => lemma00 pf3
    | EVALfix pf => lemma00 pf

prfun lemma01 {t:tm} {n:nat} .<n>. (pf: ISVAL(t,n)): EVAL (t, t, n) =
  case+ pf of
    | ISVALlam() => EVALlam()
    | ISVALunit() => EVALunit()
    | ISVALtup(pf1,pf2) => EVALtup(lemma01 pf1, lemma01 pf2)

datatype VAL (tm) =
  | VALunit(TMunit)
  | {t1,t2:tm} VALtup(TMtup(t1,t2)) of (VAL(t1),VAL(t2))
  | {ts:tms} {f:tm->tm} {m,n:nat}
       VALclo (TMlam f) of (ENV (ts, m), {t:tm} TERM (TMScons (t, ts), f t, n))

and ENV (tms,int) =
  | ENVnil (TMSnil,0)

  | {ts:tms} {t:tm} {T:tp} {n:nat}
      ENVlamcons (TMScons (t, ts),n+1) of (ISVAL0 t |  ENV (ts,n), VAL (t))

  | {ts:tms} {f:tm->tm} {T:tp} {n:nat}
      ENVfixcons (TMScons (TMfix f, ts), n+1) of
        (ENV(ts,n), {t:tm} (TERM0 (TMScons (t, ts), f t)))


typedef ENV0 (ts:tms) = [n:nat] ENV(ts,n)

dataprop FLIPCTX(ctx,ctx,int) =
  | {G:ctx} {t,t':tm} {T,T':tp}
      FLIPCTXone (CTXcons(t,T,CTXcons(t',T',G)),CTXcons(t',T',CTXcons(t,T,G)),0)
  | {G,G':ctx} {t:tm} {T:tp} {n:nat}
      FLIPCTXshi (CTXcons(t,T,G),CTXcons(t,T,G'),n+1) of FLIPCTX(G,G',n)

dataprop ADDCTX(ctx,ctx,int) =
  | {G:ctx} {t:tm} {T:tp} ADDCTXone(G,CTXcons(t,T,G),0)
  | {G,G':ctx} {t:tm} {T:tp} {n:nat}
      ADDCTXshi(CTXcons(t,T,G),CTXcons(t,T,G'),n+1) of ADDCTX(G,G',n)
//

prfun weaken
  {G,G':ctx} {t,t':tm} {T,T':tp} {n1,n2:nat} .<n1,n2>.
  (der: DER(G,t,T,n1), pf:ADDCTX(G,G',n2)): DER(G',t,T,n1) =
  $effmask_exn begin case der of
  | DERvar i => begin case+ pf of
      | ADDCTXone() => DERvar(INCTXshi i)
      | ADDCTXshi(pf') => begin case+ i of
        | INCTXone() => DERvar(INCTXone())
        | INCTXshi i' => weaken (weaken (DERvar i', pf'), ADDCTXone)
        end
    end
  | DERunit() => DERunit()
  | DERtup(der1,der2) => DERtup (weaken (der1,pf),weaken (der2,pf))
  | DERfst der => DERfst (weaken (der, pf))
  | DERsnd der => DERsnd (weaken (der, pf))
(*
  | DERlam(derf) => DERlam (lam {x:tm} => weaken (derf{x}, ADDCTXshi pf))
*)
  | DERapp(der1,der2) => DERapp (weaken (der1,pf), weaken (der2,pf))
(*
  | DERfix(derf) => DERfix (lam {x:tm} => weaken (derf{x}, ADDCTXshi pf))
*)
end // end of [weaken]

//

prfun exch
  {G,G':ctx} {t:tm} {T:tp} {n1,n2:nat} .<n1,n2>.
  (der: DER(G,t,T,n1), pf:FLIPCTX (G,G',n2)): DER(G',t,T,n1) =
  $effmask_exn begin case der of
  | DERvar(i) => begin case+ pf of
    | FLIPCTXone() => begin case+ i of
      | INCTXone() => DERvar(INCTXshi(INCTXone))
      | INCTXshi(i') => begin case+ i' of
        | INCTXone() => DERvar(INCTXone)
        | INCTXshi i'' => DERvar(INCTXshi(INCTXshi i''))
        end
      end
    | FLIPCTXshi(pf') => begin case+ i of
      | INCTXone () => DERvar (INCTXone)
      | INCTXshi i => weaken (exch (DERvar i, pf'), ADDCTXone)
      end
    end
  | DERunit() => DERunit
  | DERtup(der1,der2) => DERtup (exch (der1,pf), exch (der2,pf))
  | DERfst der => DERfst (exch (der, pf))
  | DERsnd der => DERsnd (exch (der, pf))
(*
  | DERlam(derf) => DERlam(lam {x:tm} => exch (derf{x}, FLIPCTXshi pf))
*)
  | DERapp(der1,der2) => DERapp (exch (der1,pf), exch (der2,pf))
(*
  | DERfix(derf) => DERfix(lam {x:tm} => exch (derf{x}, FLIPCTXshi pf))
*)
end // end of [exch]

//

prfun subst
  {G:ctx} {t,t':tm} {T,T':tp} {n1,n2:nat} .<n1>. 
  (der1:DER (CTXcons(t,T,G),t',T',n1), der2:DER (G,t,T,n2)) 
  : DER0 (G,t',T') = $effmask_exn begin case der1 of
  | DERvar i => (case+ i of INCTXone () => der2 | INCTXshi i' => DERvar i')
  | DERunit () => DERunit ()
  | DERtup(der11,der12) => DERtup (subst (der11, der2), subst (der12, der2))
  | DERfst der1 => DERfst (subst (der1,der2))
  | DERsnd der1 => DERsnd (subst (der1,der2))
(*
  | DERlam derf =>
      DERlam(lampara {x:tm} => subst(exch(derf{x},FLIPCTXone()),weaken(der2,ADDCTXone)))
*)
  | DERapp (der11,der12) => DERapp(subst(der11,der2),subst(der12,der2))
(*
  | DERfix derf =>
      DERfix(lampara {x:tm} => subst(exch(derf{x},FLIPCTXone()),weaken(der2,ADDCTXone)))
*)
end // end of [subst]

//

prfn fixLemma {f:tm->tm} {T:tp} {m:nat}
     (der:DER(CTXnil,TMfix f, T, m)) : DER0(CTXnil,f(TMfix f), T) =
  case+ der of
    | DERfix (derf) => subst (derf {TMfix f}, der)
    | DERvar (inctx) =/=> (case+ inctx of INCTXone() => () | INCTXshi _ => ())
// end of [fixLemma]

fun evalVar {ts:tms} {t:tm} {T:tp} {n0,n:nat}
   (i: IN (t, ts, n), der: DER0(CTXnil, t, T) |  env: ENV (ts,n0), n: int n)
  : [v:tm] (EVAL0(t,v), DER0(CTXnil, v, T) | VAL v) =
  if n ieq 0 then let
    prval INone () = i
  in 
    case+ env of
    | ENVlamcons(pf | _, v) => (lemma01 pf, der | v) 
    | ENVfixcons(env', tf) => let
        prval INone() = i
        prval der = fixLemma der
        val (pf, der | v) = eval (der | tf{...}, env)
      in
        (EVALfix pf, der | v)
      end
  end else let
    prval INshi i = i
  in 
    case+ env of
    | ENVlamcons(_ | env, _) => evalVar (i, der | env, n isub 1)
    | ENVfixcons(env, termf) => evalVar (i, der | env, n isub 1)
  end // end of [if]
(* end of [evalVar] *)

and eval {ts:tms} {t:tm} {T:tp}
  (der: DER0 (CTXnil,t,T) | e: TERM0 (ts,t), env: ENV0 ts)
  : [v:tm] (EVAL0(t,v), DER0 (CTXnil,v,T) | VAL v) = begin
  case e of
  | TERMvar (i | n) => let
      val (pf, der | v) = (evalVar (i, der | env, n))
    in
       (pf, der | v) 
    end // end of [TERMvar]

  | TERMunit () => (EVALunit(), der | VALunit())

  | TERMtup (e1,e2) => begin case+ der of
    | DERtup(der1,der2) => let
        val (pf1, der1 | v1) = eval (der1 | e1, env)
        val (pf2, der2 | v2) = eval (der2 | e2, env)
      in
        (EVALtup(pf1,pf2), DERtup(der1,der2) | VALtup(v1,v2))
      end
    | DERvar(i) =/=> (case+ i of INCTXone () => () | INCTXshi _ => ())
    end // end of [TERMtup]

  | TERMfst e => begin case+ der of
    | DERfst der => let
        val (pf, der | v) = eval (der | e, env)
      in
        case+ v of
        | VALtup (v1, _) => begin case+ der of
          | DERtup (der1, _) => (EVALfst pf, der1 | v1)
          | DERvar i =/=> (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        | VALclo _ =/=> begin case+ der of
          | DERlam _ => ()
          | DERvar i => (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        | VALunit () =/=> begin case+ der of
          | DERunit () => ()
          | DERvar i => (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
      end
    | DERvar(i) =/=> (case+ i of INCTXone () => () | INCTXshi _ => ())
    end // end of [TERMfst]

  | TERMsnd e => begin case+ der of
    | DERsnd der => let
        val (pf, der | v) = eval (der | e, env)
      in
        case+ v of
        | VALtup (_, v2) => begin case+ der of
          | DERtup (_, der2) => (EVALsnd pf, der2 | v2)
          | DERvar i =/=> (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        | VALclo _ =/=> begin case+ der of
          | DERlam _ => ()
          | DERvar i => (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        | VALunit () =/=> begin case+ der of
          | DERunit () => ()
          | DERvar i => (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        end
    | DERvar(i) =/=> (case+ i of INCTXone () => () | INCTXshi _ => ())
    end // end of [TERMsnd]

  | TERMlam ef => (EVALlam, der  | VALclo (env, ef))
  | TERMapp (e1, e2) => begin case+ der of
    | DERapp (der1, der2) => let
        val (pf1, der1 | v1) = eval (der1 | e1, env)
      in
        case+ v1 of
        | VALclo (env0, ef1) => let
            val (pf2, der2 | v2) = eval (der2 | e2, env)
          in
            case+ der1 of
            | DERlam(derf) => let
                val (pf3, der | v) = eval (
                  subst (derf{...}, der2) | ef1{...}, ENVlamcons (lemma00 pf2 | env0, v2)
                )
              in
                (EVALapp (pf1, pf2, pf3), der | v)
              end
            | DERvar(i) =/=> (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        | VALtup _ =/=> begin case+ der1 of
          | DERtup _ => ()
          | DERvar i => (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
        | VALunit () =/=> begin case+ der1 of
          | DERunit () => ()
          | DERvar i => (case+ i of INCTXone() => () | INCTXshi _ => ())
          end
      end
    | DERvar(i) =/=> (case+ i of INCTXone () => () | INCTXshi _ => ())
    end // end of [TERMapp]
  | TERMfix {..} {f} {..} ef => begin case+ der of
    | DERfix (derf) => let
        val (pf, der | v) = eval
          (fixLemma der | ef{...}, ENVfixcons {..} {f} {...} (env, ef))
      in
        (EVALfix pf, der | v)
      end
    | DERvar(i) =/=> (case+ i of INCTXone() => () | INCTXshi _ => ())
    end // end of [TERMfix]
end // end of [eval]

// Voila! Isn't this nice :)

fun evaluate {t:tm} {T:tp} (der: DER0 (CTXnil,t,T) | e: TERM0 (TMSnil,t))
  : [v:tm] (EVAL0(t,v), DER0 (CTXnil,v,T) | VAL v) =
  eval (der | e, ENVnil)

(* ****** ****** *)

(* end of [STLC-hoas.dats] *)
