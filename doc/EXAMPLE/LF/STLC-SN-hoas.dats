//
//
// simply typed lambda calculus is strongly-normalizing
// This formalization uses higher-order abstract syntax for lambda-terms.
//
//

// April 2006:
// It is completed by Kevin Donnelly and Hongwei Xi

// January 2007:
// It is ported to ATS/Geizella by Hongwei Xi

// March 3rd, 2008
// It is ported to ATS/Anairiats by Hongwei Xi

(* ****** ****** *)

// This is a proof based on Tait's method of reducibility predicates

(* Syntax *)
// definition of sort 'tm' of HOAS terms
dataparasort tm =
  TMcst of () | TMlam of (tm -> tm) | TMapp of (tm, tm)

// definition of sort 'tp' for simple types with a base type
datasort tp = TPbas | TPfun of (tp, tp) 

// sort for typing contexts (really, typed substitutions)
datasort ctx = CTXnil | CTXcons of (tm, tp, ctx)

(* Reduction *)
// small-step reduction
// RED(t, t', n) represents n length derivations of t --> t'
dataprop
RED (tm, tm, int) =
  | {f,f':tm->tm} {s:nat}
    REDlam (TMlam f, TMlam f', s+1) of {x:tm} RED (f x, f' x, s)
  | {t1,t2,t1':tm} {s:nat}
    REDapp1 (TMapp (t1, t2), TMapp (t1', t2), s+1) of RED (t1, t1', s)
  | {t1,t2,t2':tm} {s:nat}
    REDapp2 (TMapp (t1, t2), TMapp (t1, t2'), s+1) of RED (t2, t2', s)
  | {f:tm->tm;t:tm} REDapp3 (TMapp (TMlam f, t), f t, 0)
// end of [RED]

propdef RED0 (t:tm, t':tm) = [s:nat] RED (t, t', s)

(* Type Assignment *)
// dynamic type representation (and index for structural induction on types)
// TP (t) represents derivations of the judgment 't type'
dataprop TP (tp) =
  | TPbas (TPbas)
  | {T1,T2:tp} TPfun (TPfun (T1,T2)) of (TP T1, TP T2)
// end of [TP]

// Context lookup, INCTX(t, T, G) represents (t: T) \in G
dataprop
INCTX (tm,tp,ctx) = 
  | {G:ctx} {t:tm} {T:tp} INCTXone(t,T,CTXcons(t,T,G))
  | {G:ctx} {t,t':tm} {T,T':tp}
      INCTXshi(t,T,CTXcons(t',T',G)) of INCTX(t,T,G)
// end of [INCTX]

// typing derivations in first-order representation
// DER(G, t, T, n) represents n length derivations of G |- t: T
dataprop
DER (ctx,tm,tp,int) =
  | {G:ctx} {t:tm} {T:tp}
    DERvar(G,t,T,0) of (INCTX (t,T,G), TP T)
  | {G:ctx} {f:tm->tm} {T1,T2:tp} {n:nat}
    DERlam (G,TMlam f, TPfun(T1,T2), n+1) of
      (TP T1, {x:tm} DER (CTXcons (x,T1,G), f x, T2, n))
  | {G:ctx} {t1,t2:tm} {T1,T2:tp} {n1,n2:nat} 
    DERapp (G, TMapp(t1,t2), T2, n1+n2+1) of
      (DER (G, t1, TPfun(T1,T2), n1), DER (G, t2, T1, n2))
// end of [DER]

propdef DER0 (G:ctx,t:tm,T:tp) = [n:nat] DER (G, t, T, n)

(* Strong Normalization *)
dataprop
SN (tm, int) =
  | {t:tm} {n:nat} SN (t,n) of 
      {t':tm} (RED0(t, t') -<fun> [n':nat | n' < n] SN(t',n'))
// end of [SN]

propdef SN0(t:tm) = [n:nat] SN(t, n)

//

// If everything t reduces to is SN then t is SN.  We leave this as an
// unproven lemma because it is obvious, but has a complicated formal proof.
extern prval backwardSN :
  {t:tm} ({t':tm} RED0 (t, t') -<fun> SN0 t') -<fun> SN0 t

// SN is closed under reduction
prfn forwardSN {t,t':tm} {n:nat}
  (sn :SN(t, n), red :RED0(t, t')): [n':nat | n' < n] SN(t', n') =
  let prval SN fsn = sn in fsn red end

(* Reducibility *)
// reducibility
dataprop R (tm, tp) = 
  | {t:tm} Rbas(t, TPbas) of SN0(t)
  | {t:tm} {T1,T2:tp}
      Rfun (t, TPfun(T1, T2)) of {t1:tm} R(t1, T1) -<fun> R(TMapp(t, t1), T2)
// end of [R]

// sequence of redubility predicates for a substitution
dataprop RS (ctx) =
  | {G:ctx} {t:tm} {T:tp} RScons(CTXcons(t, T, G)) of (R(t, T), RS G)
  | RSnil (CTXnil)
// end of [RS]

// definition of neutral terms
dataprop NEU (tm) =
  | NEUcst(TMcst) | {t1,t2:tm} NEUapp(TMapp(t1, t2))
// end of [NEU]

prfun
lamSN {f:tm->tm;t:tm} {n:nat} .<n>.
  (sn: SN (f t, n)): SN (TMlam f, n) = let
  prval SN fsn = sn
  prfn fsn' {t':tm}
    (rd: RED0 (TMlam f, t')):<> [n':nat | n' < n] SN (t', n') = let
    prval REDlam {f,f'} frd = rd
  in
    lamSN {f',t} (fsn (frd {t}))
  end // end of [fsn']
in
  SN (fsn')     
end // end of [lamSN]

//

prfun
appSN1 {t1,t2:tm} {n:nat} .<n>.
  (sn: SN(TMapp (t1, t2), n)): SN0 t1 = let
  prval SN fsn = sn
  prfn fsn1 {t1':tm} (red: RED0 (t1, t1')): SN0 (t1') =
    appSN1 (fsn (REDapp1 (red)))
in
  backwardSN (fsn1)
end // end of [appSN1]

//

(* CR 2 *)
// R is preserved by forward reduction
prfun cr2 {t,t':tm} {T:tp} .<T>.
  (r: R(t, T), rd: RED0(t, t')): R(t', T) = begin
  case+ r of
  | Rbas sn => Rbas (forwardSN (sn, rd))
  | Rfun {t} {T1,T2} (fr) => begin
      Rfun (lam (r) =<> cr2 {..} {T2} (fr r, REDapp1 rd))
    end
end // end of [cr2]

(* CR 1 *)
// R implies strongly normalizing
prfun cr1 {t:tm} {T:tp} .<T,0>.
  (tp: TP T, pf: R(t, T)): SN0(t) = begin
  case+ pf of
  | Rbas sn => sn
  | Rfun fr => let
      prval TPfun (tp1, tp2) = tp
    in
      appSN1 (cr1 (tp2, fr (cr4 tp1)))
    end
end // end of [cr1]

(* CR4 *)
and cr4 {T:tp} .<T,2>. (tp: TP T): R (TMcst, T) = let
  prfn fr {t:tm} (red: RED0 (TMcst, t)): R (t, T) =
    case+ red of REDlam _ =/=> ()
in
  cr3 (NEUcst (), tp, fr)
end // end of [cr4]

(* CR 3*)
// (NEU t and for all t' such that t --> t' we have R(t',T)) implies R(t,T)
and cr3 {t:tm} {T:tp} .<T,1>. (
    neu: NEU(t)
  , tp: TP T
  , fr: {t':tm} RED0(t, t') -<fun> R(t', T)
  ) : R(t, T) = let
  prval fsn = lam {t':tm} => lam (red:RED0(t, t')) =<> cr1 (tp, fr red)
  prval sn = backwardSN fsn
in
  case+ tp of
  | TPbas() => Rbas sn
  | TPfun {T1,T2} (tp1, tp2) => let
      prfn fr {t1:tm} (r1: R (t1, T1)): R (TMapp (t, t1), T2) =
        cr3a (tp1, tp2, neu, r1, cr1 (tp1, r1), fr)
    in
      Rfun fr
    end
end // end of [cr3]

and cr3a {t,t1:tm} {T1,T2:tp} {m:nat} .<T2, m+2>. (
    tp1: TP T1
  , tp2: TP T2
  , neu: NEU t
  , r1: R (t1, T1)
  , sn1: SN (t1, m)
  , f: {t':tm} RED0 (t, t') -<fun> R (t', TPfun (T1, T2))
  ) : R (TMapp (t, t1), T2) = let
  prfn ff {tt:tm} (rd: RED0 (TMapp (t, t1), tt))
    : R (tt, T2) = begin case+ rd of
    | REDapp1 rd => begin
        let prval Rfun fr = f rd in fr (r1) end
      end
    | REDapp2 rd => let
        prval SN fsn1 = sn1
      in
        cr3a (tp1, tp2, neu, cr2 (r1, rd), fsn1 rd, f)
      end
    | REDapp3 _ =/=> begin
        case+ neu of NEUcst() => () | NEUapp() => ()
      end
  end // end of [ff]
in
  cr3  (NEUapp, tp2, ff)
end // end of [cr3a]

// application reducibility lemma

prfun reduceFun {f:tm->tm; t:tm} {T1,T2:tp} {n1,n2:nat} .<n1+n2>. (
    tp1: TP T1
  , tp2: TP T2
  , sn1: SN(TMlam f, n1)
  , sn2: SN(t, n2)
  , r1: R(t, T1)
  , fr2: {t:tm} R(t, T1) -<fun> R(f t, T2)
  ) : R(TMapp(TMlam f, t), T2) = let
  prfn fr {t':tm} (red:RED0 (TMapp(TMlam f, t), t')): R(t', T2) =
    case+ red of
    | REDapp1(red') => let
        prval REDlam {f,f'} fred' = red'
        prfn fr2' {t:tm} (r: R(t, T1)): R(f' t, T2) =
          cr2(fr2 r, fred'{t})
      in
        reduceFun(tp1, tp2, forwardSN(sn1, red'), sn2, r1, fr2')
      end
    | REDapp2(red') => begin
        reduceFun(tp1, tp2, sn1, forwardSN(sn2, red'), cr2(r1, red'), fr2)
      end
    | REDapp3 {f, t} () => fr2 {t} (r1)
in
  cr3(NEUapp, tp2, fr)
end // end of [reduceFun]

// the abstraction rule is sound with respect to reducible terms
prfn absSound {f:tm->tm} {T1,T2:tp} (
    tp1: TP T1
  , tp2: TP T2
  , frr: {t:tm} R(t, T1) -<fun> R(f t, T2)
  ) : R(TMlam f, TPfun(T1, T2)) = let
  prfn fr {t:tm} (rt: R(t, T1)): R(TMapp(TMlam f, t), T2) =
    let 
      prval snt = cr1(tp1, rt)
      prval snf = lamSN {f,TMcst} (cr1 (tp2, frr {TMcst} (cr4 tp1)))
    in
      reduceFun (tp1, tp2, snf, snt, rt, frr)
    end
in
  Rfun(fr)
end // end of [absSound]

// pick specified reducibility predicate from the sequence
prfun rGet {G:ctx} {t:tm} {T:tp} .<G>.
  (i: INCTX (t,T,G), rs: RS G): R(t,T) = case+ i of
  | INCTXone() => (case+ rs of RScons(r,_) => r)
  | INCTXshi i => (case+ rs of RScons(_,rs) => rGet(i, rs))

// The assigned type can be extracted from a derivation
prfun der2tp {G:ctx} {t:tm} {T:tp} {n:nat} .<n>.
  (der: DER(G,t,T,n)): TP T = begin
  case+ der of
  | DERvar (_, tp) => tp
  | DERlam (tp1, derf) => let
      prval tp2 = der2tp (derf {..})
    in
      TPfun (tp1,tp2)
    end
  | DERapp (der1, der2) => let
      prval TPfun (_, tp2) = der2tp der1
    in
      tp2
    end
end // end of [der2tp]

// main lemma
prfun reduceLemma
  {G:ctx} {t:tm} {T:tp} {n:nat} .<n>.
  (der: DER(G,t,T,n), rs: RS G): R (t, T) = begin case+ der of
  | DERvar (i,_) => rGet (i, rs)
  | DERlam {..} {f} {T1,T2} {..} (_, derf) => let 
      prval TPfun {T1,T2} (tp1, tp2) = der2tp der
      prfn gr {t:tm} (r: R(t,T1)): R(f t, T2) = let
        prval rs' = RScons (r, rs)       
        prval r' = reduceLemma (derf{t}, rs')
      in
        r'
      end
      prfn fr {t:tm} (r: R(t,T1)): R(TMapp(TMlam f, t), T2) = let    
        prval lamf_red = absSound {f} (tp1, tp2, gr)
        prval Rfun(red_imp) = lamf_red
      in
        red_imp r
      end
    in
      Rfun fr
    end
  | DERapp (der1, der2) => let
      prval r1 = reduceLemma(der1, rs)
      prval Rfun fr = r1
      prval r2 = reduceLemma(der2, rs)
    in
      fr r2
    end
end // end of [reduceLemma]

// all typable terms are reducible
prfn reduce {t:tm} {T:tp} (der: DER0 (CTXnil, t, T)): R (t,T) =
  reduceLemma(der, RSnil())

// the final payoff
prfn normalize {t:tm} {T:tp} (der: DER0 (CTXnil, t, T)): SN0 t =
  cr1(der2tp der, reduce der)

(* ****** ****** *)

(* end of [STLC-SN-hoas.dats] *)
