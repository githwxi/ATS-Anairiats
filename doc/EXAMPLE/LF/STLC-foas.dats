// A formalization of simply typed call-by-value lambda-calculus with
// products and fixed-points that makes use of an encoding based on
// a form of first-order abstract syntax. This example was meant to
// gain some experience with first-order abstract syntax.

// August 2005:
// It is completed by Hongwei Xi.

// January 2007:
// It is ported to ATS/Geizella by Hongwei Xi

datasort tm =
  | tmvar of int
  | tmlam of tm
  | tmapp of (tm, tm)

dataprop tmshi (tm, tm, int) =
  | {i,l:nat | i >= l} TMSHIvargte (tmvar i, tmvar (i+1), l)

  | {i,l:nat | i < l} TMSHIvarlt (tmvar i, tmvar i, l)

  | {t,t':tm} {l:nat}
      TMSHIlam (tmlam t, tmlam t', l) of tmshi (t, t', l+1)

  | {t1,t2,t1',t2':tm} {l:nat}
      TMSHIapp (tmapp (t1, t2), tmapp (t1', t2'), l) of
        (tmshi (t1, t1', l), tmshi (t2, t2', l))

datasort tms = tmsnil | tmsmore of (tms, tm)

dataprop subshi (tms, tms) =
  | SUBSHInil (tmsnil, tmsnil)
  | {ts,ts':tms} {t,t':tm}
      SUBSHImore (tmsmore (ts, t), tmsmore (ts', t')) of
        (subshi (ts, ts'), tmshi (t, t', 0))

extern prval subshiFun : {th:tms}[th':tms] subshi (th, th')

//

dataprop TMI (int, tm, tms) =
  | {ts:tms} {t:tm} TMIone (0, t, tmsmore (ts, t))
  | {ts:tms} {t,t':tm} {i:int | i > 0}
      TMIshi (i, t, tmsmore (ts, t')) of TMI (i-1, t, ts)

dataprop subst (tms, tm, tm) =
  | {ts:tms} {t:tm} {i:nat} SUBvar (ts, tmvar i, t) of TMI (i, t, ts)

  | {ts,ts':tms} {t,t':tm}
      SUBlam (ts, tmlam t, tmlam t') of
        (subshi (ts, ts'), subst (tmsmore (ts', tmvar 0), t, t'))

  | {ts:tms} {t1,t2,t1',t2':tm}
      SUBapp (ts, tmapp (t1, t2), tmapp (t1', t2')) of
        (subst (ts, t1, t1'), subst (ts, t2, t2'))

propdef subst1 (t1:tm, t2:tm, t3:tm) = subst (tmsmore (tmsnil, t1), t2, t3)

//

datasort tp = tpunit | tpfun of (tp, tp)

datasort tps = tpsnil | tpsmore of (tps, tp)

dataprop TPI (int, tp, tps) =
  | {Ts:tps} {T:tp} TPIone (0, T, tpsmore (Ts, T))
  | {Ts:tps} {T,T':tp} {i:int | i > 0}
      TPIshi (i, T, tpsmore (Ts, T')) of TPI (i-1, T, Ts)

//

dataprop DER (tps, tm, tp, int) =
  | {G:tps} {T:tp} {i:nat} DERvar (G, tmvar i, T, 0) of TPI (i, T, G)

  | {G:tps} {T1,T2:tp} {t:tm} {s:nat}
      DERlam (G, tmlam t, tpfun (T1, T2), s+1) of DER (tpsmore (G, T1), t, T2, s)

  | {G:tps} {T1,T2:tp} {t1,t2:tm} {s1,s2:nat}
      DERapp (G, tmapp (t1, t2), T2, s1+s2+1) of
        (DER (G, t1, tpfun (T1, T2), s1), DER (G, t2, T1, s2))

propdef DER0 (G:tps, t:tm, T:tp) = [s:nat] DER (G, t, T, s)

dataprop INS (tps, tp, int, tps) =
  | {G:tps} {T:tp} INSone (G, T, 0, tpsmore (G, T))
  | {G1,G2:tps} {T,T':tp} {i:nat}
      INSshi (tpsmore (G1, T'), T, i+1, tpsmore (G2, T')) of INS (G1, T, i, G2)

prfun dershiVarGte {G,G':tps} {T,T':tp} {i1,i2:nat | i1 >= i2} .<i1>.
     (i1: TPI (i1, T, G), i2: INS (G, T', i2, G')): TPI (i1+1, T, G') =
  case+ i2 of
    | INSone () => TPIshi i1
    | INSshi i2 => let prval TPIshi i1 = i1 in TPIshi (dershiVarGte (i1, i2)) end

prfun dershiVarLt {G,G':tps} {T,T':tp} {i1,i2:nat | i1 < i2} .<i1>.
     (i1: TPI (i1, T, G), i2: INS (G, T', i2, G')): TPI (i1, T, G') =
  let prval INSshi i2 = i2 in
     case+ i1 of
       | TPIone () => TPIone ()
       | TPIshi i1 => TPIshi (dershiVarLt (i1, i2))
  end

//

prfun dershi {G,G':tps} {T,T':tp} {t,t':tm} {i,s:nat} .<s>.
     (d: DER (G, t, T, s), i: INS (G, T', i, G'), pf: tmshi (t, t', i))
    : DER (G', t', T, s) =
  case+ d of
    | DERvar {G} {T} {i'} (i') => begin
        sif i' >= i then
           let prval TMSHIvargte () = pf in DERvar (dershiVarGte (i', i)) end
        else
           let prval TMSHIvarlt () = pf in DERvar (dershiVarLt (i', i)) end
      end

    | DERlam d =>
        let prval TMSHIlam pf = pf in
          DERlam (dershi (d, INSshi i, pf))
        end

    | DERapp (d1, d2) =>
        let prval TMSHIapp (pf1, pf2) = pf in
           DERapp (dershi (d1, i, pf1), dershi (d2, i, pf2))
        end

//

prfun dershi0 {G:tps} {T,T':tp} {t,t':tm} {s:nat} .<s>.
     (d: DER (G, t, T, s),  pf: tmshi (t, t', 0))
    : DER (tpsmore (G, T'), t', T, s) = dershi (d, INSone (), pf)

//

dataprop DERS (tps, tms, tps, int) =
  | {G0:tps} DERSnil (G0, tmsnil, tpsnil, 0)
  | {G0,G:tps} {T:tp} {ts:tms} {t:tm} {s,n:nat}
      DERSmore (G0, tmsmore (ts, t), tpsmore (G, T), n+1) of
        (DERS (G0, ts, G, n), DER (G0, t, T, s))

propdef DERS0 (G1:tps, ts:tms, G2:tps) = [n:nat] DERS (G1, ts, G2, n)

prfun dersshi {G0,G:tps} {T:tp} {ts,ts':tms} {n:nat} .<n>.
     (ds: DERS (G0, ts, G, n), pf: subshi (ts, ts'))
    : DERS (tpsmore (G0, T), ts', G, n) =
  case+ (ds, pf) of
    | (DERSnil (), SUBSHInil ()) => DERSnil ()
    | (DERSmore (ds, d), SUBSHImore (pf1, pf2)) =>
        DERSmore (dersshi (ds, pf1), dershi0 (d, pf2))
//

prfun lemma10 {G1,G2:tps} {T:tp} {ts:tms} {t,t':tm} {i:nat} .<i>.
     (ds: DERS0 (G1, ts, G2), i1: TPI (i, T, G2), i2: TMI (i, t', ts))
    : DER0 (G1, t', T) =
  case+ i1 of
    | TPIone () => begin
        let
           prval TMIone () = i2
           prval DERSmore (_, d) = ds
        in
           d
        end
      end

    | TPIshi i1 => begin
        let
           prval TMIshi i2 = i2
           prval DERSmore (ds, _) = ds
        in
           lemma10 (ds, i1, i2)
        end
      end

prfun lemma10' {G1,G2:tps} {T:tp} {ts:tms} {t:tm} {i:nat} .<i>.
  (ds: DERS0 (G1, ts, G2), i: TPI (i, T, G2)): [t':tm] TMI (i, t', ts) =
  case+ i of
  | TPIone () => let
      prval DERSmore {..} {..} {ts1} {t1} (_, _) = ds
    in
      TMIone {ts1} {t1} ()
    end
  | TPIshi i => begin
      let prval DERSmore (ds, _) = ds in TMIshi (lemma10' (ds, i)) end
    end

//

prfun substLemma {G1,G2:tps} {T:tp} {ts:tms} {t,t':tm} {s:nat} .<s>.
     (ds: DERS0 (G1, ts, G2), d: DER (G2, t, T, s), pf: subst (ts, t, t'))
    : DER0 (G1, t', T) =
  case+ d of
    | DERvar i1 => begin
        let prval SUBvar i2 = pf in
          lemma10 (ds, i1, i2)
        end
      end

    | DERlam d =>
        let
           prval SUBlam (pf1, pf2) = pf
           prval ds = DERSmore (dersshi (ds, pf1), DERvar (TPIone ()))
        in
           DERlam (substLemma (ds, d, pf2))
        end

    | DERapp (d1, d2) =>
        let prval SUBapp (pf1, pf2) = pf in
           DERapp (substLemma (ds, d1, pf1), substLemma (ds, d2, pf2))
        end

prfn substLemma0 {T1,T2:tp} {t1,t2,t2':tm}
     (d1: DER0 (tpsnil, t1, T1),
      d2: DER0 (tpsmore (tpsnil, T1), t2, T2),
      pf: subst1 (t1, t2, t2')): DER0 (tpsnil, t2', T2) =
  substLemma (DERSmore (DERSnil, d1), d2, pf)

//

dataprop ISV (tm) =
  | {t:tm} ISVlam (tmlam t)

dataprop RED (tm, tm, int) =
  | {t1,t2,t1':tm} {s:nat}
      REDapp1 (tmapp (t1, t2), tmapp (t1', t2), s+1) of RED (t1, t1', s)

  | {t1,t2,t2':tm} {s:nat}
      REDapp2 (tmapp (t1, t2), tmapp (t1, t2'), s+1) of (ISV t1, RED (t2, t2', s))

  | {t,v,t':tm} REDapp3 (tmapp (tmlam t, v), t', 0) of (ISV v, subst1 (v, t, t'))

propdef RED0 (t:tm, t':tm) = [s:nat] RED (t, t', s)

// Subject Reduction Theorem

prfun subjectReduction {T:tp} {t,t':tm} {s:nat} .<s>.
   (d: DER (tpsnil, t, T, s), pf: RED0 (t, t')): DER0 (tpsnil, t', T) =
  case+ pf of
    | REDapp1 pf =>
        let prval DERapp (d1, d2) = d in
          DERapp (subjectReduction (d1, pf), d2)
        end

    | REDapp2 (_, pf) =>
        let prval DERapp (d1, d2) = d in
          DERapp (d1, subjectReduction (d2, pf))
        end

    | REDapp3 (pf1, pf2) =>
        let
           prval DERapp (DERlam d1, d2) = d
        in
            substLemma0 (d2, d1, pf2)
        end

//

dataprop ORELSE (p1: prop, p2: prop) =
  inl (p1, p2) of p1 | inr (p1, p2) of p2

infixl ORELSE

//

prfun substLemma' {G1,G2:tps} {T:tp} {ts:tms} {t:tm} {s:nat} .<s>.
   (ds: DERS0 (G1, ts, G2), d: DER (G2, t, T, s)): [t':tm] subst (ts, t, t') =
  case+ d of
    | DERvar i => SUBvar (lemma10' (ds, i))
    | DERlam d =>
        let
           prval pf1 = subshiFun {ts}
           prval ds = DERSmore (dersshi (ds, pf1), DERvar (TPIone ()))
           prval pf2 = substLemma' (ds, d)
        in
           SUBlam (pf1, pf2)
        end

    | DERapp (d1, d2) => SUBapp (substLemma' (ds, d1), substLemma' (ds, d2))

prfn substLemma0' {T1,T2:tp} {t1,t2:tm}
   (d1: DER0 (tpsnil, t1, T1), d2: DER0 (tpsmore (tpsnil, T1), t2, T2))
  : [t2':tm] subst1 (t1, t2, t2') =
  substLemma' (DERSmore (DERSnil, d1), d2)

// Progress Theorem

prfun progress {T:tp} {t:tm} {s:nat} .<s>.
     (d: DER (tpsnil, t, T, s)): (ISV t) ORELSE [t':tm] RED0 (t, t') = 
  case+ d of
    | DERlam _ => inl (ISVlam)

    | DERapp (d1, d2) => begin case progress d1 of
        | inl pf1_l =>
          let prval ISVlam () = pf1_l in
             case+ progress d2 of
               | inl pf2_l =>
                 let prval DERlam (d1) = d1 in
                    inr (REDapp3 (pf2_l, substLemma0' (d2, d1)))
                 end
               | inr pf2_r => inr (REDapp2 (pf1_l, pf2_r))
          end

        | inr pf1_r => inr (REDapp1 pf1_r)
      end

    | DERvar i =/=> begin
        case+ i of TPIone () => () | TPIshi _ => ()
      end

(* ****** ****** *)

(* end of [STLC-foas.dats] *)
