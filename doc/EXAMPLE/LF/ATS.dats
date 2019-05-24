
(*
 *
 * A proof of the type soundness for the core of ATS is encoded as follows.
 * In addition, A verified implementation of an evaluator for ATS is given,
 * where closures are used for representing values.
 *
 *)

// October 2005:
// It is implemented by Dengping Zhu and Hongwei Xi

// February 2007:
// It is ported to ATS/Geizella by Hongwei Xi

datasort srt = // sort representation
  | srtbool // bool
  | srttype // type
  | srtfun of (srt, srt) // function sort

datasort stm = // static term representation
  | stmff // false
  | stmtt // true
  | stmunit // unit
  | stmfun of (stm, stm) // function type
  | stmgua of (stm, stm) // guarded type
  | stmass of (stm, stm) // asserting type
  | stmuni of (srt, stm -> stm) // universally quantified type
  | stmexi of (srt, stm -> stm) // existentially quantified type
  | stmsub of (stm, stm) // subtyping

datasort sds = sdsnone | sdsmore of (sds, stm, srt)

dataprop STMEQ (stm, stm) = {s:stm} STMEQ (s, s)

datasort stms = stmsnone | stmsmore of (stms, stm)

dataprop SDI (stm, srt, sds) =
  | {sds:sds; s:stm; st:srt} SDIone (s, st, sdsmore (sds, s, st))
  | {sds:sds; s:stm; s':stm; st:srt; st':srt}
      SDIshi (s, st, sdsmore (sds, s', st')) of SDI (s, st, sds)

// static derivation (assigning sorts to static terms)

dataprop SD (sds, stm, srt, int) =
  | {sds:sds; s:stm; st:srt}
      SDvar (sds, s, st, 0) of SDI (s, st, sds)
  | {sds: sds} SDff (sds, stmff, srtbool, 0)
  | {sds: sds} SDff (sds, stmtt, srtbool, 0)
  | {sds: sds} SDunit (sds, stmunit, srttype, 0)
  | {sds: sds; T1: stm; T2: stm; m:nat; n:nat}
      SDfun (sds, stmfun (T1, T2), srttype, m+n+1) of
        (SD (sds, T1, srttype, m), SD (sds, T2, srttype, n))
  | {sds: sds; P: stm; T: stm; m:nat; n:nat}
      SDgua (sds, stmgua (P, T), srttype, m+n+1) of
        (SD (sds, P, srtbool, m), SD (sds, T, srttype, n))
  | {sds: sds; P: stm; T: stm; m:nat; n:nat}
      SDass (sds, stmass (P, T), srttype, m+n+1) of
        (SD (sds, P, srtbool, m), SD (sds, T, srttype, n))
  | {sds: sds; F: stm->stm; st:srt; m:nat}
      SDuni (sds, stmuni (st, F), srttype, m+1) of
        {s:stm} (SD (sdsmore (sds, s, st), F s, srttype, m))
  | {sds: sds; F: stm->stm; st:srt; m:nat}
      SDexi (sds, stmexi (st, F), srttype, m+1) of
        {s:stm} (SD (sdsmore (sds, s, st), F s, srttype, m))
  | {sds: sds; T1: stm; T2: stm; m: nat; n: nat}
      SDsub (sds, stmsub (T1, T2), srtbool, m+n+1) of 
        (SD (sds, T1, srttype, m), SD (sds, T2, srttype, n))

propdef SD0 (sds: sds, s: stm, a: srt) = [m:nat] SD (sds, s, a, m)

datasort dtm = // dynamic term representation
  | dtmlam of (dtm -> dtm)
  | dtmapp of (dtm, dtm)
  | dtmigua of dtm
  | dtmegua of dtm
  | dtmiass of dtm
  | dtmeass of (dtm, dtm->dtm)
  | dtmiuni of dtm
  | dtmeuni of dtm
  | dtmiexi of dtm
  | dtmeexi of (dtm, dtm->dtm)

datasort dds = ddsnone | ddsmore of (dds, dtm, stm)

dataprop DTMEQ (dtm, dtm) = {t:dtm} DTMEQ (t, t)

dataprop DDI (dtm, stm, dds) =
  | {dds:dds; x:dtm; a:stm} DDIone (x, a, ddsmore (dds, x, a))
  | {dds:dds; x:dtm; x':dtm; a:stm; a':stm}
      DDIshi (x, a, ddsmore (dds, x', a')) of DDI (x, a, dds)

// Constraints (regularity rules)

sta CS: (sds, stms, stm) -> prop

extern prval cs_reg_tt : {sds:sds; bs:stms} CS (sds, bs, stmtt)
extern prval cs_reg_ff :
  {sds:sds; bs:stms; b:stm} CS (sds, bs, stmff) -<> CS (sds, bs, b)

extern prval cs_var_thin :
  {sds:sds; bs:stms; s:stm; st:srt; b:stm} 
    CS (sds, bs, b) -<> CS (sdsmore (sds, s, st), bs, b)

extern prval cs_prop_thin :
  {sds:sds; bs:stms; b:stm; b':stm} 
    CS (sds, bs, b) -<> CS (sds, stmsmore (bs, b'), b)

extern prval cs_cut : {sds:sds; bs:stms; b:stm; b':stm} 
    (CS (sds, bs, b'), CS (sds, stmsmore (bs, b'), b)) -<> CS (sds, bs, b)
       
extern prval cs_refl : {sds:sds; bs:stms; s:stm} CS (sds, bs, stmsub (s, s))

extern prval cs_trans :
  {sds:sds; bs:stms; s1:stm; s2:stm; s3:stm} 
    (CS (sds, bs, stmsub (s1, s2)), CS (sds, bs, stmsub (s2, s3))) -<>
    CS (sds, bs, stmsub (s1, s3))

extern prval cs_fun :
  {sds:sds; bs:stms; s1:stm; s2:stm; s3:stm; s4:stm} 
    (CS (sds, bs, stmsub (s3, s1)), CS (sds, bs, stmsub (s2, s4))) -<>
    CS (sds, bs, stmsub (stmfun (s1, s2), stmfun (s3, s4)))
 
extern prval cs_gua :
  {sds:sds; bs:stms; s1:stm; s2:stm; b1:stm; b2:stm}       
    (CS (sds, stmsmore (bs, b2), stmsub (s1, s2)),
     CS (sds, stmsmore (bs, b2), b1)) -<>
    CS (sds, bs, stmsub (stmgua (b1, s1), stmgua (b2, s2)))

extern prval cs_ass :
  {sds:sds; bs:stms; s1:stm; s2:stm; b1:stm; b2:stm} 
    (CS (sds, stmsmore (bs, b1), stmsub (s1, s2)),
     CS (sds, stmsmore (bs, b1), b2)) -<>
    CS (sds, bs, stmsub (stmass (b1, s1), stmass (b2, s2)))

extern prval cs_uni :
  {sds:sds; bs:stms; F1:stm->stm; F2:stm->stm; s:stm; st:srt} 
    CS (sdsmore (sds, s, st), bs, stmsub (F1 s, F2 s)) -<>
    CS (sds, bs, stmsub (stmuni (st, F1), stmuni (st, F2)))

extern prval cs_exi :
  {sds:sds; bs:stms; s1:stm->stm; s2:stm->stm; s:stm; a:srt}
    CS (sdsmore (sds, s, a), bs, stmsub (s1 s, s2 s)) -<>
    CS (sds, bs, stmsub (stmexi (a, s1), stmexi (a, s2)))

// subtyping relation is a special kind of constraint. 

propdef SUB (sds: sds, bs: stms, T1: stm, T2: stm) = 
  CS (sds, bs, stmsub (T1, T2))


(* 
 * Typing derivation: 
 *
 * Note: We use 0 and 1 to differetiate [DDsub] with all other rules since
 * [DDsub] is not syntax-directed. The inverion lemma below proves that for
 * any derivation, we can always find a derivation where the last applied
 * rule is not [DDsub]. In addition, the height of the new derivation does
 * not exceed that of the original one.
 *
 *) 

dataprop DD (sds, stms, dds, dtm, stm, int, int) = 
  | {sds:sds; bs:stms; ts:dds; t:dtm; s:stm; s':stm; k:nat; i:two}
      DDsub (sds, bs, ts, t, s', k+1, 0) of 
	(DD (sds, bs, ts, t, s, k, i), SUB (sds, bs, s, s'))

  | {sds:sds; bs:stms; ds:dds; t:dtm; s:stm; s':stm} 
      DDvar (sds, bs, ds, t, s', 0, 1) of 
        (DDI(t, s, ds), SUB (sds, bs, s, s')) 
  
  | {sds:sds; bs:stms; ts:dds; f:dtm->dtm; s:stm; s':stm; m:nat; i:two} 
      DDlam (sds, bs, ts, dtmlam f, stmfun (s, s'), m+1, 1) of 
        ({t:dtm} DD (sds, bs, ddsmore (ts, t, s), f t, s', m, i))
  
  | {sds:sds; bs:stms; ts:dds; t:dtm; t':dtm; s:stm; s':stm; m:nat; n:nat; 
     i1:two; i2:two}
      DDapp (sds, bs, ts, dtmapp (t, t'), s', m+n+1, 1) of 
        (DD (sds, bs, ts, t, stmfun (s, s'), m, i1), 
	 DD (sds, bs, ts, t', s, n, i2))
 
  | {sds:sds; bs:stms; b:stm; ds:dds; t:dtm; s:stm; m:nat; i:two}
      DDigua (sds, bs, ds, dtmigua t, stmgua (b, s), m+1, 1) of 
        DD (sds, stmsmore (bs, b), ds, t, s, m, i)

  | {sds:sds; bs:stms; b:stm; ds:dds; t:dtm; s:stm; m:nat; i:two}
      DDegua (sds, bs, ds, dtmegua t, s, m+1, 1) of
        (DD (sds, bs, ds, t, stmgua (b, s), m, i), CS (sds, bs, b))

  | {sds:sds; bs:stms; b:stm; ds:dds; t:dtm; s:stm; m:nat; i:two}
      DDiass (sds, bs, ds, dtmiass t, stmass (b, s), m+1, 1) of 
        (DD (sds, bs, ds, t, s, m, i), CS (sds, bs, b))

  | {sds:sds; bs:stms; b:stm; ts:dds; t:dtm; f:dtm->dtm; 
     s:stm; s':stm; m:nat; n:nat; i1:two; i2:two}
      DDeass (sds, bs, ts, dtmeass (t, f), s', m+n+1, 1) of 
        (DD (sds, bs, ts, t, stmass (b, s), m, i1), 
         {x:dtm} (DD (sds, stmsmore (bs, b), ddsmore (ts, x, s), f x, s', n, i2)))

  | {sds:sds; bs:stms; ts:dds; t:dtm; f:stm->stm; st:srt; m:nat; i:two}
      DDiuni (sds, bs, ts, dtmiuni t, stmuni (st, f), m+1, 1) of 
	{s:stm} DD (sdsmore (sds, s, st), bs, ts, t, f s, m, i)

  | {sds:sds; bs:stms; ts:dds; t:dtm; s:stm; f:stm->stm; st:srt; m:nat; i:two}
      DDeuni (sds, bs, ts, dtmeuni t, f s, m+1, 1) of 
	(DD (sds, bs, ts, t, stmuni (st, f), m, i), SD0 (sds, s, st))

  | {sds:sds; bs:stms; ts:dds; t:dtm; f:stm->stm; s:stm; st:srt; m:nat; i:two}
      DDiexi (sds, bs, ts, dtmiexi t, stmexi (st, f), m+1, 1) of 
        (DD (sds, bs, ts, t, f s, m, i), SD0 (sds, s, st))
 
  | {sds:sds; bs:stms; ts:dds; t1:dtm; f2:dtm->dtm; s2:stm; 
     f:stm->stm; a:srt; m:nat; n:nat; i1:two; i2:two}
      DDeexi (sds, bs, ts, dtmeexi (t1, f2), s2, m+n+1, 1) of 
	(DD (sds, bs, ts, t1, stmexi (a, f), m, i1), 
         {x:dtm; s1:stm}
           (DD (sdsmore (sds, s1, a), bs, ddsmore (ts, x, f s1), f2 x, s2, n, i2)))

propdef DD0 (sds:sds, bs:stms, ds:dds, t:dtm, s:stm, i:int) = 
  [m:nat] DD (sds, bs, ds, t, s, m, i)

// admissiable rules: needed for inversion lemma. 

extern prval admvar: {sds:sds; bs:stms; ds:dds; t:dtm; s:stm; s':stm; s'':stm} 
   (DDI(t, s, ds), SUB (sds, bs, s, s'), SUB (sds, bs, s', s'')) -<> 
   DD (sds, bs, ds, t, s'', 0, 1) 

extern prval admfun: {sds:sds; bs:stms; ds:dds; f:dtm->dtm; s1:stm; s2:stm; 
  s:stm; m:nat; i:two; x:dtm}
    (DD (sds, bs, ddsmore (ds, x, s1), f x, s2, m, i), 
     CS (sds, bs, stmsub (stmfun (s1, s2), s))) -<>
    DD (sds, bs, ds, dtmlam (f), s, m+1, 1)

extern prval admapp: {sds:sds; bs:stms; ds:dds; f:dtm; s1:stm; s2:stm; m:nat; 
  i1:two; i2:two; s3:stm; t:dtm} 
    (DD (sds, bs, ds, f, stmfun (s1, s2), m, i1),
     DD0 (sds, bs, ds, t, s1, i2),  
     SUB (sds, bs, s2, s3)) -<> 
    DD (sds, bs, ds, dtmapp (f, t), s3, m+1, 1)

extern prval admigua: {sds:sds; bs:stms; ds:dds; b:stm; t:dtm; s:stm; s':stm;
  m:nat; i:two}
    (DD (sds, stmsmore (bs, b), ds, t, s, m, i), 
     CS (sds, bs, stmsub (stmgua (b, s), s'))) -<>
    DD (sds, bs, ds, dtmigua (t), s', m+1, 1)

extern prval admegua: {sds:sds; bs:stms; ds:dds; f:dtm; s:stm; s':stm;
  m:nat;i1:two; b:stm} 
    (DD (sds, bs, ds, f, stmgua (b, s), m, i1),
     CS (sds, bs, b),  
     SUB (sds, bs, s, s')) -<> 
    DD (sds, bs, ds, dtmegua (f), s', m+1, 1)

extern prval admiass: {sds:sds; bs:stms; ds:dds; b:stm; t:dtm; s:stm; s':stm;
  m:nat; i:two}
    (DD (sds, bs, ds, t, s, m, i),
     CS (sds, bs, b),  
     CS (sds, bs, stmsub (stmass (b, s), s'))) -<>
    DD (sds, bs, ds, dtmiass (t), s', m+1, 1)

extern prval admiuni: {sds:sds; bs:stms; ds:dds; t:dtm; s:stm; a:srt; 
  s1:stm->stm; s':stm; m:nat; i:two}
    (DD (sdsmore (sds, s, a), bs, ds, t, s1 s, m, i),
     CS (sds, bs, stmsub (stmuni (a, s1), s'))) -<>
    DD (sds, bs, ds, dtmiuni (t), s', m+1, 1)

extern prval admeuni: {sds:sds; bs:stms; ts:dds; t:dtm; s:stm; s':stm; 
  f:stm->stm; a:srt; m:nat; i:two}
    (DD (sds, bs, ts, t, stmuni (a, f), m, i), SD0 (sds, s, a), 
     CS (sds, bs, stmsub (f s, s'))) -<> 
   DD (sds, bs, ts, dtmeuni t, s', m+1, 1)

extern prval admiexi: {sds:sds; bs:stms; ts:dds; t:dtm; F:stm->stm; st:srt; 
  m:nat; i:two; s:stm; s':stm}
    (DD (sds, bs, ts, t, F s, m, i), SD0 (sds, s, st),
     SUB (sds, bs, stmexi (st, F), s')) -<>
    DD (sds, bs, ts, dtmiexi t, s', m+1, 1)

(*
 *
 * Inversion lemma :
 *
 * Given any derivation, we can find a derivation where the last rule
 * applied is not DDsub. In addition, the height of the new derivation is
 * less than or equal to the height of the original derivation.
 *
 *)

prfun inversion {sds:sds; bs:stms; ds:dds; t:dtm; s:stm; m:nat; i:two} .<m>.
     (pf: DD (sds, bs, ds, t, s, m, i))
    : [n:nat | n <= m] DD (sds, bs, ds, t, s, n, 1) = 
   case+ pf of
     | DDsub (pf1, pf2) => begin  
         case+ pf1 of
           | DDvar (pf11, pf12) => admvar (pf11, pf12, pf2)  
           | DDlam pf1 => admfun (pf1, pf2)
           | DDapp (pf11, pf12) => admapp (pf11, pf12, pf2)
           | DDigua pf1 => admigua (pf1, pf2)
           | DDegua (pf11, pf12) => admegua (pf11, pf12, pf2)             
           | DDiass (pf11, pf12) => admiass (pf11, pf12, pf2) 
           | DDeass (pf11, pf12) => 
               DDeass (pf11, lam {x:dtm} => DDsub (pf12 {x}, cs_prop_thin pf2))
           | DDiuni (pf11) => admiuni (pf11, pf2)
           | DDeuni (pf11, pf12) => admeuni (pf11, pf12, pf2)
           | DDiexi (pf11, pf12) => admiexi (pf11, pf12, pf2)
           | DDeexi (pf11, pf12) => 
               DDeexi (pf11, lam {x:dtm; s1:stm} =>
                                DDsub (pf12 {x, s1}, cs_var_thin pf2))

           | DDsub (pf11, pf12) => 
               let 
                  prval pf11' = inversion pf1 
               in 
                  case+ pf11' of 
	            | DDvar (pf11, pf12) => admvar (pf11, pf12, pf2)  
                    | DDlam pf1 => admfun (pf1, pf2)
		    | DDapp (pf11, pf12) => admapp (pf11, pf12, pf2)
	            | DDigua pf11 => admigua (pf11, pf2)
	            | DDegua (pf11, pf12) => admegua (pf11, pf12, pf2)             

	            | DDiass (pf11, pf12) => admiass (pf11, pf12, pf2) 

                    | DDeass (pf11, pf12) => 
	                DDeass (pf11, lam {x:dtm} => DDsub (pf12 {x}, cs_prop_thin pf2))

	            | DDiuni (pf11) => admiuni (pf11, pf2)

	            | DDeuni (pf11, pf12) => admeuni (pf11, pf12, pf2)

	            | DDiexi (pf11, pf12) => admiexi (pf11, pf12, pf2)

	            | DDeexi (pf11, pf12) => 
	                DDeexi (pf11, lam {x:dtm; s1:stm} =>
                                         DDsub (pf12 {x, s1}, cs_var_thin pf2))
               end  
       end

     | _ =>> pf
    
// value definition

dataprop ISV (dtm, int) = // [ISV t]: t is a value
  | {f: dtm -> dtm} ISVlam (dtmlam f, 0)
  | {t: dtm} ISVigua (dtmigua t, 0)
  | {v: dtm; n:nat} ISViass (dtmiass v, n+1) of ISV (v, n)
  | {t: dtm} ISViuni (dtmiuni t, 0)
  | {v: dtm; n:nat} ISViexi (dtmiexi v, n+1) of ISV (v, n)

propdef ISV0 (t:dtm) = [n:nat] ISV (t, n)

// some properties on values

prfn isv_fun_lemma {v:dtm; s1:stm; s2:stm}
    (pf: ISV0 v, dd: DD0 (sdsnone, stmsnone, ddsnone, v, stmfun (s1, s2), 1))
   : [f:dtm->dtm] DTMEQ (v, dtmlam f) =
  case+ (pf, dd) of
    | (ISVlam (), _) => DTMEQ ()
    | (_, DDvar (i, _)) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
    | (_, _) =/=>> ()

prfn isv_gua_lemma {v:dtm; s1:stm; s2:stm}
    (pf: ISV0 v, dd: DD0 (sdsnone, stmsnone, ddsnone, v, stmgua (s1, s2), 1))
   : [t:dtm] DTMEQ (v, dtmigua t) =
  case+ (pf, dd) of
    | (ISVigua (), _) => DTMEQ ()
    | (_, DDvar (i, _)) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
    | (_, _) =/=>> ()

prfn isv_ass_lemma {v:dtm; s1:stm; s2:stm}
    (pf: ISV0 v, dd: DD0 (sdsnone, stmsnone, ddsnone, v, stmass (s1, s2), 1))
   : [t:dtm] DTMEQ (v, dtmiass t) =
  case+ (pf, dd) of
    | (ISViass _, _) => DTMEQ ()
    | (_, DDvar (i, _)) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
    | (_, _) =/=>> ()

prfn isv_uni_lemma {v:dtm; F:stm->stm; st:srt}
    (pf: ISV0 v, dd: DD0 (sdsnone, stmsnone, ddsnone, v, stmuni (st, F), 1))
   : [t:dtm] DTMEQ (v, dtmiuni t) =
  case+ (pf, dd) of
    | (ISViuni (), _) => DTMEQ ()
    | (_, DDvar (i, _)) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
    | (_, _) =/=>> ()

prfn isv_exi_lemma {v:dtm; F:stm->stm; st:srt}
    (pf: ISV0 v, dd: DD0 (sdsnone, stmsnone, ddsnone, v, stmexi (st, F), 1))
   : [t:dtm] DTMEQ (v, dtmiexi t) =
  case+ (pf, dd) of
    | (ISViexi _, _) => DTMEQ ()
    | (_, DDvar (i, _)) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
    | (_, _) =/=>> ()

// The single-step evaluation relation

dataprop EV (dtm, dtm, int) = 

  | {t:dtm; f:dtm->dtm}
      EVapp1 (dtmapp (dtmlam f, t), f t, 0) of ISV0 (t)
       
  | {t1:dtm; t2:dtm; t1':dtm; n:nat}
      EVapp2 (dtmapp (t1, t2), dtmapp (t1', t2), n+1) of
        EV (t1, t1', n)

  | {t1:dtm; t2:dtm; t2':dtm; n:nat}
      EVapp3 (dtmapp (t1, t2), dtmapp (t1, t2'), n+1) of
        (ISV0 (t1), EV (t2, t2', n))

  | {t:dtm; t':dtm; v:dtm; m:nat}
      EVegua1 (dtmegua t, dtmegua t', m+1) of (EV (t, t', m))

  | {t:dtm} EVegua2 (dtmegua (dtmigua t), t, 0)  

  | {t:dtm; t':dtm; m:nat} 
      EViass (dtmiass t, dtmiass t', m+1) of EV (t, t', m)

  | {t1:dtm; t2:dtm->dtm; t1':dtm; m:nat}
      EVeass1 (dtmeass (t1, t2), dtmeass (t1', t2), m+1) of
        EV (t1, t1', m)

  | {t:dtm->dtm; v:dtm}
      EVeass2 (dtmeass (dtmiass v, t), t v, 0) of ISV0 (v)

  | {t:dtm; t':dtm; m:nat} 
      EVeuni1 (dtmeuni t, dtmeuni t', m+1) of EV (t, t', m) 

  | {t:dtm; t':dtm} 
      EVeuni2 (dtmeuni (dtmiuni t'), t', 0)  

  | {t:dtm; t':dtm; m:nat}
      EViexi (dtmiexi t, dtmiexi t', m+1) of EV (t, t', m) 

  | {t1:dtm; t2:dtm->dtm; t1':dtm;  m:nat}
      EVeexi1 (dtmeexi (t1, t2), dtmeexi (t1', t2), m+1) of
        EV (t1, t1', m)

  | {t:dtm->dtm; v:dtm}
      EVeexi2 (dtmeexi (dtmiexi v, t), t v, 0) of ISV0 (v)
  
propdef EV0 (t:dtm, t':dtm) = [m:nat] EV (t, t', m)

// The many-step evaluation relation

dataprop EVS (dtm, dtm, int) =
  | {t:dtm} EVSnil (t, t, 0) 
  | {t:dtm; t1:dtm; t2:dtm; n:nat}
      EVScons (t, t2, n+1) of (EV0 (t, t1), EVS (t1, t2, n))

propdef EVS0 (t1:dtm, t2:dtm) = [n:nat] EVS (t1, t2, n)

prfun evs_app2 {t1:dtm; t2:dtm; t:dtm; n:nat} .<n>.
     (pf: EVS (t1, t2, n)): EVS (dtmapp (t1, t), dtmapp (t2, t), n) =
  case+ pf of
    | EVSnil () => EVSnil ()
    | EVScons (pf1, pf2) => EVScons (EVapp2 pf1, evs_app2 pf2)

prfun evs_app3 {t:dtm; t1:dtm; t2:dtm; n:nat} .<n>.
     (pf1: ISV0 t, pf2: EVS (t1, t2, n)): EVS (dtmapp (t, t1), dtmapp (t, t2), n) =
  case+ pf2 of
    | EVSnil () => EVSnil ()
    | EVScons (pf21, pf22) => EVScons (EVapp3 (pf1, pf21), evs_app3 (pf1, pf22))

prfun evs_egua1 {t:dtm; t':dtm; n:nat} .<n>.
     (pf: EVS (t, t', n)): EVS (dtmegua t, dtmegua t', n) =
  case+ pf of 
    | EVSnil () => EVSnil () 
    | EVScons (pf1, pf2) => EVScons (EVegua1 pf1, evs_egua1 (pf2)) 

prfun evs_iass {t:dtm; t':dtm; n:nat} .<n>.
     (pf: EVS (t, t', n)): EVS (dtmiass t, dtmiass t', n) =
  case+ pf of 
    | EVSnil () => EVSnil () 
    | EVScons (pf1, pf2) => EVScons (EViass pf1, evs_iass (pf2)) 

prfun evs_eass1 {t:dtm; t':dtm; t1:dtm->dtm; n:nat} .<n>.
     (pf: EVS (t, t', n)): EVS (dtmeass (t, t1),  dtmeass (t', t1), n) =
  case+ pf of 
    | EVSnil () => EVSnil () 
    | EVScons (pf1, pf2) => EVScons (EVeass1 pf1, evs_eass1 (pf2)) 

prfun evs_euni1 {t:dtm; t':dtm; n:nat} .<n>.
     (pf: EVS (t, t', n)): EVS (dtmeuni t, dtmeuni t', n) =
  case+ pf of 
    | EVSnil () => EVSnil () 
    | EVScons (pf1, pf2) => EVScons (EVeuni1 pf1, evs_euni1 (pf2)) 

prfun evs_iexi {t:dtm; t':dtm; n:nat} .<n>.
     (pf: EVS (t, t', n)): EVS (dtmiexi t, dtmiexi t', n) =
  case+ pf of 
    | EVSnil () => EVSnil () 
    | EVScons (pf1, pf2) => EVScons (EViexi pf1, evs_iexi (pf2)) 

prfun evs_eexi1 {t:dtm; t':dtm; t1:dtm->dtm; n:nat} .<n>.
     (pf: EVS (t, t', n)): EVS (dtmeexi (t, t1),  dtmeexi (t', t1), n) =
  case+ pf of 
    | EVSnil () => EVSnil () 
    | EVScons (pf1, pf2) => EVScons (EVeexi1 pf1, evs_eexi1 (pf2)) 

prfun evs_append {t1:dtm; t2:dtm; t3:dtm; n1:nat; n2:nat} .<n1>.
     (pf1: EVS (t1, t2, n1), pf2: EVS (t2, t3, n2)): EVS (t1, t3, n1+n2) =
  case+ pf1 of
    | EVSnil () => pf2
    | EVScons (pf11, pf12) => EVScons (pf11, evs_append (pf12, pf2))

// big-step evaluation relation

dataprop EVAL (dtm, dtm, int) = 
  | {f: dtm->dtm} EVALlam (dtmlam f, dtmlam f, 0)

  | {t1:dtm; t2:dtm; v1:dtm; v2:dtm; f:dtm->dtm; n1:nat; n2:nat; n3:nat}
      EVALapp (dtmapp (t1, t2), v2, n1+n2+n3+1) of
        (EVAL (t1, dtmlam f, n1), EVAL (t2, v1, n2), EVAL (f v1, v2, n3))

  | {t:dtm} EVALigua (dtmigua t, dtmigua t, 0)

  | {t:dtm; t':dtm; v:dtm; m:nat; n:nat}
      EVALegua (dtmegua t, v, m+n+1) of
        (EVAL (t, dtmigua t', m), EVAL (t', v, n))

  | {t:dtm; v:dtm; m:nat} 
      EVALiass (dtmiass t, dtmiass v, m+1) of EVAL (t, v, m)

  | {t1:dtm; t2:dtm->dtm; t3:dtm; v:dtm; m:nat; n:nat}
      EVALeass (dtmeass (t1, t2), v, m+n+1) of
        (EVAL (t1, dtmiass t3, m), EVAL (t2 t3, v, n))

  | {t:dtm} EVALiuni (dtmiuni t, dtmiuni t, 0)

  | {t:dtm; t':dtm; v:dtm; m:nat; n:nat} 
      EVALeuni (dtmeuni t, v, m+n+1) of
        (EVAL (t, dtmiuni t', m), EVAL (t', v, n)) 

  | {t:dtm; v:dtm; m:nat}
      EVALiexi (dtmiexi t, dtmiexi v, m+1) of EVAL (t, v, m)

  | {t1:dtm; t2:dtm->dtm; t3:dtm; v:dtm; m:nat; n:nat}
      EVALeexi (dtmeexi (t1, t2), v, m+n+1) of
        (EVAL (t1, dtmiexi t3, m), EVAL (t2 t3, v, n))

propdef EVAL0 (t:dtm, v:dtm) = [n:nat] EVAL (t, v, n)

// [eval_isv_lemma]: proves that big-step EVAL returns a value. 

prfun eval_isv_lemma {t:dtm; v:dtm; n:nat} .<n>.
     (pf: EVAL (t, v, n)): ISV0 v =
  case+ pf of
    | EVALlam () => ISVlam ()
    | EVALapp (_, _, pf) => eval_isv_lemma pf
    | EVALigua () => ISVigua ()
    | EVALegua (_, pf) => eval_isv_lemma pf
    | EVALiass pf => ISViass (eval_isv_lemma pf)
    | EVALeass (_, pf) => eval_isv_lemma pf
    | EVALiuni () => ISViuni ()
    | EVALeuni (_, pf) => eval_isv_lemma pf
    | EVALiexi pf => ISViexi (eval_isv_lemma pf)
    | EVALeexi (_, pf) => eval_isv_lemma pf

// [isv_eval_lemma]: proves that a value evaluates to itself

prfun isv_eval_lemma {v:dtm; n:nat} .<n>.
     (pf: ISV (v, n)): EVAL0 (v, v) =
  case+ pf of
    | ISVlam () => EVALlam ()
    | ISVigua () => EVALigua ()
    | ISViass pf => EVALiass (isv_eval_lemma pf)
    | ISViuni () => EVALiuni ()
    | ISViexi pf => EVALiexi (isv_eval_lemma pf)

// big-step implies small-step

prfun eval_evs_lemma {t:dtm; v:dtm; n:nat} .<n>.
     (pf: EVAL (t, v, n)): EVS0 (t, v) =
  case+ pf of
    | EVALlam () => EVSnil ()

    | EVALapp (pf1, pf2, pf3) =>
      let
         prval [n':int] pf1' = eval_evs_lemma pf1
         prval isv1 = eval_isv_lemma pf1
         prval pf1'' = evs_app2 pf1'
         prval pf2' = eval_evs_lemma pf2
         prval isv2 = eval_isv_lemma pf2
         prval pf2'' = evs_app3 (isv1, pf2')
         prval pf3' = eval_evs_lemma pf3
      in
         evs_append (evs_append (pf1'', pf2''), EVScons (EVapp1 isv2, pf3'))
      end

    | EVALigua () => EVSnil ()

    | EVALegua (pf1, pf2) => 
        let 
          prval pf1' = eval_evs_lemma pf1
          prval pf1'' = evs_egua1 pf1'
          prval pf2' = eval_evs_lemma pf2
        in 
          evs_append (pf1'', EVScons (EVegua2 (), pf2'))
        end 

    | EVALiass (pf1) => evs_iass (eval_evs_lemma pf1) 

    | EVALeass (pf1, pf2) => 
        let 
          prval pf1' = eval_evs_lemma pf1
          prval pf1'' = evs_eass1 pf1'
	  prval ISViass (isv) = eval_isv_lemma pf1
          prval pf2' = eval_evs_lemma pf2
        in 
          evs_append (pf1'', EVScons (EVeass2 isv, pf2'))
        end

    | EVALiuni () => EVSnil ()

    | EVALeuni (pf1, pf2) => 
        let 
          prval pf1' = eval_evs_lemma pf1
          prval pf1'' = evs_euni1 pf1'
          prval pf2' = eval_evs_lemma pf2
        in 
          evs_append (pf1'', EVScons (EVeuni2 (), pf2'))
        end  
    
   | EVALiexi (pf1) => evs_iexi (eval_evs_lemma pf1) 
 
   | EVALeexi (pf1, pf2) => 
        let 
          prval pf1' = eval_evs_lemma pf1
          prval pf1'' = evs_eexi1 pf1'
	  prval ISViexi (isv) = eval_isv_lemma pf1
          prval pf2' = eval_evs_lemma pf2
        in 
          evs_append (pf1'', EVScons (EVeexi2 isv, pf2'))
        end
 
// The weakening rule on static context

extern prval weakSD: {sds:sds; bs:stms; ds:dds; s:stm; a:srt; t:dtm; s':stm; 
  m:nat; i:two}
    DD (sds, bs, ds, t, s, m, i) -<> DD (sdsmore (sds, s', a), bs, ds, t, s, m, i)

// The exchanging rule on dynamic context

extern prval exchSD: {sds:sds; bs:stms; ds:dds; s1:stm; s2:stm; a1:srt; 
   a2:srt; t:dtm; s:stm; m:nat; i:two}
    DD (sdsmore (sdsmore (sds, s1, a1), s2, a2), bs, ds, t, s, m, i) -<>
      DD (sdsmore (sdsmore (sds, s2, a2), s1, a1), bs, ds, t, s, m, i)

// The weakening rule on propositions context

extern prval weakP: {sds:sds; bs:stms; ds:dds; t:dtm; s:stm; b:stm;
  m:nat; i:two}
    DD (sds, bs, ds, t, s, m, i) -<>
    DD (sds, stmsmore (bs, b), ds, t, s, m, i)

// the exchanging rule on propositions context

extern prval exchP: {sds:sds; bs:stms; ds:dds; b1:stm; b2:stm; t:dtm; s:stm;
  m:nat; i:two}
    DD (sds, stmsmore (stmsmore (bs, b1), b2), ds, t, s, m, i) -<>
    DD (sds, stmsmore (stmsmore (bs, b2), b1), ds, t, s, m, i)

// The weakening rule on dynamic context

extern prval weakDD: {sds:sds; bs:stms; ds:dds; t:dtm; s:stm; t':dtm; s':stm;
  m:nat; i:two}
    DD (sds, bs, ds, t, s, m, i) -<>
    DD (sds, bs, ddsmore (ds, t', s'), t, s, m, i)

// The exchanging rule on dynamic context

extern prval exchDD: {sds:sds; bs:stms; ds:dds; t1:dtm; s1:stm; t2:dtm; 
  s2:stm; t:dtm; s:stm; m:nat; i:two}
    DD (sds, bs, ddsmore (ddsmore (ds, t1, s1), t2, s2), t, s, m, i) -<>
    DD (sds, bs, ddsmore (ddsmore (ds, t2, s2), t1, s1), t, s, m, i)

// substitution lemmas
  
extern prval SubstitutionLemma1 : {sds: sds; bs: stms; ds: dds; t: dtm; s: stm; s':stm;
  a:srt; m: nat; i:two}  
   (DD (sdsmore (sds, s, a), bs, ds, t, s', m, i), SD0 (sds, s, a)) -<>
   DD0 (sds, bs, ds, t, s', i)   

extern prval SubstitutionLemma2 : 
  {sds: sds; bs: stms; b:stm; ds: dds; t:dtm; s:stm; m: nat; i:two}  
   (DD (sds, stmsmore (bs, b), ds, t, s, m, i), CS (sds, bs, b)) -<>
   DD0 (sds, bs, ds, t, s, i)

prfun SubstitutionLemma3  
  {sds: sds; bs: stms; ds: dds; b: stm; t: dtm; t': dtm; s: stm; s': stm;  
   m: nat; i1:two; i2:two} .<m>.  
   (pf1: DD (sds, bs, ddsmore (ds, t, s), t', s', m, i1), 
    pf2: DD0 (sds, bs, ds, t, s, i2))
   : DD0 (sds, bs, ds, t', s', 1) = 

   $effmask_exn (case pf1 of 
  
     | DDsub (pf11, pf12) =>
         inversion (DDsub (SubstitutionLemma3 (pf11, pf2), pf12))

     | DDvar (i, pf11) => begin
         case+ i of 
           | DDIone () => inversion (DDsub (pf2, pf11)) 
           | DDIshi i => DDvar (i, pf11)
       end
(*
     | DDlam pf1 => 
         DDlam (lampara {t:dtm} => SubstitutionLemma3 (exchDD (pf1 {t}), weakDD pf2))
*)
     | DDapp (pf11, pf12) => 
	 DDapp (SubstitutionLemma3 (pf11, pf2), SubstitutionLemma3 (pf12, pf2))

     | DDigua pf1 => DDigua (SubstitutionLemma3 (pf1, weakP pf2))

     | DDegua (pf11, pf12) => DDegua (SubstitutionLemma3 (pf11, pf2), pf12)

     | DDiass (pf11, pf12) => DDiass (SubstitutionLemma3 (pf11, pf2), pf12)    
(*
     | DDeass (pf11, pf12) => 
         DDeass (SubstitutionLemma3 (pf11, pf2), 
                   lampara {x:dtm} => SubstitutionLemma3 (exchDD (pf12 {x}), weakDD (weakP pf2)))
 
     | DDiuni (pf1) =>
         DDiuni (lampara {y:stm} => SubstitutionLemma3 (pf1 {y}, weakSD (pf2)))
*)     
     | DDeuni (pf11, pf12) =>
         DDeuni (SubstitutionLemma3 (pf11, pf2), pf12)

     | DDiexi (pf11, pf12) =>
	 DDiexi (SubstitutionLemma3 (pf11, pf2), pf12)
(*
     | DDeexi (pf11, pf12) =>
        DDeexi (
          SubstitutionLemma3 (pf11, pf2), 
          lampara {x:dtm; s1:stm} => 
             SubstitutionLemma3
               (exchDD (pf12 {x, s1}), weakSD (weakDD (pf2)))
        )
*)
  ) // end of $effmask_exn

// subject reduction theorem

prfun SubjectReduction {t: dtm; t': dtm; s: stm; n: nat} .<n>.  
   (pf1: DD (sdsnone, stmsnone, ddsnone, t, s, n, 1), pf2: EV0 (t, t')): 
    DD0 (sdsnone, stmsnone, ddsnone, t', s, 1) =
  case+ pf2 of

    | EVapp1 pf2' => 
        begin
          case+ pf1 of 
            | DDapp (pf11, pf12) => 
               begin
                 case+ inversion (pf11) of 
                   | DDlam pf11' => SubstitutionLemma3 (pf11', pf12)
                   | DDvar (i, _) =/=> 
                       (case+ i of DDIone () => () | DDIshi _ => ())
                 end
            | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
        end

    | EVapp2 pf2 => 
        begin 
          case+ pf1 of 
            | DDapp (pf11, pf12) => 
                DDapp (SubjectReduction (inversion pf11, pf2), pf12)
            | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
        end

    | EVapp3 (pf21, pf22) => 
        begin 
          case+ pf1 of 
            | DDapp (pf11, pf12) => 
                DDapp (pf11, SubjectReduction (inversion pf12, pf22))
            | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
        end

    | EVegua1 (pf2) => 
        begin 
          case+ pf1 of 
            | DDegua (pf11, pf12) => 
                DDegua (SubjectReduction (inversion pf11, pf2), pf12)
            | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
        end

    | EVegua2 () => begin 
        case+ pf1 of 
          | DDegua (pf11, pf12) => begin 
              case+ inversion (pf11) of 
                | DDigua pf11 => inversion (SubstitutionLemma2 (pf11, pf12))
                | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
            end
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end

    | EViass (pf2) => begin 
        case+ pf1 of 
          | DDiass (pf11, pf12) => DDiass (SubjectReduction (inversion pf11, pf2), pf12)
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end
    
    | EVeass1 (pf2) =>begin
        case+ pf1 of 
          | DDeass (pf11, pf12) => 
              DDeass (SubjectReduction (inversion pf11, pf2), pf12)
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end
    
    | EVeass2 (pf2) => begin 
        case+ pf1 of 
          | DDeass (pf11, pf12) => begin 
              case+ inversion (pf11) of 
                | DDiass (pf111, pf112) =>
                    let 
                       prval pf' = SubstitutionLemma2 (pf12 {...}, pf112)
                    in  
                       SubstitutionLemma3 (pf', pf111)
                    end
                | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
            end
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end

    | EVeuni1 (pf2) => begin  
        case+ pf1 of
          | DDeuni (pf11, pf12) => DDeuni (SubjectReduction (inversion pf11, pf2), pf12)
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end

    | EVeuni2 () => begin 
        case+ pf1 of 
          | DDeuni (pf11, pf12) => begin
              case+ inversion (pf11) of
                | DDiuni (pf11') => SubstitutionLemma1 (inversion (pf11' {...}), pf12)
                | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
            end
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end
    
    | EViexi (pf2) => begin
        case+ pf1 of 
          | DDiexi (pf11, pf12) => 
              DDiexi (SubjectReduction (inversion pf11, pf2), pf12)
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end

    | EVeexi1 (pf2) => begin
        case+ pf1 of 
          | DDeexi (pf11, pf12) =>
              DDeexi (SubjectReduction (inversion pf11, pf2), 
                      lam {x:dtm; s1:stm} => pf12 {x, s1})
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end  

    | EVeexi2 (pf2) => begin 
        case+ pf1 of 
          | DDeexi (pf11, pf12) => begin 
              case+ inversion (pf11) of 
                | DDiexi (pf111, pf112) =>
                    let 
                       prval pf' = SubstitutionLemma1 (pf12 {...}, pf112)
                    in 
                       SubstitutionLemma3 (pf', pf111)
                    end
                | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
            end
          | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
      end


// The type preservation theorem
//
// This theorem is needed for establishing the correctness of an evaluator
// for ATS, which is to be implemented next.

prfun TypePreservation {t: dtm; v: dtm; s: stm; n: nat} .<n>.  
   (pf1: DD0 (sdsnone, stmsnone, ddsnone, t, s, 1), pf2: EVAL (t, v, n)): 
    DD0 (sdsnone, stmsnone, ddsnone, v, s, 1) = 

   case+ pf2 of 
     | EVALlam () => pf1
     
     | EVALapp (pf21, pf22, pf23) => 
         begin
           case+ pf1 of 
             | DDapp (pf11, pf12) => 
               let 
                 prval pf11' = TypePreservation (inversion pf11, pf21)
		 prval pf12' = TypePreservation (inversion pf12, pf22)
               in 
                 case+ pf11' of 
                   | DDlam fpf11' => 
                      let 
                        prval pf13' = SubstitutionLemma3 (fpf11' {...}, pf12')
                      in 
                        TypePreservation (pf13', pf23)
                      end
                   | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
               end
             | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
          end
     
      | EVALigua () => pf1

      | EVALegua (pf21, pf22) => 
          begin 
            case+ pf1 of 
              | DDegua (pf11, pf12) =>
                 let 
                   prval pf11' = TypePreservation (inversion pf11, pf21) 
                 in 
                   case+ pf11' of 
                     | DDigua pf11' => 
                       let 
                          prval pf14' = SubstitutionLemma2 (pf11', pf12) 
                       in 
                          TypePreservation (inversion pf14', pf22)
                       end
                     | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
                 end
              | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
          end

      | EVALiass (pf2) => 
	  begin
            case+ pf1 of 
              | DDiass (pf11, pf12) => 
                let 
                  prval pf11' = TypePreservation (inversion pf11, pf2)
                in 
                  DDiass (pf11', pf12)
                end
	      | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

          end
 
      | EVALeass (pf21, pf22) => 
          begin
            case+ pf1 of 
              | DDeass (pf11, pf12) =>
		let 
		  prval pf11' = TypePreservation (inversion pf11, pf21) 
                in 
                  case+ pf11' of
		    | DDiass (pf111, pf112) => 
		      let 
                         prval pf12' = SubstitutionLemma2 (pf12 {...}, pf112)
                         prval pf12'' = SubstitutionLemma3 (pf12', pf111) 
                      in 
                         TypePreservation (pf12'', pf22)
                      end
                    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
                end
              | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
          end 

      | EVALiuni () => pf1

      | EVALeuni (pf21, pf22) => 
          begin 
            case+ pf1 of 
              | DDeuni (pf11, pf12) =>
                 let 
                   prval pf11' = TypePreservation (inversion pf11, pf21) 
                 in 
                   case+ pf11' of 
                     | DDiuni (gpf11') => 
                       let 
                         prval pf13 = SubstitutionLemma1 (gpf11' {...}, pf12) 
                       in 
                         TypePreservation (inversion pf13, pf22)
                       end
                     | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
                 end
              | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
          end

	
       | EVALiexi (pf2) => 
           begin
             case+ pf1 of 
               | DDiexi (pf11, pf12) => 
                   DDiexi (TypePreservation (inversion pf11, pf2), pf12)
               | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
           end

       | EVALeexi (pf21, pf22) =>
           begin
             case+ pf1 of 
               | DDeexi (pf11, pf12) => 
                 let 
                   prval pf11' = TypePreservation (inversion pf11, pf21) 
                 in 
                   case+ pf11' of 
                     | DDiexi (pf111, pf112) => 
                       let
                          prval pf12' = SubstitutionLemma1 (pf12 {...}, pf112)
                          prval pf12'' = SubstitutionLemma3 (pf12', pf111)
                       in 
                          TypePreservation (pf12'', pf22)
                       end
                    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
                 end
               | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())
           end

// progress theorem

dataprop ORELSE (p1: prop, p2: prop) = inl (p1, p2) of p1 | inr (p1, p2) of p2

infixl ORELSE

prfun Progress {t:dtm; s:stm; n:nat} .<n>. 
  (pf: DD (sdsnone, stmsnone, ddsnone, t, s, n, 1)) : 
  ISV0 (t) ORELSE [t':dtm] EV0 (t, t') =
    case+ pf of 

      | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

      | DDlam _ => inl (ISVlam ())

      | DDapp (pf1, pf2) =>
        let prval pf1 = inversion pf1 in case+ (Progress pf1) of 
          | inl pf1' =>
            let prval DTMEQ () = isv_fun_lemma (pf1', pf1) in
               case+ (Progress (inversion pf2)) of 
                 | inl pf2' => inr (EVapp1 pf2')
                 | inr pf2' => inr (EVapp3 (pf1', pf2'))
            end
          | inr pf1' => inr (EVapp2 (pf1'))
        end

      | DDigua _ => inl (ISVigua ())

      | DDegua (pf1, _) =>
        let prval pf1 = inversion pf1 in case+ (Progress pf1) of 
          | inl pf1' => 
            let prval DTMEQ () = isv_gua_lemma (pf1', pf1) in
               inr (EVegua2 ())
            end
          | inr pf1' => inr (EVegua1 pf1')
        end

      | DDiass (pf1, _) => begin 
          case+ (Progress (inversion pf1)) of 
            | inl pf1' => inl (ISViass pf1')
            | inr pf1' => inr (EViass pf1')
        end 

      | DDeass (pf1, _) =>
        let prval pf1 = inversion pf1 in case+ (Progress pf1) of 
          | inl pf1' => 
            let
               prval DTMEQ () = isv_ass_lemma (pf1', pf1)
               prval ISViass pf10' = pf1'
            in
               inr (EVeass2 (pf10'))
            end
          | inr pf1' => inr (EVeass1 (pf1'))
        end

      | DDiuni _ => inl (ISViuni ())

      | DDeuni (pf1, _) =>
        let prval pf1 = inversion pf1 in case+ (Progress pf1) of 
          | inl pf1' =>
            let prval DTMEQ () = isv_uni_lemma (pf1', pf1) in
               inr (EVeuni2 ())
            end
          | inr pf1' => inr (EVeuni1 pf1')
        end

      | DDiexi (pf1, _) => begin
          case+ (Progress (inversion pf1)) of 
              | inl pf1' => inl (ISViexi pf1')
              | inr pf1' => inr (EViexi pf1')
        end

      | DDeexi (pf1, _) =>
        let prval pf1 = inversion pf1 in case+ (Progress pf1) of 
          | inl pf1' => 
            let
               prval DTMEQ () = isv_exi_lemma (pf1', pf1)
               prval ISViexi pf10' = pf1'
            in
               inr (EVeexi2 pf10')
            end
          | inr pf1' => inr (EVeexi1 pf1')
        end

// A verified implementation of ATS that uses closures for values

datasort dtms = dtmsnone | dtmsmore of (dtms, dtm)

datatype DTMI (dtm, dtms) =
  | {ts:dtms; t:dtm} DTMIone (t, dtmsmore (ts, t))
  | {ts:dtms; t:dtm; t':dtm}
      DTMIshi (t, dtmsmore (ts, t')) of DTMI (t, ts)

datatype DTM (dtms, dtm) =
  | {ts:dtms; t:dtm} DTMvar (ts, t) of DTMI (t, ts)

  | {ts:dtms; f:dtm->dtm}
      DTMlam (ts, dtmlam f) of ({t:dtm} DTM (dtmsmore (ts, t), f t))

  | {ts:dtms; t1:dtm; t2:dtm}
      DTMapp (ts, dtmapp (t1, t2)) of (DTM (ts, t1), DTM (ts, t2))

  | {ts:dtms; t:dtm} DTMigua (ts, dtmigua t) of DTM (ts, t)

  | {ts:dtms; t:dtm} DTMegua (ts, dtmegua t) of DTM (ts, t)

  | {ts:dtms; t:dtm} DTMiass (ts, dtmiass t) of DTM (ts, t)

  | {ts:dtms; t1:dtm; f2:dtm -> dtm}
      DTMeass (ts, dtmeass (t1, f2)) of
        (DTM (ts, t1), {t:dtm} DTM (dtmsmore (ts, t), f2 t))

  | {ts:dtms; t:dtm} DTMiuni (ts, dtmiuni t) of DTM (ts, t)

  | {ts:dtms; t:dtm} DTMeuni (ts, dtmeuni t) of DTM (ts, t)

  | {ts:dtms; t:dtm} DTMiexi (ts, dtmiexi t) of DTM (ts, t)

  | {ts:dtms; t1:dtm; f2:dtm -> dtm}
      DTMeexi (ts, dtmeexi (t1, f2)) of
        (DTM (ts, t1), {t:dtm} DTM (dtmsmore (ts, t), f2 t))

//

datatype VAL (dtm) =
  | {ts:dtms; f: dtm->dtm} 
      VALlam (dtmlam f) of (ENV ts, {t:dtm} DTM (dtmsmore (ts, t), f t))

  | {ts:dtms; t:dtm} VALigua (dtmigua t) of (ENV ts, DTM (ts, t))

  | {t:dtm} VALiass (dtmiass t) of VAL (t)

  | {ts:dtms; t:dtm} VALiuni (dtmiuni t) of (ENV ts, DTM (ts, t))

  | {t:dtm} VALiexi (dtmiexi t) of VAL (t)

and ENV (dtms) =
  | ENVnil (dtmsnone)
  | {ts:dtms; t:dtm}
      ENVcons (dtmsmore (ts, t)) of (ISV0 t | ENV ts, VAL t)

//

fun evalVar {ts:dtms; t:dtm} (env: ENV ts, i: DTMI (t, ts)): '(ISV0 t | VAL t) =
  case+ i of
    | DTMIone () => let val ENVcons (pf | _, v) = env in '(pf | v) end
    | DTMIshi i => let val ENVcons (_ | env, _) = env in evalVar (env, i) end

//

prfn inv_lam {f:dtm->dtm; T1:stm; T2:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmlam f, stmfun (T1, T2), 1))
   : ({t:dtm} [i:two]
        DD0 (sdsnone, stmsnone, ddsmore (ddsnone, t, T1), f t, T2, i)) =
  case+ dd of
    | DDlam (fdd) => lam {t:dtm} => fdd {t}
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_app {t1:dtm; t2:dtm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmapp (t1, t2), T, 1))
   : [T1:stm]
       '([i:two] DD0 (sdsnone, stmsnone, ddsnone, t1, stmfun (T1, T), i),
         [i:two] DD0 (sdsnone, stmsnone, ddsnone, t2, T1, i)) =
  case+ dd of
    | DDapp (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_igua {t:dtm; B:stm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmigua t, stmgua (B, T), 1))
   : [i:two] DD0 (sdsnone, stmsmore (stmsnone, B), ddsnone, t, T, i) =
  case+ dd of
    | DDigua dd0 => dd0
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_egua {t:dtm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmegua t, T, 1))
   : [B:stm;i:two]
       '(DD0 (sdsnone, stmsnone, ddsnone, t, stmgua (B, T), i),
         CS (sdsnone, stmsnone, B)) =
  case+ dd of
    | DDegua (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_iass_1 {t:dtm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmiass t, T, 1))
   : [B1:stm; T1:stm; i:two]
       '(DD0 (sdsnone, stmsnone, ddsnone, t, T1, i),
         CS (sdsnone, stmsnone, B1)) =
  case+ dd of
    | DDiass (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_iass_2 {t:dtm; B:stm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmiass t, stmass (B, T), 1))
   : [i:two]
       '(DD0 (sdsnone, stmsnone, ddsnone, t, T, i),
         CS (sdsnone, stmsnone, B)) =
  case+ dd of
    | DDiass (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_eass {t:dtm; f:dtm->dtm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmeass (t, f), T, 1))
   : [B1:stm; T1:stm; i:two]
       '(DD0 (sdsnone, stmsnone, ddsnone, t, stmass (B1, T1), i),
         {x:dtm} [i2:two]
           DD0 (sdsnone, stmsmore (stmsnone, B1),
                 ddsmore (ddsnone, x, T1), f x, T, i2)) =
  case+ dd of
    | DDeass (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_iuni {t:dtm; st:srt; F:stm->stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmiuni t, stmuni (st, F), 1))
   : {s:stm} [i:two]
       DD0 (sdsmore (sdsnone, s, st), stmsnone, ddsnone, t, F s, i) =
  case+ dd of
    | DDiuni dd0 => dd0
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_euni {t:dtm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmeuni t, T, 1))
   : [F:stm->stm;s:stm;st:srt;i:two]
       '(STMEQ (T, F s),
         DD0 (sdsnone, stmsnone, ddsnone, t, stmuni (st, F), i),
         SD0 (sdsnone, s, st)) =
  case+ dd of
    | DDeuni (dd1, dd2) => '(STMEQ (), dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

////

prfn inv_iexi_1 {t:dtm; T:stm}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmiexi t, T, 1))
   : [F:stm->stm; s:stm; st:srt; i:two]
       '(DD0 (sdsnone, stmsnone, ddsnone, t, F s, i), SD0 (sdsnone, s, st)) =
  case+ dd of
    | DDiexi (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_iexi_2 {t:dtm; F:stm->stm; st:srt}
    (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmiexi t, stmexi (st, F), 1))
   : [s:stm; i:two]
       '(DD0 (sdsnone, stmsnone, ddsnone, t, F s, i), SD0 (sdsnone, s, st)) =
  case+ dd of
    | DDiexi (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

prfn inv_eexi {t1:dtm; f2: dtm -> dtm; T:stm}
     (dd: DD0 (sdsnone, stmsnone, ddsnone, dtmeexi (t1, f2), T, 1))
   : [F:stm->stm; st:srt]
       '([i:two] DD0 (sdsnone, stmsnone, ddsnone, t1, stmexi (st, F), i),
         {x:dtm; a:stm} [i:two]
           (DD0 (sdsmore (sdsnone, a, st), stmsnone,
                 ddsmore (ddsnone, x, F a), f2 x, T, i))) =
  case+ dd of
    | DDeexi (dd1, dd2) => '(dd1, dd2)
    | DDvar (i, _) =/=> (case+ i of DDIone () => () | DDIshi _ => ())

//

fun eval {ts:dtms; t:dtm; T:stm; i:two}
   (dd: DD0 (sdsnone, stmsnone, ddsnone, t, T, i) | env: ENV ts, t: DTM (ts, t))
  : [v:dtm] '(EVAL0 (t, v) | VAL v) =
  case+ t of
    | DTMvar i =>
        let val '(pf | v) = evalVar (env, i) in '(isv_eval_lemma pf | v) end

    | DTMlam body => '(EVALlam () | VALlam (env, body))

    | DTMapp (t1, t2) =>
        let
           prval dd = inversion dd
           prval '(dd1, dd2) = inv_app dd
           prval dd1 = inversion dd1
           prval dd2 = inversion dd2

           val '(pf1 | v1) = eval (dd1 | env, t1)
           prval dd1' = TypePreservation (dd1, pf1)
           prval DTMEQ () = isv_fun_lemma (eval_isv_lemma pf1, dd1')
           val VALlam (env0, tf1) = v1
           prval fdd1' = inv_lam (dd1')

           val '(pf2 | v2) = eval (dd2 | env, t2)
           prval dd2' = TypePreservation (dd2, pf2)

           prval dd3' = SubstitutionLemma3 (fdd1' {...}, dd2')

           val '(pf3 | v3) =
              eval (dd3' | ENVcons (eval_isv_lemma pf2 | env0, v2), tf1 {...})
        in
           '(EVALapp (pf1, pf2, pf3) | v3)
        end

    | DTMigua t0 => '(EVALigua () | VALigua (env, t0))

    | DTMegua t0 =>
        let
           prval dd = inversion dd
           prval '(dd1, dd2) = inv_egua dd
           prval dd1 = inversion dd1

           val '(pf0 | v0) = eval (dd1 | env, t0)
           prval dd1' = TypePreservation (dd1, pf0)
           prval DTMEQ () = isv_gua_lemma (eval_isv_lemma pf0, dd1')
           val VALigua (env0, t1) = v0

           prval dd1' = inv_igua (dd1')
           prval dd1' = SubstitutionLemma2 (dd1', dd2)

           val '(pf1 | v1) = eval (dd1' | env0, t1)
        in
           '(EVALegua (pf0, pf1) | v1)
        end

    | DTMiass t0 =>
        let
           prval dd = inversion dd
           prval '(dd1, dd2) = inv_iass_1 dd
           prval dd1 = inversion dd1
           val '(pf0 | v0) = eval (dd1 | env, t0)
        in
           '(EVALiass pf0 | VALiass v0)
        end

    | DTMeass (t1, f2) =>
        let
           prval dd = inversion dd
           prval '(dd1, fdd2) = inv_eass dd
           prval dd1 = inversion dd1

           val '(pf1 | v1) = eval (dd1 | env, t1)
           prval dd1' = TypePreservation (dd1, pf1)
           prval DTMEQ () = isv_ass_lemma (eval_isv_lemma pf1, dd1')

           prval ISViass pf10 = eval_isv_lemma pf1
           val VALiass v10 = v1

           prval '(dd11', dd12') = inv_iass_2 (dd1')
           prval dd2' = SubstitutionLemma2 (fdd2 {...}, dd12')
           prval dd2' = SubstitutionLemma3 (dd2', dd11')

           val '(pf2 | v2) =
              eval (dd2' | ENVcons (pf10 | env, v10), f2 {...})
        in
           '(EVALeass (pf1, pf2) | v2)
        end

    | DTMiuni t0 => '(EVALiuni () | VALiuni (env, t0))

    | DTMeuni t0 =>
        let
           prval dd = inversion dd
           prval '(STMEQ (), dd1, dd2) = inv_euni dd
           prval dd1 = inversion dd1

           val '(pf0 | v0) = eval (dd1 | env, t0)
           prval dd1' = TypePreservation (dd1, pf0)
           prval DTMEQ () = isv_uni_lemma (eval_isv_lemma pf0, dd1')
           val VALiuni (env0, t1) = v0

           prval dd1' = inv_iuni (dd1')
           prval dd1' = SubstitutionLemma1 (dd1', dd2)

           val '(pf1 | v1) = eval (dd1' | env0, t1)
        in
           '(EVALeuni (pf0, pf1) | v1)
        end

    | DTMiexi t0 =>
        let
           prval dd = inversion dd
           prval '(dd1, dd2) = inv_iexi_1 dd
           prval dd1 = inversion dd1
           val '(pf0 | v0) = eval (dd1 | env, t0)
        in
           '(EVALiexi pf0 | VALiexi v0)
        end

    | DTMeexi (t1, f2) =>
        let
           prval dd = inversion dd
           prval '(dd1, fdd2) = inv_eexi dd
           prval dd1 = inversion dd1

           val '(pf1 | v1) = eval (dd1 | env, t1)
           prval dd1' = TypePreservation (dd1, pf1)
           prval DTMEQ () = isv_exi_lemma (eval_isv_lemma pf1, dd1')

           prval ISViexi pf10 = eval_isv_lemma pf1
           val VALiexi v10 = v1

           prval '(dd11', dd12') = inv_iexi_2 (dd1')
           prval dd2' = SubstitutionLemma1 (fdd2 {...}, dd12')
           prval dd2' = SubstitutionLemma3 (dd2', dd11')

           val '(pf2 | v2) =
              eval (dd2' | ENVcons (pf10 | env, v10), f2 {...})
        in
           '(EVALeexi (pf1, pf2) | v2)
        end

// Voila! We now have a verified evaluator for ATS:

fun evaluate {t:dtm; s:stm; i:two}
   (dd: DD0 (sdsnone, stmsnone, ddsnone, t, s, i) | t: DTM (dtmsnone, t))
  : [v:dtm] '(EVAL0 (t, v) | VAL v) = eval (dd | ENVnil, t)
