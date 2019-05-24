(*

//
// Some commonly used lemmas on integer multiplication
// Author: Hongwei Xi (August, 2007)
//

*)

(*
// [MUL] encode mutiplication on integers:
//    1. 0 * n = 0
//    2. (m+1) * n = m * n + n ; if m >= 0
//    3. ~m * n = ~(m * n) ; if m > 0
dataprop MUL (int, int, int) =
  | {n:int} MULbas (0, n, 0)
  | {m,n,p:int | m >= 0} MULind (m+1, n, p+n) of MUL (m, n, p)
  | {m,n,p:int | m > 0} MULneg (~m, n, ~p) of MUL (m, n, p)
// end of [MUL]
*)

(* ****** ****** *)

(*
** MULprop_total : {m,n:int} () -< prf > [mn:int] MUL (m, n, mn)
*)

prfun MULprop_total {m,n:int} .< max(2*m,~2*m+1) >. (): [p:int] MUL (m, n, p) =
  sif m > 0 then MULind (MULprop_total {m-1,n} ())
  else sif m < 0 then MULneg (MULprop_total {~m,n} ())
  else MULbas ()

(*
** MULprop_unique : {m,n,p1,p2:int}
**   (MUL (m, n, p1), MUL (m, n, p2)) -< prf > [p1 == p2] void
*)

prfun MULprop_unique {m,n,p1,p2:int} .< max(2*m, ~2*m+1) >.
  (pf1: MUL (m, n, p1), pf2: MUL (m, n, p2)): [p1 == p2] void =
  case+ (pf1, pf2) of
    | (MULbas (), MULbas ()) => ()
    | (MULind pf1, MULind pf2) => MULprop_unique (pf1, pf2)
    | (MULneg pf1, MULneg pf2) => MULprop_unique (pf1, pf2)

(* ****** ****** *)

(*
** MULprop_1_n_n : {n:int} () -< prf > MUL (1, n, n)
*)

prfn MULprop_1_n_n () = MULind (MULbas ())

(*
** MULprop_m_0_p_0 : {m,p:int} MUL (m, 0, p) -< prf > [p == 0] void
*)

prfun MULprop_m_0_p_0 {m,p:int} .< max(2*m, ~2*m+1) >. (pf: MUL (m, 0, p)): [p == 0] void =
  case+ pf of
    | MULbas () => ()
    | MULind pf => MULprop_m_0_p_0 pf
    | MULneg pf => MULprop_m_0_p_0 pf

(*
** MULprop_m_1_m : {m:int} () -< prf > MUL (m, 1, m)
*)

prfun MULprop_m_1_m {m:int} .< max(2*m, ~2*m+1) >. (): MUL (m, 1, m) =
  sif m > 0 then MULind (MULprop_m_1_m {m-1} ())
  else sif m < 0 then MULneg (MULprop_m_1_m {~m} ())
  else MULbas ()

(* ****** ****** *)

(*
 * MULprop_neg : {m,n,p:int} MUL (m, n, p) -< prf > MUL (m, ~n, ~p)
 *)

prfun MULprop_neg {m,n,p:int} .< max(2*m, ~2*m+1) >. (pf: MUL (m, n, p)): MUL (m, ~n, ~p) =
  case+ pf of
  | MULbas () => MULbas ()
  | MULind (pf) => MULind (MULprop_neg pf)
  | MULneg (pf) => MULneg (MULprop_neg pf)
// end of [MULprop_neg]

(* ****** ****** *)

(*
 * MULprop_distribute : {m,n1,n2,p1,p2:int}
 *   (MUL (m, n1, p1), MUL (m, n2, p2)) -< prf > MUL (m, n1+n2, p1+p2)
 *)

prfun MULprop_distribute {m,n1,n2,p1,p2:int} .< max(2*m, ~2*m+1) >.
  (pf1: MUL (m, n1, p1), pf2: MUL (m, n2, p2)): MUL (m, n1+n2, p1+p2) =
  case+ (pf1, pf2) of
  | (MULbas (), MULbas ()) => MULbas ()
  | (MULind pf1, MULind pf2) => MULind (MULprop_distribute (pf1, pf2))
  | (MULneg pf1, MULneg pf2) => MULneg (MULprop_distribute (pf1, pf2))
// end of [MULprop_distribute]

(* ****** ****** *)

(* MULprop_commute : {m,n,mn,nm:int} 
 *   (MUL (m, n, mn), MUL (n, m, nm)) -< prf > [mn == nm] void
 *)

prfun MULprop_commute {m,n,mn,nm:int} .< max(2*m,~2*m+1) >.
  (pf1: MUL (m, n, mn), pf2: MUL (n, m, nm)): [mn == nm] void =
  case+ pf1 of
  | MULbas () => MULprop_m_0_p_0 pf2
  | MULind pf1 => let
      prval pf_mul_n_m1_nm1 = MULprop_total {n,m-1} ()
      prval () = MULprop_commute (pf1, pf_mul_n_m1_nm1) 
      prval pf_mul_n_1_n = MULprop_m_1_m {n:int} ()
      prval pf_mul_n_m_nm = MULprop_distribute (pf_mul_n_m1_nm1, pf_mul_n_1_n)
      prval () = MULprop_unique (pf2, pf_mul_n_m_nm)
    in
      ()
    end // end of [MULind]
  | MULneg pf1 => begin
      let prval pf2 = MULprop_neg pf2 in MULprop_commute (pf1, pf2) end
    end // end of [MULneg]
// end of [MULprop_commute]

(* ****** ****** *)

(*
**
** MULprop_associate : {m,n,p,mn,np,mnp:int}
**   (MUL (m, n, mn), MUL (n, p, np), MUL (mn, p, mnp)) -< prf > MUL (m, np, mnp)
**
*)

prfun MULprop_associate {m,n,p,mn,np,mnp:int} .< max(2*p, ~2*p+1) >.
  (pf1: MUL (m, n, mn), pf2: MUL (n, p, np), pf3: MUL (mn, p, mnp)): MUL (m, np, mnp) =
  sif p > 0 then let
    prval pf_mul_n_1_n = MULprop_m_1_m {n} ()
    prval pf_mul_n_p1_np1 = MULprop_total {n,p-1} ()
    prval () = MULprop_unique (pf2, MULprop_distribute (pf_mul_n_p1_np1, pf_mul_n_1_n))
    prval pf_mul_mn_p1_mnp1 = MULprop_total {mn,p-1} ()
    prval pf_mul_mn_1_mn = MULprop_m_1_m {mn} ()
    prval () = MULprop_unique (pf3, MULprop_distribute (pf_mul_mn_p1_mnp1, pf_mul_mn_1_mn))
    prval pf_mul_m_np1_mnp1 = MULprop_associate (pf1, pf_mul_n_p1_np1, pf_mul_mn_p1_mnp1)
  in
    MULprop_distribute (pf_mul_m_np1_mnp1, pf1)
  end else sif p < 0 then let
    prval pf2_neg = MULprop_neg pf2
    prval pf3_neg = MULprop_neg pf3
    prval pf_neg = MULprop_associate (pf1, pf2_neg, pf3_neg)
  in
    MULprop_neg pf_neg
  end else let
    prval () = MULprop_m_0_p_0 (pf2)
    prval () = MULprop_m_0_p_0 (pf3)
    prval pf = MULprop_total {m, np} ()
    prval () = MULprop_m_0_p_0 (pf)
  in
    pf
  end // end of [sif]
// end of [MULprop_associate]

(* ****** ****** *)

(* end of [dataprops.dats] *)
