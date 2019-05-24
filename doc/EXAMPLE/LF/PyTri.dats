(*
**
** A proof sketch for the representation
** of Pythagorean triangluar integer triples
**
** Suppose that a and b are positive integers
** satisfying gcd (a, b) = 1.
**
** If a*a + b*b = c*c for some integer c, then
**
** 1. either a or b is even
** 2. if a is even, then there exists integers
**     p, q such that:
**
**    a = 2*p*q
**    b = p*p - q*q
**    c = p*p + q*q
**
*)

(* ****** ****** *)

(*
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: February 7, 2010
*)

(* ****** ****** *)

(*
**
** HX-2010-02-08:
**
** What is written as follows is not really a proof in any rigourous
** sense. However, it is close to a style we as human being do mathematics.
** I envision a system (ATS/LF) where refinement can be done gradually to
** remove the number of __assert functions used in such a proof. Who will
** take the grand challenge :)
**
*)

(* ****** ****** *)

absprop MOD (n:int, p:int, r:int) // n mod p = r

(* ****** ****** *)

extern prfun lemma1 {n:nat} {n2:int}
  (pf1: MOD (n, 2, 0), pf2: MUL (n, n, n2)): MOD (n2, 4, 0)
// end of [lemma1]

extern prfun lemma2 {n:nat} {n2:int}
  (pf1: MOD (n, 2, 1), pf2: MUL (n, n, n2)): MOD (n2, 4, 1)
// end of [lemma2]

(* ****** ****** *)

dataprop por (A: prop, B: prop) = inl (A, B) of A | inr (A, B) of B

extern prfun lemma3 {a,b,c:nat} {a2,b2:int}
  (pfa: MUL (a, a, a2), pfb: MUL (b, b, b2), pfc: MUL (c, c, a2+b2))
  : por (MOD (a, 2, 0), MOD (b, 2, 0))

(* ****** ****** *)

extern prfun lemma5 {P,Q:pos} {n:nat}
  (pf: GCD (P, Q, 1), pf: MUL (P, Q, n*n))
  : [p,q:nat] (MUL (p, p, P), MUL (p, q, n), MUL (q, q, Q))
// end of [lemma5]

(* ****** ****** *)

extern prfun PyTri {a,b,c:pos} {a2,b2:int} (
    pfa_mod: MOD (a, 2, 0)
  , pfab_gcd: GCD (a, b, 1)
  , pfa: MUL (a, a, a2)
  , pfb: MUL (b, b, b2)
  , pfc: MUL (c, c, a2+b2)
  ) : [p,q:nat]
    [p2,pq,q2:int | a == 2*pq; b == p2-q2; c == p2+q2]
    (MUL (p, p, p2), MUL (p, q, pq), MUL (q, q, q2))
// end of [PyTri]

(* ****** ****** *)

implement PyTri {a,b,c} {a2,b2}
  (pfa_mod, pfab_gcd, pfa, pfb, pfc) = let
  prval [ha:int] () = __assert (pfa_mod) where {
    extern prfun __assert (pf: MOD (a, 2, 0)): [ha:int | 2*ha==a] void
  }
  prval [hb:int] () = __assert (pfb_mod) where {
    extern prfun __assert (pf: MOD (b, 2, 1)): [hb:int | 2*hb+1==b] void
    prval pfb_mod = __assert (pfa_mod, pfab_gcd) where {
      extern prfun __assert (pf1: MOD (a, 2, 0), pf2: GCD (a, b, 1)): MOD (b, 2, 1)
    } // end of [prval]
  } // end of [prval]
  prval [hc:int] () = __assert () where {
    extern prfun __assert (): [hc:int | 2*hc+1==c] void
  } // end of [prval]
  prval () = __assert () where {
    extern prfun __assert (): [a < c; b < c] void
  }
//
  prval [ha2:int] _pf = mul_istot {ha,ha} ()
  prval () = mul_elim (_pf)
  prval () = __assert () where {
    extern prfun __assert (): [4*ha2 == a2] void
  }
//
  prval [_a2:int] _pf = mul_istot {c+b,c-b} ()
  prval () = mul_elim (_pf)
  prval () = __assert () where {
    extern prfun __assert (): [_a2 == a2] void // (c+b)*(c-b) = c*c - b*b
  } // end of [prval]
  stadef P = hc+hb+1 and Q = hc-hb
  prval [PQ:int] pfPQ_mul = mul_istot {P,Q} ()
  prval () = mul_elim (_pf)
  prval () = __assert () where {
    extern prfun __assert (): [4*PQ == a2] void
  }
  prval pfPQ_gcd = __assert () where {
    extern prfun __assert (): GCD (P, Q, 1)
  }
  prval [p,q:int] (pfpp, pfpq, pfqq) = lemma5 {P,Q} {ha} (pfPQ_gcd, pfPQ_mul)
  // prval () = verify_constraint {false} () // check for sanity
in
  (pfpp, pfpq, pfqq)
end // end of [PyTri]

(* ****** ****** *)

(* end of [PyTri.dats] *)
