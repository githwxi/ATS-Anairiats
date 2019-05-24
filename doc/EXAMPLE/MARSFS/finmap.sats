(*
** Specifying Finite Lists
*)

(* ****** ****** *)

datasort iset = // abstract
absprop SET (xs: iset, x: int, b:bool) // membership

datasort imap = // abstract

absprop DOM (imap, iset) // domain
absprop RANGE (imap, iset) // range

absprop MAP (m:imap, x:int, y:int) // m(x) = y
absprop MAPNOT (m: imap, x: int) // x not in dom(m)

(* ****** ****** *)

absprop ADD (imap, imap, imap)

prfun
ADD_lemma1
  {m1,m2,m3:imap} {x,y:int} (
  pf: ADD (m1,m2,m3), pfm1: MAP (m1, x, y)
) : MAP (m3, x, y)

prfun
ADD_lemma2 {m1,m2,m3:imap} {x,y:int} (
  pf: ADD (m1,m2,m3), pfm1: MAPNOT (m1, x), pfm2: MAP (m2, x, y)
) : MAP (m3, x, y)

(* ****** ****** *)

absprop COMPOSE (imap, imap, imap)

prfun
COMPOSE_lemma
  {m1,m2,m3:imap}
  {x1,x2,x3:int} (
  pf: COMPOSE (m1, m2, m3)
, pfm1: MAP (m1, x1, x2), pfm2: MAP (m2, x2, x3)
) : MAP (m3, x1, x3)

(* ****** ****** *)

(* end of [finmap.sats] *)