//\begin{verbatim}
extern prfun lemma_mul_distributive {m,n1,n2,p1,p2:int}
  (pf1: MUL (m, n1, p1), pf2: MUL (m, n2, p2)): MUL (m, n1+n2, p1+p2)

implement lemma_mul_distributive (pf1, pf2) = let
  prfun aux {m:nat;n1,n2,p1,p2:int} .<m>.
    (pf1: MUL (m, n1, p1), pf2: MUL (m, n2, p2)): MUL (m,n1+n2,p1+p2) =
    case+ (pf1, pf2) of
    | (MULbas (), MULbas ()) => MULbas ()
    | (MULind pf1, MULind pf2) => MULind (aux (pf1, pf2))
in
  case+ (pf1, pf2) of
  | (MULneg pf1, MULneg pf2) => MULneg (aux (pf1, pf2))
  | (_, _) =>> aux (pf1, pf2)
end // end of [lemma_mul_distributive]
//\end{verbatim}
