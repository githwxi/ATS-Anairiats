//\begin{verbatim}
extern prfun lemma_i_mul_i_gte_0
  {i:int} (pf: MUL (i, i, ii)): [ii>=0] void

implement lemma_i_mul_i_gte_0 (pf) = let
  prfun aux1 {m:nat,n:int} .<m>.
    (pf: MUL (m, n, p)): MUL (m, n-1, p-m) = case+ pf of
    | MULbas () => MULbas ()
    | MULind (pf1) => MULind (aux1 (pf1))

  prfun aux2 {m:nat,n:int} .<m>.
    (pf: MUL (m, n, p)): MUL (m, ~n, ~p) = case+ pf of
    | MULbas () => MULbas ()
    | MULind (pf1) => MULind (aux2 (pf1))

  prfun aux3 {n:nat;p:int} (pf: MUL (n, n, p)): [p>=0] void = case+ pf of
    | MULbas () => ()
    | MULind (pf1) => let val () = aux3 (aux1 (pf1)) in () end
in
  case+ (pf) of
  | MULneg (pf1) => aux3 (aux2 (pf1))
  | _ => aux3 (pf)
end // end of [lemma_mul_one_to_one]
//\end{verbatim}
