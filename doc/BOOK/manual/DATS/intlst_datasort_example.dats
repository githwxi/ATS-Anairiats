\begin{verbatim}
datasort intlst = intlst_nil of () | intlst_cons of (int, intlst)

dataprop int_intlst_lte (int, intlst) =
  | {i:int} {x:int | i <= x} {xs:intlst}
      int_intlst_lte_cons (i, intlst_cons (x, xs)) of int_intlst_lte (i, xs)
  | {i:int} int_intlst_lte_nil (i, intlst_nil ())

// if i <= j and j <= x for each x in xs, then i <= x for each x in xs
prfun int_intlst_lte_lemma
  {i,j:int | i <= j} {xs: intlst} .<xs>.
  (pf: int_intlst_lte (j, xs)): int_intlst_lte (i, xs) = case+ pf of
  | int_intlst_lte_cons (pf) => int_intlst_lte_cons (int_intlst_lte_lemma pf)
  | int_intlst_lte_nil () => int_intlst_lte_nil ()
// end of [int_intlst_lte_lemma]

prfun intlst_lower_bound_lemma
  {xs:intlst} .<xs>. (): [x_lb:int] int_intlst_lte (x_lb, xs) =
  scase xs of
  | intlst_cons (x1, xs1) => let
      prval [x1_lb:int] pf1 = intlst_lower_bound_lemma {xs1} ()
    in
      sif x1 <= x1_lb then begin // static conditional
        int_intlst_lte_cons (int_intlst_lte_lemma {x1, x1_lb} (pf1))
      end else begin
        int_intlst_lte_cons (pf1)
      end // end of [sif]
    end // end of [intlst_cons]
  | intlst_nil () => int_intlst_lte_nil {0} ()
// end of [intlst_lower_bound_lemma]
\end{verbatim}