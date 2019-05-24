%% dataview array_v (a:viewt@ype+, int(*size*), addr(*beg*)) =
%%   | {n:nat} {l:addr}
%%     array_v_cons (a, n+1, l) of (a @ l, array_v (a, n, l+sizeof a))
%%   | {l:addr} array_v_nil (a, 0, l)
\begin{verbatim}
fn{a:t@ype} array_get_elt_at {n,i:nat | i < n} {l:addr}
  (pf: !array_v (a, n, l) | p: ptr l, i: int i): a = let
  val (pf_mul | ofs) = i imul2 sizeof<a>
  prval @(pf1, pf2) = array_v_split {a} {n,i} (pf_mul, pf)
  prval array_v_cons (pf21, pf22) = pf2
  val x = ptr_get_t<a> (pf21 | p + ofs)
  prval pf2 = array_v_cons {a} (pf21, pf22)
  prval () = pf := array_v_unsplit {a} {i,n-i} (pf_mul, pf1, pf2)
in
  x
end // end of [array_get_elt_at]

fn{a:t@ype} array_set_elt_at {n,i:nat | i < n} {l:addr}
  (pf: !array_v (a, n, l) | p: ptr l, i: int i, x: a): void = let
  val (pf_mul | ofs) = i imul2 sizeof<a>
  prval @(pf1, pf2) = array_v_split {a} {n,i} (pf_mul, pf)
  prval array_v_cons (pf21, pf22) = pf2
  val () = ptr_set_t<a> (pf21 | p + ofs, x)
  prval pf2 = array_v_cons {a} (pf21, pf22)
  prval () = pf := array_v_unsplit {a} {i,n-i} (pf_mul, pf1, pf2)
in
  // empty
end // end of [array_set_elt_at]
\end{verbatim}
