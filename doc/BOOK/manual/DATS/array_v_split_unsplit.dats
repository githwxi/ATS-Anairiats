\begin{verbatim}
prfun array_v_split
  {a:viewt@ype} {n,i:nat | i <= n} {l:addr} {ofs:int} .<i>.
  (pf_mul: MUL (i, sizeof a, ofs), pf_arr: array_v (a, n, l))
  : @(array_v (a, i, l), array_v (a, n-i, l+ofs)) =
  sif i > 0 then let
    prval array_v_cons (pf1_elt, pf2_arr) = pf_arr
    // pf1_mul : MUL (i-1, sizeof a, ofs - sizeof a)
    prval pf1_mul = mul_add_const {~1} {i, sizeof a} (pf_mul)
    prval (pf1_arr_res, pf2_arr_res) =
      array_v_split {a} {n-1,i-1} (pf1_mul, pf2_arr)
  in
    @(array_v_cons {a} (pf1_elt, pf1_arr_res), pf2_arr_res)
  end else let
    prval MULbas () = pf_mul
  in
    (array_v_nil {a} {l} (), pf_arr)
  end // end of [sif]
// end of [array_v_split]

prfun array_v_unsplit
  {a:viewt@ype} {n1,n2:nat} {l:addr} {ofs:int} .<n1>. (
    pf_mul: MUL (n1, sizeof a, ofs)
  , pf1_arr: array_v (a, n1, l)
  , pf2_arr: array_v (a, n2, l+ofs)
  ) : array_v (a, n1+n2, l) =
  sif n1 > 0 then let
    prval array_v_cons (pf11_elt, pf12_arr) = pf1_arr
    // pf1_mul : MUL (n1-1, sizeof a, ofs - sizeof a)
    prval pf1_mul = mul_add_const {~1} {n1, sizeof a} (pf_mul)
    prval pf_arr_res = array_v_unsplit {a} (pf1_mul, pf12_arr, pf2_arr)
  in
    array_v_cons {a} (pf11_elt, pf_arr_res)
  end else let
    prval array_v_nil () = pf1_arr; prval MULbas () = pf_mul
  in
    pf2_arr
  end // end of [sif]
// end of [array_v_unsplit]
\end{verbatim}
