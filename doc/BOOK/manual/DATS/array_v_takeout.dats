%% dataview array_v (a:viewt@ype+, int(*size*), addr(*beg*)) =
%%  | {n:nat} {l:addr}
%%    array_v_cons (a, n+1, l) of (a @ l, array_v (a, n, l+sizeof a))
%%  | {l:addr} array_v_nil (a, 0, l)
\begin{verbatim}
prfun array_v_takeout {a:viewt@ype}
  {n,i:nat | i < n} {l:addr} {ofs:int} .<n>.
  (pf_mul: MUL (i, sizeof a, ofs), pf_arr: array_v (a, n, l))
  : (a @ l+ofs, a @ l+ofs -<lin> array_v (a, n, l)) = let
  prval array_v_cons (pf1_at, pf2_arr) = (pf_arr)
in
  sif i > 0 then let
    prval pf1_mul = mul_add_const {~1} {i, sizeof a} (pf_mul)
    prval (pf_at, fpf_rst) = array_v_takeout {a} {n-1,i-1} (pf1_mul, pf2_arr)
  in
    (pf_at, llam pf_at =<prf> array_v_cons {a} (pf1_at, fpf_rst pf_at))
  end else let
    prval () = mul_elim {0,sizeof a} (pf_mul)
  in
    (pf1_at, llam pf_at =<prf> array_v_cons {a} (pf_at, pf2_arr))
  end // end of [sif]
end // end of [array_v_takeout]

fn{a:t@ype} array_get_elt_at {n,i:nat | i < n} {l:addr}
  (pf: !array_v (a, n, l) | p: ptr l, i: int i): a = let
  val (pf_mul | ofs) = i imul2 sizeof<a>
  prval @(pf_at, fpf_rst) = array_v_takeout {a} {n,i} (pf_mul, pf)
  val x = ptr_get_t<a> (pf_at | p + ofs)
  prval () = pf := fpf_rst (pf_at)
in
  x
end // end of [array_get_elt_at]

fn{a:t@ype} array_set_elt_at {n,i:nat | i < n} {l:addr}
  (pf: !array_v (a, n, l) | p: ptr l, i: int i, x: a): void = let
  val (pf_mul | ofs) = i imul2 sizeof<a>
  prval @(pf_at, fpf_rst) = array_v_takeout {a} {n,i} (pf_mul, pf)
  val () = ptr_set_t<a> (pf_at | p + ofs, x)
  prval () = pf := fpf_rst (pf_at)
in
  // empty
end // end of [array_set_elt_at]
\end{verbatim}
