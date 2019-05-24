%extern
%fun{a:t@ype} ptr_get1 {l:addr} (pf: !a @ l >> a @ l | p: ptr l): a
%
%extern
%fun{a:t@ype} ptr_set1 {l:addr} (pf: !a? @ l >> a @ l | p: ptr l, x: a): void
\begin{verbatim}
fn{a:t@ype} swap1 {l1,l2:addr}
  (pf1: !a @ l1, pf2: !a @ l2 | p1: ptr l1, p2: ptr l2): void = let
  val tmp = !p1
in
  !p1 := !p2; !p2 := tmp
end // end of [swap1]
\end{verbatim}
