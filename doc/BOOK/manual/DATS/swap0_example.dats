%extern
%fun{a:t@ype} ptr_get0 {l:addr} (pf: a @ l | p: ptr l): @(a @ l | a)
%extern
%fun{a:t@ype} ptr_set0 {l:addr} (pf: a? @ l | p: ptr l, x: a): @(a @ l | void)
\begin{verbatim}
fn{a:t@ype} swap0 {l1,l2:addr}
  (pf1: a @ l1, pf2: a @ l2 | p1: ptr l1, p2: ptr l2)
  : (a @ l1, a @ l2 | void) = let
  val (pf1 | tmp1) = ptr_get0<a> (pf1 | p1)
  val (pf2 | tmp2) = ptr_get0<a> (pf2 | p2)
  val (pf1 | ()) = ptr_set0<a> (pf1 | p1, tmp2)
  val (pf2 | ()) = ptr_set0<a> (pf2 | p2, tmp1)
in
  (pf1, pf2 | ())
end // end of [swap0]
\end{verbatim}
