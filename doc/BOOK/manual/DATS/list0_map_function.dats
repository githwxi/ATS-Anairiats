\begin{verbatim}
fun{a,b:t@ype} list0_map
  (xs: list0 a, f: a -<cloref1> b): list0 b = case+ xs of
  | list0_cons (x, xs) => list0_cons (f x, list0_map (xs, f))
  | list0_nil () => list0_nil ()
\end{verbatim}
