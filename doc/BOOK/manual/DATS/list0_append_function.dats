\begin{verbatim}
fun{a:t@ype} list0_append (xs: list0 a, ys: list0 a): list0 a =
  case+ xs of
  | list0_cons (x, xs) => list0_cons (x, list0_append (xs, ys))
  | list0_nil () => ys
\end{verbatim}
