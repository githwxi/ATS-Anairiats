\begin{verbatim}
extern fun{a:t@ype} list_append {n1,n2:nat}
  (xs: list (a, n1), ys: list (a, n2)): list (a, n1+n2)

// [concat] does not typecheck due to nonlinear constraints
fun{a:t@ype} concat {m,n:nat}
  (xss: list (list (a, n), m)): list (a, m * n) =
  case+ xss of
  | list_cons (xs, xss) => list_append<a> (xs, concat xss)
  | list_nil () => list_nil ()
\end{verbatim}
