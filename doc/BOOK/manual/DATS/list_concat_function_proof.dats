\begin{verbatim}
fun{a:t@ype} concat {m,n:nat}
  (xss: list (list (a, n), m)): [p:nat] (MUL (m, n, p) | list (a, p)) =
  case+ xss of
  | list_cons (xs, xss) => let
      val (pf | res) = concat xss
    in
      (MULind pf | list_append<a> (xs, res))
    end
  | list_nil () => (MULbas () | list_nil ())
\end{verbatim}
