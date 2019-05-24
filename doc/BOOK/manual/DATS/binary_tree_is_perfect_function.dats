\begin{verbatim}
datatype tree = E | B of (tree, int, tree) // for integer binary trees

fn isPerfect (t: tree): bool = let
  exception NotPerfect
  fun aux (t: tree): int = case+ t of
    | B (t1, _, t2) => let
        val h1 = aux (t1) and h2 = aux (t2)
      in
        if h1 = h2 then h1 + 1 else $raise NotPerfect ()
      end
    | E () => 0
in
  try let val _ = aux (t) in true end with ~NotPerfect () => false
end // end of [isPerfect]
\end{verbatim}
