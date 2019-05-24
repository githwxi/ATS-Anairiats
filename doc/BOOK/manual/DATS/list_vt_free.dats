\begin{verbatim}
fn{a:t@ype} list_vt_free {n:nat}
  (xs: list_vt (a, n)):<> void = loop (xs) where {
  fun loop {i:nat} .<i>.
    (xs: list_vt (a, i)):<> void = case+ xs of
    | ~list_vt_cons (_, xs1) => loop (xs1) | ~list_vt_nil () => ()
  // end of [loop]
} // end of [list_vt_free]
\end{verbatim}
