\begin{verbatim}
fn{a:viewt@ype} list_vt_length
  {n:nat} (xs: !list_vt (a, n)):<> int n = let
  fun loop {i,j:nat} .<i>.
    (xs: !list_vt (a, i), j: int j):<> int (i+j) =
    case+ xs of
    | list_vt_cons (_, !p_xs1) =>
        let val n = loop (!p_xs1, j+1) in fold@ xs; n end
    | list_vt_nil () => (fold@ xs; j)
  // end of [loop]
in
 loop (xs, 0)
end // end of [list_vt_length]
\end{verbatim}
