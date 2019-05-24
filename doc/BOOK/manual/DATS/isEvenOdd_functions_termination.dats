\begin{verbatim}
fun isEven {n:nat} .<2*n>. (x: int n): bool =
  if x > 0 then isOdd (x - 1) else true

and isOdd {n:nat} .<2*n+1>. (x: int n): bool =
  not (isEven x)
\end{verbatim}
