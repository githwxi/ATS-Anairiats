\begin{verbatim}
fun ack {m,n:nat} .<m,n>. (x: int m, y: int n): [r:nat] int r =
  if x > 0 then
    if y > 0 then ack (x - 1, ack (x, y - 1)) else ack (x - 1, 1)
  else y + 1
\end{verbatim}
