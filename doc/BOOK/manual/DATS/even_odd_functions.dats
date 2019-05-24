\begin{verbatim}
fun even (x: int): bool = if x > 0 then odd (x-1) else true
and odd (x: int): bool = if x > 0 then even (x-1) else false
\end{verbatim}
