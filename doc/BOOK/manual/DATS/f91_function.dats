\begin{verbatim}
fun f91 {i:int} .<max(101-i,0)>. (x: int i)
  : [j:int | (i <= 100 && j == 91) || (i > 100 && j == i-10)] int j =
  if x > 100 then x-10 else f91 (f91 (x+11))
\end{verbatim}
