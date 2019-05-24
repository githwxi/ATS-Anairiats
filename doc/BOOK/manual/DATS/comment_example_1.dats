\begin{verbatim}
fun f91 (x: int): int = // we implement the famous McCarthy's 91-function
  (* this function always return 91 when applied to an integer less than 101 *)
  if x < 101 then f91 (f91 (x + 11)) else x - 10
//// whatever written here or below is considered comment
\end{verbatim}
