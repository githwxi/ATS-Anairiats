\begin{verbatim}
fun{a1,a2,b:t@ype} list_zip_with {n:nat}
  (xs1: list (a1, n), xs2: list (a2, n), f: (a1, a2) -> b): list (b, n) =
  case+ (xs1, xs2) of
  | (list_cons (x1, xs1), list_cons (x2, xs2)) =>
      list_cons (f (x1, x2), list_zip_with (xs1, xs2, f))
  | (_, _) => list_nil ()
\end{verbatim}
