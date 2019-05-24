\begin{verbatim}
val sin_deriv = derivate (lam x => sin x)
val PI = 4 * (atan 1.0); val theta = PI / 3
val one = // [one] approximately equals 1.0
  square (sin theta) + square (sin_deriv theta)
\end{verbatim}
