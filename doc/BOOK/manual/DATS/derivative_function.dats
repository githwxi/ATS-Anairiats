%% %{^
%%
%% #include "libc/CATS/math.cats"
%%
%% %}
%%
%% staload "libc/SATS/math.sats"
%%
\begin{verbatim}
val epsilon = 1E-6
// [double -<cloref1> double] is the type for closures representing
// functions from double to double
fn derivate (f: double -<cloref1> double): double -<cloref1> double =
  lam x => (f (x+epsilon) - f (x)) / epsilon
\end{verbatim}
%%
%% val sin_deriv = derivate (lam x => sin x)
%% val PI = 4 * (atan 1.0); val theta = PI / 3
%% val one = square (sin theta) + square (sin_deriv theta)
%%
%% implement main () = begin
%%   printf ("sin(%f) = %f\n", @(theta, sin theta));
%%   printf ("sin_deriv(%f) = %f\n", @(theta, sin_deriv theta));
%%   printf ("one = %f\n", @(one));
%%   print_newline ()
%% end
