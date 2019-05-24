\begin{verbatim}
#define :: stream_cons // using [::] as a shorthand for [stream_cons]

fun from (n: int):<1,~ref> stream (int) = $delay (n :: from (n+1))

fun sieve (ns: stream int):<1,~ref> stream int = let
  val- n :: ns = lazy_force ns // [val-]: suppressing the warning message that
  // would otherwise be issued due to the non-exhautiveness of pattern matching
in
  $delay (n :: sieve (stream_filter<int> (ns, lam x => x mod n <> 0)))
end // end of [sieve]

val primes: stream int = sieve (from 2)
\end{verbatim}
