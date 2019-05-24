%%staload "prelude/DATS/array.dats"
%%staload "prelude/DATS/array0.dats"
\begin{verbatim}
fn fact (x: int): int = let
  // creating an array of size [x] and initialing it with 0's
  val A = array0_make_elt<int> (x, 0)  
  val () = init (0) where { // initializing [A] with 1, ..., n
    fun init (i: int):<cloref1> void =
      if i < x then (A[i] := i + 1; init (i + 1)) else ()
  } // end of [where]
  fun loop (i: int, res: int):<cloref1> int =
    if i < x then loop (i+1, res * A[i]) else res
in
  loop (0(*i*), 1(*res*))
end // end of [fact]
\end{verbatim}
%%
%%implement main () = begin
%%  printf ("fact(%i) = %i\n", @(10, fact 10))
%%end
%%
