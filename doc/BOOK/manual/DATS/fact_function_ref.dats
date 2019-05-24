%%staload _(*anonymous*) = "prelude/DATS/reference.dats"
%%
\begin{verbatim}
fun fact (x: int): int = let
  val res = ref<int> (1)
  fun loop (x: int):<cloref1> void =
    if x > 0 then (!res := !res * x; loop (x-1))
in
  loop (x); !res
end // end of [fact]
\end{verbatim}
%%
%%implement main () = begin
%%  printf ("fact (%i) = %i", @(10, fact 10)); print_newline ()
%%end
