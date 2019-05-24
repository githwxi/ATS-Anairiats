\begin{verbatim}
fun fact (x: int): int = let
  fun loop {l:addr} (pf: !int @ l | x: int, p_res: ptr l): void =
    if x > 0 then (!p_res := !p_res * x; loop (pf | x-1, p_res)) else ()
  var res: int = 1
in
  loop (view@ (res) | x, &res); res
end // end of [fact]
\end{verbatim}
%%
%%implement main () = begin
%%  printf ("fact (%i) = %i", @(10, fact 10)); print_newline ()
%%end
