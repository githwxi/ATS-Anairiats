//\begin{verbatim}
dataprop TALLY (int, int) =
  | TALLYbas (0, 0)
  | {n:nat;r:int} TALLYind (n+1, n+1+r) of TALLY (n, r)

extern fun tally {n:nat} (n: int n): [r:int] (TALLY (n, r) | int r)

implement tally (n) = let
  fun loop {n,i,r:int | 0 < i; i <= n+1}
    (pf: TALLY (i-1, r) | n: int n, i: int i, r: int r)
    : [r:int] (TALLY (n, r) | int r) =
    if i <= n then loop (TALLYind pf | n, i + 1, r + i) else (pf | r)
in
  loop (TALLYbas () | n, 1, 0)
end // end of [tally]
//\end{verbatim}
