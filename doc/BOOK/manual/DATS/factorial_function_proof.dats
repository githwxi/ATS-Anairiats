\begin{verbatim}
dataprop FACT (int, int) =
  | FACTbas (0, 1)
  | {n:nat;r,r1:int} FACTind (n+1, r1) of (FACT (n, r), MUL (r, n+1, r1))

infixl imul2 // left-associative infix operator
extern fun imul2 {m,n:int}
  (m: int m, n: int n): [p:int] (MUL (m, n, p) | int p)

extern fun fact {n:nat} (n: int n): [r:int] (FACT (n, r) | int r)

implement fact (n) = // a non-tail-recursive implementation
  if n > 0 then let
    val (pf | r) = fact (n-1); val (pf_mul | r1) = r imul2 n
  in
    (FACTind (pf, pf_mul) | r1)
  end else begin
    (FACTbas () | 1)
  end // end of [if]

implement fact (n) = let // a tail-recursive implementation
  fun loop {n,i,r:int | 0 < i; i <= n+1} .<n+1-i>.
    (pf: FACT (i-1, r) | n: int n, i: int i, r: int r)
    : [r:int] (FACT (n, r) | int r) =
    if i > n then (pf | r) else let
      val (pf_mul | r1) = r imul2 i; prval pf1 = FACTind (pf, pf_mul)
    in
      loop (pf1 | n, i + 1, r1)
    end // end of [if]
in
  loop (FACTbas () | n, 1, 1)
end // end of [fact]
\end{verbatim}
