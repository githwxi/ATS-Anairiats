fn sum2 (n: int): int = let // sum2 is non-recursive
  fun loop (n: int, res: int): int = // [loop] is tail-recursive
    if n > 0 then loop (n-1, res+n) else res
in
  loop (n, 0)
end // end of [sum2]
