#define NONDEPENDENT 0

#if NONDEPENDENT #then

fn isqrt (x: int): int = let
  fun search (x: int, l: int, r: int): int = let
    val diff = r - l
  in
    case+ 0 of
    | _ when diff > 0 => let
        val m = l + (diff / 2)
      in
        if x / m < m then search (x, l, m) else search (x, m, r)
      end // end of [if]
    | _ => l
  end // end of [search]
in
  search (x, 0, x)
end // end of [isqrt]

#else

fn isqrt {x:nat} (x: int x): int = let
  fun search {x,l,r:nat | l < r} .<r-l>.
    (x: int x, l: int l, r: int r): int = let
    val diff = r - l
  in
    case+ 0 of
    | _ when diff > 0 => let
        val m = l + (diff / 2)
      in
        if div_int_int (x, m) < m then search (x, l, m) else search (x, m, r)
      end // end of [if]
    | _ => l
  end // end of [search]
in
  search (x, 0, x)
  // if x > 0 then search (x, 0, x) else 0
end // end of [isqrt]

#endif

implement main (argc, argv) = let
  val () = assert (argc >= 2)
  val n = int1_of argv.[1]
  val () = assert (n >= 0)
in
  printf ("isqrt (%i) = %i\n", @(n, isqrt n))
end
