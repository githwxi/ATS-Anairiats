postfix 100 !!
fun !! (x: int): int = if x > 1 then x * (x-2)!! else 1


implement main () = begin
  printf ("%i! = %i\n", @(10, 10!! * 9!!))
end
