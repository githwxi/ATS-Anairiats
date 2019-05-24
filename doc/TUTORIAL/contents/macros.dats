#define PI 3.1416

// macros in long form

macrodef square_mac (r) = `(,(r) * ,(r))

fun square_fun (i: int) = ,(square_mac `(i))
fun area_of_circle_fun (r: double): double = PI * ,(square_mac `(r))

// macros in short form

macdef square_mac (r) = ,(r) * ,(r)

fun square_fun (i: int) = square_mac (i)
fun area_of_circle_fun (r: double): double = PI * square_mac (r)

//

macdef min (x, y) = if ,(x) <= ,(y) then ,(x) else ,(y)
macdef max (x, y) = if ,(x) <= ,(y) then ,(y) else ,(x)

//

// recursive macro definition
macrodef rec power (x(*code*), n(*int*)) =
  if n > 0 then `(,(x) * ,(power (x, n))) else `(1)

(* [power (3, `(x))] expands to [`(x * (x * (x * 1)))] *)

(* ****** ****** *)

(* end of [macros.dats] *)
