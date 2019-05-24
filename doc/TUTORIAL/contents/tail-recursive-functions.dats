//
// code used for illustration in tail-recursive-functions.html
//

// [sum1] is recursive but not tail-recursive
fun sum1 (n: int): int = if n > 0 then n + sum1 (n-1) else 0

%{

int sum1 (int n) {
  if (n > 0) return n + sum1 (n-1) ; else return 0 ;
}

%}

fn sum2 (n: int): int = let // sum2 is non-recursive
  // [loop] is tail-recursive
  fun loop (n: int, res: int): int =
    if n > 0 then loop (n-1, res+n) else res
  // end of [loop]
in
  loop (n, 0)
end // end of [sum2]

%{

int sum2_loop (int n, int res) {
  loop:
  if (n > 0) {
    res = res + n ; n = n - 1; goto loop; 
  } else {
    return res;
  }
}

int sum2 (int n) { return sum2_loop (n, 0) ; }

%}

// [fn*] indicates the need to combine two or more functions
// so as to translate tail-recursive calls into direct jumps
fn* even (n: int): bool = if n > 0 then odd (n-1) else true
and odd (n: int): bool = if n > 0 then even (n-1) else false

%{

#define true 1
#define false 0
typedef int bool ;

bool even_odd (int tag, int n) {

bool res ;

switch (tag) {
  case 0: goto even ;
  case 1: goto odd ;
  default: exit (1) ; /* should never happen! */
}

even: if (n > 0) { n = n - 1; goto odd; } else { res = true; goto done; }

odd: if (n > 0) { n = n - 1; goto even; } else { res = false; goto done; }

done: return res ;

}

bool even (int n) { return even_odd (0, n) ; }
bool odd (int n) { return even_odd (1, n) ; }

%}

(* ****** ****** *)

(*

// code in C
int main (int argc, char *argv[]) {
  int i, j ;

  for (i = 0; i <= 9; i += 1) {
    for (j = i; j <= 9; j += 1) {
      if (i < j) printf (", ") ; printf ("(%i, %i)", i, j) ;
    }
    printf ("\n") ;
  }

  return 0 ;
}

*)

implement main (argc, argv) = let
  fn* loop1 {i:nat} (i: int i): void =
    if i <= 9 then loop2 (i, i) else ()
  // end of [loop1]

  and loop2 {i,j:nat} (i: int i, j: int j): void =
    if j <= 9 then begin
      if i < j then begin
        print ", "; printf ("(%i, %i)", @(i, j)); loop2 (i, j+1)
      end // end of [if]
    end else begin
      print_newline (); loop1 (i+1)
    end // end of [if]
  // end of [loop2]
in
  loop1 0
end // end of [main]

(* ****** ****** *)

(* end of [tail-recursive-functions.dats] *)
