//
// code used for illustration in casting-functions.dats
//

(* ****** ****** *)

extern fun{a:t@ype} list_concat (xss: List (List a)): List a

(* ****** ****** *)

datatype lstlst (a:t@ype+, int, int) =
  | {m,t:nat} {n:nat}
    lstlst_cons (a, m+1, t+n) of (list (a, n), lstlst (a, m, t))
  | lstlst_nil (a, 0, 0) of ()

fun{a:t@ype} _concat {m,t:nat} .<m>.
  (xss: lstlst (a, m, t)): list (a, t) = case+ xss of
  | lstlst_cons (xs, xss) => list_append (xs, _concat<a> xss)
  | lstlst_nil () => list_nil ()
// end of [_concat]

(* ****** ****** *)

implement{a} list_concat (xss) =
  _concat<a> (lstlst_of_listlist xss) where {
  castfn lstlst_of_listlist
    {m:nat} .<m>. (xss: list (List a, m))
    :<> [t:nat] lstlst (a, m, t) = case+ xss of
    | list_cons (xs, xss) => lstlst_cons (xs, lstlst_of_listlist xss)
    | list_nil () => lstlst_nil ()
} // end of [list_concat]

(* ****** ****** *)

(* end of [casting-functions.dats] *)
