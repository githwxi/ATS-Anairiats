(*
** Specifying Finite Lists
*)

staload "libats/SATS/ilistp.sats"

(*
datasort ilist =
  | ilist_nil of () | ilist_cons of (int, ilist)
// end of [ilist]
*)
stadef nil () = ilist_nil ()
stadef cons (x: int, xs: ilist) = ilist_cons (x, xs)

(* ****** ****** *)

dataprop HEAD (ilist, int) =
  | {x:int} {xs:ilist} HEAD (cons (x, xs), x)
// end of [HEAD]

dataprop TAIL (ilist, ilist) =
  | {x:int} {xs:ilist} HEAD (cons (x, xs), xs)
// end of [TAIL]

(*
dataprop
LENGTH (ilist, int) =
  | LENGTHnil (ilist_nil, 0) of ()
  | {x:int} {xs:ilist} {n:nat}
    LENGTHcons (ilist_cons (x, xs), n+1) of LENGTH (xs, n)
// end of [LENGTH]
*)

(*
dataprop APPEND (ilist, ilist, ilist) =
  | {ys:ilist} APPENDnil (ilist_nil, ys, ys) of ()
  | {x:int} {xs:ilist} {ys:ilist} {zs:ilist}
    APPENDcons (ilist_cons (x, xs), ys, ilist_cons (x, zs)) of APPEND (xs, ys, zs)
// end of [APPEND]
*)

(* ****** ****** *)

(* end of [finlst.sats] *)


