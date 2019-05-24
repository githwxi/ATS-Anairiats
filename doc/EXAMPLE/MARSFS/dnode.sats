(*
** Specifying Finite Lists
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

sortdef clist = ilist
datasort dnode = // abstract

absprop inumber_p (dnode, int)
absprop content_p (dnode, clist)

(* ****** ****** *)

praxi
DNODE_content_axiom
  {dn:dnode} {cs:clist} {n:int} (
  pf: content_p (dn, cs), pflen: LENGTH (cs, n)
) : [n >= 1] void

(* ****** ****** *)

(* end of [dnode.sats] *)
