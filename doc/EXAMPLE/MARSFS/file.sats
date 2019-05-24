(*
** Specifying Finite Lists
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

staload DNODE = "dnode.sats"
sortdef dnode = $DNODE.dnode

(* ****** ****** *)

sortdef clist = ilist
datasort file = // abstract

absprop name_p (file, clist)
absprop dnode_p (file, dnode)

(* ****** ****** *)

(*
absprop NORMALFILE (file)
absprop SPECIALFILE (file)
*)

(* ****** ****** *)

praxi
FILE_name_axiom
  {f:file} {cs:clist} {n:int} (
  pf: name_p (f, cs), pflen: LENGTH (cs, n)
) : [n >= 1] void

(* ****** ****** *)

absprop content_p (file, ilist)
absprop read_p (f: file, n:int, c:int)

praxi
FILE_read_axiom
  {f:file} {n:int} {c:int} {cs:clist} (
  pf: read_p (f, n, c), pf: content_p (f, cs)
) : NTH (c, cs, n)

(* ****** ****** *)

(* end of [file.sats] *)
