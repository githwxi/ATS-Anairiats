(* ****** ****** *)

local

abst@ype qset = $extype "scull_qset_struct"

in // in of [local]

extern
fun qset_get_next
  : slnode_get_next_type (qset) = "scull_qset_get_next"
implement slnode_get_next<qset> (pf | p) = qset_get_next (pf | p)

extern
fun qset_set_next
  : slnode_set_next_type (qset) = "scull_qset_set_next"
implement slnode_set_next<qset> (pf | p, n) = qset_set_next (pf | p, n)

extern
fun qset_alloc
  : slnode_alloc_type (qset) = "scull_qset_alloc"
implement slnode_alloc<qset> () = qset_alloc ()

extern
fun qset_free
  : slnode_free_type (qset) = "scull_qset_free"
implement slnode_free<qset> (pf | p) = qset_free (pf | p)

end // end of [local]

(* ****** ****** *)

(* end of [scull_qsetlst.hats] *)
