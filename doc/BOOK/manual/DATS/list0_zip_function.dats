fun list0_zip {a,b:type}
  (xs: list0 a, ys: list0 b): list0 a = begin case+ (xs, ys) of
  | (list0_cons (x1, list0_cons (x2, xs)), list0_cons (y, ys)) =>
      list0_cons (x1, list0_cons (x2, xs))
  | (list0_cons (x1, list0_cons (x2, xs)), list0_nil ()) => list0_cons (x1, xs)
  | (_, _) => list0_nil ()
end // end of [list0_zip]
