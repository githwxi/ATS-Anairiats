(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: December, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) =
  "prelude/DATS/reference.dats"
// end of [staload]

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

local

val theTynamelst = ref<tynamelst_vt> (list_vt_nil)

in // in of [local]

implement
theTynamelst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theTynamelst)
  val ts = !p
  val () = !p := list_vt_nil
in
  ts
end // end of [theTynamelst_get]

implement
theTynamelst_add (x) = let
  val (vbox pf | p) = ref_get_view_ptr (theTynamelst)
in
  !p := list_vt_cons (x, !p)
end // end of [theTynamelst_add]

end // end of [local]

(* ****** ****** *)

local

val theSymbolStampCount = ref<int> (0)

in // in of [local]

implement theSymbolStampCount_getinc () = let
  val n = !theSymbolStampCount in !theSymbolStampCount := n+1; n
end // end of [theSymbolStampCount]

end // end of [local]

(* ****** ****** *)

local

val theSymlst = ref<symlst_vt> (list_vt_nil)

in // in of [local]

implement
theSymlst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theSymlst)
  val xs = !p
  val () = !p := list_vt_nil ()
in
  xs
end // end of [theSymlst]

implement
theSymlst_add (x) = let
  val (vbox pf | p) = ref_get_view_ptr (theSymlst)
in
  !p := list_vt_cons (x, !p)
end // end of [theSymlst_add]

end // end of [local]

(* ****** ****** *)

local

val theGrmrulelst = ref<grmrulelst_vt> (list_vt_nil)

in // in of [local]

implement
theGrmrulelst_get () = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
  val grs = !p
  val () = !p := list_vt_nil ()
in
  grs
end // end of [theGrmrulelst_get]

implement
theGrmrulelst_add (gr) = let
  val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
in
  !p := list_vt_cons (gr, !p)
end // end of [theGrmrulelst_add]

implement
theGrmrulelst_merge_all
  (sym, xs) = let
//
  fun loop {n:nat} .<n>.
    (grs: !list_vt (grmrule, n)): void =
    case+ grs of
    | list_vt_cons (gr, !p_grs) => let
        val () = grmrule_set_merged (gr, 1)
        val () = loop (!p_grs)
        val () = fold@ (grs)
      in
        // nothing
      end // end of [val]
    | list_vt_nil () => fold@ (grs)
  // end of [loop]
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (theGrmrulelst)
  in
    $effmask_ref (loop (!p))
  end // end of [val]
//
  val gr = grmrule_make_symreglst (1, list_sing (xs))
  val () = theGrmrulelst_add (gr)
in
  // nothing
end // end of [theGrmrulelst_merge]

end // end of [local]

(* ****** ****** *)

(* end of [atsgrammar_global.dats] *)
