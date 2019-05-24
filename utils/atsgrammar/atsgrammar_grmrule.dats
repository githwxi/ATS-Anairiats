(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)

typedef _grmrule = '{
  grmrule_kind= int // 0/1 : original/derived
, grmrule_merged= int // 0/1 : available/superceded
, grmrule_action= Stropt
, grmrule_precval= Stropt
, grmrule_symreglst= List (symreg)
} // end of [grmrule]

local

assume grmrule = _grmrule

in // in of [local]

implement
grmrule_make_symlst
  (xs) = let
  val xs =
    list_map_fun<symbol><symreg> (xs, lam x =<1> SYMREGlit (x))
  // end of [val]
  val xs = list_of_list_vt (xs)
in
  grmrule_make_symreglst (0(*original*), xs)
end // end of [grmrule_make_symlst]

implement
grmrule_make_symreglst (knd, xs) = '{
  grmrule_kind= knd
, grmrule_merged= 0
, grmrule_action= stropt_none
, grmrule_precval= stropt_none
, grmrule_symreglst= xs
} // end of [grmrule_make_symreglst]

(* ****** ****** *)

implement grmrule_get_kind (gr) = gr.grmrule_kind
implement grmrule_get_merged (gr) = gr.grmrule_merged
implement grmrule_get_action (gr) = gr.grmrule_action
implement grmrule_get_precval (gr) = gr.grmrule_precval
implement grmrule_get_symreglst (gr) = gr.grmrule_symreglst

end // end of [local]

(* ****** ****** *)

implement
grmrule_append_empty () =
  grmrule_append_symlst (list_nil ())
// end of [grmrule_append_empty]

(* ****** ****** *)

implement
grmrule_append_symbol (x) =
  grmrule_append_symlst (list_sing (x))
// end of [grmrule_append_symbol]

(* ****** ****** *)

implement
grmrule_append_symlst
  (xs) = gr where {
  val gr = grmrule_make_symlst (xs)
  val () = theGrmrulelst_add (gr)
} // end of [grmrule_append_symbol]

(* ****** ****** *)

implement
grmrule_append_grmrule
  (gr) = gr where {
  val () = theGrmrulelst_add (gr)
} // end of [grmrule_append_grmrule]

(* ****** ****** *)

extern
typedef "atsgrammar_grmrule_t" = _grmrule

%{$
//
ats_void_type
atsgrammar_grmrule_set_kind
  (ats_ptr_type sym, ats_int_type knd) {
  ((atsgrammar_grmrule_t)sym)->atslab_grmrule_kind = knd ;
  return ;
} /* end of [atsgrammar_grmrule_set_kind] */
//
ats_void_type
atsgrammar_grmrule_set_merged
  (ats_ptr_type sym, ats_int_type merged) {
  ((atsgrammar_grmrule_t)sym)->atslab_grmrule_merged = merged ;
  return ;
} /* end of [atsgrammar_grmrule_set_merged] */
//
ats_void_type
atsgrammar_grmrule_set_action
  (ats_ptr_type sym, ats_ptr_type action) {
  ((atsgrammar_grmrule_t)sym)->atslab_grmrule_action = action ;
  return ;
} /* end of [atsgrammar_grmrule_set_action] */
//
ats_void_type
atsgrammar_grmrule_set_precval
  (ats_ptr_type sym, ats_ptr_type precval) {
  ((atsgrammar_grmrule_t)sym)->atslab_grmrule_precval = precval ;
  return ;
} /* end of [atsgrammar_grmrule_set_precval] */
//
%} // end of [%{$]

(* ****** ****** *)

(* end of [atsgrammar_grmrule.dats] *)
