(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "fgnode.sats"
staload "tempset.sats"

(* ****** ****** *)

staload TL = "templab.sats"

(* ****** ****** *)

staload "fgraph.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/array0.dats"

(* ****** ****** *)

local

typedef fgnodeinfo = '{
  node= fgnode_t
, ismove= bool
, pred= fgnodelst_t(*pred*)
, succ= fgnodelst_t(*succ*)
, useset= tempset_t, defset= tempset_t
, inset= tempset_t, outset= tempset_t
}

assume fgnodeinfo_t = fgnodeinfo

in // in of [local]

extern typedef "fgnodeinfo_t" = fgnodeinfo

implement fgnodeinfo_make
  (fgn, ismove, uselst, deflst) = let
  val fgns_nil = fgnodelst_nil ()
  val useset = tempset_make_templst (uselst)
  val defset = tempset_make_templst (deflst)
in '{
  node= fgn
, ismove= ismove
, pred= fgns_nil, succ= fgns_nil
, useset= useset, defset= defset
, inset= useset, outset= tempset_nil ()
} end // end of [fgnodeinfo_make]

implement fgnodeinfo_ismove_get (info) = info.ismove
implement fgnodeinfo_pred_get (info) = info.pred
implement fgnodeinfo_succ_get (info) = info.succ
implement fgnodeinfo_useset_get (info) = info.useset
implement fgnodeinfo_defset_get (info) = info.defset
implement fgnodeinfo_inset_get (info) = info.inset
implement fgnodeinfo_outset_get (info) = info.outset

implement fprint_fgnodeinfo (out, info) = () where {
  val () = fprint_string (out, "node= ")
  val () = fprint_fgnode (out, info.node)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "ismove= ")
  val () = fprint_bool (out, info.ismove)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "pred= ")
  val () = fprint_fgnodelst (out, info.pred)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "succ= ")
  val () = fprint_fgnodelst (out, info.succ)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "useset= ")
  val () = fprint_tempset (out, info.useset)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "defset= ")
  val () = fprint_tempset (out, info.defset)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "inset= ")
  val () = fprint_tempset (out, info.inset)
  val () = fprint_newline (out)
//
  val () = fprint_string (out, "outset= ")
  val () = fprint_tempset (out, info.outset)
  val () = fprint_newline (out)
} // end of [fprint_fgnodeinfo]

end // end of [local]

implement print_fgnodeinfo (info) = fprint_fgnodeinfo (stdout_ref, info)
implement prerr_fgnodeinfo (info) = fprint_fgnodeinfo (stderr_ref, info)

(* ****** ****** *)

assume fgraph_t = array0 (fgnodeinfo_t)

(* ****** ****** *)

implement fprint_fgraph (out, fg) = let
  fun loop {n,i:nat | i <= n} {l:addr} .<n-i>. (
      pf_A: !array_v (fgnodeinfo_t, n, l)
    | out: FILEref, p_A: ptr l, n: size_t n, i: size_t i
    ) : void =
    if i < n then let
      val () = fprint_fgnodeinfo (out, p_A->[i]); val () = fprint_newline (out)
    in
      loop (pf_A | out, p_A, n, i+1)
    end // end of [if]
  // end of [loop
  val r_arrsz = array0_get_arrszref (fg)
  val (vbox pf_arrsz | p_arrsz) = ref_get_view_ptr (r_arrsz)
in
  $effmask_ref (
    loop (p_arrsz->1 | out, p_arrsz->2, p_arrsz->3, 0)
  ) // end of [$effmask_ref]
end (* end of [fprint_fgraph] *)

(* ****** ****** *)

implement fgraph_make_elt (n, info) = let
  val asz = size1_of_int1 n in array0_make_elt (asz, info)
end // end of [fgraph_make_elt]

(* ****** ****** *)

implement fgraph_size (fg) = array0_size (fg)

(* ****** ****** *)

implement fgraph_nodeinfo_get (fg, n) = let
  val n = int_of_fgnode (n) in array0_get_elt_at__intsz (fg, n)
end // end of [fgraph_nodeinfo_get]

implement fgraph_nodeinfo_set (fg, n, info) = let
  val n = int_of_fgnode (n) in array0_set_elt_at__intsz (fg, n, info)
end // end of [fgraph_nodeinfo_get]

(* ****** ****** *)

implement fgraph_edge_insert
  (fg, fgn_fr, fgn_to) = () where {
// modifying the representation for [n_fr]
  val () = () where {
    val info = fgraph_nodeinfo_get (fg, fgn_fr)
    val fgns_succ = fgnodeinfo_succ_get (info)
    val fgns_succ = fgnodelst_add (fgns_succ, fgn_to)
    val () = fgnodeinfo_succ_set (info, fgns_succ)
  } // end of [val]
// modifying the representation for [n_to]
  val () = () where {
    val info = fgraph_nodeinfo_get (fg, fgn_to)
    val fgns_pred = fgnodeinfo_pred_get (info)
    val fgns_pred = fgnodelst_add (fgns_pred, fgn_fr)
    val () = fgnodeinfo_pred_set (info, fgns_pred)
  } // end of [val]
} // end of [fgraph_edge_insert]

(* ****** ****** *)

%{$

ats_void_type
fgnodeinfo_pred_set
  (ats_ptr_type info, ats_ptr_type predlst) {
  ((fgnodeinfo_t)info)->atslab_pred = predlst ; return ;
}

ats_void_type
fgnodeinfo_succ_set
  (ats_ptr_type info, ats_ptr_type succlst) {
  ((fgnodeinfo_t)info)->atslab_succ = succlst ; return ;
}

ats_void_type
fgnodeinfo_inset_set
  (ats_ptr_type info, ats_ptr_type inset) {
  ((fgnodeinfo_t)info)->atslab_inset = inset ; return ;
}

ats_void_type
fgnodeinfo_outset_set
  (ats_ptr_type info, ats_ptr_type outset) {
  ((fgnodeinfo_t)info)->atslab_outset = outset ; return ;
}

%}

(* ****** ****** *)

(* end of [fgraph.dats] *)
