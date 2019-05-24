(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload AS = "assem.sats"
typedef instrlst = $AS.instrlst

staload TL = "templab.sats"
typedef temp_t = $TL.temp_t
typedef label_t = $TL.label_t

staload F = "frame.sats"

(* ****** ****** *)

staload "fgnode.sats"
staload "tempset.sats"

(* ****** ****** *)

staload "fgraph.sats"
staload "igraph.sats"

(* ****** ****** *)

staload LM = "LIB/linmap_randbst.dats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

val _cmp_lab = lam
  (l1: label_t, l2: label_t): Sgn =<cloref>
  $TL.compare_label_label (l1, l2)
// end of [val]

implement fgraph_make_instrlst (inss) = let
  val asz = list_length (inss)
  val fg = fgraph_make_elt (asz, __elt) where {
    val __elt = $extval (fgnodeinfo_t, "(ats_ptr_type)0")
  } // end of [val]
  viewtypedef labmap_vt = $LM.map_vt (label_t, fgnode_t)
  var labmap: labmap_vt = $LM.linmap_empty ()
  val () = loop_vertex (fg, labmap, inss, 0) where {
    fun loop_vertex {n:nat} (
        fg: fgraph_t, labmap: &labmap_vt, inss: instrlst, n: int n
      ) : void = begin case+ inss of 
      | list_cons _ => let
          val fgn = fgnode_make_int (n)
          val+ list_cons (ins, inss) = inss
          val ismove = $AS.instr_ismove (ins)
          val uselst = $AS.instr_uselst_get (ins)
          val deflst = $AS.instr_deflst_get (ins)
          val info = fgnodeinfo_make (fgn, ismove, uselst, deflst)
          val () = fgraph_nodeinfo_set (fg, fgn, info)
          val () = case+ ins of
          | $AS.INSTRlabel (_(*asm*), lab) => () where {
              val ans = begin
                $LM.linmap_insert<label_t,fgnode_t> (labmap, lab, fgn, _cmp_lab)
              end // end of [val]
              val () = begin
                case+ ans of | ~Some_vt _ => () | ~None_vt _ => ()
              end // end of [val]
            } // end of [INSTRlabel]
          | _ => ()
        in
          loop_vertex (fg, labmap, inss, n+1)
        end // end of [list_cons]
      | list_nil () => ()
    end // end of [loop_vertex]
  } // end of [val]
  val () = loop_edge (fg, labmap, inss, 0) where {
    fun loop_edge {n:nat} (
        fg: fgraph_t, labmap: !labmap_vt, inss: instrlst, n: int n
      ) : void = begin case+ inss of
      | list_cons (ins, inss) => let
          val fgn_fr = fgnode_make_int (n)
          val jump = $AS.instr_jump_get (ins)
          val () = case+ jump of
          | Some labs => let
              fun loop_labs (
                  fg: fgraph_t
                , labmap: !labmap_vt
                , fgn_fr: fgnode_t
                , labs: $TL.lablst
                ) : void = case+ labs of
                | list_cons (lab, labs) => let
                    val ans = $LM.linmap_search (labmap, lab, _cmp_lab)
                    val () = case+ ans of
                    | ~Some_vt fgn_to => fgraph_edge_insert (fg, fgn_fr, fgn_to)
                    | ~None_vt () => ()
                  in
                    loop_labs (fg, labmap, fgn_fr, labs)
                  end // end of [list_cons]
                | list_nil () => ()
              // end of [loop_labs]
            in
              loop_labs (fg, labmap, fgn_fr, labs)
            end // end of [Some]
          | None () => begin case+ inss of
            | list_cons _ => let
                val fgn_to = fgnode_make_int (n+1)
              in
                fgraph_edge_insert (fg, fgn_fr, fgn_to)
              end // end of [list_cons]
            | list_nil () => ()
            end (* end of [None] *)
        in
          loop_edge (fg, labmap, inss, n+1)
        end // end of [list_cons]
      | list_nil () => ()
    end (* end of [loop_edge] *)
  } // end of [val]
  val () = $LM.linmap_free (labmap)
in
  fg
end // end of [fgraph_make_instrlst]

(* ****** ****** *)

(*
**
** in[n]  = use[n] + (out[n] - def[n])
** out[n] = U (in[s]) where s ranges over succ[n]
**
*)

implement fgraph_compute_outset (fg) = let
  fun loop_one {i:nat}
    (fg: fgraph_t, flag: &int, i: int i): void =
    if i > 0 then let
      val i1 = i - 1
      val fgn = fgnode_make_int (i1)
      val info = fgraph_nodeinfo_get (fg, fgn)
      val succlst = fgnodeinfo_succ_get (info)
      val succlst = fgnodelst_list_get (succlst)
      val inset = fgnodeinfo_inset_get (info)
      val outset = fgnodeinfo_outset_get (info)
//
      val flag0 = flag
      val outset = loop_outset (fg, outset, flag, succlst) where {
        fun loop_outset (
            fg: fgraph_t
          , outset: tempset_t
          , flag: &int
          , fgns: List fgnode_t
          ) : tempset_t = case+ fgns of
          | list_cons (fgn, fgns) => let
              val info = fgraph_nodeinfo_get (fg, fgn)
              val inset = fgnodeinfo_inset_get (info)
              val outset = tempset_union_flag (outset, inset, flag)
            in
              loop_outset (fg, outset, flag, fgns)
            end // end of [list_cons]
          | list_nil () => outset
        // end of [loop_outset]
      } // end of [val]
      val () = if flag > flag0 then fgnodeinfo_outset_set (info, outset)
//
      val defset = fgnodeinfo_defset_get (info)
      val diffset = tempset_diff (outset, defset)
      val flag0 = flag
      val inset = tempset_union_flag (inset, diffset, flag)
      val () = if flag > flag0 then fgnodeinfo_inset_set (info, inset)
    in
      loop_one (fg, flag, i1)
    end // end of [if]
  // end of [loop_one]
  val sz = fgraph_size (fg)
  val sz = size1_of_size (sz)
  val sz = int1_of_size1 (sz)
  var ntimes: int = 0
  var flag: int = 0
in
  while (true) let
    val flag0 = flag
(*
    val () = begin
      print "fgraph_compute_outset: ntimes = ";
      print ntimes;
      print_newline ()
    end // end of [val]
*)
    val () = loop_one (fg, flag, sz)
    val () = ntimes := ntimes + 1
  in
    if (flag = flag0) then break
  end // end of [while]
end (* end of [fgraph_compute_outset] *)

(* ****** ****** *)

overload = with $TL.eq_temp_temp

fun igraph_nodelst_insert
  (ig: igraph_t, ts: $TL.templst): void = case+ ts of
  | list_cons (t, ts) => let
      val () = igraph_node_insert (ig, t) in igraph_nodelst_insert (ig, ts)
    end // end of [list_cons]
  | list_nil () => ()
// end of [igraph_nodelst_insert]

implement igraph_make_fgraph (fg) = ig where {
  val ig = igraph_make_empty ()
  val () = igraph_nodelst_insert (ig, $F.theSpecialReglst)
  val () = igraph_nodelst_insert (ig, $F.theGeneralReglst)
  val sz = fgraph_size (fg)
  val sz = size1_of_size (sz)
  val sz = int1_of_size1 (sz)
  val () = loop (fg, ig, 0, sz) where {
    fun loop {sz,i:nat | i <= sz} .<sz-i>. (
        fg: fgraph_t, ig: igraph_t, i: int i, sz: int sz
      ) : void =
      if i < sz then let
        val fgn = fgnode_make_int (i)
        val info = fgraph_nodeinfo_get (fg, fgn)
        val useset = fgnodeinfo_useset_get (info)
        val uselst = templst_of_tempset (useset)
        val () = igraph_nodelst_insert (ig, uselst)
        val defset = fgnodeinfo_defset_get (info)
        val deflst = templst_of_tempset (defset)
        val () = igraph_nodelst_insert (ig, deflst)
      in
        loop (fg, ig, i + 1, sz)
      end // end of [if]
    // end of [loop]
  } // end of [val]
  val () = igraph_initialize (ig)
  val () = loop (ig, fg, 0, sz) where {
    fun loop {sz,i:nat | i <= sz} (
        ig: igraph_t, fg: fgraph_t, i: int i, sz: int sz
      ) : void =
      if i < sz then let
        val fgn = fgnode_make_int (i)
        val info = fgraph_nodeinfo_get (fg, fgn)
        val ismove = fgnodeinfo_ismove_get (info)
        val defset = fgnodeinfo_defset_get (info)
        val deflst = templst_of_tempset (defset)
        val outset = fgnodeinfo_outset_get (info)
        val outlst = templst_of_tempset (outset)
(*
        val () = begin
          prerr "igraph_make_fgraph:\n";
          prerr "deflst = "; $TL.prerr_templst deflst; prerr_newline ();
          prerr "outlst = "; $TL.prerr_templst outlst; prerr_newline ();
        end // end of [val]
*)
        val () = if ~ismove then let
          fn* loop1 (
              ig: igraph_t, ts1: $TL.templst, ts2: $TL.templst
            ) : void =
            case+ ts1 of
            | list_cons (t1, ts1) => let
                val () = loop2 (ig, t1, ts2) in loop1 (ig, ts1, ts2)
              end // end of [list_cons]
            | list_nil () => ()
          // end of [loop]
          
          and loop2 (
              ig: igraph_t, t1: $TL.temp_t, ts2: $TL.templst
            ) : void =
            case+ ts2 of
            | list_cons (t2, ts2) => let
                val () = if ~(t1 = t2) then
                  igraph_int_edge_insert (ig, t1, t2)
                // end of [val]
              in
                loop2 (ig, t1, ts2)
              end // end of [list_cons]
            | list_nil () => ()
          // end of [loop2]
        in
          loop1 (ig, deflst, outlst)
        end // end of [val]
        val () = if ismove then let
          val useset = fgnodeinfo_useset_get (info)
          val uselst = templst_of_tempset (useset)
          val- list_cons (t_src, _) = uselst
          val- list_cons (t_dst, _) = deflst
          val () = igraph_mov_edge_insert (ig, t_src, t_dst)
          fun loop3 (
              ig: igraph_t
            , t_src: $TL.temp_t, t_dst: $TL.temp_t
            , ts: $TL.templst
            ) : void = begin case+ ts of
            | list_cons (t, ts) => let
                val () =
                  if t = t_src then () else
                    if t = t_dst then () else begin
                      igraph_int_edge_insert (ig, t_dst, t)
                    end
                  // end of [if]
              in
                loop3 (ig, t_src, t_dst, ts)
              end // end of [list_cons]
            | list_nil () => ()
          end // end of [loop3]
          // isout = true iff [t_dst] is unused
          val isout = tempset_ismem (outset, t_dst)
        in
          if isout then loop3 (ig, t_src, t_dst, outlst)
        end // end of [val]
      in
        loop (ig, fg, i + 1, sz)
      end // end of [if]
    // end of [loop]
  } // end of [val]
} (* end of [igraph_make_fgraph] *)

(* ****** ****** *)

implement spillcost_compute (fg, ig) = let
  fun loop_livtot (
      ig: igraph_t, ts: $TL.templst
    ) : void = begin case+ ts of
    | list_cons (t, ts) => let
        val info = igraph_nodeinfo_get (ig, t)
        val () = ignodeinfo_nlivtot_inc (info)
      in
        loop_livtot (ig, ts)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [loop_livtot]
  fun loop_usedef (
      ig: igraph_t, ts: $TL.templst
    ) : void = begin case+ ts of
    | list_cons (t, ts) => let
        val info = igraph_nodeinfo_get (ig, t)
        val () = ignodeinfo_nusedef_inc (info)
      in
        loop_usedef (ig, ts)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [loop_usedef]
  val sz = fgraph_size (fg)
  val sz = size1_of_size (sz)
  val sz = int1_of_size1 (sz)
  var i: Nat // uninitialized
  val () = for (i := 0; i < sz; i := i + 1) let
    val n = fgnode_make_int (i)
    val info = fgraph_nodeinfo_get (fg, n)
//
    val outset = fgnodeinfo_outset_get (info)
    val outlst = templst_of_tempset (outset)
    val () = loop_livtot (ig, outlst)
//
    val useset = fgnodeinfo_useset_get (info)
    val uselst = templst_of_tempset (useset)
    val () = loop_usedef (ig, uselst)
//
    val defset = fgnodeinfo_defset_get (info)
    val deflst = templst_of_tempset (defset)
    val () = loop_usedef (ig, deflst)
//
  in
    // empty
  end // end of [val]
in
  // empty
end // end of [spillcost_compute]

(* ****** ****** *)

implement
  igraph_make_instrlst (inss) = let
  val fg = fgraph_make_instrlst (inss)
  val () = fgraph_compute_outset (fg)
  val ig = igraph_make_fgraph (fg)
  val () = spillcost_compute (fg, ig)
in
  ig
end // end of [igraph_make_instrlst]

(* ****** ****** *)

(* end of [liveness.dats] *)
