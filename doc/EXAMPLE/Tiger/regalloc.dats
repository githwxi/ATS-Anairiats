(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

staload "tempset.sats"

(* ****** ****** *)

staload "igraph.sats"

(* ****** ****** *)

staload "regalloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

implement igraph_simplify0
  (ig) = loop (ig, $F.theSpecialReglst) where {
  fun loop (ig: igraph_t, ts: $TL.templst): void =
    case+ ts of
    | list_cons (t, ts) => let
        val () = igraph_node_remove (ig, t) in loop (ig, ts)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [igraph_simplify0]

(* ****** ****** *)

implement fprint_regassgn (out, rasgn) = begin
  case+ rasgn of
  | REGASSGNsimplify (tmp, intset) => () where {
      val () = fprint_string (out, "REGASSGNsimplify(")
      val () = $TL.fprint_temp (out, tmp)
      val () = fprint_string (out, "; ")
      val () = fprint_tempset (out, intset)
      val () = fprint_string (out, ")")
    } // end of [REGASSGNsimplify]
  | REGASSGNcoalesce (tmp0, tmp1) => () where {
      val () = fprint_string (out, "REGASSGNcoalesce(")
      val () = $TL.fprint_temp (out, tmp0)
      val () = fprint_string (out, "; ")
      val () = $TL.fprint_temp (out, tmp1)
      val () = fprint_string (out, ")")
    } // end of [REGASSGNcoalesce]
  | REGASSGNspill (tmp, intset) => () where {
      val () = fprint_string (out, "REGASSGNspill(")
      val () = $TL.fprint_temp (out, tmp)
      val () = fprint_string (out, "; ")
      val () = fprint_tempset (out, intset)
      val () = fprint_string (out, ")")
    } // end of [REGASSGNspill]
end // end of [fprint_regassgn]

(* ****** ****** *)

implement fprint_regassgnlst (out, rasgns) =
  case+ rasgns of
  | list_cons (rasgn, rasgns) => let
      val () = fprint_regassgn (out, rasgn)
      val () = fprint_newline (out)
    in
      fprint_regassgnlst (out, rasgns)
    end // end of [list_cons]
  | list_nil () => ()
// end of [fprint_regassgnlst]

(* ****** ****** *)

val theGeneralRegset : tempset_t =
  tempset_make_templst ($F.theGeneralReglst)

(* ****** ****** *)

staload LM = "LIB/linmap_randbst.dats"

(* ****** ****** *)

local

typedef key = $TL.temp_t
typedef itm = $TL.temp_t
  
typedef regassgnmap = ref ($LM.map_vt (key, itm))

val _cmp_temp = lam (t1: key, t2: key)
  : Sgn =<cloref> $TL.compare_temp_temp (t1, t2)
// end of [_cmp_temp]

val theRegAssgnMap = let
  val map = $LM.linmap_empty {key,itm} () in ref_make_elt (map)
end : regassgnmap // end of [val]

val theSpilledReglst = ref_make_elt<$TL.templst> (list_nil)

in // in of [local]

implement regassgn_find (tmp) = let
  val (vbox pf | p) = ref_get_view_ptr (theRegAssgnMap)
  val ans = $LM.linmap_search<key,itm> (!p, tmp, _cmp_temp)
in
  case+ ans of ~Some_vt tmp => tmp | ~None_vt () => tmp
end (* end of [regassgn_find] *)

fn regassgn_insert
  (tmp0: $TL.temp_t, tmp1: $TL.temp_t): void = let
  val (vbox pf | p) = ref_get_view_ptr (theRegAssgnMap)
  val ans = $LM.linmap_insert<key,itm> (!p, tmp0, tmp1, _cmp_temp)
  val () = case+ ans of ~Some_vt _ => () | ~None_vt () => ()
in
  // empty
end (* end of [regassgn_insert] *)

fn regassgn_clear (): void = () where {
  val (vbox pf | p) = ref_get_view_ptr (theRegAssgnMap)
  val () = $LM.linmap_free (!p)
  val map = $LM.linmap_empty {key,itm} ()
  val () = !p := map
} // end of [regassgn_clear]

(* ****** ****** *)

fn spillreglst_get () = !theSpilledReglst

fn spillreglst_add (tmp: $TL.temp_t): void = begin
  !theSpilledReglst := list_cons (tmp, !theSpilledReglst)
end // end of [spillreglst_add]

fun spillreglst_clear () = !theSpilledReglst := list_nil ()

end // end of [local]

(* ****** ****** *)

implement regassgn_select (rasgn) = let
  fun auxsel
    (rems: tempset_t, ts: $TL.templst): $TL.tempopt_vt =
    case+ ts of
    | list_cons (t, ts) => let
        val t = regassgn_find (t)
        val rems = tempset_remove (rems, t) in auxsel (rems, ts)
      end (* end of [list_cons] *)
    | list_nil () => let
        val rems = templst_of_tempset (rems) in case+ rems of
        | list_cons (t, _) => Some_vt t | list_nil () => None_vt ()
      end // end of [list_nil]
  // end of [auxsel]
  var tmp0: $TL.temp_t = $TL.temp_bogus
  val ans = (case+ rasgn of
    | REGASSGNsimplify (t0, ts) => let
        val () = tmp0 := t0
        val ts = templst_of_tempset ts in auxsel (theGeneralRegset, ts)
      end // end of [REGASSGNsimplify]
    | REGASSGNcoalesce (t0, t1) => let
        val () = tmp0 := t1; val t0 = regassgn_find (t0)
      in
        Some_vt t0
      end // end of [REGASSGNcoalesce]
    | REGASSGNspill (t0, ts) => let
(*
        val () = prerr "regassgn_select: potential spill\n"
*)
        val () = tmp0 := t0
        val ts = templst_of_tempset ts in auxsel (theGeneralRegset, ts)
      end // end of [REGASSGNspill]
  ) : $TL.tempopt_vt
  val () = case+ ans of
    | ~Some_vt tmp1 => let
        val () = regassgn_insert (tmp0, tmp1)
      in
(*
        prerr "regassgn_select: ";
        $TL.prerr_temp tmp0; prerr " --> "; $TL.prerr_temp tmp1;
        prerr_newline ()
*)
      end // end of [Some_vt]
    | ~None_vt () => let
        val () = spillreglst_add (tmp0)
      in
(*
        prerr "regassgn_select: ";
        $TL.prerr_temp tmp0; prerr " --> (spill)";
        prerr_newline ()
*)
      end // end of [None_vt]
in
  // empty        
end // end of [regassgn_select]

(* ****** ****** *)

local

staload "assem.sats"

typedef key = $TL.temp_t
typedef itm = $F.access_t
viewtypedef spillmap_vt = $LM.map_vt (key, itm)

val _cmp_temp = lam (t1: key, t2: key)
  : Sgn =<cloref> $TL.compare_temp_temp (t1, t2)
// end of [_cmp_temp]

in // in of [local]

fn instr_spill_rewrite (
    spillmap: !spillmap_vt, ins0: instr, res: &instrlst_vt
  ) : void = let
  macdef emit (ins) = (res := list_vt_cons {instr} (,(ins), res))
  fun emitlst
    (res: &instrlst_vt, inss: instrlst_vt): void = case+ inss of
    | ~list_vt_cons (ins, inss) => let
        val () = res := list_vt_cons (ins, res) in emitlst (res, inss)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => ()
  // end of [emitlst]
in
  case+ ins0 of
  | INSTRoper (asm, src, dst, jump) => let
      var inss_rd: instrlst_vt = list_vt_nil ()
      val src = auxsrc (spillmap, src, inss_rd) where {
        fun auxsrc (
            spillmap: !spillmap_vt, ts: $TL.templst, inss_rd: &instrlst_vt
          ) : $TL.templst = case+ ts of
          | list_cons (t, ts) => let
              val ts = auxsrc (spillmap, ts, inss_rd)
              val ans = $LM.linmap_search<key,itm> (spillmap, t, _cmp_temp)
              val t = (case+ ans of
                | ~Some_vt (acc) => t_new where {
                    val t_new = $TL.temp_make_new ()
                    val ins_rd = $F.instr_make_mem_read (acc, t_new)
                    val () = inss_rd := list_vt_cons (ins_rd, inss_rd)
                  } // end of [Some_vt]
                | ~None_vt () => t
              ) : $TL.temp_t // end of [val]
            in
              list_cons (t, ts)
            end // end of [list_cons]
          | list_nil () => list_nil ()
      } // end of [val]
      var inss_wrt: instrlst_vt = list_vt_nil ()
      val dst = auxdst (spillmap, dst, inss_wrt) where {
        fun auxdst (
            spillmap: !spillmap_vt, ts: $TL.templst, inss_wrt: &instrlst_vt
          ) : $TL.templst = case+ ts of
          | list_cons (t, ts) => let
              val ts = auxdst (spillmap, ts, inss_wrt)
              val ans = $LM.linmap_search<key,itm> (spillmap, t, _cmp_temp)
              val t = (case+ ans of
                | ~Some_vt (acc) => t_new where {
                    val t_new = $TL.temp_make_new ()
                    val ins_wrt = $F.instr_make_mem_write (acc, t_new)
                    val () = inss_wrt := list_vt_cons (ins_wrt, inss_wrt)
                  } // end of [Some_vt]
                | ~None_vt () => t
              ) : $TL.temp_t // end of [val]
            in
              list_cons (t, ts)
            end // end of [list_cons]
          | list_nil () => list_nil ()
      } // end of [val]
      val () = emitlst (res, inss_rd)
      val () = emit (INSTRoper (asm, src, dst, jump))
      val () = emitlst (res, inss_wrt)
    in
      // empty
    end // end of [val]
  | INSTRlabel _ => emit (ins0)
  | INSTRmove (asm, src, dst) => let
      val ans = $LM.linmap_search<key,itm> (spillmap, src, _cmp_temp)
      var insopt_rd: instropt_vt // uninitialized
      val src = case+ ans of
        | ~Some_vt acc => src_new where {
            val src_new = $TL.temp_make_new ()
            val ins_rd = $F.instr_make_mem_read (acc, src_new)
            val () = insopt_rd := Some_vt (ins_rd)
          } // end of [Some_vt]
        | ~None_vt () => src where {
            val () = insopt_rd := None_vt ()
          } // end of [None_vt]
      // end of [val]
      var insopt_wrt: instropt_vt // uninitialized
      val ans = $LM.linmap_search<key,itm> (spillmap, dst, _cmp_temp)
      val dst = case+ ans of
        | ~Some_vt acc => dst_new where {
            val dst_new = $TL.temp_make_new ()
            val ins_wrt = $F.instr_make_mem_write (acc, dst_new)
            val () = insopt_wrt := Some_vt (ins_wrt)
          } // end of [Some_vt]
        | ~None_vt () => dst where {
            val () = insopt_wrt := None_vt ()
          } // end of [None_vt]
      // end of [dst]
      val () = case+ insopt_rd of
        | ~Some_vt ins_rd => emit (ins_rd) | ~None_vt () => ()
      // end of [val]
      val () = emit (INSTRmove (asm, src, dst))
      val () = case+ insopt_wrt of
        | ~Some_vt ins_wrt => emit (ins_wrt) | ~None_vt () => ()
      // end of [val]
    in
    end // end of [INSTRmove]
end // end of [instr_spill]

fun instrlst_spill_rewrite (
    spillmap: !spillmap_vt
  , inss: instrlst, res: &instrlst_vt
  ) : void = begin case+ inss of
  | list_cons (ins, inss) => let
      val () = instr_spill_rewrite (spillmap, ins, res)
    in
      instrlst_spill_rewrite (spillmap, inss, res)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [instrlst_spill]

fun instrlst_spill_codegen (
    frm: $F.frame_t, spills: $TL.templst, inss: instrlst
  ) : instrlst = let
  var spillmap = $LM.linmap_empty {key,itm} ()
  val () = loop (frm, spills, spillmap) where {
    fun loop (
        frm: $F.frame_t, ts: $TL.templst, map: &spillmap_vt
      ) : void = case+ ts of
      | list_cons (t, ts) => let
          val acc = $F.frame_alloc_local (frm, true(*escape*))
          val ans = $LM.linmap_insert<key,itm> (map, t, acc, _cmp_temp)
          val () = case+ ans of ~Some_vt _ => () | ~None_vt () => ()
        in
          loop (frm, ts, map)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop]
  } // end of [val]
  var res: instrlst_vt = list_vt_nil ()
  val () = instrlst_spill_rewrite (spillmap, inss, res)
  val res = list_vt_reverse (res)
  val inss_new = list_of_list_vt (res)
  val () = $LM.linmap_free (spillmap)
in
  inss_new
end // end of [instrlst_spill_codegen]

end // end of [local]

(* ****** ****** *)

extern fun igraph_regalloc (ig: igraph_t): void

implement igraph_regalloc (ig) = let
  fun loop1 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_lowdeg (ig) in
    case+ ans of
    | ~Some_vt tmp => let
        val () = begin
(*
          prerr "igraph_regalloc: loop1(simplify): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
*)
        end // end of [val]
        val info = igraph_nodeinfo_get (ig, tmp)
        val intset = ignodeinfo_intset_get (info)
        val rasgn = REGASSGNsimplify (tmp, intset)
        val () = rasgns := list_cons (rasgn, rasgns)
        val () = igraph_node_remove (ig, tmp)
      in
        loop1 (ig, rasgns)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop1]
  fun loop2 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_coalesce (ig) in
    case+ ans of
    | ~Some_vt tmptmp => let
        val tmp0 = tmptmp.0 and tmp1 = tmptmp.1
(*
        val () = begin
          prerr "igraph_regalloc: loop2(coalesce): ";
          $TL.prerr_temp tmp0;
          prerr " <=> ";
          $TL.prerr_temp tmp1;
          prerr_newline ()
        end // end of [val]
*)
        val rasgn = REGASSGNcoalesce (tmp0, tmp1)
        val () = rasgns := list_cons (rasgn, rasgns)
        val () = igraph_node_coalesce (ig, tmp0, tmp1)
      in
        loop1 (ig, rasgns); loop2 (ig, rasgns)
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop2]
  fun loop3 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_freeze (ig) in
    case+ ans of
    | ~Some_vt tmp => let
(*
        val () = begin
          prerr "igraph_regalloc: loop3(freeze): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
*)
        val () = igraph_node_freeze (ig, tmp)
        val () = loop1 (ig, rasgns)
        val () = loop2 (ig, rasgns)
        val () = loop3 (ig, rasgns)
      in
        // empty
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop3]
  fun loop4 (
      ig: igraph_t, rasgns: &regassgnlst
    ) : void = let
    val ans = igraph_search_spill (ig) in
    case+ ans of
    | ~Some_vt tmp => let
(*
        val () = begin
          prerr "igraph_regalloc: loop4(spill): tmp = ";
          $TL.prerr_temp tmp;
          prerr_newline ()
        end // end of [val]
*)
        val info = igraph_nodeinfo_get (ig, tmp)
        val intset = ignodeinfo_intset_get (info)
        val rasgn = REGASSGNspill (tmp, intset)
        val () = rasgns := list_cons (rasgn, rasgns)
        val () = igraph_node_remove (ig, tmp)
        val () = loop1 (ig, rasgns)
        val () = loop2 (ig, rasgns)
        val () = loop3 (ig, rasgns)
        val () = loop4 (ig, rasgns)
      in
        // empty
      end // end of [Some_vt]
    | ~None_vt () => ()
  end // end of [loop4]
  var rasgns: regassgnlst = list_nil ()
  val () = loop1 (ig, rasgns) // simplify
  val () = loop2 (ig, rasgns) // coalesce
  val () = loop3 (ig, rasgns) // freeze
  val () = loop4 (ig, rasgns) // spill
(*
  val () = begin
    prerr "igraph_regalloc: rasgns =\n";
    fprint_regassgnlst (stderr_ref, rasgns);
    prerr_newline ()
  end // end of [val]
*)
  val () = regassgn_clear ()
  val () = spillreglst_clear ()
  val () = loop5 (rasgns) where {
    fun loop5 (rasgns: regassgnlst): void =
      case+ rasgns of
      | list_cons (rasgn, rasgns) => let
          val () = regassgn_select (rasgn) in loop5 (rasgns)
        end // end of [list_cons]
      | list_nil () => ()
    // end of [loop5]
  } // end of [val]
in
  // empty
end // end of [igraph_regalloc]

(* ****** ****** *)

implement instrlst_regalloc
  (frm, inss0) = loop (frm, inss0) where {
  fun loop (frm: $F.frame_t, inss: $AS.instrlst): $AS.instrlst = let
(*
    val () = prerr "instrlst_regalloc: loop: inss =\n"
    val () = $AS.prerr_instrlst (inss)
*)
    val ig = igraph_make_instrlst (inss)
(*
    val () = prerr "instrlst_regalloc: loop: ig(init) =\n"
    val () = fprint_igraph (stderr_ref, ig)
*)
    val () = igraph_simplify0 (ig)
(*
    val () = prerr "instrlst_regalloc: loop: ig(simplify0) =\n"
    val () = fprint_igraph (stderr_ref, ig)
*)
    val () = igraph_regalloc (ig)
(*
    val () = prerr "instrlst_regalloc: loop: ig(regalloc) =\n"
    val () = fprint_igraph (stderr_ref, ig)
*)
    val spills = spillreglst_get ()
  in
    case+ spills of
    | list_cons _ => let
        val inss = instrlst_spill_codegen (frm, spills, inss)
      in
        loop (frm, inss)
      end // end of [list_cons]
    | list_nil () => inss
  end // end of [val]
} // end of [instrlst_regalloc]

(* ****** ****** *)

implement regalloc_tmpfmt (tmp) = let
  val tmp = regassgn_find (tmp) in $F.register_name_get (tmp)
end // end of [regalloc_tmpfmt]

implement regalloc_insfmt (ins) = $AS.instr_format (regalloc_tmpfmt, ins)

(* ****** ****** *)

(* end of [regalloc.dats] *)
