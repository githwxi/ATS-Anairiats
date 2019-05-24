(*
**
** For documenting the grammar of ATS/Anairiats
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

staload "atsgrammar.sats"

(* ****** ****** *)
//
dynload "atsgrammar_tyname.dats"
dynload "atsgrammar_symbol.dats"
dynload "atsgrammar_grmrule.dats"
dynload "atsgrammar_global.dats"
//
dynload "atsgrammar_emit_yats.dats"
dynload "atsgrammar_emit_yats_html.dats"
dynload "atsgrammar_emit_desc.dats"
dynload "atsgrammar_emit_desc_html.dats"
//
(* ****** ****** *)

macdef SYMREGoptlit (x) = SYMREGopt(SYMREGlit ,(x))
macdef SYMREGstarlit (x) = SYMREGstar(SYMREGlit ,(x))
macdef SYMREGpluslit (x) = SYMREGplus(SYMREGlit ,(x))

macdef SYMREGaltlit (x1, x2) = SYMREGalt(SYMREGlit ,(x1), SYMREGlit ,(x2))
macdef SYMREGseqlit (x1, x2) = SYMREGseq(SYMREGlit ,(x1), SYMREGlit ,(x2))

(* ****** ****** *)

fn tyname_make_namdef (
  nam: string, def: string
) : tyname = x where {
  val x = tyname_make_namdef (nam, def)
  val () = theTynamelst_add (x)
(*
  val () = (
    print ("tyname_make_namdef: x = "); print x; print_newline ()
  ) // end of [val]
*)
} // end of [tyname_make_namdef]

(* ****** ****** *)

val t0kn_tyname = tyname_make_namdef ("t0kn", "t0kn_t")
val c0har_tyname = tyname_make_namdef ("c0har", "c0har_t")
val e0xtcode_tyname = tyname_make_namdef ("e0xtcode", "e0xtcode_t")
val f0loat_tyname = tyname_make_namdef ("f0loat", "f0loat_t")
val f0loatsp_tyname = tyname_make_namdef ("f0loatsp", "f0loatsp_t")
val i0nt_tyname = tyname_make_namdef ("i0nt", "i0nt_t")
val i0ntsp_tyname = tyname_make_namdef ("i0ntsp", "i0ntsp_t")
val s0tring_tyname = tyname_make_namdef ("s0tring", "s0tring_t")
val i0de_tyname = tyname_make_namdef ("i0de", "i0de_t")
val i0delst_tyname = tyname_make_namdef ("i0delst", "i0delst_t")
val l0ab_tyname = tyname_make_namdef ("l0ab", "l0ab_t")
val p0rec_tyname = tyname_make_namdef ("p0rec", "p0rec_t")

(* ****** ****** *)

val abskind_tyname = tyname_make_namdef ("abskind", "abskind_t")
val dcstkind_tyname = tyname_make_namdef ("dcstkind", "dcstkind_t")
val datakind_tyname = tyname_make_namdef ("datakind", "datakind_t")
val stadefkind_tyname = tyname_make_namdef ("stadefkind", "stadefkind_t")

val valkind_tyname = tyname_make_namdef ("valkind", "valkind_t")
val funkind_tyname = tyname_make_namdef ("funkind", "funkind_t")
val lamkind_tyname = tyname_make_namdef ("lamkind", "lamkind_t")
val fixkind_tyname = tyname_make_namdef ("fixkind", "fixkind_t")

val srpifkindtok_tyname = tyname_make_namdef ("srpifkindtok", "srpifkindtok_t")

(* ****** ****** *)

val e0xp_tyname = tyname_make_namdef ("e0xp", "e0xp_t")
val e0xplst_tyname = tyname_make_namdef ("e0xplst", "e0xplst_t")
val e0xpopt_tyname = tyname_make_namdef ("e0xpopt", "e0xpopt_t")

val e0fftag_tyname = tyname_make_namdef ("e0fftag", "e0fftag_t")
val e0fftaglst_tyname = tyname_make_namdef ("e0fftaglst", "e0fftaglst_t")
val e0fftaglstopt_tyname = tyname_make_namdef ("e0fftaglstopt", "e0fftaglstopt_t")

val s0rt_tyname = tyname_make_namdef ("s0rt", "s0rt_t")
val s0rtq_tyname = tyname_make_namdef ("s0rtq", "s0rtq_t")
val s0rtlst_tyname = tyname_make_namdef ("s0rtlst", "s0rtlst_t")
val s0rtopt_tyname = tyname_make_namdef ("s0rtopt", "s0rtopt_t")
val s0rtpol_tyname = tyname_make_namdef ("s0rtpol", "s0rtpol_t")

val d0atsrtcon_tyname = tyname_make_namdef ("d0atsrtcon", "d0atsrtcon_t")
val d0atsrtconlst_tyname = tyname_make_namdef ("d0atsrtconlst", "d0atsrtconlst_t")
val d0atsrtdec_tyname = tyname_make_namdef ("d0atsrtdec", "d0atsrtdec_t")
val d0atsrtdeclst_tyname = tyname_make_namdef ("d0atsrtdeclst", "d0atsrtdeclst_t")

val s0taq_tyname = tyname_make_namdef ("s0taq", "s0taq_t")
val d0ynq_tyname = tyname_make_namdef ("d0ynq", "d0ynq_t")

val sqi0de_tyname = tyname_make_namdef ("sqi0de", "sqi0de_t")
val dqi0de_tyname = tyname_make_namdef ("dqi0de", "dqi0de_t")
val arrqi0de_tyname = tyname_make_namdef ("arrqi0de", "arrqi0de_t")
val tmpqi0de_tyname = tyname_make_namdef ("tmpqi0de", "tmpqi0de_t")

val s0arg_tyname = tyname_make_namdef ("s0arg", "s0arg_t")
val s0arglst_tyname = tyname_make_namdef ("s0arglst", "s0arglst_t")
val s0arglstlst_tyname = tyname_make_namdef ("s0arglstlst", "s0arglstlst_t")

val sp0at_tyname = tyname_make_namdef ("sp0at", "sp0at_t")

val s0exp_tyname = tyname_make_namdef ("s0exp", "s0exp_t")
val s0expext_tyname = tyname_make_namdef ("s0expext", "s0expext_t")
val s0explst_tyname = tyname_make_namdef ("s0explst", "s0explst_t")
val s0expopt_tyname = tyname_make_namdef ("s0expopt", "s0expopt_t")
val s0explstlst_tyname = tyname_make_namdef ("s0explstlst", "s0explstlst_t")
val s0explstopt_tyname = tyname_make_namdef ("s0explstopt", "s0explstopt_t")
val labs0explst_tyname = tyname_make_namdef ("labs0explst", "labs0explst_t")
val s0arrind_tyname = tyname_make_namdef ("s0arrind", "s0arrind_t")
val t1mps0explstlst_tyname = tyname_make_namdef ("t1mps0explstlst", "t1mps0explstlst_t")

val s0qua_tyname = tyname_make_namdef ("s0qua", "s0qua_t")
val s0qualst_tyname = tyname_make_namdef ("s0qualst", "s0qualst_t")
val s0qualstlst_tyname = tyname_make_namdef ("s0qualstlst", "s0qualstlst_t")
val s0qualstopt_tyname = tyname_make_namdef ("s0qualstopt", "s0qualstopt_t")
val s0rtext_tyname = tyname_make_namdef ("s0rtext", "s0rtext_t")

val impqi0de_tyname = tyname_make_namdef ("impqi0de", "impqi0de_t")

(*
** static declarations
*)
val s0rtdef_tyname = tyname_make_namdef ("s0rtdef", "s0rtdef_t")
val s0rtdeflst_tyname = tyname_make_namdef ("s0rtdeflst", "s0rtdeflst_t")
val d0atarg_tyname = tyname_make_namdef ("d0atarg", "d0atarg_t")
val d0atarglst_tyname = tyname_make_namdef ("d0atarglst", "d0atarglst_t")
val s0tacon_tyname = tyname_make_namdef ("s0tacon", "s0tacon_t")
val s0taconlst_tyname = tyname_make_namdef ("s0taconlst", "s0taconlst_t")
val s0tacst_tyname = tyname_make_namdef ("s0tacst", "s0tacst_t")
val s0tacstlst_tyname = tyname_make_namdef ("s0tacstlst", "s0tacstlst_t")
val s0tavar_tyname = tyname_make_namdef ("s0tavar", "s0tavar_t")
val s0tavarlst_tyname = tyname_make_namdef ("s0tavarlst", "s0tavarlst_t")

val s0expdef_tyname = tyname_make_namdef ("s0expdef", "s0expdef_t")
val s0expdeflst_tyname = tyname_make_namdef ("s0expdeflst", "s0expdeflst_t")
val s0aspdec_tyname = tyname_make_namdef ("s0aspdec", "s0aspdec_t")

(*
** dataprop/type/view/viewtype declarations
*)
val d0atcon_tyname = tyname_make_namdef ("d0atcon", "d0atcon_t")
val d0atconlst_tyname = tyname_make_namdef ("d0atconlst", "d0atconlst_t")
val d0atdec_tyname = tyname_make_namdef ("d0atdec", "d0atdec_t")
val d0atdeclst_tyname = tyname_make_namdef ("d0atdeclst", "d0atdeclst_t")
val e0xndec_tyname = tyname_make_namdef ("e0xndec", "e0xndec_t")
val e0xndeclst_tyname = tyname_make_namdef ("e0xndeclst", "e0xndeclst_t")

val p0arg_tyname = tyname_make_namdef ("p0arg", "p0arg_t")
val p0arglst_tyname = tyname_make_namdef ("p0arglst", "p0arglst_t")
val d0arg_tyname = tyname_make_namdef ("d0arg", "d0arg_t")
val d0arglst_tyname = tyname_make_namdef ("d0arglst", "d0arglst_t")

val extnamopt_tyname = tyname_make_namdef ("extnamopt", "extnamopt_t")
val d0cstdec_tyname = tyname_make_namdef ("d0cstdec", "d0cstdec_t")
val d0cstdeclst_tyname = tyname_make_namdef ("d0cstdeclst", "d0cstdeclst_t")

val s0vararg_tyname = tyname_make_namdef ("s0vararg", "s0vararg_t")
val s0exparg_tyname = tyname_make_namdef ("s0exparg", "s0exparg_t")
val s0elop_tyname = tyname_make_namdef ("s0elop", "s0elop_t")
val witht0ype_tyname = tyname_make_namdef ("witht0ype", "witht0ype_t")

(*
** dynamic patterns
*)
val p0at_tyname = tyname_make_namdef ("p0at", "p0at_t")
val p0atlst_tyname = tyname_make_namdef ("p0atlst", "p0atlst_t")
val labp0atlst_tyname = tyname_make_namdef ("labp0atlst", "labp0atlst_t")

val f0arg_tyname = tyname_make_namdef ("f0arg", "f0arg_t")
val f0arglst_tyname = tyname_make_namdef ("f0arglst", "f0arglst_t")

(*
** dynamic expressions
*)
val d0exp_tyname = tyname_make_namdef ("d0exp", "d0exp_t")
val d0explst_tyname = tyname_make_namdef ("d0explst", "d0explst_t")
val d0expopt_tyname = tyname_make_namdef ("d0expopt", "d0expopt_t")
val labd0explst_tyname = tyname_make_namdef ("labd0explst", "labd0explst_t")
val d0arrind_tyname = tyname_make_namdef ("d0arrind", "d0arrind_t")

val ifhead_tyname = tyname_make_namdef ("ifhead", "ifhead_t")
val casehead_tyname = tyname_make_namdef ("casehead", "casehead_t")
val loophead_tyname = tyname_make_namdef ("loophead", "loophead_t")
val tryhead_tyname = tyname_make_namdef ("tryhead", "tryhead_t")

(*
** pattern matching
*)
val m0atch_tyname = tyname_make_namdef ("m0atch", "m0atch_t")
val m0atchlst_tyname = tyname_make_namdef ("m0atchlst", "m0atchlst_t")
val guap0at_tyname = tyname_make_namdef ("guap0at", "guap0at_t")
val c0lau_tyname = tyname_make_namdef ("c0lau", "c0lau_t")
val c0laulst_tyname = tyname_make_namdef ("c0laulst", "c0laulst_t")
val sc0lau_tyname = tyname_make_namdef ("sc0lau", "sc0lau_t")
val sc0laulst_tyname = tyname_make_namdef ("sc0laulst", "sc0laulst_t")

(*
** invariants
*)
val i0nvarg_tyname = tyname_make_namdef ("i0nvarg", "i0nvarg_t")
val i0nvarglst_tyname = tyname_make_namdef ("i0nvarglst", "i0nvarglst_t")
val i0nvresstate_tyname = tyname_make_namdef ("i0nvresstate", "i0nvresstate_t")
val loopi0nv_tyname = tyname_make_namdef ("loopi0nv", "loopi0nv_t")
val initestpost_tyname = tyname_make_namdef ("initestpost", "initestpost_t")

(*
** macro definitions
*)
val m0acarg_tyname = tyname_make_namdef ("m0acarg", "m0acarg_t")
val m0acarglst_tyname = tyname_make_namdef ("m0acarglst", "m0acarglst_t")
val m0acdef_tyname = tyname_make_namdef ("m0acdef", "m0acdef_t")
val m0acdeflst_tyname = tyname_make_namdef ("m0acdeflst", "m0acdeflst_t")

(*
**
*)
val v0aldec_tyname = tyname_make_namdef ("v0aldec", "v0aldec_t")
val v0aldeclst_tyname = tyname_make_namdef ("v0aldeclst", "v0aldeclst_t")
val f0undec_tyname = tyname_make_namdef ("f0undec", "f0undec_t")
val f0undeclst_tyname = tyname_make_namdef ("f0undeclst", "f0undeclst_t")
val v0arwth_tyname = tyname_make_namdef ("v0arwth", "v0arwth_t")
val v0ardec_tyname = tyname_make_namdef ("v0ardec", "v0ardec_t")
val v0ardeclst_tyname = tyname_make_namdef ("v0ardeclst", "v0ardeclst_t")
val i0mpdec_tyname = tyname_make_namdef ("i0mpdec", "i0mpdec_t")

(*
** generic declarations
*)
val d0ec_tyname = tyname_make_namdef ("d0ec", "d0ec_t")
val d0eclst_tyname = tyname_make_namdef ("d0eclst", "d0eclst_t")

(* ****** ****** *)

local
//
assume symbol_open_v (s:int) = unit_v
//
in // in of [local]
//
implement
symbol_open (sym) = (unit_v () | ())
//
implement
symbol_close
  (pf | sym) = let
  prval unit_v () = pf
  val grs1 = theGrmrulelst_get ()
  val grs2 = symbol_get_grmrulelst (sym)
  val grs = revapp (grs1, grs2) where {
    fun revapp (
      grs1: grmrulelst_vt, grs2: grmrulelst
    ) : grmrulelst = case+ grs1 of
      | ~list_vt_cons (gr, grs1) => revapp (grs1, list_cons (gr, grs2))
      | ~list_vt_nil () => grs2
    // end of [revapp]
  } // end of [val]
in
  symbol_set_grmrulelst (sym, grs)
end // end of [symbol_close]
//
end // end of [local]

(* ****** ****** *)

fn symbol_make
  (name: string): symbol = x where {
  val x = symbol_make (name)
  val () = theSymlst_add (x)
(*
  val () = (
    print ("symbol_make: x = "); print x; print_newline ()
  ) // end of [val]
*)
} // end of [symbol_make]

fn symbol_make_nt
  (name: string): symbol = x where {
  val x = symbol_make_nt (name)
  val () = theSymlst_add (x)
(*
  val () = (
    print ("symbol_make_nt: x = "); print x; print_newline ()
  ) // end of [val]
*)
} // end of [symbol_make_nt]

(* ****** ****** *)
//
val YYBEG_i0de = symbol_make "YYBEG_i0de"
val YYBEG_s0rtid = symbol_make "YYBEG_s0rtid"
val YYBEG_si0de = symbol_make "YYBEG_si0de"
val YYBEG_di0de = symbol_make "YYBEG_di0de"
//
val YYBEG_s0exp = symbol_make "YYBEG_s0exp"
val YYBEG_d0exp = symbol_make "YYBEG_d0exp"
val YYBEG_d0ecseq_sta = symbol_make "YYBEG_d0ecseq_sta"
val YYBEG_d0ecseq_dyn = symbol_make "YYBEG_d0ecseq_dyn"
//
val TOKEN_eof = symbol_make "TOKEN_eof"
//
(* ****** ****** *)
//
val LITERAL_char = symbol_make "LITERAL_char"
val () = symbol_set_tyname (LITERAL_char, c0har_tyname)
//
val LITERAL_extcode = symbol_make "LITERAL_extcode"
val () = symbol_set_tyname (LITERAL_extcode, e0xtcode_tyname)
//
val LITERAL_float = symbol_make "LITERAL_float"
val () = symbol_set_tyname (LITERAL_float, f0loat_tyname)
val LITERAL_floatsp = symbol_make "LITERAL_floatsp"
val () = symbol_set_tyname (LITERAL_floatsp, f0loatsp_tyname)
//
val LITERAL_int = symbol_make "LITERAL_int"
val () = symbol_set_tyname (LITERAL_int, i0nt_tyname)
val LITERAL_intsp = symbol_make "LITERAL_intsp"
val () = symbol_set_tyname (LITERAL_intsp, i0ntsp_tyname)
//
val LITERAL_string = symbol_make "LITERAL_string"
val () = symbol_set_tyname (LITERAL_string, s0tring_tyname)
//
val IDENTIFIER_alp = symbol_make "IDENTIFIER_alp"
val () = symbol_set_fullname
  (IDENTIFIER_alp, "ALNUMRIC_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_alp, i0de_tyname)
//
val IDENTIFIER_sym = symbol_make "IDENTIFIER_sym"
val () = symbol_set_fullname (IDENTIFIER_sym, "SYMBOLIC_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_sym, i0de_tyname)
//
val IDENTIFIER_arr = symbol_make "IDENTIFIER_arr"
val () = symbol_set_fullname (IDENTIFIER_arr, "ARRAY_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_arr, i0de_tyname)
//
val IDENTIFIER_tmp = symbol_make "IDENTIFIER_tmp"
val () = symbol_set_fullname (IDENTIFIER_tmp, "TEMPLATE_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_tmp, i0de_tyname)
//
val IDENTIFIER_ext = symbol_make "IDENTIFIER_ext"
val () = symbol_set_fullname (IDENTIFIER_ext, "EXTERNAL_IDENTIFIER")
val () = symbol_set_tyname (IDENTIFIER_ext, i0de_tyname)
//
val IDENTIFIER_dlr = symbol_make "IDENTIFIER_dlr"
val () = symbol_set_tyname (IDENTIFIER_dlr, i0de_tyname)
//
val IDENTIFIER_srp = symbol_make "IDENTIFIER_srp"
val () = symbol_set_tyname (IDENTIFIER_srp, i0de_tyname)
//
(* ****** ****** *)
//
val ABSPROP = symbol_make "ABSPROP"
val () = symbol_set_fullname (ABSPROP, "\"absprop\"")
val () = symbol_set_tyname (ABSPROP, t0kn_tyname)
//
val ABSTYPE = symbol_make "ABSTYPE"
val () = symbol_set_fullname (ABSTYPE, "\"abstype\"")
val () = symbol_set_tyname (ABSTYPE, t0kn_tyname)
//
val ABST0YPE = symbol_make "ABST0YPE"
val () = symbol_set_fullname (ABST0YPE, "\"abst@ype\"")
val () = symbol_set_tyname (ABST0YPE, t0kn_tyname)
//
val ABSVIEW = symbol_make "ABSVIEW"
val () = symbol_set_fullname (ABSVIEW, "\"absview\"")
val () = symbol_set_tyname (ABSVIEW, t0kn_tyname)
//
val ABSVIEWTYPE = symbol_make "ABSVIEWTYPE"
val () = symbol_set_fullname (ABSVIEWTYPE, "\"absviewtype\"")
val () = symbol_set_tyname (ABSVIEWTYPE, t0kn_tyname)
//
val ABSVIEWT0YPE = symbol_make "ABSVIEWT0YPE"
val () = symbol_set_fullname (ABSVIEWT0YPE, "\"absviewt@ype\"")
val () = symbol_set_tyname (ABSVIEWT0YPE, t0kn_tyname)
//
val AND = symbol_make "AND"
val () = symbol_set_fullname (AND, "\"and\"")
val () = symbol_set_tyname (AND, t0kn_tyname)
//
val AS = symbol_make "AS"
val () = symbol_set_fullname (AS, "\"as\"")
val () = symbol_set_tyname (AS, t0kn_tyname)
//
val ASSUME = symbol_make "ASSUME"
val () = symbol_set_fullname (ASSUME, "\"assume\"")
val () = symbol_set_tyname (ASSUME, t0kn_tyname)
//
val ATLAM = symbol_make "ATLAM"
val () = symbol_set_fullname (ATLAM, "\"@lam\"")
val () = symbol_set_tyname (ATLAM, t0kn_tyname)
val ATLLAM = symbol_make "ATLLAM"
val () = symbol_set_fullname (ATLLAM, "\"@llam\"")
val () = symbol_set_tyname (ATLLAM, t0kn_tyname)
val ATFIX = symbol_make "ATFIX"
val () = symbol_set_fullname (ATFIX, "\"@fix\"")
val () = symbol_set_tyname (ATFIX, t0kn_tyname)
//
val BEGIN = symbol_make "BEGIN"
val () = symbol_set_fullname (BEGIN, "\"begin\"")
val () = symbol_set_tyname (BEGIN, t0kn_tyname)
//
val BREAK = symbol_make "BREAK"
val () = symbol_set_fullname (BREAK, "\"break\"")
val () = symbol_set_tyname (BREAK, t0kn_tyname)
//
val CASE = symbol_make "CASE"
val () = symbol_set_fullname (CASE, "\"case\"")
val () = symbol_set_tyname (CASE, t0kn_tyname)
val CASEMINUS = symbol_make "CASEMINUS"
val () = symbol_set_fullname (CASEMINUS, "\"case-\"")
val () = symbol_set_tyname (CASEMINUS, t0kn_tyname)
val CASEPLUS = symbol_make "CASEPLUS"
val () = symbol_set_fullname (CASEPLUS, "\"case+\"")
val () = symbol_set_tyname (CASEPLUS, t0kn_tyname)
//
val CASTFN = symbol_make "CASTFN"
val () = symbol_set_fullname (CASTFN, "\"castfn\"")
val () = symbol_set_tyname (CASTFN, t0kn_tyname)
//
val CLASSDEC = symbol_make "CLASSDEC"
val () = symbol_set_fullname (CLASSDEC, "\"classdec\"")
val () = symbol_set_tyname (CLASSDEC, t0kn_tyname)
//
val CONTINUE = symbol_make "CONTINUE"
val () = symbol_set_fullname (CONTINUE, "\"continue\"")
val () = symbol_set_tyname (CONTINUE, t0kn_tyname)
//
val DATASORT = symbol_make "DATASORT"
val () = symbol_set_fullname (DATASORT, "\"datasort\"")
val () = symbol_set_tyname (DATASORT, t0kn_tyname)
val DATAPARASORT = symbol_make "DATAPARASORT"
val () = symbol_set_fullname (DATAPARASORT, "\"dataparasort\"")
val () = symbol_set_tyname (DATAPARASORT, t0kn_tyname)
//
val DATAPROP = symbol_make "DATAPROP"
val () = symbol_set_fullname (DATAPROP, "\"dataprop\"")
val () = symbol_set_tyname (DATAPROP, t0kn_tyname)
val DATATYPE = symbol_make "DATATYPE"
val () = symbol_set_fullname (DATATYPE, "\"datatype\"")
val () = symbol_set_tyname (DATATYPE, t0kn_tyname)
val DATAVIEW = symbol_make "DATAVIEW"
val () = symbol_set_fullname (DATAVIEW, "\"dataview\"")
val () = symbol_set_tyname (DATAVIEW, t0kn_tyname)
val DATAVIEWTYPE = symbol_make "DATAVIEWTYPE"
val () = symbol_set_fullname (DATAVIEWTYPE, "\"dataviewtype\"")
val () = symbol_set_tyname (DATAVIEWTYPE, t0kn_tyname)
//
val DO = symbol_make "DO"
val () = symbol_set_fullname (DO, "\"do\"")
val () = symbol_set_tyname (DO, t0kn_tyname)
//
val DYN = symbol_make "DYN"
val () = symbol_set_fullname (DYN, "\"dyn\"")
val () = symbol_set_tyname (DYN, t0kn_tyname)
//
val DYNLOAD = symbol_make "DYNLOAD"
val () = symbol_set_fullname (DYNLOAD, "\"dynload\"")
val () = symbol_set_tyname (DYNLOAD, t0kn_tyname)
//
val ELSE = symbol_make "ELSE"
val () = symbol_set_fullname (ELSE, "\"else\"")
val () = symbol_set_tyname (ELSE, t0kn_tyname)
//
val END = symbol_make "END"
val () = symbol_set_fullname (END, "\"end\"")
val () = symbol_set_tyname (END, t0kn_tyname)
//
val EXCEPTION = symbol_make "EXCEPTION"
val () = symbol_set_fullname (EXCEPTION, "\"exception\"")
val () = symbol_set_tyname (EXCEPTION, t0kn_tyname)
//
val EXTERN = symbol_make "EXTERN"
val () = symbol_set_fullname (EXTERN, "\"extern\"")
val () = symbol_set_tyname (EXTERN, t0kn_tyname)
//
val FIX = symbol_make "FIX"
val () = symbol_set_fullname (FIX, "\"fix\"")
val () = symbol_set_tyname (FIX, t0kn_tyname)
//
val FN = symbol_make "FN"
val () = symbol_set_fullname (FN, "\"fn\"")
val () = symbol_set_tyname (FN, t0kn_tyname)
val FNSTAR = symbol_make "FNSTAR"
val () = symbol_set_fullname (FNSTAR, "\"fn*\"")
val () = symbol_set_tyname (FNSTAR, t0kn_tyname)
//
val FOR = symbol_make "FOR"
val () = symbol_set_fullname (FOR, "\"for\"")
val () = symbol_set_tyname (FOR, t0kn_tyname)
val FORSTAR = symbol_make "FORSTAR"
val () = symbol_set_fullname (FORSTAR, "\"for*\"")
val () = symbol_set_tyname (FORSTAR, t0kn_tyname)
//
val FUN = symbol_make "FUN"
val () = symbol_set_fullname (FUN, "\"fun\"")
val () = symbol_set_tyname (FUN, t0kn_tyname)
//
val IF = symbol_make "IF"
val () = symbol_set_fullname (IF, "\"if\"")
val () = symbol_set_tyname (IF, t0kn_tyname)
//
val IMPLEMENT = symbol_make "IMPLEMENT"
val () = symbol_set_fullname (IMPLEMENT, "\"implement\"")
val () = symbol_set_tyname (IMPLEMENT, t0kn_tyname)
//
val IN = symbol_make "IN"
val () = symbol_set_fullname (IN, "\"in\"")
val () = symbol_set_tyname (IN, t0kn_tyname)
//
val INFIX = symbol_make "INFIX"
val () = symbol_set_fullname (INFIX, "\"infix\"")
val () = symbol_set_tyname (INFIX, t0kn_tyname)
val INFIXL = symbol_make "INFIXL"
val () = symbol_set_fullname (INFIXL, "\"infixl\"")
val () = symbol_set_tyname (INFIXL, t0kn_tyname)
val INFIXR = symbol_make "INFIXR"
val () = symbol_set_fullname (INFIXR, "\"infixr\"")
val () = symbol_set_tyname (INFIXR, t0kn_tyname)
//
val LAM = symbol_make "LAM"
val () = symbol_set_fullname (LAM, "\"lam\"")
val () = symbol_set_tyname (LAM, t0kn_tyname)
//
val LET = symbol_make "LET"
val () = symbol_set_fullname (LET, "\"let\"")
val () = symbol_set_tyname (LET, t0kn_tyname)
//
val LLAM = symbol_make "LLAM"
val () = symbol_set_fullname (LLAM, "\"llam\"")
val () = symbol_set_tyname (LLAM, t0kn_tyname)
//
val LOCAL = symbol_make "LOCAL"
val () = symbol_set_fullname (LOCAL, "\"local\"")
val () = symbol_set_tyname (LOCAL, t0kn_tyname)
//
val MACDEF = symbol_make "MACDEF"
val () = symbol_set_fullname (MACDEF, "\"macdef\"")
val () = symbol_set_tyname (MACDEF, t0kn_tyname)
val MACRODEF = symbol_make "MACRODEF"
val () = symbol_set_fullname (MACRODEF, "\"macrodef\"")
val () = symbol_set_tyname (MACRODEF, t0kn_tyname)
//
val NONFIX = symbol_make "NONFIX"
val () = symbol_set_fullname (NONFIX, "\"nonfix\"")
val () = symbol_set_tyname (NONFIX, t0kn_tyname)
//
val OF = symbol_make "OF"
val () = symbol_set_fullname (OF, "\"of\"")
val () = symbol_set_tyname (OF, t0kn_tyname)
//
val OP = symbol_make "OP"
val () = symbol_set_fullname (OP, "\"op\"")
val () = symbol_set_tyname (OP, t0kn_tyname)
//
val OVERLOAD = symbol_make "OVERLOAD"
val () = symbol_set_fullname (OVERLOAD, "\"overload\"")
val () = symbol_set_tyname (OVERLOAD, t0kn_tyname)
//
val PAR = symbol_make "PAR"
val () = symbol_set_fullname (PAR, "\"par\"")
val () = symbol_set_tyname (PAR, t0kn_tyname)
//
val POSTFIX = symbol_make "POSTFIX"
val () = symbol_set_fullname (POSTFIX, "\"postfix\"")
val () = symbol_set_tyname (POSTFIX, t0kn_tyname)
//
val PRAXI = symbol_make "PRAXI"
val () = symbol_set_fullname (PRAXI, "\"praxi\"")
val () = symbol_set_tyname (PRAXI, t0kn_tyname)
//
val PREFIX = symbol_make "PREFIX"
val () = symbol_set_fullname (PREFIX, "\"prefix\"")
val () = symbol_set_tyname (PREFIX, t0kn_tyname)
//
val PRFN = symbol_make "PRFN"
val () = symbol_set_fullname (PRFN, "\"prfn\"")
val () = symbol_set_tyname (PRFN, t0kn_tyname)
//
val PRFUN = symbol_make "PRFUN"
val () = symbol_set_fullname (PRFUN, "\"prfun\"")
val () = symbol_set_tyname (PRFUN, t0kn_tyname)
//
val PROPDEF = symbol_make "PROPDEF"
val () = symbol_set_fullname (PROPDEF, "\"propdef\"")
val () = symbol_set_tyname (PROPDEF, t0kn_tyname)
val PROPMINUS = symbol_make "PROPMINUS"
val () = symbol_set_fullname (PROPMINUS, "\"prop-\"")
val () = symbol_set_tyname (PROPMINUS, t0kn_tyname)
val PROPPLUS = symbol_make "PROPPLUS"
val () = symbol_set_fullname (PROPPLUS, "\"prop+\"")
val () = symbol_set_tyname (PROPPLUS, t0kn_tyname)
//
val PRVAL = symbol_make "PRVAL"
val () = symbol_set_fullname (PRVAL, "\"prval\"")
val () = symbol_set_tyname (PRVAL, t0kn_tyname)
//
val REC = symbol_make "REC"
val () = symbol_set_fullname (REC, "\"rec\"")
val () = symbol_set_tyname (REC, t0kn_tyname)
//
val R0EAD = symbol_make "R0EAD"
val () = symbol_set_fullname (R0EAD, "\"r@ead\"")
val () = symbol_set_tyname (R0EAD, t0kn_tyname)
//
val SCASE = symbol_make "SCASE"
val () = symbol_set_fullname (SCASE, "\"scase\"")
val () = symbol_set_tyname (SCASE, t0kn_tyname)
//
val SIF = symbol_make "SIF"
val () = symbol_set_fullname (SIF, "\"sif\"")
val () = symbol_set_tyname (SIF, t0kn_tyname)
//
val SORTDEF = symbol_make "SORTDEF"
val () = symbol_set_fullname (SORTDEF, "\"sortdef\"")
val () = symbol_set_tyname (SORTDEF, t0kn_tyname)
//
val STACST = symbol_make "STACST"
val () = symbol_set_fullname (STACST, "\"stacst\"")
val () = symbol_set_tyname (STACST, t0kn_tyname)
//
val STADEF = symbol_make "STADEF"
val () = symbol_set_fullname (STADEF, "\"stadef\"")
val () = symbol_set_tyname (STADEF, t0kn_tyname)
//
val STAIF = symbol_make "STAIF"
val () = symbol_set_fullname (STAIF, "\"staif\"")
val () = symbol_set_tyname (STAIF, t0kn_tyname)
//
val STALOAD = symbol_make "STALOAD"
val () = symbol_set_fullname (STALOAD, "\"staload\"")
val () = symbol_set_tyname (STALOAD, t0kn_tyname)
//
val STAVAR = symbol_make "STAVAR"
val () = symbol_set_fullname (STAVAR, "\"stavar\"")
val () = symbol_set_tyname (STAVAR, t0kn_tyname)
//
val SYMELIM = symbol_make "SYMELIM"
val () = symbol_set_fullname (SYMELIM, "\"symelim\"")
val () = symbol_set_tyname (SYMELIM, t0kn_tyname)
val SYMINTR = symbol_make "SYMINTR"
val () = symbol_set_fullname (SYMINTR, "\"symintr\"")
val () = symbol_set_tyname (SYMINTR, t0kn_tyname)
//
val THEN = symbol_make "THEN"
val () = symbol_set_fullname (THEN, "\"then\"")
val () = symbol_set_tyname (THEN, t0kn_tyname)
//
val TRY = symbol_make "TRY"
val () = symbol_set_fullname (TRY, "\"try\"")
val () = symbol_set_tyname (TRY, t0kn_tyname)
//
val TYPEDEF = symbol_make "TYPEDEF"
val () = symbol_set_fullname (TYPEDEF, "\"typedef\"")
val () = symbol_set_tyname (TYPEDEF, t0kn_tyname)
val TYPEMINUS = symbol_make "TYPEMINUS"
val () = symbol_set_fullname (TYPEMINUS, "\"type-\"")
val () = symbol_set_tyname (TYPEMINUS, t0kn_tyname)
val TYPEPLUS = symbol_make "TYPEPLUS"
val () = symbol_set_fullname (TYPEPLUS, "\"type+\"")
val () = symbol_set_tyname (TYPEPLUS, t0kn_tyname)
//
val T0YPE = symbol_make "T0YPE"
val () = symbol_set_fullname (T0YPE, "\"t@ype\"")
val () = symbol_set_tyname (T0YPE, t0kn_tyname)
val T0YPEMINUS = symbol_make "T0YPEMINUS"
val () = symbol_set_fullname (T0YPEMINUS, "\"t@ype-\"")
val () = symbol_set_tyname (T0YPEMINUS, t0kn_tyname)
val T0YPEPLUS = symbol_make "T0YPEPLUS"
val () = symbol_set_fullname (T0YPEPLUS, "\"t@ype+\"")
val () = symbol_set_tyname (T0YPEPLUS, t0kn_tyname)
//
val VAL = symbol_make "VAL"
val () = symbol_set_fullname (VAL, "\"val\"")
val () = symbol_set_tyname (VAL, t0kn_tyname)
val VALMINUS = symbol_make "VALMINUS"
val () = symbol_set_fullname (VALMINUS, "\"val-\"")
val () = symbol_set_tyname (VALMINUS, t0kn_tyname)
val VALPLUS = symbol_make "VALPLUS"
val () = symbol_set_fullname (VALPLUS, "\"val+\"")
val () = symbol_set_tyname (VALPLUS, t0kn_tyname)
//
val VAR = symbol_make "VAR"
val () = symbol_set_fullname (VAR, "\"var\"")
val () = symbol_set_tyname (VAR, t0kn_tyname)
//
val VIEWDEF = symbol_make "VIEWDEF"
val () = symbol_set_fullname (VIEWDEF, "\"viewdef\"")
val () = symbol_set_tyname (VIEWDEF, t0kn_tyname)
val VIEWMINUS = symbol_make "VIEWMINUS"
val () = symbol_set_fullname (VIEWMINUS, "\"view-\"")
val () = symbol_set_tyname (VIEWMINUS, t0kn_tyname)
val VIEWPLUS = symbol_make "VIEWPLUS"
val () = symbol_set_fullname (VIEWPLUS, "\"view+\"")
val () = symbol_set_tyname (VIEWPLUS, t0kn_tyname)
//
val VIEWTYPEDEF = symbol_make "VIEWTYPEDEF"
val () = symbol_set_fullname (VIEWTYPEDEF, "\"viewtypedef\"")
val () = symbol_set_tyname (VIEWTYPEDEF, t0kn_tyname)
val VIEWTYPEMINUS = symbol_make "VIEWTYPEMINUS"
val () = symbol_set_fullname (VIEWTYPEMINUS, "\"viewtype-\"")
val () = symbol_set_tyname (VIEWTYPEMINUS, t0kn_tyname)
val VIEWTYPEPLUS = symbol_make "VIEWTYPEPLUS"
val () = symbol_set_fullname (VIEWTYPEPLUS, "\"viewtype+\"")
val () = symbol_set_tyname (VIEWTYPEPLUS, t0kn_tyname)
//
val VIEWT0YPE = symbol_make "VIEWT0YPE"
val () = symbol_set_fullname (VIEWT0YPE, "\"viewt@ype\"")
val () = symbol_set_tyname (VIEWT0YPE, t0kn_tyname)
val VIEWT0YPEMINUS = symbol_make "VIEWT0YPEMINUS"
val () = symbol_set_fullname (VIEWT0YPEMINUS, "\"viewt@ype-\"")
val () = symbol_set_tyname (VIEWT0YPEMINUS, t0kn_tyname)
val VIEWT0YPEPLUS = symbol_make "VIEWT0YPEPLUS"
val () = symbol_set_fullname (VIEWT0YPEPLUS, "\"viewt@ype+\"")
val () = symbol_set_tyname (VIEWT0YPEPLUS, t0kn_tyname)
//
val WHEN = symbol_make "WHEN"
val () = symbol_set_fullname (WHEN, "\"when\"")
val () = symbol_set_tyname (WHEN, t0kn_tyname)
//
val WHERE = symbol_make "WHERE"
val () = symbol_set_fullname (WHERE, "\"where\"")
val () = symbol_set_tyname (WHERE, t0kn_tyname)
//
val WHILE = symbol_make "WHILE"
val () = symbol_set_fullname (WHILE, "\"while\"")
val () = symbol_set_tyname (WHILE, t0kn_tyname)
val WHILESTAR = symbol_make "WHILESTAR"
val () = symbol_set_fullname (WHILESTAR, "\"while*\"")
val () = symbol_set_tyname (WHILESTAR, t0kn_tyname)
//
val WITH = symbol_make "WITH"
val () = symbol_set_fullname (WITH, "\"with\"")
val () = symbol_set_tyname (WITH, t0kn_tyname)
//
val WITHPROP = symbol_make "WITHPROP"
val () = symbol_set_fullname (WITHPROP, "\"withprop\"")
val () = symbol_set_tyname (WITHPROP, t0kn_tyname)
val WITHTYPE = symbol_make "WITHTYPE"
val () = symbol_set_fullname (WITHTYPE, "\"withtype\"")
val () = symbol_set_tyname (WITHTYPE, t0kn_tyname)
val WITHVIEW = symbol_make "WITHVIEW"
val () = symbol_set_fullname (WITHVIEW, "\"withview\"")
val () = symbol_set_tyname (WITHVIEW, t0kn_tyname)
val WITHVIEWTYPE = symbol_make "WITHVIEWTYPE"
val () = symbol_set_fullname (WITHVIEWTYPE, "\"withviewtype\"")
val () = symbol_set_tyname (WITHVIEWTYPE, t0kn_tyname)
//
(* ****** ****** *)
//
val AMPERSAND = symbol_make ("AMPERSAND")
val () = symbol_set_fullname (AMPERSAND, "\"&\"")
val () = symbol_set_tyname (AMPERSAND, t0kn_tyname)
//
val BACKQUOTE = symbol_make ("BACKQUOTE")
val () = symbol_set_fullname (BACKQUOTE, "\"`\"")
val () = symbol_set_tyname (BACKQUOTE, t0kn_tyname)
//
val BACKSLASH = symbol_make ("BACKSLASH")
val () = symbol_set_fullname (BACKSLASH, "\"\\\"")
val () = symbol_set_tyname (BACKSLASH, t0kn_tyname)
//
val BANG = symbol_make ("BANG")
val () = symbol_set_fullname (BANG, "\"!\"")
val () = symbol_set_tyname (BANG, t0kn_tyname)
//
val BAR = symbol_make ("BAR")
val () = symbol_set_fullname (BAR, "\"|\"")
val () = symbol_set_tyname (BAR, t0kn_tyname)
//
val COMMA = symbol_make ("COMMA")
val () = symbol_set_fullname (COMMA, "\",\"")
val () = symbol_set_tyname (COMMA, t0kn_tyname)
//
val COLON = symbol_make ("COLON")
val () = symbol_set_fullname (COLON, "\":\"")
val () = symbol_set_tyname (COLON, t0kn_tyname)
//
val SEMICOLON = symbol_make ("SEMICOLON")
val () = symbol_set_fullname (SEMICOLON, "\";\"")
val () = symbol_set_tyname (SEMICOLON, t0kn_tyname)
//
val DOT = symbol_make ("DOT")
val () = symbol_set_fullname (DOT, "\".\"")
val () = symbol_set_tyname (DOT, t0kn_tyname)
//
val EQ = symbol_make ("EQ")
val () = symbol_set_fullname (EQ, "\"=\"")
val () = symbol_set_tyname (EQ, t0kn_tyname)
//
val LT = symbol_make ("LT")
val () = symbol_set_fullname (LT, "\"<\"")
val () = symbol_set_tyname (LT, t0kn_tyname)
val GT = symbol_make ("GT")
val () = symbol_set_fullname (GT, "\">\"")
val () = symbol_set_tyname (GT, t0kn_tyname)
//
val DOLLAR = symbol_make ("DOLLAR")
val () = symbol_set_fullname (DOLLAR, "\"$\"")
val () = symbol_set_tyname (DOLLAR, t0kn_tyname)
//
val HASH = symbol_make ("HASH")
val () = symbol_set_fullname (HASH, "\"#\"")
val () = symbol_set_tyname (HASH, t0kn_tyname)
//
val TILDE = symbol_make ("TILDE")
val () = symbol_set_fullname (TILDE, "\"~\"")
val () = symbol_set_tyname (TILDE, t0kn_tyname)
//
val DOTDOT = symbol_make ("DOTDOT")
val () = symbol_set_fullname (DOTDOT, "\"..\"")
val () = symbol_set_tyname (DOTDOT, t0kn_tyname)
val DOTDOTDOT = symbol_make ("DOTDOTDOT")
val () = symbol_set_fullname (DOTDOTDOT, "\"...\"")
val () = symbol_set_tyname (DOTDOTDOT, t0kn_tyname)
//
val EQLT = symbol_make ("EQLT")
val () = symbol_set_fullname (EQLT, "\"=<\"")
val () = symbol_set_tyname (EQLT, t0kn_tyname)
val EQGT = symbol_make ("EQGT")
val () = symbol_set_fullname (EQGT, "\"=>\"")
val () = symbol_set_tyname (EQGT, t0kn_tyname)
val EQLTGT = symbol_make ("EQLTGT")
val () = symbol_set_fullname (EQLTGT, "\"=<>\"")
val () = symbol_set_tyname (EQLTGT, t0kn_tyname)
val EQGTGT = symbol_make ("EQGTGT")
val () = symbol_set_fullname (EQGTGT, "\"=>>\"")
val () = symbol_set_tyname (EQGTGT, t0kn_tyname)
//
val EQSLASHEQGT = symbol_make ("EQSLASHEQGT")
val () = symbol_set_fullname (EQSLASHEQGT, "\"=/=>\"")
val () = symbol_set_tyname (EQSLASHEQGT, t0kn_tyname)
val EQSLASHEQGTGT = symbol_make ("EQSLASHEQGTGT")
val () = symbol_set_fullname (EQSLASHEQGTGT, "\"=/=>>\"")
val () = symbol_set_tyname (EQSLASHEQGTGT, t0kn_tyname)
//
val GTLT = symbol_make ("GTLT")
val () = symbol_set_fullname (GTLT, "\"><\"")
val () = symbol_set_tyname (GTLT, t0kn_tyname)
//
val DOTLT = symbol_make ("DOTLT")
val () = symbol_set_fullname (DOTLT, "\".<\"")
val () = symbol_set_tyname (DOTLT, t0kn_tyname)
val GTDOT = symbol_make ("GTDOT")
val () = symbol_set_fullname (GTDOT, "\">.\"")
val () = symbol_set_tyname (GTDOT, t0kn_tyname)
val DOTLTGTDOT = symbol_make ("DOTLTGTDOT")
val () = symbol_set_fullname (DOTLTGTDOT, "\".<>.\"")
val () = symbol_set_tyname (DOTLTGTDOT, t0kn_tyname)
//
val MINUSLT = symbol_make ("MINUSLT")
val () = symbol_set_fullname (MINUSLT, "\"-<\"")
val () = symbol_set_tyname (MINUSLT, t0kn_tyname)
val MINUSGT = symbol_make ("MINUSGT")
val () = symbol_set_fullname (MINUSGT, "\"->\"")
val () = symbol_set_tyname (MINUSGT, t0kn_tyname)
val MINUSLTGT = symbol_make ("MINUSLTGT")
val () = symbol_set_fullname (MINUSLTGT, "\"-<>\"")
val () = symbol_set_tyname (MINUSLTGT, t0kn_tyname)
//
val COLONLT = symbol_make ("COLONLT")
val () = symbol_set_fullname (COLONLT, "\":<\"")
val () = symbol_set_tyname (COLONLT, t0kn_tyname)
val COLONLTGT = symbol_make ("COLONLTGT")
val () = symbol_set_fullname (COLONLTGT, "\":<>\"")
val () = symbol_set_tyname (COLONLTGT, t0kn_tyname)
//
val BACKQUOTELPAREN = symbol_make ("BACKQUOTELPAREN")
val () = symbol_set_fullname (BACKQUOTELPAREN, "\"`(\"")
val () = symbol_set_tyname (BACKQUOTELPAREN, t0kn_tyname)
val COMMALPAREN = symbol_make ("COMMALPAREN")
val () = symbol_set_fullname (COMMALPAREN, "\",(\"")
val () = symbol_set_tyname (COMMALPAREN, t0kn_tyname)
val PERCENTLPAREN = symbol_make ("PERCENTLPAREN")
val () = symbol_set_fullname (PERCENTLPAREN, "\"%(\"")
val () = symbol_set_tyname (PERCENTLPAREN, t0kn_tyname)
(*
//
// HX: these symbols were reserved for supporting MP
//
val BACKQUOTELBRACKET = symbol_make ("BACKQUOTELBRACKET")
val () = symbol_set_fullname (BACKQUOTELBRACKET, "\"`[\"")
val () = symbol_set_tyname (BACKQUOTELBRACKET, t0kn_tyname)
val PERCENTLBRACKET = symbol_make ("PERCENTLBRACKET")
val () = symbol_set_fullname (COMMALBRACE, "\"%[\"")
val () = symbol_set_tyname (PERCENTLBRACKET, t0kn_tyname)
val COMMALBRACKET = symbol_make ("COMMALBRACKET")
val () = symbol_set_fullname (COMMALBRACKET, "\",[\"")
val () = symbol_set_tyname (COMMALBRACKET, t0kn_tyname)
//
val BACKQUOTELBRACE = symbol_make ("BACKQUOTELBRACE")
val () = symbol_set_fullname (BACKQUOTELBRACE, "\"`{\"")
val () = symbol_set_tyname (BACKQUOTELBRACE, t0kn_tyname)
val PERCENTLBRACE = symbol_make ("PERCENTLBRACE")
val () = symbol_set_fullname (COMMALBRACE, "\"%{\"")
val () = symbol_set_tyname (PERCENTLBRACE, t0kn_tyname)
val COMMALBRACE = symbol_make ("COMMALBRACE")
val () = symbol_set_fullname (COMMALBRACE, "\",{\"")
val () = symbol_set_tyname (COMMALBRACE, t0kn_tyname)
*)
(* ****** ****** *)
//
val DLRARRSZ = symbol_make "DLRARRSZ"
val () = symbol_set_fullname (DLRARRSZ, "\"$arrsz\"")
val () = symbol_set_tyname (DLRARRSZ, t0kn_tyname)
//
val DLRLST_T = symbol_make "DLRLST_T"
val () = symbol_set_fullname (DLRLST_T, "\"$lst_t\"")
val () = symbol_set_tyname (DLRLST_T, t0kn_tyname)
val DLRLST_VT = symbol_make "DLRLST_VT"
val () = symbol_set_fullname (DLRLST_VT, "\"$lst_vt\"")
val () = symbol_set_tyname (DLRLST_VT, t0kn_tyname)
//
val DLRREC_T = symbol_make "DLRREC_T"
val () = symbol_set_fullname (DLRREC_T, "\"$rec_t\"")
val () = symbol_set_tyname (DLRREC_T, t0kn_tyname)
val DLRREC_VT = symbol_make "DLRREC_VT"
val () = symbol_set_fullname (DLRREC_VT, "\"$rec_vt\"")
val () = symbol_set_tyname (DLRREC_VT, t0kn_tyname)
//
val DLRTUP_T = symbol_make "DLRTUP_T"
val () = symbol_set_fullname (DLRTUP_T, "\"$tup_t\"")
val () = symbol_set_tyname (DLRTUP_T, t0kn_tyname)
val DLRTUP_VT = symbol_make "DLRTUP_VT"
val () = symbol_set_fullname (DLRTUP_VT, "\"$tup_vt\"")
val () = symbol_set_tyname (DLRTUP_VT, t0kn_tyname)
//
val DLRDELAY = symbol_make "DLRDELAY"
val () = symbol_set_fullname (DLRDELAY, "\"$delay\"")
val () = symbol_set_tyname (DLRDELAY, t0kn_tyname)
val DLRLDELAY = symbol_make "DLRLDELAY"
val () = symbol_set_fullname (DLRLDELAY, "\"$ldelay\"")
val () = symbol_set_tyname (DLRLDELAY, t0kn_tyname)
//
val DLRDYNLOAD = symbol_make "DLRDYNLOAD"
val () = symbol_set_fullname (DLRDYNLOAD, "\"$dynload\"")
val () = symbol_set_tyname (DLRDYNLOAD, t0kn_tyname)
//
val DLREFFMASK_ALL = symbol_make "DLREFFMASK_ALL"
val () = symbol_set_fullname (DLREFFMASK_ALL, "\"$effmask_all\"")
val () = symbol_set_tyname (DLREFFMASK_ALL, t0kn_tyname)
//
val DLREFFMASK_EXN = symbol_make "DLREFFMASK_EXN"
val () = symbol_set_fullname (DLREFFMASK_EXN, "\"$effmask_exn\"")
val () = symbol_set_tyname (DLREFFMASK_EXN, t0kn_tyname)
//
val DLREFFMASK_NTM = symbol_make "DLREFFMASK_NTM"
val () = symbol_set_fullname (DLREFFMASK_NTM, "\"$effmask_ntm\"")
val () = symbol_set_tyname (DLREFFMASK_NTM, t0kn_tyname)
//
val DLREFFMASK_REF = symbol_make "DLREFFMASK_REF"
val () = symbol_set_fullname (DLREFFMASK_REF, "\"$effmask_ref\"")
val () = symbol_set_tyname (DLREFFMASK_REF, t0kn_tyname)
//
val DLRDECRYPT = symbol_make "DLRDECRYPT"
val () = symbol_set_fullname (DLRDECRYPT, "\"$decrypt\"")
val () = symbol_set_tyname (DLRDECRYPT, t0kn_tyname)
val DLRENCRYPT = symbol_make "DLRENCRYPT"
val () = symbol_set_fullname (DLRENCRYPT, "\"$encrypt\"")
val () = symbol_set_tyname (DLRENCRYPT, t0kn_tyname)
//
val DLREXTERN = symbol_make "DLREXTERN"
val () = symbol_set_fullname (DLREXTERN, "\"$extern\"")
val () = symbol_set_tyname (DLREXTERN, t0kn_tyname)
val DLREXTVAL = symbol_make "DLREXTVAL"
val () = symbol_set_fullname (DLREXTVAL, "\"$extval\"")
val () = symbol_set_tyname (DLREXTVAL, t0kn_tyname)
//
val DLREXTYPE = symbol_make "DLREXTYPE"
val () = symbol_set_fullname (DLREXTYPE, "\"$extype\"")
val () = symbol_set_tyname (DLREXTYPE, t0kn_tyname)
val DLREXTYPE_STRUCT = symbol_make "DLREXTYPE_STRUCT"
val () = symbol_set_fullname (DLREXTYPE_STRUCT, "\"$extype_struct\"")
val () = symbol_set_tyname (DLREXTYPE_STRUCT, t0kn_tyname)
//
val DLRFOLD = symbol_make "DLRFOLD"
val () = symbol_set_fullname (DLRFOLD, "\"$fold\"")
val () = symbol_set_tyname (DLRFOLD, t0kn_tyname)
val DLRUNFOLD = symbol_make "DLRUNFOLD"
val () = symbol_set_fullname (DLRUNFOLD, "\"$unfold\"")
val () = symbol_set_tyname (DLRUNFOLD, t0kn_tyname)
//
val DLRRAISE = symbol_make "DLRRAISE"
val () = symbol_set_fullname (DLRRAISE, "\"$raise\"")
val () = symbol_set_tyname (DLRRAISE, t0kn_tyname)
//
val DLRTYPEOF = symbol_make "DLRTYPEOF"
val () = symbol_set_fullname (DLRTYPEOF, "\"$typeof\"")
val () = symbol_set_tyname (DLRTYPEOF, t0kn_tyname)
//
(* ****** ****** *)
//
val SRPFILENAME = symbol_make "SRPFILENAME"
val () = symbol_set_fullname (SRPFILENAME, "\"#FILENAME\"")
val () = symbol_set_tyname (SRPFILENAME, t0kn_tyname)
val SRPLOCATION = symbol_make "SRPLOCATION"
val () = symbol_set_fullname (SRPLOCATION, "\"#LOCATION\"")
val () = symbol_set_tyname (SRPLOCATION, t0kn_tyname)
val SRPCHARCOUNT = symbol_make "SRPCHARCOUNT"
val () = symbol_set_fullname (SRPCHARCOUNT, "\"#CHARCOUNT\"")
val () = symbol_set_tyname (SRPCHARCOUNT, t0kn_tyname)
val SRPLINECOUNT = symbol_make "SRPLINECOUNT"
val () = symbol_set_fullname (SRPLINECOUNT, "\"#LINECOUNT\"")
val () = symbol_set_tyname (SRPLINECOUNT, t0kn_tyname)
//
val SRPASSERT = symbol_make "SRPASSERT"
val () = symbol_set_fullname (SRPASSERT, "\"#assert\"")
val () = symbol_set_tyname (SRPASSERT, t0kn_tyname)
val SRPDEFINE = symbol_make "SRPDEFINE"
val () = symbol_set_fullname (SRPDEFINE, "\"#define\"")
val () = symbol_set_tyname (SRPDEFINE, t0kn_tyname)
val SRPELSE = symbol_make "SRPELSE"
val () = symbol_set_fullname (SRPELSE, "\"#else\"")
val () = symbol_set_tyname (SRPELSE, t0kn_tyname)
val SRPELIF = symbol_make "SRPELIF"
val () = symbol_set_fullname (SRPELIF, "\"#elif\"")
val () = symbol_set_tyname (SRPELIF, t0kn_tyname)
val SRPELIFDEF = symbol_make "SRPELIFDEF"
val () = symbol_set_fullname (SRPELIFDEF, "\"#elifdef\"")
val () = symbol_set_tyname (SRPELIFDEF, t0kn_tyname)
val SRPELIFNDEF = symbol_make "SRPELIFNDEF"
val () = symbol_set_fullname (SRPELIFNDEF, "\"#elifndef\"")
val () = symbol_set_tyname (SRPELIFNDEF, t0kn_tyname)
val SRPENDIF = symbol_make "SRPENDIF"
val () = symbol_set_fullname (SRPENDIF, "\"#endif\"")
val () = symbol_set_tyname (SRPENDIF, t0kn_tyname)
val SRPERROR = symbol_make "SRPERROR"
val () = symbol_set_fullname (SRPERROR, "\"#error\"")
val () = symbol_set_tyname (SRPERROR, t0kn_tyname)
val SRPIF = symbol_make "SRPIF"
val () = symbol_set_fullname (SRPIF, "\"#if\"")
val () = symbol_set_tyname (SRPIF, t0kn_tyname)
val SRPIFDEF = symbol_make "SRPIFDEF"
val () = symbol_set_fullname (SRPIFDEF, "\"#ifdef\"")
val () = symbol_set_tyname (SRPIFDEF, t0kn_tyname)
val SRPIFNDEF = symbol_make "SRPIFNDEF"
val () = symbol_set_fullname (SRPIFNDEF, "\"#ifndef\"")
val () = symbol_set_tyname (SRPIFNDEF, t0kn_tyname)
val SRPINCLUDE = symbol_make "SRPINCLUDE"
val () = symbol_set_fullname (SRPINCLUDE, "\"#include\"")
val () = symbol_set_tyname (SRPINCLUDE, t0kn_tyname)
val SRPPRINT = symbol_make "SRPPRINT"
val () = symbol_set_fullname (SRPPRINT, "\"#print\"")
val () = symbol_set_tyname (SRPPRINT, t0kn_tyname)
val SRPTHEN = symbol_make "SRPTHEN"
val () = symbol_set_fullname (SRPTHEN, "\"#then\"")
val () = symbol_set_tyname (SRPTHEN, t0kn_tyname)
val SRPUNDEF = symbol_make "SRPUNDEF"
val () = symbol_set_fullname (SRPUNDEF, "\"#undef\"")
val () = symbol_set_tyname (SRPUNDEF, t0kn_tyname)
//
(* ****** ****** *)
//
val FOLDAT = symbol_make "FOLDAT"
val () = symbol_set_fullname (FOLDAT, "\"fold@\"")
val () = symbol_set_tyname (FOLDAT, t0kn_tyname)
//
val FREEAT = symbol_make "FREEAT"
val () = symbol_set_fullname (FREEAT, "\"free@\"")
val () = symbol_set_tyname (FREEAT, t0kn_tyname)
//
val VIEWAT = symbol_make "VIEWAT"
val () = symbol_set_fullname (VIEWAT, "\"view@\"")
val () = symbol_set_tyname (VIEWAT, t0kn_tyname)
//
(* ****** ****** *)

val LPAREN = symbol_make "LPAREN"
val () = symbol_set_fullname (LPAREN, "\"(\"")
val () = symbol_set_tyname (LPAREN, t0kn_tyname)
val RPAREN = symbol_make "RPAREN"
val () = symbol_set_fullname (RPAREN, "\")\"")
val () = symbol_set_tyname (RPAREN, t0kn_tyname)
//
val LBRACKET = symbol_make "LBRACKET"
val () = symbol_set_fullname (LBRACKET, "\"[\"")
val () = symbol_set_tyname (LBRACKET, t0kn_tyname)
val RBRACKET = symbol_make "RBRACKET"
val () = symbol_set_fullname (RBRACKET, "\"]\"")
val () = symbol_set_tyname (RBRACKET, t0kn_tyname)
//
val LBRACE = symbol_make "LBRACE"
val () = symbol_set_fullname (LBRACE, "\"{\"")
val () = symbol_set_tyname (LBRACE, t0kn_tyname)
val RBRACE = symbol_make "RBRACE"
val () = symbol_set_fullname (RBRACE, "\"}\"")
val () = symbol_set_tyname (RBRACE, t0kn_tyname)
//
val ATLPAREN = symbol_make "ATLPAREN"
val () = symbol_set_fullname (ATLPAREN, "\"@(\"")
val () = symbol_set_tyname (ATLPAREN, t0kn_tyname)
val ATLBRACKET = symbol_make "ATLBRACKET"
val () = symbol_set_fullname (ATLBRACKET, "\"@[\"")
val () = symbol_set_tyname (ATLBRACKET, t0kn_tyname)
val ATLBRACE = symbol_make "ATLBRACE"
val () = symbol_set_fullname (ATLBRACE, "\"@{\"")
val () = symbol_set_tyname (ATLBRACE, t0kn_tyname)
//
val QUOTELPAREN = symbol_make "QUOTELPAREN"
val () = symbol_set_fullname (QUOTELPAREN, "\"'(\"")
val () = symbol_set_tyname (QUOTELPAREN, t0kn_tyname)
val QUOTELBRACKET = symbol_make "QUOTELBRACKET"
val () = symbol_set_fullname (QUOTELBRACKET, "\"'[\"")
val () = symbol_set_tyname (QUOTELBRACKET, t0kn_tyname)
val QUOTELBRACE = symbol_make "QUOTELBRACE"
val () = symbol_set_fullname (QUOTELBRACE, "\"'{\"")
val () = symbol_set_tyname (QUOTELBRACE, t0kn_tyname)
//
val HASHLPAREN = symbol_make "HASHLPAREN"
val () = symbol_set_fullname (HASHLPAREN, "\"#(\"")
val () = symbol_set_tyname (HASHLPAREN, t0kn_tyname)
val HASHLBRACKET = symbol_make "HASHLBRACKET"
val () = symbol_set_fullname (HASHLBRACKET, "\"#[\"")
val () = symbol_set_tyname (HASHLBRACKET, t0kn_tyname)
val HASHLBRACE = symbol_make "HASHLBRACE"
val () = symbol_set_fullname (HASHLBRACE, "\"#{\"")
val () = symbol_set_tyname (HASHLBRACE, t0kn_tyname)
//
(* ****** ****** *)

val theStartEntry = symbol_make_nt "theStartEntry"
val () = symbol_set_fullname (theStartEntry, "program")
val () = symbol_set_tyname (theStartEntry, d0eclst_tyname)

(* ****** ****** *)
//
val abskind = symbol_make_nt "abskind"
val () = symbol_set_tyname (abskind, abskind_tyname)
val dcstkind = symbol_make_nt "dcstkind"
val () = symbol_set_tyname (dcstkind, dcstkind_tyname)
val datakind = symbol_make_nt "datakind"
val () = symbol_set_tyname (datakind, datakind_tyname)
val stadefkind = symbol_make_nt "stadefkind"
val () = symbol_set_tyname (stadefkind, stadefkind_tyname)
//
val valkind = symbol_make_nt "valkind"
val () = symbol_set_tyname (valkind, valkind_tyname)
val funkind = symbol_make_nt "funkind"
val () = symbol_set_tyname (funkind, funkind_tyname)
//
val lamkind = symbol_make_nt "lamkind"
val () = symbol_set_tyname (lamkind, lamkind_tyname)
val fixkind = symbol_make_nt "fixkind"
val () = symbol_set_tyname (fixkind, fixkind_tyname)
//
val srpifkind = symbol_make_nt "srpifkind"
val () = symbol_set_tyname (srpifkind, srpifkindtok_tyname)
val srpelifkind = symbol_make_nt "srpelifkind"
val () = symbol_set_tyname (srpelifkind, srpifkindtok_tyname)
val srpthenopt = symbol_make_nt "srpthenopt"
//
(* ****** ****** *)

val i0de = symbol_make_nt "i0de"
val () = symbol_set_tyname (i0de, i0de_tyname)
val i0de_dlr = symbol_make_nt "i0de_dlr"
val () = symbol_set_tyname (i0de_dlr, i0de_tyname)
val i0deseq = symbol_make_nt "i0deseq"
val () = symbol_set_tyname (i0deseq, i0delst_tyname)
val i0dext = symbol_make_nt "i0dext"
val () = symbol_set_tyname (i0dext, i0de_tyname)

val l0ab = symbol_make_nt "l0ab"
val () = symbol_set_tyname (l0ab, l0ab_tyname)
val stai0de = symbol_make_nt "stai0de"
val () = symbol_set_tyname (stai0de, i0de_tyname)
val p0rec = symbol_make_nt "p0rec"
val () = symbol_set_tyname (p0rec, p0rec_tyname)

(* ****** ****** *)

val e0xp = symbol_make_nt "e0xp"
val () = symbol_set_tyname (e0xp, e0xp_tyname)
val atme0xp = symbol_make_nt "atme0xp"
val () = symbol_set_tyname (atme0xp, e0xp_tyname)
val e0xpseq = symbol_make_nt "e0xpseq"
val () = symbol_set_tyname (e0xpseq, e0xplst_tyname)
val commae0xpseq = symbol_make_nt "commae0xpseq"
val () = symbol_set_tyname (commae0xpseq, e0xplst_tyname)
val e0xpopt = symbol_make_nt "e0xpopt"
val () = symbol_set_tyname (e0xpopt, e0xpopt_tyname)

(* ****** ****** *)

val e0ffid = symbol_make_nt "e0ffid"
val () = symbol_set_tyname (e0ffid, i0de_tyname)
val e0fftag = symbol_make_nt "e0fftag"
val () = symbol_set_tyname (e0fftag, e0fftag_tyname)
val e0fftagseq = symbol_make_nt "e0fftagseq"
val () = symbol_set_tyname (e0fftagseq, e0fftaglst_tyname)
val commae0fftagseq = symbol_make_nt "commae0fftagseq"
val () = symbol_set_tyname (commae0fftagseq, e0fftaglst_tyname)
val colonwith = symbol_make_nt "colonwith"
val () = symbol_set_tyname (colonwith, e0fftaglstopt_tyname)

(* ****** ****** *)

val s0rt = symbol_make_nt "s0rt"
val () = symbol_set_tyname (s0rt, s0rt_tyname)
val s0rtq = symbol_make_nt "s0rtq"
val () = symbol_set_tyname (s0rtq, s0rtq_tyname)
val s0rtid = symbol_make_nt "s0rtid"
val () = symbol_set_tyname (s0rtid, i0de_tyname)
val atms0rt = symbol_make_nt "atms0rt"
val () = symbol_set_tyname (atms0rt, s0rt_tyname)
val s0rtseq = symbol_make_nt "s0rtseq"
val () = symbol_set_tyname (s0rtseq, s0rtlst_tyname)
val commas0rtseq = symbol_make_nt "commas0rtseq"
val () = symbol_set_tyname (commas0rtseq, s0rtlst_tyname)
val s0rtpol = symbol_make_nt "s0rtpol"
val () = symbol_set_tyname (s0rtpol, s0rtpol_tyname)

(* ****** ****** *)

val d0atsrtcon = symbol_make_nt "d0atsrtcon"
val () = symbol_set_tyname (d0atsrtcon, d0atsrtcon_tyname)
val d0atsrtconseq = symbol_make_nt "d0atsrtconseq"
val () = symbol_set_tyname (d0atsrtconseq, d0atsrtconlst_tyname)
val bard0atsrtconseq = symbol_make_nt "bard0atsrtconseq"
val () = symbol_set_tyname (bard0atsrtconseq, d0atsrtconlst_tyname)
val d0atsrtdec = symbol_make_nt "d0atsrtdec"
val () = symbol_set_tyname (d0atsrtdec, d0atsrtdec_tyname)
val andd0atsrtdecseq = symbol_make_nt "andd0atsrtdecseq"
val () = symbol_set_tyname (andd0atsrtdecseq, d0atsrtdeclst_tyname)

(* ****** ****** *)

val s0taq = symbol_make_nt "s0taq"
val () = symbol_set_tyname (s0taq, s0taq_tyname)
val d0ynq = symbol_make_nt "d0ynq"
val () = symbol_set_tyname (d0ynq, d0ynq_tyname)

(* ****** ****** *)

val si0de = symbol_make_nt "si0de"
val () = symbol_set_tyname (si0de, i0de_tyname)
val sqi0de = symbol_make_nt "sqi0de"
val () = symbol_set_tyname (sqi0de, sqi0de_tyname)
val commasi0deseq = symbol_make_nt "commasi0deseq"
val () = symbol_set_tyname (commasi0deseq, i0delst_tyname)

(* ****** ****** *)

val di0de = symbol_make_nt "di0de"
val () = symbol_set_tyname (di0de, i0de_tyname)
val dqi0de = symbol_make_nt "dqi0de"
val () = symbol_set_tyname (dqi0de, dqi0de_tyname)
val pi0de = symbol_make_nt "pi0de"
val () = symbol_set_tyname (pi0de, i0de_tyname)
val fi0de = symbol_make_nt "fi0de"
val () = symbol_set_tyname (fi0de, i0de_tyname)
val arri0de = symbol_make_nt "arri0de"
val () = symbol_set_tyname (arri0de, i0de_tyname)
val arrqi0de = symbol_make_nt "arrqi0de"
val () = symbol_set_tyname (arrqi0de, arrqi0de_tyname)
val tmpi0de = symbol_make_nt "tmpi0de"
val () = symbol_set_tyname (tmpi0de, i0de_tyname)
val tmpqi0de = symbol_make_nt "tmpqi0de"
val () = symbol_set_tyname (tmpqi0de, tmpqi0de_tyname)

val colons0rtopt = symbol_make_nt "colons0rtopt"
val () = symbol_set_tyname (colons0rtopt, s0rtopt_tyname)

val s0arg = symbol_make_nt "s0arg"
val () = symbol_set_tyname (s0arg, s0arg_tyname)
val s0argseq = symbol_make_nt "s0argseq"
val () = symbol_set_tyname (s0argseq, s0arglst_tyname)
val commas0argseq = symbol_make_nt "commas0argseq"
val () = symbol_set_tyname (commas0argseq, s0arglst_tyname)
val s0argseqseq = symbol_make_nt "s0argseqseq"
val () = symbol_set_tyname (s0argseqseq, s0arglstlst_tyname)

val decs0argseq = symbol_make_nt "decs0argseq"
val () = symbol_set_tyname (decs0argseq, s0arglst_tyname)
val commadecs0argseq = symbol_make_nt "commadecs0argseq"
val () = symbol_set_tyname (commadecs0argseq, s0arglst_tyname)
val decs0argseqseq = symbol_make_nt "decs0argseqseq"
val () = symbol_set_tyname (decs0argseqseq, s0arglstlst_tyname)

val sp0at = symbol_make_nt "sp0at"
val () = symbol_set_tyname (sp0at, sp0at_tyname)

(* ****** ****** *)

(*
** static expressions
*)

val s0exp = symbol_make_nt "s0exp"
val () = symbol_set_tyname (s0exp, s0exp_tyname)
val atms0exp = symbol_make_nt "atms0exp"
val () = symbol_set_tyname (atms0exp, s0exp_tyname)
val apps0exp = symbol_make_nt "apps0exp"
val () = symbol_set_tyname (apps0exp, s0exp_tyname)
val exts0exp = symbol_make_nt "exts0exp"
val () = symbol_set_tyname (exts0exp, s0expext_tyname)

val s0expelt = symbol_make_nt "s0expelt"
val () = symbol_set_tyname (s0expelt, s0expopt_tyname)
val s0arrind = symbol_make_nt "s0arrind"
val () = symbol_set_tyname (s0arrind, s0arrind_tyname)

val s0qua = symbol_make_nt "s0qua"
val () = symbol_set_tyname (s0qua, s0qua_tyname)
val s0quaseq = symbol_make_nt "s0quaseq"
val () = symbol_set_tyname (s0quaseq, s0qualst_tyname)
val barsemis0quaseq = symbol_make_nt "barsemis0quaseq"
val () = symbol_set_tyname (barsemis0quaseq, s0qualst_tyname)
val s0rtext = symbol_make_nt "s0rtext"
val () = symbol_set_tyname (s0rtext, s0rtext_tyname)

val s0expseq = symbol_make_nt "s0expseq"
val () = symbol_set_tyname (s0expseq, s0explst_tyname)
val barsemis0expseq = symbol_make_nt "barsemis0expseq"
val () = symbol_set_tyname (barsemis0expseq, s0explst_tyname)
val commas0expseq = symbol_make_nt "commas0expseq"
val () = symbol_set_tyname (commas0expseq, s0explst_tyname)
val s0expseq1 = symbol_make_nt "s0expseq1"
val () = symbol_set_tyname (s0expseq1, s0explst_tyname)

val labs0expseq = symbol_make_nt "labs0expseq"
val () = symbol_set_tyname (labs0expseq, labs0explst_tyname)
val commalabs0expseq = symbol_make_nt "commalabs0expseq"
val () = symbol_set_tyname (commalabs0expseq, labs0explst_tyname)

(* ****** ****** *)

(*
** template argument expressions
*)
val t0mps0exp = symbol_make_nt "t0mps0exp"
val () = symbol_set_tyname (t0mps0exp, s0exp_tyname)
val t1mps0exp = symbol_make_nt "t1mps0exp"
val () = symbol_set_tyname (t1mps0exp, s0exp_tyname)
val t1mps0expseq = symbol_make_nt "t1mps0expseq"
val () = symbol_set_tyname (t1mps0expseq, s0explst_tyname)
val commat1mps0expseq = symbol_make_nt "commat1mps0expseq"
val () = symbol_set_tyname (commat1mps0expseq, s0explst_tyname)
val gtlt_t1mps0expseqseq = symbol_make_nt "gtlt_t1mps0expseqseq"
val () = symbol_set_tyname (gtlt_t1mps0expseqseq, t1mps0explstlst_tyname)

(* ****** ****** *)

val impqi0de = symbol_make_nt "impqi0de"
val () = symbol_set_tyname (impqi0de, impqi0de_tyname)

(* ****** ****** *)

(*
** static declarations
*)
val s0rtdef = symbol_make_nt "s0rtdef"
val () = symbol_set_tyname (s0rtdef, s0rtdef_tyname)
val ands0rtdefseq = symbol_make_nt "ands0rtdefseq"
val () = symbol_set_tyname (ands0rtdefseq, s0rtdeflst_tyname)

val d0atarg = symbol_make_nt "d0atarg"
val () = symbol_set_tyname (d0atarg, d0atarg_tyname)
val d0atargseq = symbol_make_nt "d0atargseq"
val () = symbol_set_tyname (d0atargseq, d0atarglst_tyname)
val commad0atargseq = symbol_make_nt "commad0atargseq"
val () = symbol_set_tyname (commad0atargseq, d0atarglst_tyname)

val s0tacon = symbol_make_nt "s0tacon"
val () = symbol_set_tyname (s0tacon, s0tacon_tyname)
val ands0taconseq = symbol_make_nt "ands0taconseq"
val () = symbol_set_tyname (ands0taconseq, s0taconlst_tyname)
val s0tacst = symbol_make_nt "s0tacst"
val () = symbol_set_tyname (s0tacst, s0tacst_tyname)
val ands0tacstseq = symbol_make_nt "ands0tacstseq"
val () = symbol_set_tyname (ands0tacstseq, s0tacstlst_tyname)
val s0tavar = symbol_make_nt "s0tavar"
val () = symbol_set_tyname (s0tavar, s0tavar_tyname)
val ands0tavarseq = symbol_make_nt "ands0tavarseq"
val () = symbol_set_tyname (ands0tavarseq, s0tavarlst_tyname)

val s0expdef = symbol_make_nt "s0expdef"
val () = symbol_set_tyname (s0expdef, s0expdef_tyname)
val ands0expdefseq = symbol_make_nt "ands0expdefseq"
val () = symbol_set_tyname (ands0expdefseq, s0expdeflst_tyname)
val s0aspdec = symbol_make_nt "s0aspdec"
val () = symbol_set_tyname (s0aspdec, s0aspdec_tyname)

(* ****** ****** *)

(*
** dataprop/type/view/viewtype declarations
*)
val conq0uaseq = symbol_make_nt "conq0uaseq"
val () = symbol_set_tyname (conq0uaseq, s0qualstlst_tyname)
val coni0ndopt = symbol_make_nt "coni0ndopt"
val () = symbol_set_tyname (coni0ndopt, s0expopt_tyname)
val cona0rgopt = symbol_make_nt "cona0rgopt"
val () = symbol_set_tyname (cona0rgopt, s0expopt_tyname)
val d0atcon = symbol_make_nt "d0atcon"
val () = symbol_set_tyname (d0atcon, d0atcon_tyname)
val d0atconseq = symbol_make_nt "d0atconseq"
val () = symbol_set_tyname (d0atconseq, d0atconlst_tyname)
val bard0atconseq = symbol_make_nt "bard0atconseq"
val () = symbol_set_tyname (bard0atconseq, d0atconlst_tyname)
val d0atdec = symbol_make_nt "d0atdec"
val () = symbol_set_tyname (d0atdec, d0atdec_tyname)
val andd0atdecseq = symbol_make_nt "andd0atdecseq"
val () = symbol_set_tyname (andd0atdecseq, d0atdeclst_tyname)
val s0expdefseqopt = symbol_make_nt "s0expdefseqopt"
val () = symbol_set_tyname (s0expdefseqopt, s0expdeflst_tyname)

(*
** exception constructor declaration
*)
val e0xndec = symbol_make_nt "e0xndec"
val () = symbol_set_tyname (e0xndec, e0xndec_tyname)
val ande0xndecseq = symbol_make_nt "ande0xndecseq"
val () = symbol_set_tyname (ande0xndecseq, e0xndeclst_tyname)

(* ****** ****** *)

(*
** dynamic variable with optional type annotation
*)
val p0arg = symbol_make_nt "p0arg"
val () = symbol_set_tyname (p0arg, p0arg_tyname)
val p0argseq = symbol_make_nt "p0argseq"
val () = symbol_set_tyname (p0argseq, p0arglst_tyname)
val commap0argseq = symbol_make_nt "commap0argseq"
val () = symbol_set_tyname (commap0argseq, p0arglst_tyname)
val d0arg = symbol_make_nt "d0arg"
val () = symbol_set_tyname (d0arg, d0arg_tyname)
val d0argseq = symbol_make_nt "d0argseq"
val () = symbol_set_tyname (d0argseq, d0arglst_tyname)

val extnamopt = symbol_make_nt "extnamopt"
val () = symbol_set_tyname (extnamopt, extnamopt_tyname)
val d0cstdec = symbol_make_nt "d0cstdec"
val () = symbol_set_tyname (d0cstdec, d0cstdec_tyname)
val andd0cstdecseq = symbol_make_nt "andd0cstdecseq"
val () = symbol_set_tyname (andd0cstdecseq, d0cstdeclst_tyname)

val s0vararg = symbol_make_nt "s0vararg"
val () = symbol_set_tyname (s0vararg, s0vararg_tyname)
val s0exparg = symbol_make_nt "s0exparg"
val () = symbol_set_tyname (s0exparg, s0exparg_tyname)
val s0elop = symbol_make_nt "s0elop"
val () = symbol_set_tyname (s0elop, s0elop_tyname)
val witht0ype = symbol_make_nt "witht0ype"
val () = symbol_set_tyname (witht0ype, witht0ype_tyname)

(* ****** ****** *)

(*
** dynamic patterns
*)
val p0at = symbol_make_nt "p0at"
val () = symbol_set_tyname (p0at, p0at_tyname)
val atmp0at = symbol_make_nt "atmp0at"
val () = symbol_set_tyname (atmp0at, p0at_tyname)
val argp0at = symbol_make_nt "argp0at"
val () = symbol_set_tyname (argp0at, p0at_tyname)
val argp0atseq = symbol_make_nt "argp0atseq"
val () = symbol_set_tyname (argp0atseq, p0atlst_tyname)
val p0atseq = symbol_make_nt "p0atseq"
val () = symbol_set_tyname (p0atseq, p0atlst_tyname)
val commap0atseq = symbol_make_nt "commap0atseq"
val () = symbol_set_tyname (commap0atseq, p0atlst_tyname)
val labp0atseq = symbol_make_nt "labp0atseq"
val () = symbol_set_tyname (labp0atseq, labp0atlst_tyname)
val commalabp0atseq = symbol_make_nt "commalabp0atseq"
val () = symbol_set_tyname (commalabp0atseq, labp0atlst_tyname)

val f0arg1 = symbol_make_nt "f0arg1"
val () = symbol_set_tyname (f0arg1, f0arg_tyname)
val f0arg1seq = symbol_make_nt "f0arg1seq"
val () = symbol_set_tyname (f0arg1seq, f0arglst_tyname)
val f0arg2 = symbol_make_nt "f0arg2"
val () = symbol_set_tyname (f0arg2, f0arg_tyname)
val f0arg2seq = symbol_make_nt "f0arg2seq"
val () = symbol_set_tyname (f0arg2seq, f0arglst_tyname)

(* ****** ****** *)

(*
** dynamic expressions
*)
val d0exp = symbol_make_nt "d0exp"
val () = symbol_set_tyname (d0exp, d0exp_tyname)
val atmd0exp = symbol_make_nt "atmd0exp"
val () = symbol_set_tyname (atmd0exp, d0exp_tyname)
val s0expdarg = symbol_make_nt "s0expdarg"
val () = symbol_set_tyname (s0expdarg, d0exp_tyname)
val s0expdargseq = symbol_make_nt "s0expdargseq"
val () = symbol_set_tyname (s0expdargseq, d0explst_tyname)
val argd0exp = symbol_make_nt "argd0exp"
val () = symbol_set_tyname (argd0exp, d0exp_tyname)
val argd0expseq = symbol_make_nt "argd0expseq"
val () = symbol_set_tyname (argd0expseq, d0explst_tyname)
val d0arrind = symbol_make_nt "d0arrind"
val () = symbol_set_tyname (d0arrind, d0arrind_tyname)
val colons0expopt = symbol_make_nt "colons0expopt"
val () = symbol_set_tyname (colons0expopt, s0expopt_tyname)
val funarrow = symbol_make_nt "funarrow"
val () = symbol_set_tyname (funarrow, e0fftaglstopt_tyname)

val caseinv = symbol_make_nt "caseinv"
val () = symbol_set_tyname (caseinv, i0nvresstate_tyname)
val ifhead = symbol_make_nt "ifhead"
val () = symbol_set_tyname (ifhead, ifhead_tyname)
val sifhead = symbol_make_nt "sifhead"
val () = symbol_set_tyname (sifhead, ifhead_tyname)
val casehead = symbol_make_nt "casehead"
val () = symbol_set_tyname (casehead, casehead_tyname)
val scasehead = symbol_make_nt "scasehead"
val () = symbol_set_tyname (scasehead, casehead_tyname)

val forhead = symbol_make_nt "forhead"
val () = symbol_set_tyname (forhead, loophead_tyname)
val whilehead = symbol_make_nt "whilehead"
val () = symbol_set_tyname (whilehead, loophead_tyname)
val tryhead = symbol_make_nt "tryhead"
val () = symbol_set_tyname (tryhead, tryhead_tyname)

val d0expcommaseq = symbol_make_nt "d0expcommaseq"
val () = symbol_set_tyname (d0expcommaseq, d0explst_tyname)
val commad0expseq = symbol_make_nt "commad0expseq"
val () = symbol_set_tyname (commad0expseq, d0explst_tyname)
val d0expsemiseq0 = symbol_make_nt "d0expsemiseq0"
val () = symbol_set_tyname (d0expsemiseq0, d0explst_tyname)
val d0expsemiseq1 = symbol_make_nt "d0expsemiseq1"
val () = symbol_set_tyname (d0expsemiseq1, d0explst_tyname)
val labd0expseq = symbol_make_nt "labd0expseq"
val () = symbol_set_tyname (labd0expseq, labd0explst_tyname)
val commalabd0expseq = symbol_make_nt "commalabd0expseq"
val () = symbol_set_tyname (commalabd0expseq, labd0explst_tyname)

(* ****** ****** *)

(*
** pattern matching
*)
val m0atch = symbol_make_nt "m0atch"
val () = symbol_set_tyname (m0atch, m0atch_tyname)
val m0atchseq = symbol_make_nt "m0atchseq"
val () = symbol_set_tyname (m0atchseq, m0atchlst_tyname)
val andm0atchseq = symbol_make_nt "andm0atchseq"
val () = symbol_set_tyname (andm0atchseq, m0atchlst_tyname)
val guap0at = symbol_make_nt "guap0at"
val () = symbol_set_tyname (guap0at, guap0at_tyname)
val c0lau = symbol_make_nt "c0lau"
val () = symbol_set_tyname (c0lau, c0lau_tyname)
val c0lauseq = symbol_make_nt "c0lauseq"
val () = symbol_set_tyname (c0lauseq, c0laulst_tyname)
val barc0lauseq = symbol_make_nt "barc0lauseq"
val () = symbol_set_tyname (barc0lauseq, c0laulst_tyname)
val sc0lau = symbol_make_nt "sc0lau"
val () = symbol_set_tyname (sc0lau, sc0lau_tyname)
val sc0lauseq = symbol_make_nt "sc0lauseq"
val () = symbol_set_tyname (sc0lauseq, sc0laulst_tyname)
val barsc0lauseq = symbol_make_nt "barsc0lauseq"
val () = symbol_set_tyname (barsc0lauseq, sc0laulst_tyname)

(* ****** ****** *)

(*
** invariants
*)
val i0nvqua = symbol_make_nt "i0nvqua"
val () = symbol_set_tyname (i0nvqua, s0qualstopt_tyname)
val i0nvmet = symbol_make_nt "i0nvmet"
val () = symbol_set_tyname (i0nvmet, s0qualstopt_tyname)
val i0nvarg = symbol_make_nt "i0nvarg"
val () = symbol_set_tyname (i0nvarg, i0nvarg_tyname)
val i0nvargseq = symbol_make_nt "i0nvargseq"
val () = symbol_set_tyname (i0nvargseq, i0nvarglst_tyname)
val commai0nvargseq = symbol_make_nt "commai0nvargseq"
val () = symbol_set_tyname (commai0nvargseq, i0nvarglst_tyname)
val i0nvargstate = symbol_make_nt "i0nvargstate"
val () = symbol_set_tyname (i0nvargstate, i0nvarglst_tyname)
val i0nvresqua = symbol_make_nt "i0nvresqua"
val () = symbol_set_tyname (i0nvresqua, s0qualstopt_tyname)
val i0nvresstate = symbol_make_nt "i0nvresstate"
val () = symbol_set_tyname (i0nvresstate, i0nvresstate_tyname)
val loopi0nv = symbol_make_nt "loopi0nv"
val () = symbol_set_tyname (loopi0nv, loopi0nv_tyname)
val initestpost = symbol_make_nt "initestpost"
val () = symbol_set_tyname (initestpost, initestpost_tyname)

(* ****** ****** *)

(*
** macro definitions
*)
val m0arg = symbol_make_nt "m0arg"
val () = symbol_set_tyname (m0arg, i0de_tyname)
val m0argseq = symbol_make_nt "m0argseq"
val () = symbol_set_tyname (m0argseq, i0delst_tyname)
val commam0argseq = symbol_make_nt "commam0argseq"
val () = symbol_set_tyname (commam0argseq, i0delst_tyname)
val m0acarg = symbol_make_nt "m0acarg"
val () = symbol_set_tyname (m0acarg, m0acarg_tyname)
val m0acargseq = symbol_make_nt "m0acargseq"
val () = symbol_set_tyname (m0acargseq, m0acarglst_tyname)
val m0acdef = symbol_make_nt "m0acdef"
val () = symbol_set_tyname (m0acdef, m0acdef_tyname)
val andm0acdefseq = symbol_make_nt "andm0acdefseq"
val () = symbol_set_tyname (andm0acdefseq, m0acdeflst_tyname)

(* ****** ****** *)

(*
** individual declarations
*)
val v0aldec = symbol_make_nt "v0aldec"
val () = symbol_set_tyname (v0aldec, v0aldec_tyname)
val andv0aldecseq = symbol_make_nt "andv0aldecseq"
val () = symbol_set_tyname (andv0aldecseq, v0aldeclst_tyname)
val f0undec = symbol_make_nt "f0undec"
val () = symbol_set_tyname (f0undec, f0undec_tyname)
val andf0undecseq = symbol_make_nt "andf0undecseq"
val () = symbol_set_tyname (andf0undecseq, f0undeclst_tyname)
val v0arwth = symbol_make_nt "v0arwth"
val () = symbol_set_tyname (v0arwth, v0arwth_tyname)
val v0ardec = symbol_make_nt "v0ardec"
val () = symbol_set_tyname (v0ardec, v0ardec_tyname)
val andv0ardecseq = symbol_make_nt "andv0ardecseq"
val () = symbol_set_tyname (andv0ardecseq, v0ardeclst_tyname)
val i0mpdec = symbol_make_nt "i0mpdec"
val () = symbol_set_tyname (i0mpdec, i0mpdec_tyname)

(* ****** ****** *)

(*
** generic declarations
*)
val d0ec = symbol_make_nt "d0ec"
val () = symbol_set_tyname (d0ec, d0ec_tyname)
//
val d0ecarg = symbol_make_nt "d0ecarg"
val () = symbol_set_tyname (d0ecarg, s0qualst_tyname)
val d0ecargseq = symbol_make_nt "d0ecargseq"
val () = symbol_set_tyname (d0ecargseq, s0qualstlst_tyname)
//
val semicolonseq = symbol_make_nt "semicolonseq"
//
val d0ec_sta = symbol_make_nt "d0ec_sta" // static declaration
val () = symbol_set_tyname (d0ec_sta, d0ec_tyname)
val guad0ec_sta = symbol_make_nt "guad0ec_sta"
val () = symbol_set_tyname (guad0ec_sta, d0eclst_tyname)
val d0ecseq_sta = symbol_make_nt "d0ecseq_sta"
val () = symbol_set_tyname (d0ecseq_sta, d0eclst_tyname)
val d0ecseq_sta_rev = symbol_make_nt "d0ecseq_sta_rev"
val () = symbol_set_tyname (d0ecseq_sta_rev, d0eclst_tyname)
//
val d0ec_dyn = symbol_make_nt "d0ec_dyn" // dynamic declaration
val () = symbol_set_tyname (d0ec_dyn, d0ec_tyname)
val guad0ec_dyn = symbol_make_nt "guad0ec_dyn"
val () = symbol_set_tyname (guad0ec_dyn, d0eclst_tyname)
val d0ecseq_dyn = symbol_make_nt "d0ecseq_dyn"
val () = symbol_set_tyname (d0ecseq_dyn, d0eclst_tyname)
val d0ecseq_dyn_rev = symbol_make_nt "d0ecseq_dyn_rev"
val () = symbol_set_tyname (d0ecseq_dyn_rev, d0eclst_tyname)

(* ****** ****** *)

(*
theStartEntry
  : YYBEG_d0ecseq_sta d0ecseq_sta TOKEN_eof
                                        { theYYVALyyres = atsopt_yyres_d0eclst($2) ; return 0 ; }
  | YYBEG_d0ecseq_dyn d0ecseq_dyn TOKEN_eof
                                        { theYYVALyyres = atsopt_yyres_d0eclst($2) ; return 0 ; }
  | YYBEG_i0de i0de TOKEN_eof           { theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }
  | YYBEG_s0rtid s0rtid TOKEN_eof       { theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }
  | YYBEG_si0de si0de TOKEN_eof         { theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }
  | YYBEG_di0de di0de TOKEN_eof         { theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }
  | YYBEG_s0exp s0exp TOKEN_eof         { theYYVALyyres = atsopt_yyres_s0exp($2) ; return 0 ; }
  | YYBEG_d0exp d0exp TOKEN_eof         { theYYVALyyres = atsopt_yyres_d0exp($2) ; return 0 ; }
; /* end of [theStartEntry] */
*)
fun theStartEntry_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (theStartEntry)
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_d0ecseq_sta d0ecseq_sta TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_d0eclst($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_d0ecseq_dyn d0ecseq_dyn TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_d0eclst($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_i0de i0de TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_s0rtid s0rtid TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_si0de si0de TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_di0de di0de TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_i0de($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_s0exp s0exp TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_s0exp($2) ; return 0 ; }")
//
val gr = grmrule_append
  ($lst_t {symbol} (tupz! YYBEG_d0exp d0exp TOKEN_eof))
val () = grmrule_set_action (gr, "{ theYYVALyyres = atsopt_yyres_d0exp($2) ; return 0 ; }")
//
val () = symbol_close (pf | theStartEntry)
} // end of [theStartEntry_proc]

(* ****** ****** *)

(*
abskind
  : ABSPROP                             { $$ = abskind_prop () ; }
  | ABSTYPE                             { $$ = abskind_type () ; }
  | ABST0YPE                            { $$ = abskind_t0ype () ; }
  | ABSVIEW                             { $$ = abskind_view () ; }
  | ABSVIEWTYPE                         { $$ = abskind_viewtype () ; }
  | ABSVIEWT0YPE                        { $$ = abskind_viewt0ype () ; }
  ;
*)
fun abskind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (abskind)
//
val gr = grmrule_append (ABSPROP)
val () = grmrule_set_action (gr, "{ $$ = abskind_prop () ; }")
val gr = grmrule_append (ABSTYPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_type () ; }")
val gr = grmrule_append (ABST0YPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_t0ype () ; }")
val gr = grmrule_append (ABSVIEW)
val () = grmrule_set_action (gr, "{ $$ = abskind_view () ; }")
val gr = grmrule_append (ABSVIEWTYPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_viewtype () ; }")
val gr = grmrule_append (ABSVIEWT0YPE)
val () = grmrule_set_action (gr, "{ $$ = abskind_viewt0ype () ; }")
//
val () = symbol_close (pf | abskind)
} // end of [abskind_proc]

(* ****** ****** *)

(*
dcstkind
  : FUN                                 { $$ = dcstkind_fun () ; }
  | VAL                                 { $$ = dcstkind_val () ; }
  | CASTFN                              { $$ = dcstkind_castfn () ; }
  | PRAXI                               { $$ = dcstkind_praxi () ; }
  | PRFUN                               { $$ = dcstkind_prfun () ; }
  | PRVAL                               { $$ = dcstkind_prval () ; }
;
*)
fun dcstkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (dcstkind)
//
val gr = grmrule_append (FUN)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_fun () ; }")
val gr = grmrule_append (VAL)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_val () ; }")
val gr = grmrule_append (CASTFN)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_castfn () ; }")
val gr = grmrule_append (PRAXI)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_praxi () ; }")
val gr = grmrule_append (PRFUN)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_prfun () ; }")
val gr = grmrule_append (PRVAL)
val () = grmrule_set_action (gr, "{ $$ = dcstkind_prval () ; }")
//
val () = symbol_close (pf | dcstkind)
} // end of [dcstkind_proc]

(* ****** ****** *)

(*
datakind
  : DATAPROP                            { $$ = datakind_prop () ; }
  | DATATYPE                            { $$ = datakind_type () ; }
  | DATAVIEW                            { $$ = datakind_view () ; }
  | DATAVIEWTYPE                        { $$ = datakind_viewtype () ; }
;
*)
fun datakind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (datakind)
//
val gr = grmrule_append (DATAPROP)
val () = grmrule_set_action (gr, "{ $$ = datakind_prop () ; }")
val gr = grmrule_append (DATATYPE)
val () = grmrule_set_action (gr, "{ $$ = datakind_type () ; }")
val gr = grmrule_append (DATAVIEW)
val () = grmrule_set_action (gr, "{ $$ = datakind_view () ; }")
val gr = grmrule_append (DATAVIEWTYPE)
val () = grmrule_set_action (gr, "{ $$ = datakind_viewtype () ; }")
//
val () = symbol_close (pf | datakind)
} // end of [datakind_proc]

(* ****** ****** *)

(*
stadefkind
  : STADEF                              { $$ = stadefkind_generic () ; }
  | PROPDEF                             { $$ = stadefkind_prop ($1) ; }
  | TYPEDEF                             { $$ = stadefkind_type ($1) ; }
  | VIEWDEF                             { $$ = stadefkind_view ($1) ; }
  | VIEWTYPEDEF                         { $$ = stadefkind_viewtype ($1) ; }
;
*)
fun stadefkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (stadefkind)
//
val gr = grmrule_append (STADEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_generic () ; }")
val gr = grmrule_append (PROPDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_prop ($1) ; }")
val gr = grmrule_append (TYPEDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_type ($1) ; }")
val gr = grmrule_append (VIEWDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_view ($1) ; }")
val gr = grmrule_append (VIEWTYPEDEF)
val () = grmrule_set_action (gr, "{ $$ = stadefkind_viewtype ($1) ; }")
//
val () = symbol_close (pf | stadefkind)
} // end of [stadefkind_proc]

(* ****** ****** *)

(*
valkind
  : VAL                                 { $$ = valkind_val () ; }
  | VALMINUS                            { $$ = valkind_valminus () ; }
  | VALPLUS                             { $$ = valkind_valplus () ; }
  | PRVAL                               { $$ = valkind_prval () ; }
;
*)
fun valkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (valkind)
//
val gr = grmrule_append (VAL)
val () = grmrule_set_action (gr, "{ $$ = valkind_val () ; }")
val gr = grmrule_append (VALMINUS)
val () = grmrule_set_action (gr, "{ $$ = valkind_valminus () ; }")
val gr = grmrule_append (VALPLUS)
val () = grmrule_set_action (gr, "{ $$ = valkind_valplus () ; }")
val gr = grmrule_append (PRVAL)
val () = grmrule_set_action (gr, "{ $$ = valkind_prval () ; }")
//
val () = symbol_close (pf | valkind)
} // end of [valkind_proc]

(* ****** ****** *)

(*
funkind
  : FN                                  { $$ = funkind_fn () ; }
  | FNSTAR                              { $$ = funkind_fnstar () ; }
  | FUN                                 { $$ = funkind_fun () ; }
  | CASTFN                              { $$ = funkind_castfn () ; }
  | PRFN                                { $$ = funkind_prfn () ; }
  | PRFUN                               { $$ = funkind_prfun () ; }
;
*)
fun funkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (funkind)
//
val gr = grmrule_append (FN)
val () = grmrule_set_action (gr, "{ $$ = funkind_fn () ; }")
val gr = grmrule_append (FNSTAR)
val () = grmrule_set_action (gr, "{ $$ = funkind_fnstar () ; }")
val gr = grmrule_append (FUN)
val () = grmrule_set_action (gr, "{ $$ = funkind_fun () ; }")
val gr = grmrule_append (CASTFN)
val () = grmrule_set_action (gr, "{ $$ = funkind_castfn () ; }")
val gr = grmrule_append (PRFN)
val () = grmrule_set_action (gr, "{ $$ = funkind_prfn () ; }")
val gr = grmrule_append (PRFUN)
val () = grmrule_set_action (gr, "{ $$ = funkind_prfun () ; }")
//
val () = symbol_close (pf | funkind)
//
} // end of [funkind_proc]

(* ****** ****** *)

(*
lamkind
  : LAM                                 { $$ = lamkind_lam ($1) ; }
  | ATLAM                               { $$ = lamkind_atlam ($1) ; }
  | LLAM                                { $$ = lamkind_llam ($1) ; }
  | ATLLAM                              { $$ = lamkind_atllam ($1) ; }
;
*)
fun lamkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (lamkind)
//
val gr = grmrule_append (LAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_lam ($1) ; }")
val gr = grmrule_append (ATLAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_atlam ($1) ; }")
val gr = grmrule_append (LLAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_llam ($1) ; }")
val gr = grmrule_append (ATLLAM)
val () = grmrule_set_action (gr, "{ $$ = lamkind_atllam ($1) ; }")
//
val () = symbol_close (pf | lamkind)
//
} // end of [lamkind_proc]

(* ****** ****** *)

(*
fixkind
  : FIX                                 { $$ = fixkind_fix ($1) ; }
  | ATFIX                               { $$ = fixkind_atfix ($1) ; }
;
*)
fun fixkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (fixkind)
//
val gr = grmrule_append (FIX)
val () = grmrule_set_action (gr, "{ $$ = fixkind_fix ($1) ; }")
val gr = grmrule_append (ATFIX)
val () = grmrule_set_action (gr, "{ $$ = fixkind_atfix ($1) ; }")
//
val () = symbol_close (pf | fixkind)
//
} // end of [fixkind_proc]

(* ****** ****** *)

(*
srpifkind
  : SRPIF                               { $$ = srpifkindtok_if ($1) ; }
  | SRPIFDEF                            { $$ = srpifkindtok_ifdef ($1) ; }
  | SRPIFNDEF                           { $$ = srpifkindtok_ifndef ($1) ; }
;
*)
fun srpifkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (srpifkind)
//
val gr = grmrule_append (SRPIF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_if ($1) ; }")
val gr = grmrule_append (SRPIFDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifdef ($1) ; }")
val gr = grmrule_append (SRPIFNDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifndef ($1) ; }")
//
val () = symbol_close (pf | srpifkind)
//
} // end of [srpifkind]

(*
srpelifkind
  : SRPELIF                             { $$ = srpifkindtok_if ($1) ; }
  | SRPELIFDEF                          { $$ = srpifkindtok_ifdef ($1) ; }
  | SRPELIFNDEF                         { $$ = srpifkindtok_ifndef ($1) ; }
;
*)
fun srpelifkind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (srpelifkind)
//
val gr = grmrule_append (SRPELIF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_if ($1) ; }")
val gr = grmrule_append (SRPELIFDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifdef ($1) ; }")
val gr = grmrule_append (SRPELIFNDEF)
val () = grmrule_set_action (gr, "{ $$ = srpifkindtok_ifndef ($1) ; }")
//
val () = symbol_close (pf | srpelifkind)
//
} // end of [srpelifkind]

(*
srpthenopt
  : /* empty */                         { ; }
  | SRPTHEN                             { ; }
;
*)
fun srpthenopt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (srpthenopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ ; }")
val gr = grmrule_append (SRPTHEN)
val () = grmrule_set_action (gr, "{ ; }")
//
val () = theGrmrulelst_merge_all (srpthenopt, SYMREGoptlit(SRPTHEN))
//
val () = symbol_close (pf | srpthenopt)
//
} // end of [srpthenopt]

(* ****** ****** *)

(*
i0de /* identifier */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
/* keysymb */
  | AMPERSAND                           { $$ = i0de_make_ampersand($1) ; }
  | BACKSLASH                           { $$ = i0de_make_backslash($1) ; }
  | BANG                                { $$ = i0de_make_bang($1) ; }
  | EQ                                  { $$ = i0de_make_eq($1) ; }
  | GT                                  { $$ = i0de_make_gt($1) ; }
  | LT                                  { $$ = i0de_make_lt($1) ; }
  | MINUSGT                             { $$ = i0de_make_minusgt($1) ; }
  | MINUSLTGT                           { $$ = i0de_make_minusltgt($1) ; }
  | TILDE                               { $$ = i0de_make_tilde($1) ; }
; /* end of [i0de] */
*)
fun i0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0de)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (AMPERSAND)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_ampersand($1) ; }")
val gr = grmrule_append (BACKSLASH)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_backslash($1) ; }")
val gr = grmrule_append (BANG)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_bang($1) ; }")
val gr = grmrule_append (EQ)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_eq($1) ; }")
val gr = grmrule_append (GT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_gt($1) ; }")
val gr = grmrule_append (GTLT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_gtlt($1) ; }")
val gr = grmrule_append (LT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_lt($1) ; }")
val gr = grmrule_append (MINUSGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusgt($1) ; }")
val gr = grmrule_append (MINUSLTGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusltgt($1) ; }")
val gr = grmrule_append (TILDE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_tilde($1) ; }")
//
val () = symbol_close (pf | i0de)
//
} // end of [i0de_proc]

(* ****** ****** *)

(*
/* identifier beginning with $ */
  : IDENTIFIER_dlr                      { $$ = $1 ; }
; /* end of [i0de_dlr] */
*)
fun i0de_dlr_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0de_dlr)
//
val gr = grmrule_append (IDENTIFIER_dlr)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | i0de_dlr)
//
} // end of [i0de_dlr_proc]

(* ****** ****** *)

(*
i0deseq /* identifier sequence */
  : /* empty */                         { $$ = i0delst_nil() ; }
  | i0de i0deseq                        { $$ = i0delst_cons($1, $2) ; }
; /* end of [i0deseq] */
*)
fun i0deseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0deseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0delst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de i0deseq))
val () = grmrule_set_action (gr, "{ $$ = i0delst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (i0deseq, SYMREGstarlit(i0de))
//
val () = symbol_close (pf | i0deseq)
//
} // end of [i0deseq_proc]

(* ****** ****** *)

(*
i0dext /* extern identifier for loading syndef */
  : IDENTIFIER_ext                      { $$ = $1 ; }
/* keyword */
  | DO                                  { $$ = i0de_make_DO($1) ; }
  | WHILE                               { $$ = i0de_make_WHILE($1) ; }
; /* end of [i0dext] */
*)
fun i0dext_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (i0dext)
//
val gr = grmrule_append (IDENTIFIER_ext)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (DO)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_DO($1) ; }")
val gr = grmrule_append (WHILE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_WHILE($1) ; }")
//
val () = symbol_close (pf | i0dext)
//
} // end of [i0dext_proc]

(* ****** ****** *)

(*
l0ab /* label */
  : i0de                                { $$ = l0ab_ide($1) ; }
  | LITERAL_int                         { $$ = l0ab_int($1) ; }
  | LPAREN l0ab RPAREN                  { $$ = $2 ; }
; /* end of [l0ab] */
*)
fun l0ab_proc (): void = () where {
//
val (pf | ()) = symbol_open (l0ab)
//
val gr = grmrule_append (i0de)
val () = grmrule_set_action (gr, "{ $$ = l0ab_ide($1) ; }")
val gr = grmrule_append (LITERAL_int)
val () = grmrule_set_action (gr, "{ $$ = l0ab_int($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN l0ab RPAREN))
val () = grmrule_set_action (gr, "{ $$ = $2 ; }")
//
val () = symbol_close (pf | l0ab)
//
} /* end of [l0ab_proc] */

(*
stai0de /* idenitifer for packages */
  : IDENTIFIER_alp                      { $$ = stai0de_make($1) ; }
; /* end of [stai0de] */
*)
fun stai0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (stai0de)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! IDENTIFIER_alp))
val () = grmrule_set_action (gr, "{ $$ = stai0de_make($1) ; }")
//
val () = symbol_close (pf | stai0de)
//
} /* end of [stai0de_proc] */

(* ****** ****** *)

(*
p0rec /* precedence */
  : /* empty */                         { $$ = p0rec_emp() ; }
  | LITERAL_int                         { $$ = p0rec_int($1) ; }
  | LPAREN i0de RPAREN                  { $$ = p0rec_ide($2) ; }
  | LPAREN i0de IDENTIFIER_sym LITERAL_int RPAREN
                                        { $$ = p0rec_opr($2, $3, $4) ; }
; /* end of [p0rec] */
*)
fun p0rec_proc (): void = () where {
//
val (pf | ()) = symbol_open (p0rec)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = p0rec_emp() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_int))
val () = grmrule_set_action (gr, "{ $$ = p0rec_int($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN i0de RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0rec_ide($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN i0de IDENTIFIER_sym LITERAL_int RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0rec_opr($2, $3, $4) ; }")
//
val () = symbol_close (pf | p0rec)
//
} // end of [p0rec_proc]

(* ****** ****** *)

(*
e0xp /* generic expression */
  : e0xp atme0xp                        { $$ = e0xp_app($1, $2) ; }
  | atme0xp                             { $$ = $1 ; }
; /* end of [e0xp] */
*)
fun e0xp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0xp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! e0xp atme0xp))
val () = grmrule_set_action (gr, "{ $$ = e0xp_app($1, $2) ; }")
val gr = grmrule_append (atme0xp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = theGrmrulelst_merge_all (e0xp, SYMREGpluslit(atme0xp))
//
val () = symbol_close (pf | e0xp)
//
} // end of [e0xp_proc]

(* ****** ****** *)

(*
atme0xp /* atomic generic expression */
  : LITERAL_char                        { $$ = e0xp_char($1) ; }
  | LITERAL_float                       { $$ = e0xp_float($1) ; }
  | LITERAL_int                         { $$ = e0xp_int($1) ; }
  | LITERAL_string                      { $$ = e0xp_string($1) ; }
  | SRPFILENAME                         { $$ = e0xp_FILENAME($1) ; }
  | SRPLOCATION                         { $$ = e0xp_LOCATION($1) ; }
  | i0de                                { $$ = e0xp_ide($1) ; }
  | LPAREN e0xpseq RPAREN               { $$ = e0xp_list($1, $2, $3) ; }
  | PERCENTLPAREN e0xp RPAREN           { $$ = e0xp_eval($1, $2, $3) ; }
; /* end of [atme0xp] */
*)
fun atme0xp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (atme0xp)
//
val gr = grmrule_append (LITERAL_char)
val () = grmrule_set_action (gr, "{ $$ = e0xp_char($1) ; }")
val gr = grmrule_append (LITERAL_float)
val () = grmrule_set_action (gr, "{ $$ = e0xp_float($1) ; }")
val gr = grmrule_append (LITERAL_int)
val () = grmrule_set_action (gr, "{ $$ = e0xp_int($1) ; }")
val gr = grmrule_append (LITERAL_string)
val () = grmrule_set_action (gr, "{ $$ = e0xp_string($1) ; }")
val gr = grmrule_append (SRPFILENAME)
val () = grmrule_set_action (gr, "{ $$ = e0xp_FILENAME($1) ; }")
val gr = grmrule_append (SRPLOCATION)
val () = grmrule_set_action (gr, "{ $$ = e0xp_LOCATION($1) ; }")
val gr = grmrule_append (i0de)
val () = grmrule_set_action (gr, "{ $$ = e0xp_ide($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN e0xpseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = e0xp_list($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! PERCENTLPAREN e0xp RPAREN))
val () = grmrule_set_action (gr, "{ $$ = e0xp_eval($1, $2, $3) ; }")
//
val () = symbol_close (pf | atme0xp)
//
} // end of [atme0xp]

(* ****** ****** *)

(*
e0xpseq /* generic expression sequence */
  : /* empty */                         { $$ = e0xplst_nil() ; }
  | e0xp commae0xpseq                   { $$ = e0xplst_cons($1, $2) ; }
; /* end of [e0xpseq] */
*)
fun e0xpseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0xpseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = e0xplst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! e0xp commae0xpseq))
val () = grmrule_set_action (gr, "{ $$ = e0xplst_cons($1, $2) ; }")
//
val () = symbol_close (pf | e0xpseq)
//
} // end of [e0xpseq_proc]

(* ****** ****** *)

(*
commae0xpseq
  : /* empty */                         { $$ = e0xplst_nil() ; }
  | COMMA e0xp commae0xpseq             { $$ = e0xplst_cons($2, $3) ; }
; /* end of [commae0xpseq] */
*)
fun commae0xpseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commae0xpseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = e0xplst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA e0xp commae0xpseq))
val () = grmrule_set_action (gr, "{ $$ = e0xplst_cons($2, $3) ; }")
//
val commae0xp = SYMREGseqlit (COMMA, e0xp)
val () = theGrmrulelst_merge_all (commae0xpseq, SYMREGstar(commae0xp))
//
val () = symbol_close (pf | commae0xpseq)
//
} // end of [comme0xpseq_proc]

(* ****** ****** *)

(*
e0xpopt
  : /* empty */                         { $$ = e0xpopt_none() ; }
  | e0xp                                { $$ = e0xpopt_some($1) ; }
; /* end of [e0xpopt] */
*)  
fun e0xpopt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0xpopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = e0xpopt_none() ; }")
val gr = grmrule_append (e0xp)
val () = grmrule_set_action (gr, "{ $$ = e0xpopt_some($1) ; }")
//
val () = theGrmrulelst_merge_all (e0xpopt, SYMREGoptlit(e0xp))
//
val () = symbol_close (pf | e0xpopt)
//
} // end of [e0xpopt_proc]

(* ****** ****** *)

(*
e0ffid /* alphanum identifier for effects */
  : IDENTIFIER_alp                      { $$ = $1 ; }
; /* end of [e0ffid] */
*)
fun e0ffid_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0ffid)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | e0ffid)
//
} // end of [e0ffid_proc]

(* ****** ****** *)

(*
e0fftag /* effect tag */
  : BANG e0ffid                         { $$ = e0fftag_cst (0, $2) ; }
  | TILDE e0ffid                        { $$ = e0fftag_cst (1, $2) ; }
  | e0ffid                              { $$ = e0fftag_var($1) ; }
  | FUN                                 { $$ = e0fftag_var_fun($1) ; }
  | LITERAL_int                         { $$ = e0fftag_int($1) ; }
; /* end of [e0fftag] */
*)
fun e0fftag_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0fftag)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! BANG e0ffid))
val () = grmrule_set_action (gr, "{ $$ = e0fftag_cst (0, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! TILDE e0ffid))
val () = grmrule_set_action (gr, "{ $$ = e0fftag_cst (1, $2) ; }")
val gr = grmrule_append (e0ffid)
val () = grmrule_set_action (gr, "{ $$ = e0fftag_var($1) ; }")
val gr = grmrule_append (FUN)
val () = grmrule_set_action (gr, "{ $$ = e0fftag_var_fun($1) ; }")
val gr = grmrule_append (LITERAL_int)
val () = grmrule_set_action (gr, "{ $$ = e0fftag_int($1) ; }")
//
val () = symbol_close (pf | e0fftag)
//
} // end of [e0fftag_proc]

(* ****** ****** *)

(*
e0fftagseq /* effect tag sequence */
  : /* empty */                         { $$ = e0fftaglst_nil() ; }
  | e0fftag commae0fftagseq             { $$ = e0fftaglst_cons($1, $2) ; }
; /* end of [e0fftagseq] */
*)
fun e0fftagseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0fftagseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = e0fftaglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! e0fftag commae0fftagseq))
val () = grmrule_set_action (gr, "{ $$ = e0fftaglst_cons($1, $2) ; }")
//
val () = symbol_close (pf | e0fftagseq)
//
} // end of [e0fftagseq_proc]

(* ****** ****** *)

(*
commae0fftagseq
  : /* empty */                         { $$ = e0fftaglst_nil() ; }
  | COMMA e0fftag commae0fftagseq       { $$ = e0fftaglst_cons($2, $3) ; }
; /* end of [commae0fftagseq] */
*)
fun commae0fftagseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commae0fftagseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = e0fftaglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA e0fftag commae0fftagseq))
val () = grmrule_set_action (gr, "{ $$ = e0fftaglst_cons($2, $3) ; }")
//
val commae0fftag = SYMREGseqlit (COMMA, e0fftag)
val () = theGrmrulelst_merge_all (commae0fftagseq, SYMREGstar(commae0fftag))
//
val () = symbol_close (pf | commae0fftagseq)
//
} // end of [commae0fftagseq_proc]

(* ****** ****** *)

(*
colonwith /* effection annotation */
  : COLON                               { $$ = e0fftaglstopt_none() ; }
  | COLONLTGT                           { $$ = e0fftaglstopt_some(e0fftaglst_nil()) ; }
  | COLONLT e0fftagseq GT               { $$ = e0fftaglstopt_some($2) ; }
; /* end of [colonwith] */
*)
fun colonwith_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (colonwith)
//
val gr = grmrule_append (COLON)
val () = grmrule_set_action (gr, "{ $$ = e0fftaglstopt_none() ; }")
val gr = grmrule_append (COLONLTGT)
val () = grmrule_set_action (gr, "{ $$ = e0fftaglstopt_some(e0fftaglst_nil()) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COLONLT e0fftagseq GT))
val () = grmrule_set_action (gr, "{ $$ = e0fftaglstopt_some($2) ; }")
//
val () = symbol_close (pf | colonwith)
//
} // end of [colonwith_proc]

(* ****** ****** *)

(*
s0rt /* sort */
  : s0rt atms0rt                        { $$ = s0rt_app($1, $2) ; }
  | atms0rt                             { $$ = $1 ; }
; /* end of [s0rt] */
*)
fun s0rt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rt)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! s0rt atms0rt))
val () = grmrule_set_action (gr, "{ $$ = s0rt_app($1, $2) ; }")
val gr = grmrule_append (atms0rt)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = theGrmrulelst_merge_all (s0rt, SYMREGpluslit(atms0rt))
//
val () = symbol_close (pf | s0rt)
//
} // end of [s0rt_proc]

(* ****** ****** *)

(*
s0rtq /* sort qualifier */
  : i0de_dlr DOT                        { $$ = s0rtq_sym($1) ; }
  | DOLLAR LITERAL_string DOT           { $$ = s0rtq_str($2) ; }
; /* end of [s0rtq] */
*)
fun s0rtq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de_dlr DOT))
val () = grmrule_set_action (gr, "{ $$ = s0rtq_sym($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOLLAR LITERAL_string DOT))
val () = grmrule_set_action (gr, "{ $$ = s0rtq_str($2) ; }")
//
val () = symbol_close (pf | s0rtq)
//
} // end of [s0rtq_proc]

(* ****** ****** *)

(*
s0rtid /* sort identifier */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
  | T0YPE                               { $$ = i0de_make_t0ype($1) ; }
  | VIEWT0YPE                           { $$ = i0de_make_viewt0ype($1) ; }
  | BACKSLASH                           { $$ = i0de_make_backslash($1) ; }
  | MINUSGT                             { $$ = i0de_make_minusgt($1) ; }
  | MINUSLTGT                           { $$ = i0de_make_minusltgt($1) ; }
; /* end of [s0rtid] */
*)
fun s0rtid_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtid)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val gr = grmrule_append (T0YPE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_t0ype($1) ; }")
//
val gr = grmrule_append (VIEWT0YPE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_viewt0ype($1) ; }")
//
val gr = grmrule_append (BACKSLASH)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_backslash($1) ; }")
//
val gr = grmrule_append (MINUSGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusgt($1) ; }")
//
val gr = grmrule_append (MINUSLTGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusltgt($1) ; }")
//
val () = symbol_close (pf | s0rtid)
//
} // end of [s0rtid_proc]

(* ****** ****** *)

(*
atms0rt /* atomic sort */
  : s0rtid                              { $$ = s0rt_ide($1) ; }
  | s0rtq s0rtid                        { $$ = s0rt_qid($1, $2) ; }
  | LPAREN s0rtseq RPAREN               { $$ = s0rt_list($1, $2, $3) ; }
  | ATLPAREN s0rtseq RPAREN             { $$ = s0rt_tup($1, $2, $3) ; }
; /* end of [atms0rt] */
*)
fun atms0rt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (atms0rt)
//
val gr = grmrule_append (s0rtid)
val () = grmrule_set_action (gr, "{ $$ = s0rt_ide($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0rtq s0rtid))
val () = grmrule_set_action (gr, "{ $$ = s0rt_qid($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN s0rtseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0rt_list($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN s0rtseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0rt_tup($1, $2, $3) ; }")
//
val () = symbol_close (pf | atms0rt)
//
} // end of [atms0rt_proc]

(* ****** ****** *)

(*
s0rtseq /* sort sequence */
  : /* empty */                         { $$ = s0rtlst_nil() ; }
  | s0rt commas0rtseq                   { $$ = s0rtlst_cons($1, $2) ; }
; /* end of [s0rtseq] */
*)
fun s0rtseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0rtlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0rt commas0rtseq))
val () = grmrule_set_action (gr, "{ $$ = s0rtlst_cons($1, $2) ; }")
//
val () = symbol_close (pf | s0rtseq)
//
} // end of [s0rtseq_proc]

(* ****** ****** *)

(*
commas0rtseq
  : /* empty */                         { $$ = s0rtlst_nil() ; }
  | COMMA s0rt commas0rtseq             { $$ = s0rtlst_cons($2, $3) ; }
; /* end of [commas0rtseq] */
*)
fun commas0rtseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commas0rtseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0rtlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA s0rt commas0rtseq))
val () = grmrule_set_action (gr, "{ $$ = s0rtlst_cons($2, $3) ; }")
//
val commas0rt = SYMREGseqlit (COMMA, s0rt)
val () = theGrmrulelst_merge_all (commas0rtseq, SYMREGstar(commas0rt))
//
val () = symbol_close (pf | commas0rtseq)
//
} // end of [commas0rtseq_proc]

(* ****** ****** *)

(*
s0rtpol /* sort with polarity */
  : s0rt                                { $$ = s0rtpol_make($1, 0) ; }
  | PROPMINUS                           { $$ = s0rtpol_make(s0rt_prop($1), -1) ; }
  | PROPPLUS                            { $$ = s0rtpol_make(s0rt_prop($1),  1) ; }
  | TYPEMINUS                           { $$ = s0rtpol_make(s0rt_type($1), -1) ; }
  | TYPEPLUS                            { $$ = s0rtpol_make(s0rt_type($1),  1) ; }
  | T0YPEMINUS                          { $$ = s0rtpol_make(s0rt_t0ype($1), -1) ; }
  | T0YPEPLUS                           { $$ = s0rtpol_make(s0rt_t0ype($1),  1) ; }
  | VIEWMINUS                           { $$ = s0rtpol_make(s0rt_view($1), -1) ; }
  | VIEWPLUS                            { $$ = s0rtpol_make(s0rt_view($1),  1) ; }
  | VIEWTYPEMINUS                       { $$ = s0rtpol_make(s0rt_viewtype($1), -1) ; }
  | VIEWTYPEPLUS                        { $$ = s0rtpol_make(s0rt_viewtype($1),  1) ; }
  | VIEWT0YPEMINUS                      { $$ = s0rtpol_make(s0rt_viewt0ype($1), -1) ; }
  | VIEWT0YPEPLUS                       { $$ = s0rtpol_make(s0rt_viewt0ype($1),  1) ; }
; /* end of [s0rtpol] */
*)
fun s0rtpol_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtpol)
//
val gr = grmrule_append (s0rt)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make($1, 0) ; }")
//
val gr = grmrule_append (PROPMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_prop($1), -1) ; }")
val gr = grmrule_append (PROPPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_prop($1),  1) ; }")
//
val gr = grmrule_append (TYPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_type($1), -1) ; }")
val gr = grmrule_append (TYPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_type($1),  1) ; }")
//
val gr = grmrule_append (T0YPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_t0ype($1), -1) ; }")
val gr = grmrule_append (T0YPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_t0ype($1),  1) ; }")
//
val gr = grmrule_append (VIEWMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_view($1), -1) ; }")
val gr = grmrule_append (VIEWPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_view($1),  1) ; }")
//
val gr = grmrule_append (VIEWTYPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewtype($1), -1) ; }")
val gr = grmrule_append (VIEWTYPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewtype($1),  1) ; }")
//
val gr = grmrule_append (VIEWT0YPEMINUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewt0ype($1), -1) ; }")
val gr = grmrule_append (VIEWT0YPEPLUS)
val () = grmrule_set_action (gr, "{ $$ = s0rtpol_make(s0rt_viewt0ype($1),  1) ; }")
//
val () = symbol_close (pf | s0rtpol)
//
} // end of [s0rtpol_proc]

(* ****** ****** *)

(*
d0atsrtcon /* datasort constructor */
  : i0de                                { $$ = d0atsrtcon_make_none($1) ; }
  | i0de OF s0rt                        { $$ = d0atsrtcon_make_some($1, $3) ; }
; /* end of [d0atsrtcon] */
*)
fun d0atsrtcon_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0atsrtcon)
//
val gr = grmrule_append (i0de)
val () = grmrule_set_action (gr, "{ $$ = d0atsrtcon_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de OF s0rt))
val () = grmrule_set_action (gr, "{ $$ = d0atsrtcon_make_some($1, $3) ; }")
//
val () = symbol_close (pf | d0atsrtcon)
//
} // end of [d0atsrtcon_proc]

(* ****** ****** *)

(*
d0atsrtconseq /* datasort constructor sequence */
  : bard0atsrtconseq                    { $$ = $1 ; }
  | d0atsrtcon bard0atsrtconseq         { $$ = d0atsrtconlst_cons($1, $2) ; }
; /* end of [d0atsrtconseq] */
*)
fun d0atsrtconseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0atsrtconseq)
//
val gr = grmrule_append (bard0atsrtconseq)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0atsrtcon bard0atsrtconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atsrtconlst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0atsrtconseq)
//
} // end of [d0atsrtconseq_proc]

(*
bard0atsrtconseq
  : /* empty */                         { $$ = d0atsrtconlst_nil() ; }
  | BAR d0atsrtcon bard0atsrtconseq     { $$ = d0atsrtconlst_cons($2, $3) ; }
; /* end of [bard0atsrtconseq] */
*)
fun bard0atsrtconseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (bard0atsrtconseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0atsrtconlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BAR d0atsrtcon bard0atsrtconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atsrtconlst_cons($2, $3) ; }")
//
val bard0atsrtcon = SYMREGseqlit (BAR, d0atsrtcon)
val () = theGrmrulelst_merge_all (bard0atsrtconseq, SYMREGstar(bard0atsrtcon))
//
val () = symbol_close (pf | bard0atsrtconseq)
//
} // end of [bard0atsrtconseq_proc]

(*
d0atsrtdec /* datasort declaration */
  : i0de EQ d0atsrtconseq               { $$ = d0atsrtdec_make($1, $3) ; }
; /* end of [d0atsrtdec] */
*)
fun d0atsrtdec_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0atsrtdec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de EQ d0atsrtconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atsrtdec_make($1, $3) ; }")
//
val () = symbol_close (pf | d0atsrtdec)
//
} // end of [d0atsrtdec_proc]

(*
andd0atsrtdecseq /* additional datasort declaration sequence */
  : /* empty */                         { $$ = d0atsrtdeclst_nil() ; }
  | AND d0atsrtdec andd0atsrtdecseq     { $$ = d0atsrtdeclst_cons($2, $3) ; }
; /* end of [andd0atsrtdecseq] */
*)
fun andd0atsrtdecseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (andd0atsrtdecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0atsrtdeclst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND d0atsrtdec andd0atsrtdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0atsrtdeclst_cons($2, $3) ; }")
//
val andd0atsrtdec = SYMREGseqlit (AND, d0atsrtdec)
val () = theGrmrulelst_merge_all (andd0atsrtdecseq, SYMREGstar(andd0atsrtdec))
//
val () = symbol_close (pf | andd0atsrtdecseq)
//
} // end of [d0atsrtdec_proc]

(* ****** ****** *)

(*
s0taq /* static qualifier */
  : i0de_dlr DOT                        { $$ = s0taq_symdot($1) ; }
  | i0de_dlr COLON                      { $$ = s0taq_symcolon($1) ; }
  | DOLLAR LITERAL_string DOT           { $$ = s0taq_fildot($2) ; }
; /* end of [s0taq] */
*)
fun s0taq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0taq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de_dlr DOT))
val () = grmrule_set_action (gr, "{ $$ = s0taq_symdot($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de_dlr COLON))
val () = grmrule_set_action (gr, "{ $$ = s0taq_symcolon($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOLLAR LITERAL_string DOT))
val () = grmrule_set_action (gr, "{ $$ = s0taq_fildot($2) ; }")
//
val () = symbol_close (pf | s0taq)
//
} // end of [s0taq_proc]

(* ****** ****** *)

(*
d0ynq /* dynamic qualifier */
  : i0de_dlr DOT                        { $$ = d0ynq_symdot($1) ; }
  | i0de_dlr COLON                      { $$ = d0ynq_symcolon($1) ; }
  | i0de_dlr i0de_dlr COLON             { $$ = d0ynq_symdot_symcolon ($1, $2) ; }
  | DOLLAR LITERAL_string DOT           { $$ = d0ynq_fildot($2) ; }
  | DOLLAR LITERAL_string i0de_dlr COLON
                                        { $$ = d0ynq_fildot_symcolon($2, $3) ; }
;  /* end of [d0ynq] */
*)
fun d0ynq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ynq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de_dlr DOT))
val () = grmrule_set_action (gr, "{ $$ = d0ynq_symdot($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de_dlr COLON))
val () = grmrule_set_action (gr, "{ $$ = d0ynq_symcolon($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de_dlr i0de_dlr COLON))
val () = grmrule_set_action (gr, "{ $$ = d0ynq_symdot_symcolon ($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOLLAR LITERAL_string DOT))
val () = grmrule_set_action (gr, "{ $$ = d0ynq_fildot($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOLLAR LITERAL_string i0de_dlr COLON))
val () = grmrule_set_action (gr, "{ $$ = d0ynq_fildot_symcolon($2, $3) ; }")
//
val () = symbol_close (pf | d0ynq)
//
} // end of [d0ynq_proc]

(* ****** ****** *)

(*
si0de /* static identifiers */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
/* keyword */
  | R0EAD                               { $$ = i0de_make_r0ead($1) ; }
/* keysymb */
  | AMPERSAND                           { $$ = i0de_make_ampersand($1) ; }
  | BACKSLASH                           { $$ = i0de_make_backslash($1) ; }
  | BANG                                { $$ = i0de_make_bang($1) ; }
  | GT                                  { $$ = i0de_make_gt($1) ; }
  | LT                                  { $$ = i0de_make_lt($1) ; }
  | MINUSGT                             { $$ = i0de_make_minusgt($1) ; }
  | TILDE                               { $$ = i0de_make_tilde($1) ; }
; /* end of [si0de] */
*)
fun si0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (si0de)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val gr = grmrule_append (R0EAD)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_r0ead($1) ; }")
//
val gr = grmrule_append (AMPERSAND)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_ampersand($1) ; }")
val gr = grmrule_append (BACKSLASH)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_backslash($1) ; }")
val gr = grmrule_append (BANG)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_bang($1) ; }")
val gr = grmrule_append (GT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_gt($1) ; }")
val gr = grmrule_append (LT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_lt($1) ; }")
val gr = grmrule_append (MINUSGT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_minusgt($1) ; }")
val gr = grmrule_append (TILDE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_tilde($1) ; }")
//
val () = symbol_close (pf | si0de)
//
} // end of [si0de_proc]

(* ****** ****** *)

(*
sqi0de /* qualified static identifier */
  : si0de                               
  | s0taq si0de                         { $$ = sqi0de_make_some($1, $2) ; }
; /* end of [sqi0de] */
*)
fun sqi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (sqi0de)
//
val gr = grmrule_append (si0de)
val () = grmrule_set_action (gr, "{ $$ = sqi0de_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0taq si0de))
val () = grmrule_set_action (gr, "{ $$ = sqi0de_make_some($1, $2) ; }")
//
val () = symbol_close (pf | sqi0de)
//
} // end of [sqi0de_proc]

(* ****** ****** *)

(*
commasi0deseq /* additional static identifier sequence */
  : /* empty */                         { $$ = i0delst_nil() ; }
  | COMMA si0de commasi0deseq           { $$ = i0delst_cons($2, $3) ; }
; /* end of [commasi0deseq] */
*)
fun commasi0deseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commasi0deseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0delst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA si0de commasi0deseq))
val () = grmrule_set_action (gr, "{ $$ = i0delst_cons($2, $3) ; }")
//
val commasi0de = SYMREGseqlit (COMMA, si0de)
val () = theGrmrulelst_merge_all (commasi0deseq, SYMREGstar(commasi0de))
//
val () = symbol_close (pf | commasi0deseq)
//
} // end of [commasi0deseq_proc]

(* ****** ****** *)

(*
di0de /* dynamic identifier */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
/* keysymb identifier */
  | BACKSLASH                           { $$ = i0de_make_backslash($1) ; }
  | BANG                                { $$ = i0de_make_bang($1) ; }
  | EQ                                  { $$ = i0de_make_eq($1) ; }
  | GT                                  { $$ = i0de_make_gt($1) ; }
  | GTLT                                { $$ = i0de_make_gtlt($1) ; }
  | LT                                  { $$ = i0de_make_lt($1) ; }
  | TILDE                               { $$ = i0de_make_tilde($1) ; }
; /* end of [di0de] */
*)
fun di0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (di0de)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val gr = grmrule_append (BACKSLASH)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_backslash($1) ; }")
val gr = grmrule_append (BANG)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_bang($1) ; }")
val gr = grmrule_append (EQ)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_eq($1) ; }")
val gr = grmrule_append (GT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_gt($1) ; }")
val gr = grmrule_append (GTLT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_gtlt($1) ; }")
val gr = grmrule_append (LT)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_lt($1) ; }")
val gr = grmrule_append (TILDE)
val () = grmrule_set_action (gr, "{ $$ = i0de_make_tilde($1) ; }")
//
val () = symbol_close (pf | di0de)
//
} // end of [di0de_proc]

(* ****** ****** *)

(*
dqi0de /* qualified dynamic identifier */
  : di0de                               { $$ = dqi0de_make_none($1) ; }
  | d0ynq di0de                         { $$ = dqi0de_make_some($1, $2) ; }
; /* end of [dqi0de] */
*)
fun dqi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (dqi0de)
//
val gr = grmrule_append (di0de)
val () = grmrule_set_action (gr, "{ $$ = dqi0de_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ynq di0de))
val () = grmrule_set_action (gr, "{ $$ = dqi0de_make_some($1, $2) ; }")
//
val () = symbol_close (pf | dqi0de)
//
} // end of [dqi0de_proc]

(* ****** ****** *)

(*
pi0de /* dynamic pattern identifier */
  : IDENTIFIER_alp                      { $$ = $1 ; }
  | IDENTIFIER_sym                      { $$ = $1 ; }
; /* end of [pi0de] */
*)
fun pi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (pi0de)
//
val gr = grmrule_append (IDENTIFIER_alp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (IDENTIFIER_sym)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | pi0de)
//
} // end of [pi0de_proc]

(* ****** ****** *)

(*
fi0de /* dynamic function identifier */
  : di0de                               { $$ = $1 ; }
  | OP di0de                            { $$ = $2 ; }
; /* end of [fi0de] */
*)
fun fi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (fi0de)
//
val gr = grmrule_append (di0de)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OP di0de))
val () = grmrule_set_action (gr, "{ $$ = $2 ; }")
//
val () = symbol_close (pf | fi0de)
//
} // end of [fi0de_proc]

(* ****** ****** *)
  
(*
arri0de /* array identifier */
  : IDENTIFIER_arr                      { $$ = $1 ; }
; /* end of [arri0de] */
*)
fun arri0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (arri0de)
//
val gr = grmrule_append (IDENTIFIER_arr)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | arri0de)
//
} // end of [arri0de_proc]

(*
arrqi0de /* qualified array identifier */
  : arri0de                             { $$ = arrqi0de_make_none($1) ; }
  | d0ynq arri0de                       { $$ = arrqi0de_make_some($1, $2) ; }
; /* end of [arrqi0de] */
*)
fun arrqi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (arrqi0de)
//
val gr = grmrule_append (arri0de)
val () = grmrule_set_action (gr, "{ $$ = arrqi0de_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ynq arri0de))
val () = grmrule_set_action (gr, "{ $$ = arrqi0de_make_some($1, $2) ; }")
//
val () = symbol_close (pf | arrqi0de)
//
} // end of [arrqi0de_proc]

(* ****** ****** *)

(*
tmpi0de /* template identifier */
  : IDENTIFIER_tmp                      { $$ = $1 ; }
; /* end of [tmpi0de] */
*)
fun tmpi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (tmpi0de)
//
val gr = grmrule_append (IDENTIFIER_tmp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | tmpi0de)
//
} // end of [tmpi0de_proc]

(*
tmpqi0de /* qualified template identifier */
  : tmpi0de                             { $$ = tmpqi0de_make_none($1) ; }
  | d0ynq tmpi0de                       { $$ = tmpqi0de_make_some($1, $2) ; }
; /* end of [tmpqi0de] */
*)
fun tmpqi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (tmpqi0de)
//
val gr = grmrule_append (tmpi0de)
val () = grmrule_set_action (gr, "{ $$ = tmpqi0de_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ynq tmpi0de))
val () = grmrule_set_action (gr, "{ $$ = tmpqi0de_make_some($1, $2) ; }")
//
val () = symbol_close (pf | tmpqi0de)
//
} // end of [tmpqi0de_proc]

(* ****** ****** *)

(*
colons0rtopt /* optional sort annotation */
  : /* empty */                         { $$ = s0rtopt_none() ; }
  | COLON s0rt                          { $$ = s0rtopt_some($2) ; }
; /* end of [colons0rtopt] */
*)
fun colons0rtopt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (colons0rtopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0rtopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COLON s0rt))
val () = grmrule_set_action (gr, "{ $$ = s0rtopt_some($2) ; }")
//
val colons0rt = SYMREGseqlit (COLON, s0rt)
val () = theGrmrulelst_merge_all (colons0rtopt, SYMREGopt(colons0rt))
//
val () = symbol_close (pf | colons0rtopt)
//
} // end of [colons0rtopt_proc]

(* ****** ****** *)

(*
s0arg /* static argument */
  : si0de colons0rtopt                  { $$ = s0arg_make($1, $2) ; }
; /* end of [s0arg] */
*)
fun s0arg_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0arg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de colons0rtopt))
val () = grmrule_set_action (gr, "{ $$ = s0arg_make($1, $2) ; }")
//
val () = symbol_close (pf | s0arg)
//
} // end of [s0arg_proc]

(* ****** ****** *)

(*
s0argseq /* static argument sequence */
  : /* empty */                         { $$ = s0arglst_nil() ; }
  | s0arg commas0argseq                 { $$ = s0arglst_cons ($1, $2) ; }
; /* end of [s0argseq] */
*)
fun s0argseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0arg commas0argseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglst_cons($1, $2) ; }")
//
val () = symbol_close (pf | s0argseq)
//
} // end of [s0argseq_proc]

(* ****** ****** *)

(*
commas0argseq
  : /* empty */                         { $$ = s0arglst_nil() ; }
  | COMMA s0arg commas0argseq           { $$ = s0arglst_cons ($2, $3) ; }
; /* end of [commas0argseq] */
*)
fun commas0argseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commas0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA s0arg commas0argseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglst_cons($2, $3) ; }")
//
val commas0arg = SYMREGseqlit (COMMA, s0arg)
val () = theGrmrulelst_merge_all (commas0argseq, SYMREGstar(commas0arg))
//
val () = symbol_close (pf | commas0argseq)
//
} // end of [commas0argseq_proc]

(* ****** ****** *)

(*
s0argseqseq /* static argument sequence sequence */
  : /* empty */                         { $$ = s0arglstlst_nil() ; }
  | si0de s0argseqseq                   { $$ = s0arglstlst_cons_ide($1, $2) ; }
  | LPAREN s0argseq RPAREN s0argseqseq  { $$ = s0arglstlst_cons($2, $4); }
; /* end of [s0argseqseq] */
*)
fun s0argseqseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0argseqseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0arglstlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de s0argseqseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglstlst_cons_ide($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN s0argseq RPAREN s0argseqseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglstlst_cons($2, $4); }")
//
val () = symbol_close (pf | s0argseqseq)
//
} // end of [s0argseqseq_proc]

(* ****** ****** *)

(*
** template argument variables
*)

(*
decs0argseq
  : /* empty */ %prec TMPSARG           { $$ = s0arglst_nil() ; }
  | s0arg commadecs0argseq              { $$ = s0arglst_cons($1, $2) ; }
; /* end of [decs0argseq] */
*)
fun decs0argseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (decs0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0arglst_nil() ; }")
val () = grmrule_set_precval (gr, "%prec TMPSARG")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0arg commadecs0argseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglst_cons($1, $2) ; }")
//
val () = symbol_close (pf | decs0argseq)
//
} // end of [decs0argseq_proc]

(*
commadecs0argseq
  : /* empty */ %prec TMPSARG           { $$ = s0arglst_nil() ; }
  | COMMA s0arg commadecs0argseq        { $$ = s0arglst_cons($2, $3) ; }
; /* end of [commadecs0argseq] */
*)
fun commadecs0argseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commadecs0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0arglst_nil() ; }")
val () = grmrule_set_precval (gr, "%prec TMPSARG")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA s0arg commadecs0argseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglst_cons($2, $3) ; }")
//
val commas0arg = SYMREGseqlit (COMMA, s0arg)
val () = theGrmrulelst_merge_all (commadecs0argseq, SYMREGstar(commas0arg))
//
val () = symbol_close (pf | commadecs0argseq)
//
} // end of [commadecs0argseq_proc]

(* ****** ****** *)

(*
** template argument variables
*)

(*
decs0argseqseq
  : /* empty */                         { $$ = s0arglstlst_nil() ; }
  | LBRACE decs0argseq RBRACE decs0argseqseq
                                        { $$ = s0arglstlst_cons($2, $4) ; }
; /* end of [decs0argseqseq] */
*)
fun decs0argseqseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (decs0argseqseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0arglstlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE decs0argseq RBRACE decs0argseqseq))
val () = grmrule_set_action (gr, "{ $$ = s0arglstlst_cons($2, $4) ; }")
//
val () = symbol_close (pf | decs0argseqseq)
//
} // end of [decs0argseqseq_proc]

(* ****** ****** *)

(*
sp0at /* static pattern */
  : sqi0de LPAREN s0argseq RPAREN       { $$ = sp0at_con($1, $3, $4) ; }
; /* end of [sp0at] */
*)
fun sp0at_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (sp0at)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! sqi0de LPAREN s0argseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = sp0at_con($1, $3, $4) ; }")
//
val () = symbol_close (pf | sp0at)
//
} // end of [sp0at_proc]

(* ****** ****** *)

(*
** static expressions
*)

(*
s0exp /* static expression */
  : apps0exp                            { $$ = $1 ; }
  | exts0exp                            { $$ = s0exp_extern($1) ; }
  | s0exp COLON s0rt                    { $$ = s0exp_ann($1, $3) ; }
  | LAM s0argseqseq colons0rtopt EQGT s0exp %prec SEXPLAM
                                        { $$ = s0exp_lams($1, $2, $3, $5) ; }
; /* end of [s0exp] */
*)
fun s0exp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0exp)
//
val gr = grmrule_append (apps0exp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append (exts0exp)
val () = grmrule_set_action (gr, "{ $$ = s0exp_extern($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0exp COLON s0rt))
val () = grmrule_set_action (gr, "{ $$ = s0exp_ann($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LAM s0argseqseq colons0rtopt EQGT s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0exp_lams($1, $2, $3, $5) ; }")
val () = grmrule_set_precval (gr, " %prec SEXPLAM")
//
val () = symbol_close (pf | s0exp)
//
} // end of [s0exp_proc]

(* ****** ****** *)

(*
atms0exp /* atomic static expression */
  : LITERAL_char                        { $$ = s0exp_char($1) ; }
  | LITERAL_int                         { $$ = s0exp_int($1) ; }
  | LITERAL_intsp                       { $$ = s0exp_intsp_err($1) ; }
  | si0de                               { $$ = s0exp_ide($1) ; }
  | OP si0de                            { $$ = s0exp_opide($1, $2) ; }
  | s0taq si0de                         { $$ = s0exp_qid($1, $2) ; }
/*
  | sqi0de HASHLBRACE labs0expseq RBRACE
                                        { $$ = s0exp_mod($1, $3, $4) ; }
*/
  | LPAREN s0expseq RPAREN              { $$ = s0exp_list($1, $2, $3) ; }
  | LPAREN s0expseq BAR s0expseq RPAREN { $$ = s0exp_list2($1, $2, $4, $5) ; }

  | ATLPAREN s0expseq RPAREN            { $$ = s0exp_tytup(0, $1, $2, $3) ; }
  | QUOTELPAREN s0expseq RPAREN         { $$ = s0exp_tytup(1, $1, $2, $3) ; }
  | DLRTUP_T LPAREN s0expseq RPAREN     { $$ = s0exp_tytup(2, $1, $3, $4) ; }
  | DLRTUP_VT LPAREN s0expseq RPAREN    { $$ = s0exp_tytup(3, $1, $3, $4) ; }

  | ATLPAREN s0expseq BAR s0expseq RPAREN
                                        { $$ = s0exp_tytup2(0, $1, $2, $4, $5) ; }
  | QUOTELPAREN s0expseq BAR s0expseq RPAREN
                                        { $$ = s0exp_tytup2(1, $1, $2, $4, $5) ; }
  | DLRTUP_T LPAREN s0expseq BAR s0expseq RPAREN
                                        { $$ = s0exp_tytup2(2, $1, $3, $5, $6) ; }
  | DLRTUP_VT LPAREN s0expseq BAR s0expseq RPAREN
                                        { $$ = s0exp_tytup2(3, $1, $3, $5, $6) ; }

  | ATLBRACE labs0expseq RBRACE         { $$ = s0exp_tyrec(0, $1, $2, $3) ; }
  | QUOTELBRACE labs0expseq RBRACE      { $$ = s0exp_tyrec(1, $1, $2, $3) ; }
  | DLRREC_T LBRACE labs0expseq RBRACE  { $$ = s0exp_tyrec(2, $1, $3, $4) ; }
  | DLRREC_VT LBRACE labs0expseq RBRACE { $$ = s0exp_tyrec(3, $1, $3, $4) ; }
  | DLREXTYPE_STRUCT LITERAL_string OF LBRACE labs0expseq RBRACE
                                        { $$ = s0exp_tyrec_ext($1, $2, $5, $6) ; }

  | ATLBRACKET s0exp RBRACKET LBRACKET s0arrind
                                        { $$ = s0exp_tyarr($1, $2, $5) ; }

/*
//
// HX-2010-11-01: it is removed to simplify the syntax of ATS
//
  | STRUCT LBRACE labs0expseq RBRACE    { $$ = s0exp_struct($1, $3, $4) ; }
  | UNION atms0exp LBRACE labs0expseq RBRACE
                                        { $$ = s0exp_union($1, $2, $4, $5) ; }
*/
  | MINUSLT e0fftagseq GT               { $$ = s0exp_imp($1, $2, $3) ; }
  | MINUSLTGT                           { $$ = s0exp_imp_emp($1) ; }
  | LBRACE s0quaseq RBRACE              { $$ = s0exp_uni($1, $2, $3) ; }
  | LBRACKET s0quaseq RBRACKET          { $$ = s0exp_exi($1, 0/*funres*/, $2, $3) ; }
  | HASHLBRACKET s0quaseq RBRACKET      { $$ = s0exp_exi($1, 1/*funres*/, $2, $3) ; }
; /* end of [atms0exp] */
*)
fun atms0exp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (atms0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_char))
val () = grmrule_set_action (gr, "{ $$ = s0exp_char($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_int))
val () = grmrule_set_action (gr, "{ $$ = s0exp_int($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_intsp))
val () = grmrule_set_action (gr, "{ $$ = s0exp_intsp_err($1) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de))
val () = grmrule_set_action (gr, "{ $$ = s0exp_ide($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OP si0de))
val () = grmrule_set_action (gr, "{ $$ = s0exp_opide($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0taq si0de))
val () = grmrule_set_action (gr, "{ $$ = s0exp_qid($1, $2) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_list($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN s0expseq BAR s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_list2($1, $2, $4, $5) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup(0, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELPAREN s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup(1, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRTUP_T LPAREN s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup(2, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRTUP_VT LPAREN s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup(3, $1, $3, $4) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN s0expseq BAR s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup2(0, $1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELPAREN s0expseq BAR s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup2(1, $1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRTUP_T LPAREN s0expseq BAR s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup2(2, $1, $3, $5, $6) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRTUP_VT LPAREN s0expseq BAR s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tytup2(3, $1, $3, $5, $6) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLBRACE labs0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tyrec(0, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELBRACE labs0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tyrec(1, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRREC_T LBRACE labs0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tyrec(2, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRREC_VT LBRACE labs0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tyrec(3, $1, $3, $4) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREXTYPE_STRUCT LITERAL_string OF LBRACE labs0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tyrec_ext($1, $2, $5, $6) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLBRACKET s0exp RBRACKET LBRACKET s0arrind))
val () = grmrule_set_action (gr, "{ $$ = s0exp_tyarr($1, $2, $5) ; }")
//
val gr = grmrule_append ($lst_t {symbol} (tupz! MINUSLT e0fftagseq GT))
val () = grmrule_set_action (gr, "{ $$ = s0exp_imp($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! MINUSLTGT))
val () = grmrule_set_action (gr, "{ $$ = s0exp_imp_emp($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0quaseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0exp_uni($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACKET s0quaseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = s0exp_exi($1, 0/*funres*/, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! HASHLBRACKET s0quaseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = s0exp_exi($1, 1/*funres*/, $2, $3) ; }")
//
val () = symbol_close (pf | atms0exp)
//
} // end of [atms0exp_proc]

(* ****** ****** *)

(*
apps0exp /* static application */
  : apps0exp atms0exp                   { $$ = s0exp_app($1, $2) ; }
  | atms0exp                            { $$ = $1 ; }
; /* end of [apps0exp] */
*)
fun apps0exp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (apps0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! apps0exp atms0exp))
val () = grmrule_set_action (gr, "{ $$ = s0exp_app($1, $2) ; }")
val gr = grmrule_append (atms0exp)
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = theGrmrulelst_merge_all (apps0exp, SYMREGpluslit(atms0exp))
//
val () = symbol_close (pf | apps0exp)
//
} // end of [apps0exp_proc]

(* ****** ****** *)

(*
exts0exp
  : DLREXTYPE LITERAL_string            { $$ = s0expext_nam($1, $2) ; }
  | exts0exp atms0exp                   { $$ = s0expext_app($1, $2) ; }
; /* exts0exp */
*)
fun exts0exp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (exts0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREXTYPE LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = s0expext_nam($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! exts0exp atms0exp))
val () = grmrule_set_action (gr, "{ $$ = s0expext_app($1, $2) ; }")
//
val () = symbol_close (pf | exts0exp)
//
} // end of [exts0exp_proc]

(* ****** ****** *)

(*
s0expelt /* type for array or list elements */
  : /* empty */                         { $$ = s0expopt_none () ; }
  | LBRACE s0exp RBRACE                 { $$ = s0expopt_some ($2) ; }
  | LBRACKET s0exp RBRACEKET            { $$ = s0expopt_some ($2) ; }
; /* end of [s0expelt] */
*)
fun s0expelt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0expelt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0expopt_none () ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0exp RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0expopt_some ($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACKET s0exp RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = s0expopt_some ($2) ; }")
//
val () = symbol_close (pf | s0expelt)
//
} // end of [s0expelt_proc]

(* ****** ****** *)

(*
s0arrind /* static array indexes */
  : s0expseq RBRACKET %prec SARRIND     { $$ = s0arrind_make_sing($1, $2) ; }
  | s0expseq RBRACKET LBRACKET s0arrind { $$ = s0arrind_make_cons($1, $4) ; }
; /* end of [s0arrind] */
*)
fun s0arrind_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0arrind)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! s0expseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = s0arrind_make_sing($1, $2) ; }")
val () = grmrule_set_precval (gr, "%prec SARRIND")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0expseq RBRACKET LBRACKET s0arrind))
val () = grmrule_set_action (gr, "{ $$ = s0arrind_make_cons($1, $4) ; }")
//
val () = symbol_close (pf | s0arrind)
//
} // end of [s0arrind_proc]

(* ****** ****** *)

(*
s0qua /* static quantification */
  : apps0exp                            { $$ = s0qua_prop($1) ; }
  | si0de commasi0deseq COLON s0rtext   { $$ = s0qua_vars($1, $2, $4) ; }
; /* end of [s0qua] */
*)
fun s0qua_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0qua)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! apps0exp))
val () = grmrule_set_action (gr, "{ $$ = s0qua_prop($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de commasi0deseq COLON s0rtext))
val () = grmrule_set_action (gr, "{ $$ = s0qua_vars($1, $2, $4) ; }")
//
val () = symbol_close (pf | s0qua)
//
} // end of [s0qua_proc]

(*
s0quaseq /* static quantification sequence */
  : /* empty */                         { $$ = s0qualst_nil() ; }
  | s0qua barsemis0quaseq               { $$ = s0qualst_cons($1, $2) ; }
; /* end of [s0quaseq] */
*)
fun s0quaseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0quaseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0qua barsemis0quaseq))
val () = grmrule_set_action (gr, "{ $$ = s0qualst_cons($1, $2) ; }")
//
val () = symbol_close (pf | s0quaseq)
//
} // end of [s0quaseq_proc]

(*
barsemis0quaseq /* semicolon may substitute for bar */
  : /* empty */                         { $$ = s0qualst_nil() ; }
  | BAR s0qua barsemis0quaseq           { $$ = s0qualst_cons($2, $3) ; }
  | SEMICOLON s0qua barsemis0quaseq     { $$ = s0qualst_cons($2, $3) ; }
; /* end of [barsemis0quaseq] */
*)
fun barsemis0quaseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (barsemis0quaseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BAR s0qua barsemis0quaseq))
val () = grmrule_set_action (gr, "{ $$ = s0qualst_cons($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SEMICOLON s0qua barsemis0quaseq))
val () = grmrule_set_action (gr, "{ $$ = s0qualst_cons($2, $3) ; }")
//
val barsemi = SYMREGaltlit (BAR, SEMICOLON)
val barsemis0qua = SYMREGseq (barsemi, SYMREGlit s0qua)
val () = theGrmrulelst_merge_all (barsemis0quaseq, SYMREGstar (barsemis0qua))
//
val () = symbol_close (pf | barsemis0quaseq)
//
} // end of [barsemis0quaseq_proc]

(* ****** ****** *)

(*
s0rtext /* extended sort (sort and subset sort) */
  : s0rt                                { $$ = s0rtext_srt($1) ; }
  | LBRACE si0de COLON s0rtext BAR s0exp barsemis0expseq RBRACE
                                        { $$ = s0rtext_sub($1, $2, $4, $6, $7, $8) ; }
; /* end of [s0rtext] */
*)
fun s0rtext_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtext)
//
val gr = grmrule_append (s0rt)
val () = grmrule_set_action (gr, "{ $$ = s0rtext_srt($1) ; }")
val gr = grmrule_append
  ($lst_t {symbol} (tupz! LBRACE si0de COLON s0rtext BAR s0exp barsemis0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0rtext_sub($1, $2, $4, $6, $7, $8) ; }")
//
val () = symbol_close (pf | s0rtext)
//
} // end of [s0rtext_proc]

(* ****** ****** *)

(*
s0expseq /* static expression sequence */
  : /* empty */                         { $$ = s0explst_nil() ; }
  | s0expseq1                           { $$ = $1 ; }
; /* end of [s0expseq] */
*)
fun s0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0expseq1))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | s0expseq)
//
} // end of [s0expseq_proc]

(* ****** ****** *)

(*
barsemis0expseq /* semicolon may substitute for bar */
  : /* empty */                         { $$ = s0explst_nil() ; }
  | BAR s0exp barsemis0expseq               { $$ = s0explst_cons($2, $3) ; }
  | SEMICOLON s0exp barsemis0expseq         { $$ = s0explst_cons($2, $3) ; }
; /* end of [barsemis0expseq] */
*)
fun barsemis0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (barsemis0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BAR s0exp barsemis0expseq))
val () = grmrule_set_action (gr, "{ $$ = s0explst_cons($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SEMICOLON s0exp barsemis0expseq))
val () = grmrule_set_action (gr, "{ $$ = s0explst_cons($2, $3) ; }")
//
val barsemi = SYMREGaltlit (BAR, SEMICOLON)
val barsemis0exp = SYMREGseq (barsemi, SYMREGlit s0exp)
val () = theGrmrulelst_merge_all (barsemis0expseq, SYMREGstar (barsemis0exp))
//
val () = symbol_close (pf | barsemis0expseq)
//
} // end of [barsemis0expseq_proc]

(* ****** ****** *)

(*
commas0expseq
  : /* empty */                         { $$ = s0explst_nil() ; }
  | COMMA s0exp commas0expseq           { $$ = s0explst_cons($2, $3) ; }
; /* end of [commas0expseq] */
*)
fun commas0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commas0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA s0exp commas0expseq))
val () = grmrule_set_action (gr, "{ $$ = s0explst_cons($2, $3) ; }")
//
val commas0exp = SYMREGseqlit (COMMA, s0exp)
val () = theGrmrulelst_merge_all (commas0expseq, SYMREGstar (commas0exp))
//
val () = symbol_close (pf | commas0expseq)
//
} // end of [commas0expseq_proc]

(* ****** ****** *)

(*
s0expseq1
  : s0exp commas0expseq                 { $$ = s0explst_cons($1, $2) ; }
; /* end of [s0expseq1] */
*)
fun s0expseq1_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0expseq1)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! s0exp commas0expseq))
val () = grmrule_set_action (gr, "{ $$ = s0explst_cons($1, $2) ; }")
//
val () = symbol_close (pf | s0expseq1)
//
} // end of [s0expseq1_proc]

(* ****** ****** *)

(*
labs0expseq /* labeled static expression sequence */
  : /* empty */                         { $$ = labs0explst_nil() ; }
  | l0ab EQ s0exp commalabs0expseq      { $$ = labs0explst_cons($1, $3, $4) ; }
; /* end of [labs0expseq] */
*)
fun labs0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (labs0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = labs0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! l0ab EQ s0exp commalabs0expseq))
val () = grmrule_set_action (gr, "{ $$ = labs0explst_cons($1, $3, $4) ; }")
//
val () = symbol_close (pf | labs0expseq)
//
} // end of [labs0expseq_proc]

(* ****** ****** *)

(*
commalabs0expseq
  : /* empty */                         { $$ = labs0explst_nil() ; }
  | COMMA l0ab EQ s0exp commalabs0expseq
                                        { $$ = labs0explst_cons($2, $4, $5) ; }
; /* end of [commalabs0expseq] */
*)
fun commalabs0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commalabs0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = labs0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA l0ab EQ s0exp commalabs0expseq))
val () = grmrule_set_action (gr, "{ $$ = labs0explst_cons($2, $4, $5) ; }")
//
val commal0ab = SYMREGseqlit (COMMA, l0ab)
val commal0abeq = SYMREGseq (commal0ab, SYMREGlit EQ)
val commal0abeqs0exp = SYMREGseq (commal0abeq, SYMREGlit s0exp)
val () = theGrmrulelst_merge_all (commalabs0expseq, SYMREGstar (commal0abeqs0exp))
//
val () = symbol_close (pf | commalabs0expseq)
//
} // end of [commalabs0expseq_proc]

(* ****** ****** *)

(*
** template argument expressions
*)

(*
t0mps0exp
  : atms0exp                            { $$ = $1 ; }
  | t0mps0exp atms0exp                  { $$ = s0exp_app($1, $2) ; }
; /* end of [t0mps0exp] */
*)
fun t0mps0exp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (t0mps0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! atms0exp))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! t0mps0exp atms0exp))
val () = grmrule_set_action (gr, "{ $$ = s0exp_app($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (t0mps0exp, SYMREGpluslit(atms0exp))
//
val () = symbol_close (pf | t0mps0exp)
//
} /* end of [t0mps0exp_proc] */

(*
t1mps0exp
  : t0mps0exp %prec TMPSEXP             { $$ = $1 ; }
/*
// HX-2010-12-04: inadequate design
  | si0de EQ t0mps0exp %prec TMPSEXP    { $$ = s0exp_named ($1, $3) ; }
*/
; /* end of [t1mps0exp] */
*)
fun t1mps0exp_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (t1mps0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! t0mps0exp))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val () = grmrule_set_precval (gr, "%prec TMPSEXP")
//
val () = symbol_close (pf | t1mps0exp)
//
} /* end of [t1mps0exp_proc] */

(*
t1mps0expseq
  : /* empty */ %prec TMPSEXP           { $$ = s0explst_nil() ; }
  | t1mps0exp commat1mps0expseq         { $$ = s0explst_cons($1, $2) ; }
; /* end of [t1mps0expseq] */
*)
fun t1mps0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (t1mps0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0explst_nil() ; }")
val () = grmrule_set_precval (gr, "%prec TMPSEXP")
val gr = grmrule_append ($lst_t {symbol} (tupz! t1mps0exp commat1mps0expseq))
val () = grmrule_set_action (gr, "{ $$ = s0explst_cons($1, $2) ; }")
//
val () = symbol_close (pf | t1mps0expseq)
//
} /* end of [t1mps0expseq_proc] */

(*
commat1mps0expseq
  : /* empty */ %prec TMPSEXP           { $$ = s0explst_nil() ; }
  | COMMA t1mps0exp commat1mps0expseq   { $$ = s0explst_cons($2, $3) ; }
; /* end of [commat1mps0expseq] */
*)
fun commat1mps0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commat1mps0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0explst_nil() ; }")
val () = grmrule_set_precval (gr, "%prec TMPSEXP")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA t1mps0exp commat1mps0expseq))
val () = grmrule_set_action (gr, "{ $$ = s0explst_cons($2, $3) ; }")
//
val commat1mps0exp = SYMREGseqlit (COMMA, t1mps0exp)
val () = theGrmrulelst_merge_all (commat1mps0expseq, SYMREGstar (commat1mps0exp))
//
val () = symbol_close (pf | commat1mps0expseq)
//
} /* end of [commat1mps0expseq_proc] */

(*
gtlt_t1mps0expseqseq
  : /* empty */                         { $$ = gtlt_t1mps0expseqseq_nil() ; }
  | GTLT t1mps0expseq gtlt_t1mps0expseqseq
                                        { $$ = gtlt_t1mps0expseqseq_cons_tok($1, $2, $3) ; }
; /* end of [gtlt_t1mps0expseqseq] */
*)
fun gtlt_t1mps0expseqseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (gtlt_t1mps0expseqseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = gtlt_t1mps0expseqseq_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! GTLT t1mps0expseq gtlt_t1mps0expseqseq))
val () = grmrule_set_action (gr, "{ $$ = gtlt_t1mps0expseqseq_cons_tok($1, $2, $3) ; }")
//
val () = symbol_close (pf | gtlt_t1mps0expseqseq)
//
} /* end of [gtlt_t1mps0expseqseq_proc] */

(*
impqi0de
  : dqi0de                              { $$ = impqi0de_make_none($1) ; }
  | tmpqi0de t1mps0expseq gtlt_t1mps0expseqseq GT
                                        { $$ = impqi0de_make_some($1, $2, $3, $4) ; }
; /* end of [impqi0de] */
*)
fun impqi0de_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (impqi0de)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! dqi0de))
val () = grmrule_set_action (gr, "{ $$ = impqi0de_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! tmpqi0de t1mps0expseq gtlt_t1mps0expseqseq GT))
val () = grmrule_set_action (gr, "{ $$ = impqi0de_make_some($1, $2, $3, $4) ; }")
//
val () = symbol_close (pf | impqi0de)
//
} /* end of [impqi0de_proc] */

(* ****** ****** *)

(*
** static declarations
*)

(*
s0rtdef /* sort definition */
  : s0rtid EQ s0rtext                   { $$ = s0rtdef_make($1, $3) ; }
; /* end of [s0rtdef] */
*)
fun s0rtdef_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0rtdef)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! s0rtid EQ s0rtext))
val () = grmrule_set_action (gr, "{ $$ = s0rtdef_make($1, $3) ; }")
//
val () = symbol_close (pf | s0rtdef)
//
} /* end of [s0rtdef_proc] */

(*
ands0rtdefseq /* additional sort definition sequence */
  : /* empty */                         { $$ = s0rtdeflst_nil() ; }
  | AND s0rtdef ands0rtdefseq           { $$ = s0rtdeflst_cons($2, $3) ; }
; /* end of [ands0rtdefseq] */
*)
fun ands0rtdefseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (ands0rtdefseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0rtdeflst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND s0rtdef ands0rtdefseq))
val () = grmrule_set_action (gr, "{ $$ = s0rtdeflst_cons($2, $3) ; }")
//
val ands0rtdef = SYMREGseqlit (AND, s0rtdef)
val () = theGrmrulelst_merge_all (ands0rtdefseq, SYMREGstar(ands0rtdef))
//
val ()= symbol_close (pf | ands0rtdefseq)
//
} /* end of [ands0rtdefseq_proc] */

(* ****** ****** *)

(*
d0atarg /* datatype argument */
  : s0rtpol                             { $$ = d0atarg_srt($1) ; }
  | i0de COLON s0rtpol                  { $$ = d0atarg_id_srt($1, $3) ; }
; /* end of [d0atarg] */
*)
fun d0atarg_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0atarg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! s0rtpol))
val () = grmrule_set_action (gr, "{ $$ = d0atarg_srt($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0de COLON s0rtpol))
val () = grmrule_set_action (gr, "{ $$ = d0atarg_id_srt($1, $3) ; }")
//
val () = symbol_close (pf | d0atarg)
//
} /* end of [d0atarg_proc] */

(*
d0atargseq /* datatype argument sequence */
  : /* empty */                         { $$ = d0atarglst_nil() ; }
  | d0atarg commad0atargseq             { $$ = d0atarglst_cons($1, $2) ; }
; /* end of [d0atargseq] */
*)
fun d0atargseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0atargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0atarglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0atarg commad0atargseq))
val () = grmrule_set_action (gr, "{ $$ = d0atarglst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0atargseq)
//
} /* end of [d0atargseq_proc] */

(*
commad0atargseq
  : /* empty */                         { $$ = d0atarglst_nil() ; }
  | COMMA d0atarg commad0atargseq       { $$ = d0atarglst_cons($2, $3) ; }
; /* end of [commad0atargseq] */
*)
fun commad0atargseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (commad0atargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0atarglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA d0atarg commad0atargseq))
val () = grmrule_set_action (gr, "{ $$ = d0atarglst_cons($2, $3) ; }")
//
val commad0atarg = SYMREGseqlit (COMMA, d0atarg)
val () = theGrmrulelst_merge_all (commad0atargseq, SYMREGstar (commad0atarg))
//
val () = symbol_close (pf | commad0atargseq)
//
} /* end of [commad0atargseq_proc] */

(* ****** ****** *)

(*
s0tacon /* abstract static constructor */
  : si0de                               { $$ = s0tacon_make_none_none($1) ; }
  | si0de LPAREN d0atargseq RPAREN      { $$ = s0tacon_make_some_none($1, $3, $4) ; }
  | si0de EQ s0exp                      { $$ = s0tacon_make_none_some($1, $3) ; }
  | si0de LPAREN d0atargseq RPAREN EQ s0exp
                                        { $$ = s0tacon_make_some_some($1, $3, $6) ; }
; /* end of [s0tacon] */
*)
fun s0tacon_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0tacon)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de))
val () = grmrule_set_action (gr, "{ $$ = s0tacon_make_none_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de LPAREN d0atargseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0tacon_make_some_none($1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de EQ s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0tacon_make_none_some($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de LPAREN d0atargseq RPAREN EQ s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0tacon_make_some_some($1, $3, $6) ; }")
//
val () = symbol_close (pf | s0tacon)
//
} /* end of [s0tacon_proc] */

(*
ands0taconseq /* additional abstract static constructor sequence */
  : /* empty */                         { $$ = s0taconlst_nil() ; }
  | AND s0tacon ands0taconseq           { $$ = s0taconlst_cons($2, $3) ; }
; /* end of [ands0taconseq] */
*)
fun ands0taconseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (ands0taconseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0taconlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND s0tacon ands0taconseq))
val () = grmrule_set_action (gr, "{ $$ = s0taconlst_cons($2, $3) ; }")
//
val ands0tacon = SYMREGseqlit (AND, s0tacon)
val () = theGrmrulelst_merge_all (ands0taconseq, SYMREGstar (ands0tacon))
//
val () = symbol_close (pf | ands0taconseq)
//
} /* end of [ands0taconseq_proc] */

(* ****** ****** *)

(*
s0tacst /* static constant */
  : si0de COLON s0rt                    { $$ = s0tacst_make_none($1, $3) ; }
  | si0de LPAREN d0atargseq RPAREN COLON s0rt { $$ = s0tacst_make_some($1, $3, $6) ; }
; /* end of [s0tacst] */
*)
fun s0tacst_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0tacst)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de COLON s0rt))
val () = grmrule_set_action (gr, "{ $$ = s0tacst_make_none($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de LPAREN d0atargseq RPAREN COLON s0rt))
val () = grmrule_set_action (gr, "{ $$ = s0tacst_make_some($1, $3, $6) ; }")
//
val () = symbol_close (pf | s0tacst)
//
} /* end of [s0tacst_proc] */

(*
ands0tacstseq /* additional static constant sequence */
  : /* empty */                         { $$ = s0tacstlst_nil() ; }
  | AND s0tacst ands0tacstseq           { $$ = s0tacstlst_cons($2, $3) ; }
; /* end of [ands0tacstseq] */
*)
fun ands0tacstseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (ands0tacstseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0tacstlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND s0tacst ands0tacstseq))
val () = grmrule_set_action (gr, "{ $$ = s0tacstlst_cons($2, $3) ; }")
//
val ands0tacst = SYMREGseqlit (AND, s0tacst)
val () = theGrmrulelst_merge_all (ands0tacstseq, SYMREGstar (ands0tacst))
//
val () = symbol_close (pf | ands0tacstseq)
//
} /* end of [ands0tacstseq_proc] */

(* ****** ****** *)

(*
s0tavar /* static variable */
  : si0de COLON s0rt                    { $$ = s0tavar_make($1, $3) ; }
; /* end of [s0tavar] */
*)
fun s0tavar_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0tavar)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de COLON s0rt))
val () = grmrule_set_action (gr, "{ $$ = s0tavar_make($1, $3) ; }")
//
val () = symbol_close (pf | s0tavar)
//
} /* end of [s0tavar_proc] */

(*
ands0tavarseq /* additional static constant sequence */
  : /* empty */                         { $$ = s0tavarlst_nil() ; }
  | AND s0tavar ands0tavarseq           { $$ = s0tavarlst_cons($2, $3) ; }
; /* end of [ands0tavarseq] */
*)
fun ands0tavarseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (ands0tavarseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0tavarlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND s0tavar ands0tavarseq))
val () = grmrule_set_action (gr, "{ $$ = s0tavarlst_cons($2, $3) ; }")
//
val ands0tavar = SYMREGseqlit (AND, s0tavar)
val () = theGrmrulelst_merge_all (ands0tavarseq, SYMREGstar (ands0tavar))
//
val () = symbol_close (pf | ands0tavarseq)
//
} /* end of [ands0tavarseq_proc] */

(* ****** ****** *)

(*
s0expdef /* static definition */
  : si0de s0argseqseq colons0rtopt EQ s0exp
                                        { $$ = s0expdef_make ($1, $2, $3, $5) ; }
; /* end of [s0expdef] */
*)
fun s0expdef_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0expdef)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de s0argseqseq colons0rtopt EQ s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0expdef_make ($1, $2, $3, $5) ; }")
//
val () = symbol_close (pf | s0expdef)
//
} /* end of [s0expdef_proc] */

(*
ands0expdefseq /* additional static definition sequence */
  : /* empty */                         { $$ = s0expdeflst_nil() ; }
  | AND s0expdef ands0expdefseq         { $$ = s0expdeflst_cons($2, $3) ; }
; /* end of [ands0expdefseq] */
*)
fun ands0expdefseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (ands0expdefseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0expdeflst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND s0expdef ands0expdefseq))
val () = grmrule_set_action (gr, "{ $$ = s0expdeflst_cons($2, $3) ; }")
//
val ands0expdef = SYMREGseqlit (AND, s0expdef)
val () = theGrmrulelst_merge_all (ands0expdefseq, SYMREGstar (ands0expdef))
//
val () = symbol_close (pf | ands0expdefseq)
//
} /* end of [ands0expdefseq_proc] */

/* ****** ****** */

(*
s0aspdec /* static assumption (for a static abstract constructor) */
  : sqi0de s0argseqseq colons0rtopt EQ s0exp
                                        { $$ = s0aspdec_make($1, $2, $3, $5) ; }
; /* end of [s0aspdec] */
*)
fun s0aspdec_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0aspdec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! sqi0de s0argseqseq colons0rtopt EQ s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0aspdec_make($1, $2, $3, $5) ; }")
//
val () = symbol_close (pf | s0aspdec)
//
} /* end of [s0aspdec_proc] */

(* ****** ****** *)

(*
conq0uaseq /* quantifiers */
  : /* empty */                         { $$ = s0qualstlst_nil() ; }
  | LBRACE s0quaseq RBRACE conq0uaseq   { $$ = s0qualstlst_cons($2, $4) ; }
; /* end of [conq0uaseq] */
*)
fun conq0uaseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (conq0uaseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualstlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0quaseq RBRACE conq0uaseq))
val () = grmrule_set_action (gr, "{ $$ = s0qualstlst_cons($2, $4) ; }")
//
val () = symbol_close (pf | conq0uaseq)
//
} // end of [conq0uaseq_proc]

(*
coni0ndopt /* type indexes are optional */
  : /* empty */                         { $$ = s0expopt_none() ; }
  | LPAREN s0expseq RPAREN              { $$ = s0expopt_some(s0exp_list($1, $2, $3)) ; }
; /* end of [coni0ndopt] */
*)
fun coni0ndopt_proc (): void = () where {
//
val (pf | ()) = symbol_open (coni0ndopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0expopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN s0expseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = s0expopt_some(s0exp_list($1, $2, $3)) ; }")
//
val () = symbol_close (pf | coni0ndopt)
//
} // end of [coni0ndopt_proc]

(*
cona0rgopt /* arguments are optional */
  : /* empty */                         { $$ = s0expopt_none() ; }
  | OF s0exp                            { $$ = s0expopt_some($2) ; }
; /* end of [cona0rgopt] */
*)
fun cona0rgopt_proc (): void = () where {
//
val (pf | ()) = symbol_open (cona0rgopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0expopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OF s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0expopt_some($2) ; }")
//
val () = symbol_close (pf | cona0rgopt)
//
} // end of [cona0rgopt_proc]

(*
d0atcon /* data constructor */
  : conq0uaseq di0de coni0ndopt cona0rgopt
                                        { $$ = d0atcon_make($1, $2, $3, $4) ; }
; /* end of [d0atcon] */
*)
fun d0atcon_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0atcon)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! conq0uaseq di0de coni0ndopt cona0rgopt))
val () = grmrule_set_action (gr, "{ $$ = d0atcon_make($1, $2, $3, $4) ; }")
//
val () = symbol_close (pf | d0atcon)
//
} // end of [d0atcon_proc]

(*
d0atconseq /* data constructor sequence: the first bar is optional */
  : bard0atconseq                       { $$ = $1 ; }
  | d0atcon bard0atconseq               { $$ = d0atconlst_cons($1, $2) ; }
; /* end of [d0atconseq] */
*)
fun d0atconseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0atconseq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! bard0atconseq))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0atcon bard0atconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atconlst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0atconseq)
//
} // end of [d0atconseq_proc]

(*
bard0atconseq
  : /* empty */                         { $$ = d0atconlst_nil() ; }
  | BAR d0atcon bard0atconseq           { $$ = d0atconlst_cons($2, $3) ; }
; /* end of [bard0atconseq] */
*)
fun bard0atconseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (bard0atconseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0atconlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BAR d0atcon bard0atconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atconlst_cons($2, $3) ; }")
//
val bard0atcon = SYMREGseqlit (BAR, d0atcon)
val () = theGrmrulelst_merge_all (bard0atconseq, SYMREGstar (bard0atcon))
//
val () = symbol_close (pf | bard0atconseq)
//
} // end of [bard0atconseq_proc]

(*
d0atdec /* datatype declaration */
  : si0de EQ d0atconseq                 { $$ = d0atdec_make_none($1, $3) ; }
  | si0de LPAREN d0atargseq RPAREN EQ d0atconseq
                                        { $$ = d0atdec_make_some($1, $3, $4, $6) ; }
; /* end of [d0atdec] */
*)
fun d0atdec_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0atdec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de EQ d0atconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atdec_make_none($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! si0de LPAREN d0atargseq RPAREN EQ d0atconseq))
val () = grmrule_set_action (gr, "{ $$ = d0atdec_make_some($1, $3, $4, $6) ; }")
//
val () = symbol_close (pf | d0atdec)
//
} // end of [d0atdec_proc]

(*
andd0atdecseq /* additional datatype declaration sequence */
  : /* empty */                         { $$ = d0atdeclst_nil() ; }
  | AND d0atdec andd0atdecseq           { $$ = d0atdeclst_cons($2, $3) ; }
; /* end of [andd0atdecseq] */
*)
fun andd0atdecseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andd0atdecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0atdeclst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND d0atdec andd0atdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0atdeclst_cons($2, $3) ; }")
//
val andd0atdec = SYMREGseqlit (AND, d0atdec)
val () = theGrmrulelst_merge_all (andd0atdecseq, SYMREGstar (andd0atdec))
//
val () = symbol_close (pf | andd0atdecseq)
//
} // end of [andd0atdecseq_proc]

(*
s0expdefseqopt /* optional static definition sequence */
  : /* empty */                         { $$ = s0expdeflst_nil() ; }
  | WHERE s0expdef ands0expdefseq       { $$ = s0expdeflst_cons($2, $3) ; }
; /* end of [s0expdefseqopt] */
*)
fun s0expdefseqopt_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0expdefseqopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0expdeflst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! WHERE s0expdef ands0expdefseq))
val () = grmrule_set_action (gr, "{ $$ = s0expdeflst_cons($2, $3) ; }")
//
val () = symbol_close (pf | s0expdefseqopt)
//
} // end of [s0expdefseqopt_proc]

(* ****** ****** *)

(*
** exception constructor declaration
*)

(*
e0xndec
  : conq0uaseq di0de cona0rgopt         { $$ = e0xndec_make($1, $2, $3) ; }
; /* end of [e0xndec] */
*)
fun e0xndec_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (e0xndec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! conq0uaseq di0de cona0rgopt))
val () = grmrule_set_action (gr, "{ $$ = e0xndec_make($1, $2, $3) ; }")
//
val () = symbol_close (pf | e0xndec)
//
} // end of [e0xndec_proc]

(*
ande0xndecseq
  : /* empty */                         { $$ = e0xndeclst_nil() ; }
  | AND e0xndec ande0xndecseq           { $$ = e0xndeclst_cons($2, $3) ; }
; /* end of [ande0xndecseq] */
*)
fun ande0xndecseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (ande0xndecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = e0xndeclst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND e0xndec ande0xndecseq))
val () = grmrule_set_action (gr, "{ $$ = e0xndeclst_cons($2, $3) ; }")
//
val ande0xndec = SYMREGseqlit (AND, e0xndec)
val () = theGrmrulelst_merge_all (ande0xndecseq, SYMREGstar (ande0xndec))
//
val () = symbol_close (pf | ande0xndecseq)
//
} // end of [ande0xndecseq_proc]

(* ****** ****** *)

(*
** dynamic variable with optional type annotation
*)
(*
p0arg
  : pi0de                               { $$ = p0arg_make_none($1) ; }
  | pi0de COLON s0exp                   { $$ = p0arg_make_some($1, $3) ; }
; /* end of [p0arg] */
*)
fun p0arg_proc (): void = () where {
//
val (pf | ()) = symbol_open (p0arg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de))
val () = grmrule_set_action (gr, "{ $$ = p0arg_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de COLON s0exp))
val () = grmrule_set_action (gr, "{ $$ = p0arg_make_some($1, $3) ; }")
//
val () = symbol_close (pf | p0arg)
//
} // end of [p0arg_proc]

(*
p0argseq
  : /* empty */                         { $$ = p0arglst_nil() ; }
  | p0arg commap0argseq                 { $$ = p0arglst_cons($1, $2) ; }
; /* end of [p0argseq] */
*)
fun p0argseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (p0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = p0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! p0arg commap0argseq))
val () = grmrule_set_action (gr, "{ $$ = p0arglst_cons($1, $2) ; }")
//
val () = symbol_close (pf | p0argseq)
//
} // end of [p0argseq_proc]

(*
commap0argseq
  : /* empty */                         { $$ = p0arglst_nil() ; }
  | COMMA p0arg commap0argseq           { $$ = p0arglst_cons($2, $3) ; }
; /* end of [commap0argseq] */
*)
fun commap0argseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (commap0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = p0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA p0arg commap0argseq))
val () = grmrule_set_action (gr, "{ $$ = p0arglst_cons($2, $3) ; }")
//
val commap0arg = SYMREGseqlit (COMMA, p0arg)
val () = theGrmrulelst_merge_all (commap0argseq, SYMREGstar (commap0arg))
//
val () = symbol_close (pf | commap0argseq)
//
} // end of [commap0argseq_proc]

(*
d0arg
  : pi0de                               { $$ = d0arg_var($1) ; }
  | LPAREN p0argseq RPAREN              { $$ = d0arg_dyn($1, $2, $3) ; }
  | LPAREN p0argseq BAR p0argseq RPAREN { $$ = d0arg_dyn2($1, $2, $4, $5) ; }
  | LBRACE s0quaseq RBRACE              { $$ = d0arg_sta($1, $2, $3) ; }
; /* end of [d0arg] */
*)
fun d0arg_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0arg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de))
val () = grmrule_set_action (gr, "{ $$ = d0arg_var($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN p0argseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0arg_dyn($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN p0argseq BAR p0argseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0arg_dyn2($1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0quaseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0arg_sta($1, $2, $3) ; }")
//
val () = symbol_close (pf | d0arg)
//
} // end of [d0arg_proc]

(*
d0argseq
  : /* empty */                         { $$ = d0arglst_nil() ; }
  | d0arg d0argseq                      { $$ = d0arglst_cons($1, $2) ; }
; /* end of [d0argseq] */
*)
fun d0argseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0arg d0argseq))
val () = grmrule_set_action (gr, "{ $$ = d0arglst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (d0argseq, SYMREGstarlit (d0arg))
//
val () = symbol_close (pf | d0argseq)
//
} // end of [d0argseq_proc]

(* ****** ****** *)

(*
extnamopt
  : /* empty */                         { $$ = extnamopt_none() ; }
  | EQ LITERAL_string                   { $$ = extnamopt_some($2) ; }
; /* end of [extnamope] */
*)
fun extnamopt_proc (): void = () where {
//
val (pf | ()) = symbol_open (extnamopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = extnamopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! EQ LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = extnamopt_some($2) ; }")
//
val () = symbol_close (pf | extnamopt)
//
} // end of [extnamopt_proc]

(*
d0cstdec
  : di0de d0argseq colonwith s0exp extnamopt
                                        { $$ = d0cstdec_make($1, $2, $3, $4, $5) ; }
; /* end of [d0cstdec] */
*)
fun d0cstdec_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0cstdec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! di0de d0argseq colonwith s0exp extnamopt))
val () = grmrule_set_action (gr, "{ $$ = d0cstdec_make($1, $2, $3, $4, $5) ; }")
//
val () = symbol_close (pf | d0cstdec)
//
} // end of [d0cstdec_proc]

(*
andd0cstdecseq
  : /* empty */                         { $$ = d0cstdeclst_nil() ; }
  | AND d0cstdec andd0cstdecseq         { $$ = d0cstdeclst_cons($2, $3) ; }
; /* end of [andd0cstdecseq] */
*)
fun andd0cstdecseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andd0cstdecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0cstdeclst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND d0cstdec andd0cstdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0cstdeclst_cons($2, $3) ; }")
//
val andd0cstdec = SYMREGseqlit (AND, d0cstdec)
val () = theGrmrulelst_merge_all (andd0cstdecseq, SYMREGstar (andd0cstdec))
//
val () = symbol_close (pf | andd0cstdecseq)
//
} // end of [andd0cstdecseq_proc]

(* ****** ****** *)

(*
s0vararg
  : DOTDOT                              { $$ = s0vararg_one() ; }
  | DOTDOTDOT                           { $$ = s0vararg_all() ; }
  | s0argseq                            { $$ = s0vararg_seq($1) ; }
; /* end of [s0vararg] */
*)
fun s0vararg_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0vararg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTDOT))
val () = grmrule_set_action (gr, "{ $$ = s0vararg_one() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTDOTDOT))
val () = grmrule_set_action (gr, "{ $$ = s0vararg_all() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0argseq))
val () = grmrule_set_action (gr, "{ $$ = s0vararg_seq($1) ; }")
//
val () = symbol_close (pf | s0vararg)
//
} // end of [s0vararg_proc]

(*
s0exparg
  : DOTDOT                              { $$ = s0exparg_one() ; }
  | DOTDOTDOT                           { $$ = s0exparg_all() ; }
  | s0expseq1                           { $$ = s0exparg_seq($1) ; }
; /* end of [s0exparg] */
*)
fun s0exparg_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0exparg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTDOT))
val () = grmrule_set_action (gr, "{ $$ = s0exparg_one() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTDOTDOT))
val () = grmrule_set_action (gr, "{ $$ = s0exparg_all() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0expseq1))
val () = grmrule_set_action (gr, "{ $$ = s0exparg_seq($1) ; }")
//
val () = symbol_close (pf | s0exparg)
//
} // end of [s0exparg_proc]

(*
s0elop
  : DOT                                 { $$ = s0elop_make (0, $1) ; }
  | MINUSGT                             { $$ = s0elop_make (1, $1) ; }
; /* end of [s0elop] */
*)
fun s0elop_proc (): void = () where {
//
val (pf | ()) = symbol_open (s0elop)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! DOT))
val () = grmrule_set_action (gr, "{ $$ = s0elop_make (0, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! MINUSGT))
val () = grmrule_set_action (gr, "{ $$ = s0elop_make (1, $1) ; }")
//
val () = symbol_close (pf | s0elop)
//
} // end of [s0elop_proc]

(*
witht0ype
  : /* empty */                         { $$ = witht0ype_none() ; }
  | WITHPROP s0exp                      { $$ = witht0ype_prop($2) ; }
  | WITHTYPE s0exp                      { $$ = witht0ype_type($2) ; }
  | WITHVIEW s0exp                      { $$ = witht0ype_view($2) ; }
  | WITHVIEWTYPE s0exp                  { $$ = witht0ype_viewtype($2) ; }
; /* end of [withtype] */
*)
fun witht0ype_proc (): void = () where {
//
val (pf | ()) = symbol_open (witht0ype)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = witht0ype_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! WITHPROP s0exp))
val () = grmrule_set_action (gr, "{ $$ = witht0ype_prop($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! WITHTYPE s0exp))
val () = grmrule_set_action (gr, "{ $$ = witht0ype_type($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! WITHVIEW s0exp))
val () = grmrule_set_action (gr, "{ $$ = witht0ype_view($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! WITHVIEWTYPE s0exp))
val () = grmrule_set_action (gr, "{ $$ = witht0ype_viewtype($2) ; }")
//
val () = symbol_close (pf | witht0ype)
//
} // end of [witht0ype_proc]

(* ****** ****** *)

(*
** dynamic patterns
*)

(*
p0at
  : atmp0at argp0atseq                  { $$ = p0at_apps($1, $2) ; }
  | p0at COLON s0exp                    { $$ = p0at_ann($1, $3) ; }
  | pi0de AS p0at %prec PATAS           { $$ = p0at_as($1, $3) ; }
  | BANG pi0de AS p0at %prec PATAS      { $$ = p0at_refas($1, $2, $4) ; }
  | TILDE p0at %prec PATFREE            { $$ = p0at_free($1, $2) ; }
; /* end of [p0at] */
*)
fun p0at_proc (): void = () where {
//
val (pf | ()) = symbol_open (p0at)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! atmp0at argp0atseq))
val () = grmrule_set_action (gr, "{ $$ = p0at_apps($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! p0at COLON s0exp))
val () = grmrule_set_action (gr, "{ $$ = p0at_ann($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de AS p0at))
val () = grmrule_set_action (gr, "{ $$ = p0at_as($1, $3) ; }")
val () = grmrule_set_precval (gr, "%prec PATAS") 
val gr = grmrule_append ($lst_t {symbol} (tupz! BANG pi0de AS p0at))
val () = grmrule_set_action (gr, "{ $$ = p0at_refas($1, $2, $4) ; }")
val () = grmrule_set_precval (gr, "%prec PATAS") 
val gr = grmrule_append ($lst_t {symbol} (tupz! TILDE p0at))
val () = grmrule_set_action (gr, "{ $$ = p0at_free($1, $2) ; }")
val () = grmrule_set_precval (gr, "%prec PATFREE") 
//
val () = symbol_close (pf | p0at)
//
} // end of [p0at_proc]

(*
atmp0at
  : LITERAL_char                        { $$ = p0at_char($1) ; }
  | LITERAL_int                         { $$ = p0at_int($1) ; }
  | LITERAL_float                       { $$ = p0at_float($1) ; }
  | LITERAL_string                      { $$ = p0at_string($1) ; }
  | pi0de                               { $$ = p0at_ide($1) ; }
  | BANG pi0de                          { $$ = p0at_ref($1, $2) ; }
  | OP pi0de                            { $$ = p0at_opide($1, $2) ; }
  | d0ynq pi0de                         { $$ = p0at_qid($1, $2) ; }
  | LPAREN p0atseq RPAREN               { $$ = p0at_list($1, $2, $3) ; }
  | LPAREN p0atseq BAR p0atseq RPAREN   { $$ = p0at_list2($1, $2, $4, $5) ; }
  | QUOTELBRACKET p0atseq RBRACKET      { $$ = p0at_lst($1, $2, $3) ; }
  | ATLPAREN p0atseq RPAREN             { $$ = p0at_tup(0, $1, $2, $3) ; }
  | QUOTELPAREN p0atseq RPAREN          { $$ = p0at_tup(1, $1, $2, $3) ; }
  | ATLPAREN p0atseq BAR p0atseq RPAREN { $$ = p0at_tup2(0, $1, $2, $4, $5) ; }
  | QUOTELPAREN p0atseq BAR p0atseq RPAREN
                                        { $$ = p0at_tup2(1, $1, $2, $4, $5) ; }
  | ATLBRACE labp0atseq RBRACE          { $$ = p0at_rec(0, $1, $2, $3) ; }
  | QUOTELBRACE labp0atseq RBRACE       { $$ = p0at_rec(1, $1, $2, $3) ; }
  | LBRACKET s0argseq RBRACKET          { $$ = p0at_exist($1, $2, $3) ; }
; /* end of [atmp0at] */
*)
fun atmp0at_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (atmp0at)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_char))
val () = grmrule_set_action (gr, "{ $$ = p0at_char($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_int))
val () = grmrule_set_action (gr, "{ $$ = p0at_int($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_float))
val () = grmrule_set_action (gr, "{ $$ = p0at_float($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = p0at_string($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de))
val () = grmrule_set_action (gr, "{ $$ = p0at_ide($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BANG pi0de))
val () = grmrule_set_action (gr, "{ $$ = p0at_ref($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OP pi0de))
val () = grmrule_set_action (gr, "{ $$ = p0at_opide($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ynq pi0de))
val () = grmrule_set_action (gr, "{ $$ = p0at_qid($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN p0atseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0at_list($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN p0atseq BAR p0atseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0at_list2($1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELBRACKET p0atseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = p0at_lst($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN p0atseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0at_tup(0, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELPAREN p0atseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0at_tup(1, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN p0atseq BAR p0atseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0at_tup2(0, $1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELPAREN p0atseq BAR p0atseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = p0at_tup2(1, $1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLBRACE labp0atseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = p0at_rec(0, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELBRACE labp0atseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = p0at_rec(1, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACKET s0argseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = p0at_exist($1, $2, $3) ; }")
//
val () = symbol_close (pf | atmp0at)
//
} // end of [atmp0at_proc]

(*
argp0at
  : atmp0at                             { $$ = $1 ; }
  | LBRACE s0vararg RBRACE              { $$ = p0at_svararg($1, $2, $3) ; }
; /* end of [argp0at] */
*)
fun argp0at_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (argp0at)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! atmp0at))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0vararg RBRACE))
val () = grmrule_set_action (gr, "{ $$ = p0at_svararg($1, $2, $3) ; }")
//
val () = symbol_close (pf | argp0at)
//
} // end of [argp0at_proc]

(*
argp0atseq
  : /* empty */                         { $$ = p0atlst_nil() ; }
  | argp0at argp0atseq                  { $$ = p0atlst_cons($1, $2) ; }
; /* end of [argp0atseq] */
*)
fun argp0atseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (argp0atseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = p0atlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! argp0at argp0atseq))
val () = grmrule_set_action (gr, "{ $$ = p0atlst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (argp0atseq, SYMREGstarlit (argp0at))
//
val () = symbol_close (pf | argp0atseq)
//
} // end of [argp0atseq_proc]

(*
p0atseq
  : /* empty */                         { $$ = p0atlst_nil() ; }
  | p0at commap0atseq                   { $$ = p0atlst_cons($1, $2) ; }
; /* end of [p0atseq] */
*)
fun p0atseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (p0atseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = p0atlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! p0at commap0atseq))
val () = grmrule_set_action (gr, "{ $$ = p0atlst_cons($1, $2) ; }")
//
val () = symbol_close (pf | p0atseq)
//
} // end of [p0atseq_proc]

(*
commap0atseq
  : /* empty */                         { $$ = p0atlst_nil() ; }
  | COMMA p0at commap0atseq             { $$ = p0atlst_cons($2, $3) ; }
; /* end of [commap0atseq] */
*)
fun commap0atseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commap0atseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = p0atlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA p0at commap0atseq))
val () = grmrule_set_action (gr, "{ $$ = p0atlst_cons($2, $3) ; }")
//
val commap0at = SYMREGseqlit (COMMA, p0at)
val () = theGrmrulelst_merge_all (commap0atseq, SYMREGstar (commap0at))
//
val () = symbol_close (pf | commap0atseq)
//
} // end of [commap0atseq_proc]

(*
labp0atseq
  : /* empty */                         { $$ = labp0atlst_nil() ; }
  | DOTDOTDOT                           { $$ = labp0atlst_dot() ; }
  | l0ab EQ p0at commalabp0atseq        { $$ = labp0atlst_cons($1, $3, $4) ; } 
; /* end of [labp0atseq] */
*)
fun labp0atseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (labp0atseq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTDOTDOT))
val () = grmrule_set_action (gr, "{ $$ = labp0atlst_dot() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! l0ab EQ p0at commalabp0atseq))
val () = grmrule_set_action (gr, "{ $$ = labp0atlst_cons($1, $3, $4) ; } ")
//
val () = symbol_close (pf | labp0atseq)
//
} // end of [labp0atseq_proc]

(*
commalabp0atseq
  : /* empty */                         { $$ = labp0atlst_nil() ; }
  | COMMA DOTDOTDOT                     { $$ = labp0atlst_dot() ; }
  | COMMA l0ab EQ p0at commalabp0atseq  { $$ = labp0atlst_cons($2, $4, $5) ; }
; /* end of [commalabp0atseq] */
*)
fun commalabp0atseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commalabp0atseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = labp0atlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA DOTDOTDOT))
val () = grmrule_set_action (gr, "{ $$ = labp0atlst_dot() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA l0ab EQ p0at commalabp0atseq))
val () = grmrule_set_action (gr, "{ $$ = labp0atlst_cons($2, $4, $5) ; }")
//
val commal0ab = SYMREGseqlit (COMMA, l0ab)
val commal0abeq = SYMREGseq (commal0ab, SYMREGlit EQ)
val commal0abeqp0at = SYMREGseq (commal0abeq, SYMREGlit p0at)
val () = theGrmrulelst_merge_all (commalabp0atseq, SYMREGstar (commal0abeqp0at))
//
val () = symbol_close (pf | commalabp0atseq)
//
} // end of [commalabp0atseq_proc]

(* ****** ****** *)

(*
** dynamic function arguments
*)

(*
f0arg1
  : LBRACE s0quaseq RBRACE              { $$ = f0arg_sta1($1, $2, $3) ; }
  | atmp0at                             { $$ = f0arg_dyn($1) ; }
  | DOTLT s0expseq GTDOT                { $$ = f0arg_met_some($1, $2, $3) ; }
  | DOTLTGTDOT                          { $$ = f0arg_met_none($1) ; }
; /* end of [f0arg1] */
*)
fun f0arg1_proc (): void = () where {
//
val (pf | ()) = symbol_open (f0arg1)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0quaseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = f0arg_sta1($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! atmp0at))
val () = grmrule_set_action (gr, "{ $$ = f0arg_dyn($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTLT s0expseq GTDOT))
val () = grmrule_set_action (gr, "{ $$ = f0arg_met_some($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTLTGTDOT))
val () = grmrule_set_action (gr, "{ $$ = f0arg_met_none($1) ; }")
//
val () = symbol_close (pf | f0arg1)
//
} // end of [f0arg1_proc]

(*
f0arg1seq
  : /* empty */                         { $$ = f0arglst_nil() ; }
  | f0arg1 f0arg1seq                    { $$ = f0arglst_cons($1, $2) ; }
; /* end of [f0arg1seq] */
*)
fun f0arg1seq_proc (): void = () where {
//
val (pf | ()) = symbol_open (f0arg1seq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = f0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! f0arg1 f0arg1seq))
val () = grmrule_set_action (gr, "{ $$ = f0arglst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (f0arg1seq, SYMREGstarlit (f0arg1))
//
val () = symbol_close (pf | f0arg1seq)
//
} // end of [f0arg1seq_proc]

(*
f0arg2
  : LBRACE s0argseq RBRACE              { $$ = f0arg_sta2($1, $2, $3) ; }
  | atmp0at                             { $$ = f0arg_dyn($1) ; }
/*
  | DOTLT s0expseq GTDOT                { $$ = f0arg_met_some($1, $2, $3) ; }
  | DOTLTGTDOT                          { $$ = f0arg_met_none($1) ; }
*/
; /* end of [f0arg2] */
*)
fun f0arg2_proc (): void = () where {
//
val (pf | ()) = symbol_open (f0arg2)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0argseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = f0arg_sta2($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! atmp0at))
val () = grmrule_set_action (gr, "{ $$ = f0arg_dyn($1) ; }")
//
val () = symbol_close (pf | f0arg2)
//
} // end of [f0arg2_proc]

(*
f0arg2seq
  : /* empty */                         { $$ = f0arglst_nil() ; }
  | f0arg2 f0arg2seq                    { $$ = f0arglst_cons($1, $2) ; }
; /* end of [f0arg2seq] */
*)
fun f0arg2seq_proc (): void = () where {
//
val (pf | ()) = symbol_open (f0arg2seq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = f0arglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! f0arg2 f0arg2seq))
val () = grmrule_set_action (gr, "{ $$ = f0arglst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (f0arg2seq, SYMREGstarlit (f0arg2))
//
val () = symbol_close (pf | f0arg2seq)
//
} // end of [f0arg2seq_proc]

(* ****** ****** *)

(*
** dynamic expressions
*)
(*
d0exp
  : atmd0exp argd0expseq                { $$ = d0exp_apps($1, $2) ; }
  | d0exp COLON s0exp                   { $$ = d0exp_ann($1, $3) ; }
  | ifhead d0exp THEN d0exp %prec DEXPIF
                                        { $$ = d0exp_if_none($1, $2, $4) ; }
  | ifhead d0exp THEN d0exp ELSE d0exp %prec DEXPIF
                                        { $$ = d0exp_if_some($1, $2, $4, $6) ; }
  | sifhead s0exp THEN d0exp ELSE d0exp %prec DEXPIF
                                        { $$ = d0exp_sif($1, $2, $4, $6) ; }
  | casehead d0exp OF c0lauseq %prec DEXPCASE
                                        { $$ = d0exp_caseof($1, $2, $3, $4) ; }
  | scasehead s0exp OF sc0lauseq %prec DEXPCASE
                                        { $$ = d0exp_scaseof($1, $2, $3, $4) ; }
  | lamkind f0arg1seq colons0expopt funarrow d0exp %prec DEXPLAM
                                        { $$ = d0exp_lam($1, $2, $3, $4, $5 ) ; }
  | fixkind di0de f0arg1seq colons0expopt funarrow d0exp %prec DEXPLAM
                                        { $$ = d0exp_fix($1, $2, $3, $4, $5, $6) ; }
  | forhead initestpost d0exp %prec DEXPFOR
                                        { $$ = d0exp_for_itp ($1, $2, $3) ; }
  | whilehead atmd0exp d0exp %prec DEXPWHILE
                                        { $$ = d0exp_while ($1, $2, $3) ; }
  | DLRRAISE d0exp %prec DEXPRAISE      { $$ = d0exp_raise($1, $2) ; }
  | tryhead d0expsemiseq0 WITH c0lauseq %prec DEXPTRY
                                        { $$ = d0exp_trywith_seq($1, $2, $3, $4) ; }
  | d0exp WHERE LBRACE d0ecseq_dyn RBRACE
                                        { $$ = d0exp_where ($1, $4, $5) ; }
; /* end of [d0exp] */
*)
fun d0exp_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! atmd0exp argd0expseq))
val () = grmrule_set_action (gr, "{ $$ = d0exp_apps($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp COLON s0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_ann($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ifhead d0exp THEN d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_if_none($1, $2, $4) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPIF") 
val gr = grmrule_append ($lst_t {symbol} (tupz! ifhead d0exp THEN d0exp ELSE d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_if_some($1, $2, $4, $6) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPIF") 
val gr = grmrule_append ($lst_t {symbol} (tupz! sifhead s0exp THEN d0exp ELSE d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_sif($1, $2, $4, $6) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPIF") 
val gr = grmrule_append ($lst_t {symbol} (tupz! casehead d0exp OF c0lauseq))
val () = grmrule_set_action (gr, "{ $$ = d0exp_caseof($1, $2, $3, $4) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPCASE") 
val gr = grmrule_append ($lst_t {symbol} (tupz! scasehead s0exp OF sc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = d0exp_scaseof($1, $2, $3, $4) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPCASE") 
val gr = grmrule_append ($lst_t {symbol} (tupz! lamkind f0arg1seq colons0expopt funarrow d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_lam($1, $2, $3, $4, $5 ) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPLAM") 
val gr = grmrule_append ($lst_t {symbol} (tupz! fixkind di0de f0arg1seq colons0expopt funarrow d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_fix($1, $2, $3, $4, $5, $6) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPLAM") 
val gr = grmrule_append ($lst_t {symbol} (tupz! forhead initestpost d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_for_itp ($1, $2, $3) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPFOR") 
val gr = grmrule_append ($lst_t {symbol} (tupz! whilehead atmd0exp d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_while ($1, $2, $3) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPWHILE") 
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRRAISE d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_raise($1, $2) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPRAISE") 
val gr = grmrule_append ($lst_t {symbol} (tupz! tryhead d0expsemiseq0 WITH c0lauseq))
val () = grmrule_set_action (gr, "{ $$ = d0exp_trywith_seq($1, $2, $3, $4) ; }")
val () = grmrule_set_precval (gr, "%prec DEXPTRY") 
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp WHERE LBRACE d0ecseq_dyn RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_where ($1, $4, $5) ; }")
//
val () = symbol_close (pf | d0exp)
//
} // end of [d0exp_proc]

(* ****** ****** *)

(*
atmd0exp /* atomic dynamic expressions */
  : LITERAL_char                        { $$ = d0exp_char($1) ; }
  | LITERAL_float                       { $$ = d0exp_float($1) ; }
  | LITERAL_floatsp                     { $$ = d0exp_floatsp($1) ; }
  | LITERAL_int                         { $$ = d0exp_int($1) ; }
  | LITERAL_intsp                       { $$ = d0exp_intsp($1) ; }
  | LITERAL_string                      { $$ = d0exp_string($1) ; }
/* */
  | SRPFILENAME                         { $$ = d0exp_FILENAME($1) ; }
  | SRPLOCATION                         { $$ = d0exp_LOCATION($1) ; }
/* */
  | di0de                               { $$ = d0exp_ide($1) ; }
  | OP di0de                            { $$ = d0exp_opide($1, $2) ; }
  | d0ynq i0de                          { $$ = d0exp_qid($1, $2) ; }
/* */
  | i0dext                              { $$ = d0exp_idext($1) ; }
/* */
  | AMPERSAND                           { $$ = d0exp_ptrof($1) ; }
  | BREAK                               { $$ = d0exp_loopexn(0, $1) ; }
  | CONTINUE                            { $$ = d0exp_loopexn(1, $1) ; }
  | FOLDAT s0expdargseq                 { $$ = d0exp_foldat($1, $2) ; }
  | FREEAT s0expdargseq                 { $$ = d0exp_freeat($1, $2) ; }
  | VIEWAT                              { $$ = d0exp_viewat($1) ; }
  | DLRDECRYPT                          { $$ = d0exp_crypt (-1, $1) ; }
  | DLRENCRYPT                          { $$ = d0exp_crypt ( 1, $1) ; }
  | DLRDELAY                            { $$ = d0exp_delay(0, $1) ; }
  | DLRLDELAY                           { $$ = d0exp_delay(1, $1) ; }
  | DLRDYNLOAD                          { $$ = d0exp_dynload($1) ; }
  | DLREFFMASK_ALL                      { $$ = d0exp_effmask_all($1) ; }
  | DLREFFMASK_EXN                      { $$ = d0exp_effmask_exn($1) ; }
  | DLREFFMASK_NTM                      { $$ = d0exp_effmask_ntm($1) ; }
  | DLREFFMASK_REF                      { $$ = d0exp_effmask_ref($1) ; }
  | ATLBRACKET s0exp RBRACKET LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_arrinit_none ($1, $2, $5, $6) ; }
  | ATLBRACKET s0exp RBRACKET LBRACKET d0exp RBRACKET LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_arrinit_some ($1, $2, $5, $8, $9) ; }
  | DLRARRSZ s0expelt LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_arrsize ($1, $2, $3, $4, $5) ; }
  | arrqi0de d0arrind                   { $$ = d0exp_arrsub ($1, $2) ; }
  | s0elop l0ab                         { $$ = d0exp_sel_lab ($1, $2) ; }
  | s0elop LBRACKET d0arrind            { $$ = d0exp_sel_ind ($1, $3) ; }
  | tmpqi0de t1mps0expseq gtlt_t1mps0expseqseq GT
                                        { $$ = d0exp_tmpid ($1, $2, $3, $4) ; }
  | HASHLBRACKET s0exparg BAR d0exp RBRACKET
                                        { $$ = d0exp_exist ($1, $2, $3, $4, $5) ; }
  | LPAREN d0expcommaseq RPAREN         { $$ = d0exp_list ($1, $2, $3) ; }
  | LPAREN d0expcommaseq BAR d0expcommaseq RPAREN
                                        { $$ = d0exp_list2 ($1, $2, $4, $5) ; }

  | DLRLST_T s0expelt LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_lst (0, $1, $2, $3, $4, $5) ; }
  | DLRLST_VT s0expelt LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_lst (1, $1, $2, $3, $4, $5) ; }
  | QUOTELBRACKET d0expcommaseq RBRACKET
                                        { $$ = d0exp_lst_quote ($1, $2, $3) ; }

  | BEGIN d0expsemiseq0 END             { $$ = d0exp_seq ($1, $2, $3) ; }
  | LPAREN d0expsemiseq1 RPAREN         { $$ = d0exp_seq ($1, $2, $3) ; }

/* dynamic tuples */
  | ATLPAREN d0expcommaseq RPAREN       { $$ = d0exp_tup (0, $1, $2, $3) ; }
  | QUOTELPAREN d0expcommaseq RPAREN    { $$ = d0exp_tup (1, $1, $2, $3) ; }
  | DLRTUP_T LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_tup (2, $1, $3, $4) ; }
  | DLRTUP_VT LPAREN d0expcommaseq RPAREN
                                        { $$ = d0exp_tup (3, $1, $3, $4) ; }

/* dynamic tuple pairs */
  | ATLPAREN d0expcommaseq BAR d0expcommaseq RPAREN
                                        { $$ = d0exp_tup2 (0, $1, $2, $4, $5) ; }
  | QUOTELPAREN d0expcommaseq BAR d0expcommaseq RPAREN
                                        { $$ = d0exp_tup2 (1, $1, $2, $4, $5) ; }

/* dynamic records */
  | ATLBRACE labd0expseq RBRACE         { $$ = d0exp_rec (0, $1, $2, $3) ; }
  | QUOTELBRACE labd0expseq RBRACE      { $$ = d0exp_rec (1, $1, $2, $3) ; }
  | DLRREC_T LBRACE labd0expseq RBRACE  { $$ = d0exp_rec (2, $1, $3, $4) ; }
  | DLRREC_VT LBRACE labd0expseq RBRACE { $$ = d0exp_rec (3, $1, $3, $4) ; }

/*
//
// HX-2010-05-12: the OOP plan is permanently abandoned
//
    // dynamic objects
  | objkind objc0ls LBRACE m0thdecseq RBRACE
                                        { $$ = d0exp_obj($1, $2, $4, $5) ; }
*/
    /* external dynamic value */
  | DLREXTVAL LPAREN s0exp COMMA LITERAL_string RPAREN
                                        { $$ = d0exp_extval($1, $3, $5, $6) ; }
/* macsyn */
  | PERCENTLPAREN d0exp RPAREN          { $$ = d0exp_macsyn_cross($1, $2, $3) ; }
  | COMMALPAREN d0exp RPAREN            { $$ = d0exp_macsyn_decode($1, $2, $3) ; }
  | BACKQUOTELPAREN d0expsemiseq0 RPAREN
                                        { $$ = d0exp_macsyn_encode_seq($1, $2, $3) ; }
/* letexp */
  | LET d0ecseq_dyn IN d0expsemiseq0 END
                                        { $$ = d0exp_let_seq($1, $2, $3, $4, $5) ; }
/* decseq as exp */
  | LBRACE d0ecseq_dyn RBRACE           { $$ = d0exp_decseq($1, $2, $3) ; }
; /* end of [atmd0exp] */
*)
fun atmd0exp_proc (): void = () where {
//
val (pf | ()) = symbol_open (atmd0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_char))
val () = grmrule_set_action (gr, "{ $$ = d0exp_char($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_float))
val () = grmrule_set_action (gr, "{ $$ = d0exp_float($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_floatsp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_floatsp($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_int))
val () = grmrule_set_action (gr, "{ $$ = d0exp_int($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_intsp))
val () = grmrule_set_action (gr, "{ $$ = d0exp_intsp($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = d0exp_string($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPFILENAME))
val () = grmrule_set_action (gr, "{ $$ = d0exp_FILENAME($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPLOCATION))
val () = grmrule_set_action (gr, "{ $$ = d0exp_LOCATION($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! di0de))
val () = grmrule_set_action (gr, "{ $$ = d0exp_ide($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OP di0de))
val () = grmrule_set_action (gr, "{ $$ = d0exp_opide($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ynq i0de))
val () = grmrule_set_action (gr, "{ $$ = d0exp_qid($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0dext))
val () = grmrule_set_action (gr, "{ $$ = d0exp_idext($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AMPERSAND))
val () = grmrule_set_action (gr, "{ $$ = d0exp_ptrof($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BREAK))
val () = grmrule_set_action (gr, "{ $$ = d0exp_loopexn(0, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! CONTINUE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_loopexn(1, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! FOLDAT s0expdargseq))
val () = grmrule_set_action (gr, "{ $$ = d0exp_foldat($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! FREEAT s0expdargseq))
val () = grmrule_set_action (gr, "{ $$ = d0exp_freeat($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! VIEWAT))
val () = grmrule_set_action (gr, "{ $$ = d0exp_viewat($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRDECRYPT))
val () = grmrule_set_action (gr, "{ $$ = d0exp_crypt (-1, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRENCRYPT))
val () = grmrule_set_action (gr, "{ $$ = d0exp_crypt ( 1, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRDELAY))
val () = grmrule_set_action (gr, "{ $$ = d0exp_delay(0, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRLDELAY))
val () = grmrule_set_action (gr, "{ $$ = d0exp_delay(1, $1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRDYNLOAD))
val () = grmrule_set_action (gr, "{ $$ = d0exp_dynload($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREFFMASK_ALL))
val () = grmrule_set_action (gr, "{ $$ = d0exp_effmask_all($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREFFMASK_EXN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_effmask_exn($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREFFMASK_NTM))
val () = grmrule_set_action (gr, "{ $$ = d0exp_effmask_ntm($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREFFMASK_REF))
val () = grmrule_set_action (gr, "{ $$ = d0exp_effmask_ref($1) ; }")
val gr = grmrule_append ($lst_t {symbol}
  (tupz! ATLBRACKET s0exp RBRACKET LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_arrinit_none ($1, $2, $5, $6) ; }")
val gr = grmrule_append ($lst_t {symbol}
  (tupz! ATLBRACKET s0exp RBRACKET LBRACKET d0exp RBRACKET LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_arrinit_some ($1, $2, $5, $8, $9) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRARRSZ s0expelt LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_arrsize ($1, $2, $3, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! arrqi0de d0arrind))
val () = grmrule_set_action (gr, "{ $$ = d0exp_arrsub ($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0elop l0ab))
val () = grmrule_set_action (gr, "{ $$ = d0exp_sel_lab ($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0elop LBRACKET d0arrind))
val () = grmrule_set_action (gr, "{ $$ = d0exp_sel_ind ($1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! tmpqi0de t1mps0expseq gtlt_t1mps0expseqseq GT))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tmpid ($1, $2, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! HASHLBRACKET s0exparg BAR d0exp RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = d0exp_exist ($1, $2, $3, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_list ($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN d0expcommaseq BAR d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_list2 ($1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRLST_T s0expelt LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_lst (0, $1, $2, $3, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRLST_VT s0expelt LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_lst (1, $1, $2, $3, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELBRACKET d0expcommaseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = d0exp_lst_quote ($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BEGIN d0expsemiseq0 END))
val () = grmrule_set_action (gr, "{ $$ = d0exp_seq ($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN d0expsemiseq1 RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_seq ($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tup (0, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tup (1, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRTUP_T LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tup (2, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRTUP_VT LPAREN d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tup (3, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLPAREN d0expcommaseq BAR d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tup2 (0, $1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELPAREN d0expcommaseq BAR d0expcommaseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_tup2 (1, $1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ATLBRACE labd0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_rec (0, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! QUOTELBRACE labd0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_rec (1, $1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRREC_T LBRACE labd0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_rec (2, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLRREC_VT LBRACE labd0expseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_rec (3, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DLREXTVAL LPAREN s0exp COMMA LITERAL_string RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_extval($1, $3, $5, $6) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! PERCENTLPAREN d0exp RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_macsyn_cross($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMALPAREN d0exp RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_macsyn_decode($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BACKQUOTELPAREN d0expsemiseq0 RPAREN))
val () = grmrule_set_action (gr, "{ $$ = d0exp_macsyn_encode_seq($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LET d0ecseq_dyn IN d0expsemiseq0 END))
val () = grmrule_set_action (gr, "{ $$ = d0exp_let_seq($1, $2, $3, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE d0ecseq_dyn RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_decseq($1, $2, $3) ; }")
//
val () = symbol_close (pf | atmd0exp)
//
} // end of [atmd0exp_proc]

(* ****** ****** *)

(*
s0expdarg
  : LBRACE s0exparg RBRACE              { $$ = d0exp_sexparg($1, $2, $3) ; }
; /* end of [s0expdarg] */
*)
fun s0expdarg_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0expdarg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0exparg RBRACE))
val () = grmrule_set_action (gr, "{ $$ = d0exp_sexparg($1, $2, $3) ; }")
//
val () = symbol_close (pf | s0expdarg)
//
} // end of [s0expdarg_proc]

(*
s0expdargseq
  : /* empty */ %prec SEXPDARGSEQEMPTY  { $$ = d0explst_nil() ; }
  | s0expdarg s0expdargseq              { $$ = d0explst_cons($1, $2) ;  }
; /* end of [s0expdargseq] */
*)
fun s0expdargseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (s0expdargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0explst_nil() ; }")
val () = grmrule_set_precval (gr, "%prec SEXPDARGSEQEMPTY")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0expdarg s0expdargseq))
val () = grmrule_set_action (gr, "{ $$ = d0explst_cons($1, $2) ;  }")
//
val () = theGrmrulelst_merge_all (s0expdargseq, SYMREGstarlit (s0expdarg))
//
val () = symbol_close (pf | s0expdargseq)
//
} // end of [s0expdargseq_proc]

(*
argd0exp
  : atmd0exp                            { $$ = $1 ; }
  | s0expdarg                           { $$ = $1 ; }
; /* end of [argd0exp] */
*)
fun argd0exp_proc (): void = () where {
//
val (pf | ()) = symbol_open (argd0exp)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! atmd0exp))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! s0expdarg))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
// val () = theGrmrulelst_merge_all (argd0exp, SYMREGaltlit (atmd0exp, s0expdarg))
//
val () = symbol_close (pf | argd0exp)
//
} // end of [argd0exp_proc]

(*
argd0expseq
  : /* empty */                         { $$ = d0explst_nil() ; }
  | argd0exp argd0expseq                { $$ = d0explst_cons($1, $2) ; }
; /* end of [argd0expseq] */
*)
fun argd0expseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (argd0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! argd0exp argd0expseq))
val () = grmrule_set_action (gr, "{ $$ = d0explst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (argd0expseq, SYMREGstarlit (argd0exp))
//
val () = symbol_close (pf | argd0expseq)
//
} // end of [argd0expseq_proc]

(*
d0arrind
  : d0expcommaseq RBRACKET              { $$ = d0arrind_make_sing($1, $2) ; }
  | d0expcommaseq RBRACKET LBRACKET d0arrind
                                        { $$ = d0arrind_make_cons($1, $4) ; }
; /* end of [d0arrind] */
*)
fun d0arrind_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0arrind)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! d0expcommaseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = d0arrind_make_sing($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0expcommaseq RBRACKET LBRACKET d0arrind))
val () = grmrule_set_action (gr, "{ $$ = d0arrind_make_cons($1, $4) ; }")
//
val () = symbol_close (pf | d0arrind)
//
} // end of [d0arrind_proc]

(*
colons0expopt
  : /* empty */                         { $$ = s0expopt_none() ; }
  | COLON s0exp                         { $$ = s0expopt_some($2) ; }
; /* end of [colons0expopt] */
*)
fun colons0expopt_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (colons0expopt)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0expopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COLON s0exp))
val () = grmrule_set_action (gr, "{ $$ = s0expopt_some($2) ; }")
//
val () = symbol_close (pf | colons0expopt)
//
} // end of [colons0expopt_proc]

(* ****** ****** *)

(*
funarrow
  : EQGT                                { $$ = e0fftaglstopt_none() ; }
  | EQLTGT                              { $$ = e0fftaglstopt_some(e0fftaglst_nil()) ; }
  | EQLT e0fftagseq GT                  { $$ = e0fftaglstopt_some($2) ; }
; /* end of [funarrow] */
*)
fun funarrow_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (funarrow)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! EQGT))
val () = grmrule_set_action (gr, "{ $$ = e0fftaglstopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! EQLTGT))
val () = grmrule_set_action (gr, "{ $$ = e0fftaglstopt_some(e0fftaglst_nil()) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! EQLT e0fftagseq GT))
val () = grmrule_set_action (gr, "{ $$ = e0fftaglstopt_some($2) ; }")
//
val () = symbol_close (pf | funarrow)
//
} /* end of [funarrow_proc] */

(*
caseinv
  : /* empty */                         { $$ = i0nvresstate_none() ; }
  | i0nvresstate EQGT                   { $$ = $1 ; }
; /* end of [caseinv] */
*)
fun caseinv_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (caseinv)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0nvresstate_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0nvresstate EQGT))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | caseinv)
//
} // end of [caseinv_proc]

(*
ifhead
  : IF caseinv                          { $$ = ifhead_make($1, $2) ; }
; /* end of [ifhead] */
*)
fun ifhead_proc 
  (): void = () where {
//
val (pf | ()) = symbol_open (ifhead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! IF caseinv))
val () = grmrule_set_action (gr, "{ $$ = ifhead_make($1, $2) ; }")
//
val () = symbol_close (pf | ifhead)
//
} // end of [ifhead_proc]

(*
sifhead
  : SIF caseinv                         { $$ = ifhead_make($1, $2) ; }
; /* end of [sifhead] */
*)
fun sifhead_proc 
  (): void = () where {
//
val (pf | ()) = symbol_open (sifhead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! SIF caseinv))
val () = grmrule_set_action (gr, "{ $$ = ifhead_make($1, $2) ; }")
//
val () = symbol_close (pf | sifhead)
//
} // end of [sifhead_proc]

(*
casehead
  : CASE caseinv                        { $$ = casehead_make(0, $1, $2) ; }
  | CASEMINUS caseinv                   { $$ = casehead_make(-1, $1, $2) ; }
  | CASEPLUS caseinv                    { $$ = casehead_make(1, $1, $2) ; }
; /* end of [casehead] */
*)
fun casehead_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (casehead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! CASE caseinv))
val () = grmrule_set_action (gr, "{ $$ = casehead_make(0, $1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! CASEMINUS caseinv))
val () = grmrule_set_action (gr, "{ $$ = casehead_make(-1, $1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! CASEPLUS caseinv))
val () = grmrule_set_action (gr, "{ $$ = casehead_make(1, $1, $2) ; }")
//
val () = symbol_close (pf | casehead)
//
} // end of [casehead_proc]

(*
scasehead
  : SCASE caseinv                       { $$ = casehead_make(0, $1, $2) ; }
; /* end of [scasehead] */
*)
fun scasehead_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (scasehead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! SCASE caseinv))
val () = grmrule_set_action (gr, "{ $$ = casehead_make(0, $1, $2) ; }")
//
val () = symbol_close (pf | scasehead)
//
} // end of [scasehead_proc]

(*
forhead
  : FOR                                 { $$ = loophead_make_none($1) ; }
  | FORSTAR loopi0nv EQGT               { $$ = loophead_make_some($1, $2, $3) ; }
; /* end of [forhead] */
*)
fun forhead_proc (): void = () where {
//
val (pf | ()) = symbol_open (forhead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! FOR))
val () = grmrule_set_action (gr, "{ $$ = loophead_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! FORSTAR loopi0nv EQGT))
val () = grmrule_set_action (gr, "{ $$ = loophead_make_some($1, $2, $3) ; }")
//
val () = symbol_close (pf | forhead)
//
} // end of [forhead_proc]

(*
whilehead
/*
  : WHILE                               { $$ = loophead_make_none($1) ; }
*/
  : WHILESTAR loopi0nv EQGT             { $$ = loophead_make_some($1, $2, $3) ; }
; /* end of [whilehead] */
*)
fun whilehead_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (whilehead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! WHILESTAR loopi0nv EQGT))
val () = grmrule_set_action (gr, "{ $$ = loophead_make_some($1, $2, $3) ; }")
//
val () = symbol_close (pf | whilehead)
//
} // end of [whilehead]

(*
tryhead
  : TRY /* no invariant */              { $$ = tryhead_make($1) ; }
; /* end of [tryhead] */
*)
fun tryhead_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (tryhead)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! TRY))
val () = grmrule_set_action (gr, "{ $$ = tryhead_make($1) ; }")
//
val () = symbol_close (pf | tryhead)
//
} // end of [tryhead_proc]

(* ****** ****** *)

(*
** dynamic expression sequences
*)

(*
d0expcommaseq
  : /* empty */                         { $$ = d0explst_nil() ; }
  | d0exp commad0expseq                 { $$ = d0explst_cons($1, $2) ; }
; /* end of [d0expcommaseq] */
*)
fun d0expcommaseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0expcommaseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp commad0expseq))
val () = grmrule_set_action (gr, "{ $$ = d0explst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0expcommaseq)
//
} // end of [d0expcommaseq_proc]

(*
commad0expseq
  : /* empty */                         { $$ = d0explst_nil() ; }
  | COMMA d0exp commad0expseq           { $$ = d0explst_cons($2, $3) ; }
; /* end of [commad0expseq] */
*)
fun commad0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commad0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA d0exp commad0expseq))
val () = grmrule_set_action (gr, "{ $$ = d0explst_cons($2, $3) ; }")
//
val commad0exp = SYMREGseqlit (COMMA, d0exp)
val () = theGrmrulelst_merge_all (commad0expseq, SYMREGstar (commad0exp))
//
val () = symbol_close (pf | commad0expseq)
//
} // end of [commad0expseq_proc]

(*
d0expsemiseq0
  : /* empty */                         { $$ = d0explst_nil() ; }
  | d0exp                               { $$ = d0explst_sing($1) ; }
  | d0exp SEMICOLON d0expsemiseq0       { $$ = d0explst_cons($1, $3) ; }
; /* end of [d0expsemiseq0] */
*)
fun d0expsemiseq0_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0expsemiseq0)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0explst_sing($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp SEMICOLON d0expsemiseq0))
val () = grmrule_set_action (gr, "{ $$ = d0explst_cons($1, $3) ; }")
//
val () = symbol_close (pf | d0expsemiseq0)
//
} // end of [d0expsemiseq0_proc]

(*
d0expsemiseq1 // containing at least on semicolon
  : d0exp SEMICOLON d0expsemiseq0       { $$ = d0explst_cons($1, $3) ; }
; /* end of [d0expsemiseq1] */
*)
fun d0expsemiseq1_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0expsemiseq1)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp SEMICOLON d0expsemiseq0))
val () = grmrule_set_action (gr, "{ $$ = d0explst_cons($1, $3) ; }")
//
val () = symbol_close (pf | d0expsemiseq1)
//
} // end of [d0expsemiseq1_proc]

(*
labd0expseq
  : /* empty */                         { $$ = labd0explst_nil() ; }
  | l0ab EQ d0exp commalabd0expseq      { $$ = labd0explst_cons($1, $3, $4) ; }
; /* end of [labd0expseq] */
*)
fun labd0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (labd0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = labd0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! l0ab EQ d0exp commalabd0expseq))
val () = grmrule_set_action (gr, "{ $$ = labd0explst_cons($1, $3, $4) ; }")
//
val () = symbol_close (pf | labd0expseq)
//
} // end of [labd0expseq_proc]

(*
commalabd0expseq
  : /* empty */                         { $$ = labd0explst_nil() ; }
  | COMMA l0ab EQ d0exp commalabd0expseq
                                        { $$ = labd0explst_cons($2, $4, $5) ; }
; /* end of [commalabd0expseq] */
*)
fun commalabd0expseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (commalabd0expseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = labd0explst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA l0ab EQ d0exp commalabd0expseq))
val () = grmrule_set_action (gr, "{ $$ = labd0explst_cons($2, $4, $5) ; }")
//
val commal0ab = SYMREGseqlit (COMMA, l0ab)
val commal0abeq = SYMREGseq (commal0ab, SYMREGlit EQ)
val commal0abeqd0exp = SYMREGseq (commal0abeq, SYMREGlit d0exp)
val () = theGrmrulelst_merge_all (commalabd0expseq, SYMREGstar (commal0abeqd0exp))
//
val () = symbol_close (pf | commalabd0expseq)
//
} // end of [commalabd0expseq_proc]

(* ****** ****** *)

(*
m0atch
  : d0exp                               { $$ = m0atch_make_none ($1) ; }
  | d0exp AS p0at                       { $$ = m0atch_make_some ($1, $3) ; }
; /* end of [m0atch] */
*)
fun m0atch_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0atch)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp))
val () = grmrule_set_action (gr, "{ $$ = m0atch_make_none ($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0exp AS p0at))
val () = grmrule_set_action (gr, "{ $$ = m0atch_make_some ($1, $3) ; }")
//
val () = symbol_close (pf | m0atch)
//
} // end of [m0atch_proc]

(*
m0atchseq
  : m0atch andm0atchseq                 { $$ = m0atchlst_cons ($1, $2 ) ; }
; /* end of [m0atchseq] */
*)
fun m0atchseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0atchseq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! m0atch andm0atchseq))
val () = grmrule_set_action (gr, "{ $$ = m0atchlst_cons ($1, $2 ) ; }")
//
val () = symbol_close (pf | m0atchseq)
//
} // end of [m0atchseq_proc]

(*
andm0atchseq
  : /* empty */                         { $$ = m0atchlst_nil () ; }
  | AND m0atch andm0atchseq             { $$ = m0atchlst_cons ($2, $3 ) ; }
; /* end of [andm0atchseq] */
*)
fun andm0atchseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andm0atchseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = m0atchlst_nil () ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND m0atch andm0atchseq))
val () = grmrule_set_action (gr, "{ $$ = m0atchlst_cons ($2, $3 ) ; }")
//
val andm0atch = SYMREGseqlit (AND, m0atch)
val () = theGrmrulelst_merge_all (andm0atchseq, SYMREGstar (andm0atch))
//
val () = symbol_close (pf | andm0atchseq)
//
} // end of [andm0atchseq_proc]

(*
guap0at
  : p0at                                { $$ = guap0at_make_none($1) ; }
  | p0at WHEN m0atchseq                 { $$ = guap0at_make_some($1, $3) ; }
; /* end of [guap0at] */
*)
fun guap0at_proc (): void = () where {
//
val (pf | ()) = symbol_open (guap0at)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! p0at))
val () = grmrule_set_action (gr, "{ $$ = guap0at_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! p0at WHEN m0atchseq))
val () = grmrule_set_action (gr, "{ $$ = guap0at_make_some($1, $3) ; }")
//
val () = symbol_close (pf | guap0at)
//
} // end of [guap0at_proc]

(*
c0lau
  : guap0at EQGT d0exp %prec CLAUS      { $$ = c0lau_make ($1, 0, 0, $3) ; }
  | guap0at EQGTGT d0exp %prec CLAUS    { $$ = c0lau_make ($1, 1, 0, $3) ; }
  | guap0at EQSLASHEQGT d0exp %prec CLAUS
                                        { $$ = c0lau_make ($1, 0, 1, $3) ; }
  | guap0at EQSLASHEQGTGT d0exp %prec CLAUS
                                        { $$ = c0lau_make ($1, 1, 1, $3) ; }
; /* end of [c0lau] */
*)
fun c0lau_proc (): void = () where {
//
val (pf | ()) = symbol_open (c0lau)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! guap0at EQGT d0exp))
val () = grmrule_set_action (gr, "{ $$ = c0lau_make ($1, 0, 0, $3) ; }")
val () = grmrule_set_precval (gr, "%prec CLAUS") 
val gr = grmrule_append ($lst_t {symbol} (tupz! guap0at EQGTGT d0exp))
val () = grmrule_set_action (gr, "{ $$ = c0lau_make ($1, 1, 0, $3) ; }")
val () = grmrule_set_precval (gr, "%prec CLAUS") 
val gr = grmrule_append ($lst_t {symbol} (tupz! guap0at EQSLASHEQGT d0exp))
val () = grmrule_set_action (gr, "{ $$ = c0lau_make ($1, 0, 1, $3) ; }")
val () = grmrule_set_precval (gr, "%prec CLAUS") 
val gr = grmrule_append ($lst_t {symbol} (tupz! guap0at EQSLASHEQGTGT d0exp))
val () = grmrule_set_action (gr, "{ $$ = c0lau_make ($1, 1, 1, $3) ; }")
val () = grmrule_set_precval (gr, "%prec CLAUS") 
//
val () = symbol_close (pf | c0lau)
//
} // end of [c0lau_proc]

(*
c0lauseq
  : barc0lauseq                         { $$ = $1 ; }
  | c0lau barc0lauseq                   { $$ = c0laulst_cons($1, $2) ; }
; /* end of [c0lauseq] */
*)
fun c0lauseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (c0lauseq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! barc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! c0lau barc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = c0laulst_cons($1, $2) ; }")
//
val () = symbol_close (pf | c0lauseq)
//
} // end of [c0lauseq_proc]

(*
barc0lauseq
  : /* empty */ %prec BARCLAUSSEQNONE   { $$ = c0laulst_nil() ; } 
  | BAR c0lau barc0lauseq               { $$ = c0laulst_cons($2, $3) ; }
; /* end of [barc0lauseq] */
*)
fun barc0lauseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (barc0lauseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = c0laulst_nil() ; } ")
val () = grmrule_set_precval (gr, "%prec BARCLAUSSEQNONE")
val gr = grmrule_append ($lst_t {symbol} (tupz! BAR c0lau barc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = c0laulst_cons($2, $3) ; }")
//
val barc0lau = SYMREGseqlit (BAR, c0lau)
val () = theGrmrulelst_merge_all (barc0lauseq, SYMREGstar (barc0lau))
//
val () = symbol_close (pf | barc0lauseq)
//
} // end of [barc0lauseq_proc]

(*
sc0lau
  : sp0at EQGT d0exp %prec CLAUS        { $$ = sc0lau_make($1, $3) ; }
; /* end of [sc0lau] */
*)
fun sc0lau_proc (): void = () where {
//
val (pf | ()) = symbol_open (sc0lau)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! sp0at EQGT d0exp))
val () = grmrule_set_action (gr, "{ $$ = sc0lau_make($1, $3) ; }")
val () = grmrule_set_precval (gr, "%prec CLAUS") 
//
val () = symbol_close (pf | sc0lau)
//
} // end of [sc0lau_proc]

(*
sc0lauseq
  : barsc0lauseq                        { $$ = $1 ; }
  | sc0lau barsc0lauseq                 { $$ = sc0laulst_cons($1, $2) ; }
; /* end of [sc0lauseq] */
*)
fun sc0lauseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (sc0lauseq)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! barsc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! sc0lau barsc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = sc0laulst_cons($1, $2) ; }")
//
val () = symbol_close (pf | sc0lauseq)
//
} // end of [sc0lauseq_proc]

(*
barsc0lauseq
  : /* empty */ %prec BARCLAUSSEQNONE   { $$ = sc0laulst_nil() ; }
  | BAR sc0lau barsc0lauseq             { $$ = sc0laulst_cons($2, $3) ; }
; /* end of [barsc0lauseq] */
*)
fun barsc0lauseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (barsc0lauseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = sc0laulst_nil() ; } ")
val () = grmrule_set_precval (gr, "%prec BARCLAUSSEQNONE")
val gr = grmrule_append ($lst_t {symbol} (tupz! BAR sc0lau barsc0lauseq))
val () = grmrule_set_action (gr, "{ $$ = sc0laulst_cons($2, $3) ; }")
//
val barsc0lau = SYMREGseqlit (BAR, sc0lau)
val () = theGrmrulelst_merge_all (barsc0lauseq, SYMREGstar (barsc0lau))
//
val () = symbol_close (pf | barsc0lauseq)
//
} // end of [barsc0lauseq_proc]

(* ****** ****** *)

(*
** invariants
*)

(*
i0nvqua
  : /* empty */                         { $$ = s0qualstopt_none() ; }
  | LBRACE s0quaseq RBRACE              { $$ = s0qualstopt_some($2) ; }
; /* end of [i0nvqua] */
*)
fun i0nvqua_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvqua)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualstopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0quaseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = s0qualstopt_some($2) ; }")
//
val () = symbol_close (pf | i0nvqua)
//
} // end of [i0nvqua_proc]

(*
i0nvmet
  : /* empty */                         { $$ = s0explstopt_none() ; }
  | DOTLT s0expseq GTDOT                { $$ = s0explstopt_some($2) ; }
  | DOTLTGTDOT                          { $$ = s0explstopt_some(s0explst_nil()) ; }
; /* end of [i0nvmet] */ /* end of [i0nvmet] */
*)
fun i0nvmet_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvmet)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0explstopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTLT s0expseq GTDOT))
val () = grmrule_set_action (gr, "{ $$ = s0explstopt_some($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DOTLTGTDOT))
val () = grmrule_set_action (gr, "{ $$ = s0explstopt_some(s0explst_nil()) ; }")
//
val () = symbol_close (pf | i0nvmet)
//
} // end of [i0nvmet_proc]

(*
i0nvarg
  : di0de COLON                         { $$ = i0nvarg_make_none($1) ; }
  | di0de COLON s0exp                   { $$ = i0nvarg_make_some($1, $3) ; }
; /* end of [i0nvarg] */ /* end of [i0nvarg] */
*)
fun i0nvarg_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvarg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! di0de COLON))
val () = grmrule_set_action (gr, "{ $$ = i0nvarg_make_none($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! di0de COLON s0exp))
val () = grmrule_set_action (gr, "{ $$ = i0nvarg_make_some($1, $3) ; }")
//
val () = symbol_close (pf | i0nvarg)
//
} // end of [i0nvarg_proc]

(*
i0nvargseq
  : /* empty */                         { $$ = i0nvarglst_nil() ; }
  | i0nvarg commai0nvargseq             { $$ = i0nvarglst_cons($1, $2) ; }
; /* end of [i0nvargseq] */ /* end of [i0nvargseq] */
*)
fun i0nvargseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0nvarglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! i0nvarg commai0nvargseq))
val () = grmrule_set_action (gr, "{ $$ = i0nvarglst_cons($1, $2) ; }")
//
val () = symbol_close (pf | i0nvargseq)
//
} // end of [i0nvargseq_proc]

(*
commai0nvargseq
  : /* empty */                         { $$ = i0nvarglst_nil() ; }
  | COMMA i0nvarg commai0nvargseq       { $$ = i0nvarglst_cons($2, $3) ; }
; /* end of [commai0nvargseq] */ /* end of [commai0nvargseq] */
*)
fun commai0nvargseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (commai0nvargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0nvarglst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA i0nvarg commai0nvargseq))
val () = grmrule_set_action (gr, "{ $$ = i0nvarglst_cons($2, $3) ; }")
//
val commai0nvarg = SYMREGseqlit (COMMA, i0nvarg)
val () = theGrmrulelst_merge_all (commai0nvargseq, SYMREGstar (commai0nvarg))
//
val () = symbol_close (pf | commai0nvargseq)
//
} // end of [commai0nvargseq_proc]

(*
i0nvargstate
  : LPAREN i0nvargseq RPAREN            { $$ = $2 ; }
; /* end of [i0nvargstate] */ /* end of [i0nvargstate] */
*)
fun i0nvargstate_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvargstate)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN i0nvargseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = $2 ; }")
//
val () = symbol_close (pf | i0nvargstate)
//
} // end of [i0nvargstate_proc]

(*
i0nvresqua
  : /* empty */                         { $$ = s0qualstopt_none() ; }
  | LBRACKET s0quaseq RBRACKET          { $$ = s0qualstopt_some($2) ; }
; /* end of [i0nvresqua] */ /* end of [i0nvresqua] */
*)
fun i0nvresqua_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvresqua)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualstopt_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACKET s0quaseq RBRACKET))
val () = grmrule_set_action (gr, "{ $$ = s0qualstopt_some($2) ; }")
//
val () = symbol_close (pf | i0nvresqua)
//
} // end of [i0nvresqua_proc]

(*
i0nvresstate
  : /* empty */                         { $$ = i0nvresstate_none() ; }
  | COLON i0nvresqua LPAREN i0nvargseq RPAREN
                                        { $$ = i0nvresstate_some($2, $4) ; }
; /* end of [i0nvresstate] */ /* end of [i0nvresstate] */
*)
fun i0nvresstate_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0nvresstate)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0nvresstate_none() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COLON i0nvresqua LPAREN i0nvargseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = i0nvresstate_some($2, $4) ; }")
//
val () = symbol_close (pf | i0nvresstate)
//
} // end of [i0nvresstate_proc]

(*
loopi0nv
  : i0nvqua i0nvmet i0nvargstate i0nvresstate
                                        { $$ = loopi0nv_make($1, $2, $3, $4) ; }
; /* end of [loopi0nv] */ /* end of [loopi0nv] */
*)
fun loopi0nv_proc (): void = () where {
//
val (pf | ()) = symbol_open (loopi0nv)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! i0nvqua i0nvmet i0nvargstate i0nvresstate))
val () = grmrule_set_action (gr, "{ $$ = loopi0nv_make($1, $2, $3, $4) ; }")
//
val () = symbol_close (pf | loopi0nv)
//
} // end of [loopi0nv_proc]

(*
initestpost
  : LPAREN d0expcommaseq SEMICOLON d0expcommaseq SEMICOLON d0expcommaseq RPAREN
                                        { $$ = initestpost_make ($1,$2,$3,$4,$5,$6,$7) ; }
; /* end of [initestpost] */ /* end of [initestpost] */
*)
fun initestpost_proc (): void = () where {
//
val (pf | ()) = symbol_open (initestpost)
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! LPAREN d0expcommaseq SEMICOLON d0expcommaseq SEMICOLON d0expcommaseq RPAREN)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = initestpost_make ($1,$2,$3,$4,$5,$6,$7) ; }")
//
val () = symbol_close (pf | initestpost)
//
} // end of [initestpost_proc]

(* ****** ****** *)

(*
** macro declarations
*)

(*
m0arg : pi0de                           { $$ = $1 ; }
; /* end of [m0arg] */
*)
fun m0arg_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0arg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
//
val () = symbol_close (pf | m0arg)
//
} // end of [m0arg_proc]

(*
m0argseq
  : /* empty */                         { $$ = i0delst_nil() ; }
  | m0arg commam0argseq                 { $$ = i0delst_cons($1, $2) ; }
; /* end of [m0argseq] */
*)
fun m0argseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0delst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! m0arg commam0argseq))
val () = grmrule_set_action (gr, "{ $$ = i0delst_cons($1, $2) ; }")
//
val () = symbol_close (pf | m0argseq)
//
} // end of [m0argseq_proc]

(*
commam0argseq
  : /* empty */                         { $$ = i0delst_nil() ; }
  | COMMA m0arg commam0argseq           { $$ = i0delst_cons($2, $3) ; }
; /* end of [commam0argseq] */
*)
fun commam0argseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (commam0argseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = i0delst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! COMMA m0arg commam0argseq))
val () = grmrule_set_action (gr, "{ $$ = i0delst_cons($2, $3) ; }")
//
val commam0arg = SYMREGseqlit (COMMA, m0arg)
val () = theGrmrulelst_merge_all (commam0argseq, SYMREGstar (commam0arg))
//
val () = symbol_close (pf | commam0argseq)
//
} // end of [commam0argseq_proc]

(*
m0acarg
  : m0arg                               { $$ = m0acarg_one ($1) ; }
  | LPAREN m0argseq RPAREN              { $$ = m0acarg_lst ($1, $2, $3) ; }
; /* end of [m0acarg] */
*)
fun m0acarg_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0acarg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! m0arg))
val () = grmrule_set_action (gr, "{ $$ = m0acarg_one ($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LPAREN m0argseq RPAREN))
val () = grmrule_set_action (gr, "{ $$ = m0acarg_lst ($1, $2, $3) ; }")
//
val () = symbol_close (pf | m0acarg)
//
} // end of [m0acarg_proc]

(*
m0acargseq
  : /* empty */                         { $$ = m0acarglst_nil () ; }
  | m0acarg m0acargseq                  { $$ = m0acarglst_cons ($1, $2) ; }
; /* end of [m0acargseq] */
*)
fun m0acargseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0acargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = m0acarglst_nil () ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! m0acarg m0acargseq))
val () = grmrule_set_action (gr, "{ $$ = m0acarglst_cons ($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (m0acargseq, SYMREGstarlit (m0acarg))
//
val () = symbol_close (pf | m0acargseq)
//
} // end of [m0acargseq_proc]

(*
m0acdef
  : di0de m0acargseq EQ d0exp           { $$ = m0acdef_make($1, $2, $4) ; }
; /* end of [m0acdef] */
*)
fun m0acdef_proc (): void = () where {
//
val (pf | ()) = symbol_open (m0acdef)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! di0de m0acargseq EQ d0exp))
val () = grmrule_set_action (gr, "{ $$ = m0acdef_make($1, $2, $4) ; }")
//
val () = symbol_close (pf | m0acdef)
//
} // end of [m0acdef_proc]

(*
andm0acdefseq
  : /* empty */                         { $$ = m0acdeflst_nil() ; }
  | AND m0acdef andm0acdefseq           { $$ = m0acdeflst_cons($2, $3) ; }
; /* end of [andm0acdefseq] */
*)
fun andm0acdefseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andm0acdefseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = m0acdeflst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND m0acdef andm0acdefseq))
val () = grmrule_set_action (gr, "{ $$ = m0acdeflst_cons($2, $3) ; }")
//
val andm0acdef = SYMREGseqlit (AND, m0acdef)
val () = theGrmrulelst_merge_all (andm0acdefseq, SYMREGstar (andm0acdef))
//
val () = symbol_close (pf | andm0acdefseq)
//
} // end of [andm0acdefseq_proc]

(* ****** ****** *)

(*
v0aldec
  : p0at EQ d0exp witht0ype             { $$ = v0aldec_make ($1, $3, $4) ; }
; /* end of [v0aldec] */
*)
fun v0aldec_proc (): void = () where {
//
val (pf | ()) = symbol_open (v0aldec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! p0at EQ d0exp witht0ype))
val () = grmrule_set_action (gr, "{ $$ = v0aldec_make ($1, $3, $4) ; }")
//
val () = symbol_close (pf | v0aldec)
//
} // end of [v0aldec_proc]

(*
andv0aldecseq
  : /* empty */                         { $$ = v0aldeclst_nil() ; }
  | AND v0aldec andv0aldecseq           { $$ = v0aldeclst_cons($2, $3) ; }
; /* end of [andv0aldecseq] */
*)
fun andv0aldecseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andv0aldecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = v0aldeclst_nil() ; }")
val gr = grmrule_append($lst_t {symbol} (tupz! AND v0aldec andv0aldecseq))
val () = grmrule_set_action (gr, "{ $$ = v0aldeclst_cons($2, $3) ; }")
//
val andv0aldec = SYMREGseqlit (AND, v0aldec)
val () = theGrmrulelst_merge_all (andv0aldecseq, SYMREGstar (andv0aldec))
//
val () = symbol_close (pf | andv0aldecseq)
//
} // end of [andv0aldecseq_proc]

(*
f0undec
  : fi0de f0arg1seq EQ d0exp witht0ype
                                        { $$ = f0undec_make_none($1, $2, $4, $5) ; }
  | fi0de f0arg1seq colonwith s0exp EQ d0exp witht0ype
                                        { $$ = f0undec_make_some($1, $2, $3, $4, $6, $7) ; }
; /* end of [f0undec] */
*)
fun f0undec_proc (): void = () where {
//
val (pf | ()) = symbol_open (f0undec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! fi0de f0arg1seq EQ d0exp witht0ype))
val () = grmrule_set_action (gr, "{ $$ = f0undec_make_none($1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! fi0de f0arg1seq colonwith s0exp EQ d0exp witht0ype))
val () = grmrule_set_action (gr, "{ $$ = f0undec_make_some($1, $2, $3, $4, $6, $7) ; }")
//
val () = symbol_close (pf | f0undec)
//
} // end of [f0undec_proc]

(*
andf0undecseq
  : /* empty */                         { $$ = f0undeclst_nil() ; }
  | AND f0undec andf0undecseq           { $$ = f0undeclst_cons($2, $3) ; }
; /* end of [andf0undecseq] */
*)
fun andf0undecseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andf0undecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = f0undeclst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND f0undec andf0undecseq))
val () = grmrule_set_action (gr, "{ $$ = f0undeclst_cons($2, $3) ; }")
//
val andf0undec = SYMREGseqlit (AND, f0undec)
val () = theGrmrulelst_merge_all (andf0undecseq, SYMREGstar (andf0undec))
//
val () = symbol_close (pf | andf0undecseq)
//
} // end of [andf0undecseq_proc]

(*
v0arwth
  : /* empty */                         { $$ = v0arwth_none () ; }
  | WITH pi0de                          { $$ = v0arwth_some ($2) ; }
; /* end of [v0arwth] */
*)
fun v0arwth_proc (): void = () where {
//
val (pf | ()) = symbol_open (v0arwth)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = v0arwth_none () ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! WITH pi0de))
val () = grmrule_set_action (gr, "{ $$ = v0arwth_some ($2) ; }")
//
val () = symbol_close (pf | v0arwth)
//
} // end of [v0arwth_proc]

(*
v0ardec /* stack-allocated variable */
  : pi0de v0arwth EQ d0exp              { $$ = v0ardec_make_none_some(0, $1, $2, $4) ; }
  | BANG pi0de v0arwth EQ d0exp         { $$ = v0ardec_make_none_some(1, $2, $3, $5) ; }
  | pi0de COLON s0exp v0arwth           { $$ = v0ardec_make_some_none(0, $1, $3, $4) ; }
  | pi0de COLON s0exp v0arwth EQ d0exp  { $$ = v0ardec_make_some_some(0, $1, $3, $4, $6) ; }
; /* end of [v0ardec] */
*)
fun v0ardec_proc (): void = () where {
//
val (pf | ()) = symbol_open (v0ardec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de v0arwth EQ d0exp))
val () = grmrule_set_action (gr, "{ $$ = v0ardec_make_none_some(0, $1, $2, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! BANG pi0de v0arwth EQ d0exp))
val () = grmrule_set_action (gr, "{ $$ = v0ardec_make_none_some(1, $2, $3, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de COLON s0exp v0arwth))
val () = grmrule_set_action (gr, "{ $$ = v0ardec_make_some_none(0, $1, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! pi0de COLON s0exp v0arwth EQ d0exp))
val () = grmrule_set_action (gr, "{ $$ = v0ardec_make_some_some(0, $1, $3, $4, $6) ; }")
//
val () = symbol_close (pf | v0ardec)
//
} // end of [v0ardec_proc]

(*
andv0ardecseq
  : /* empty */                         { $$ = v0ardeclst_nil() ; }
  | AND v0ardec andv0ardecseq           { $$ = v0ardeclst_cons($2, $3) ; }
; /* end of [andv0ardecseq] */
*)
fun andv0ardecseq_proc (): void = () where {
//
val (pf | ()) = symbol_open (andv0ardecseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = v0ardeclst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! AND v0ardec andv0ardecseq))
val () = grmrule_set_action (gr, "{ $$ = v0ardeclst_cons($2, $3) ; }")
//
val andv0ardec = SYMREGseqlit (AND, v0ardec)
val () = theGrmrulelst_merge_all (andv0ardecseq, SYMREGstar (andv0ardec))
//
val () = symbol_close (pf | andv0ardecseq)
//
} // end of [andv0ardecseq_proc]

(*
i0mpdec
  : impqi0de f0arg2seq colons0expopt EQ d0exp
                                        { $$ = i0mpdec_make($1, $2, $3, $5) ; }
; /* end of [i0mpdec] */ /* end of [i0mpdec] */
*)
fun i0mpdec_proc (): void = () where {
//
val (pf | ()) = symbol_open (i0mpdec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! impqi0de f0arg2seq colons0expopt EQ d0exp))
val () = grmrule_set_action (gr, "{ $$ = i0mpdec_make($1, $2, $3, $5) ; }")
//
val () = symbol_close (pf | i0mpdec)
//
} // end of [i0mpdec_proc]

(* ****** ****** *)

(*
** generic dynamic declarations
*)

(*
d0ec
  : INFIX p0rec i0deseq                 { $$ = d0ec_infix($1, $2,  0, $3) ; }
  | INFIXL p0rec i0deseq                { $$ = d0ec_infix($1, $2, -1, $3) ; }
  | INFIXR p0rec i0deseq                { $$ = d0ec_infix($1, $2,  1, $3) ; }
  | PREFIX p0rec i0deseq                { $$ = d0ec_prefix($1, $2, $3) ; }
  | POSTFIX p0rec i0deseq               { $$ = d0ec_postfix($1, $2, $3) ; }
  | NONFIX i0deseq                      { $$ = d0ec_nonfix($1, $2) ; }
  | SYMINTR i0deseq                     { $$ = d0ec_symintr($1, $2) ; }
  | SRPUNDEF i0de                       { $$ = d0ec_e0xpundef($2) ; }
  | SRPDEFINE i0de e0xpopt              { $$ = d0ec_e0xpdef($2, $3) ; }
  | SRPASSERT e0xp                      { $$ = d0ec_e0xpact_assert($2) ; }
  | SRPERROR e0xp                       { $$ = d0ec_e0xpact_error($2) ; }
  | SRPPRINT e0xp                       { $$ = d0ec_e0xpact_print($2) ; }
  | SORTDEF s0rtdef ands0rtdefseq       { $$ = d0ec_srtdefs($2, $3) ; }
  | DATASORT d0atsrtdec andd0atsrtdecseq
                                        { $$ = d0ec_datsrts(0, $2, $3) ; }
  | DATAPARASORT d0atsrtdec andd0atsrtdecseq
                                        { $$ = d0ec_datsrts(1, $2, $3) ; }
  | abskind s0tacon ands0taconseq       { $$ = d0ec_stacons($1, $2, $3) ; }
  | STACST s0tacst ands0tacstseq        { $$ = d0ec_stacsts($2, $3) ; }
  | STAVAR s0tavar ands0tavarseq        { $$ = d0ec_stavars($2, $3) ; }
  | stadefkind s0expdef ands0expdefseq  { $$ = d0ec_sexpdefs($1, $2, $3) ; }
  | ASSUME s0aspdec                     { $$ = d0ec_saspdec($2) ; }
  | datakind d0atdec andd0atdecseq s0expdefseqopt
                                        { $$ = d0ec_datdecs($1, $2, $3, $4) ; }
  | EXCEPTION e0xndec ande0xndecseq     { $$ = d0ec_exndecs($1, $2, $3) ; } 
/*
// HX-2010-05-12: the OOP plan is permanently abandoned
  | clskind d0ecargseq c0lassdec s0expdefseqopt
                                        { $$ = d0ec_classdec($1, $2, $3, $4) ; }
*/
  | CLASSDEC si0de                      { $$ = d0ec_classdec_none ($1, $2) ; }
  | CLASSDEC si0de COLON s0exp          { $$ = d0ec_classdec_some ($1, $2, $4) ; }

  | OVERLOAD di0de WITH dqi0de          { $$ = d0ec_overload($1, $2, $4) ; }
  | OVERLOAD LBRACKET RBRACKET WITH dqi0de
                                        { $$ = d0ec_overload_lrbrackets($1, $2, $3, $5) ; }
  | MACDEF m0acdef andm0acdefseq        { $$ = d0ec_macdefs(0, $2, $3) ; }
  | MACDEF REC m0acdef andm0acdefseq    { $$ = d0ec_macdefs(-1/*error*/, $3, $4) ; }
  | MACRODEF m0acdef andm0acdefseq      { $$ = d0ec_macdefs(1, $2, $3) ; }
  | MACRODEF REC m0acdef andm0acdefseq  { $$ = d0ec_macdefs(2, $3, $4) ; }
  | STALOAD LITERAL_string              { $$ = d0ec_staload_none($2) ; }
  | STALOAD stai0de EQ LITERAL_string   { $$ = d0ec_staload_some($2, $4) ; }
; /* end of [d0ec] */
*)
fun d0ec_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0ec)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! INFIX p0rec i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_infix($1, $2,  0, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! INFIXL p0rec i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_infix($1, $2, -1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! INFIXR p0rec i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_infix($1, $2,  1, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! PREFIX p0rec i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_prefix($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! POSTFIX p0rec i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_postfix($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! NONFIX i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_nonfix($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SYMINTR i0deseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_symintr($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPUNDEF i0de))
val () = grmrule_set_action (gr, "{ $$ = d0ec_e0xpundef($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPDEFINE i0de e0xpopt))
val () = grmrule_set_action (gr, "{ $$ = d0ec_e0xpdef($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPASSERT e0xp))
val () = grmrule_set_action (gr, "{ $$ = d0ec_e0xpact_assert($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPERROR e0xp))
val () = grmrule_set_action (gr, "{ $$ = d0ec_e0xpact_error($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPPRINT e0xp))
val () = grmrule_set_action (gr, "{ $$ = d0ec_e0xpact_print($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SORTDEF s0rtdef ands0rtdefseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_srtdefs($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DATASORT d0atsrtdec andd0atsrtdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_datsrts(0, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DATAPARASORT d0atsrtdec andd0atsrtdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_datsrts(1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! abskind s0tacon ands0taconseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_stacons($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! STACST s0tacst ands0tacstseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_stacsts($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! STAVAR s0tavar ands0tavarseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_stavars($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! stadefkind s0expdef ands0expdefseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_sexpdefs($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! ASSUME s0aspdec))
val () = grmrule_set_action (gr, "{ $$ = d0ec_saspdec($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! datakind d0atdec andd0atdecseq s0expdefseqopt))
val () = grmrule_set_action (gr, "{ $$ = d0ec_datdecs($1, $2, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! EXCEPTION e0xndec ande0xndecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_exndecs($1, $2, $3) ; } ")
val gr = grmrule_append ($lst_t {symbol} (tupz! CLASSDEC si0de))
val () = grmrule_set_action (gr, "{ $$ = d0ec_classdec_none ($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! CLASSDEC si0de COLON s0exp))
val () = grmrule_set_action (gr, "{ $$ = d0ec_classdec_some ($1, $2, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OVERLOAD di0de WITH dqi0de))
val () = grmrule_set_action (gr, "{ $$ = d0ec_overload($1, $2, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! OVERLOAD LBRACKET RBRACKET WITH dqi0de))
val () = grmrule_set_action (gr, "{ $$ = d0ec_overload_lrbrackets($1, $2, $3, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! MACDEF m0acdef andm0acdefseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_macdefs(0, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! MACDEF REC m0acdef andm0acdefseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_macdefs(-1/*error*/, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! MACRODEF m0acdef andm0acdefseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_macdefs(1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! MACRODEF REC m0acdef andm0acdefseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_macdefs(2, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! STALOAD LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = d0ec_staload_none($2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! STALOAD stai0de EQ LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = d0ec_staload_some($2, $4) ; }")
//
val () = symbol_close (pf | d0ec)
//
} // end of [d0ec_proc]

(* ****** ****** *)

(*
d0ecarg
  : LBRACE s0quaseq RBRACE              { $$ = $2 ; }
; /* end of [d0ecarg] */
*)
fun d0ecarg_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0ecarg)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! LBRACE s0quaseq RBRACE))
val () = grmrule_set_action (gr, "{ $$ = $2 ; }")
//
val () = symbol_close (pf | d0ecarg)
//
} /* end of [d0ecarg_proc] */

(* ****** ****** *)

(*
d0ecargseq
  : /* empty */                         { $$ = s0qualstlst_nil() ; }
  | d0ecarg d0ecargseq                  { $$ = s0qualstlst_cons($1, $2) ; }
; /* end of [d0ecargseq] */
*)
fun d0ecargseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecargseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = s0qualstlst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ecarg d0ecargseq))
val () = grmrule_set_action (gr, "{ $$ = s0qualstlst_cons($1, $2) ; }")
//
val () = theGrmrulelst_merge_all (d0ecargseq, SYMREGstarlit(d0ecarg))
//
val () = symbol_close (pf | d0ecargseq)
//
} // end of [d0ecargseq_proc]

(* ****** ****** *)

(*
semicolonseq
  : /* empty */                         { ; }
  | semicolonseq SEMICOLON              { ; }
; /* end of [semicolonseq] */
*)
fun semicolonseq_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (semicolonseq)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! semicolonseq SEMICOLON))
val () = grmrule_set_action (gr, "{ ; }")
//
val () = theGrmrulelst_merge_all (semicolonseq, SYMREGstarlit(SEMICOLON))
//
val () = symbol_close (pf | semicolonseq)
//
} // end of [semicolonseq_proc]

(* ****** ****** *)

(*
d0ec_sta
  : d0ec                                { $$ = $1 ; }
  | dcstkind d0ecargseq d0cstdec andd0cstdecseq
                                        { $$ = d0ec_dcstdecs($1, $2, $3, $4) ; }
  | LITERAL_extcode                     { $$ = d0ec_extcode_sta($1) ; }
  | srpifkind guad0ec_sta               { $$ = d0ec_guadec($1, $2) ; }
  | SRPINCLUDE LITERAL_string           { $$ = d0ec_include(0/*sta*/, $2) ; }
  | LOCAL d0ecseq_sta IN d0ecseq_sta END
                                        { $$ = d0ec_local($1, $2, $4, $5) ; }
; /* end of [d0ec_sta] */
*)
fun d0ec_sta_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ec_sta)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ec))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! dcstkind d0ecargseq d0cstdec andd0cstdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_dcstdecs($1, $2, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_extcode))
val () = grmrule_set_action (gr, "{ $$ = d0ec_extcode_sta($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! srpifkind guad0ec_sta))
val () = grmrule_set_action (gr, "{ $$ = d0ec_guadec($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPINCLUDE LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = d0ec_include(0/*sta*/, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LOCAL d0ecseq_sta IN d0ecseq_sta END))
val () = grmrule_set_action (gr, "{ $$ = d0ec_local($1, $2, $4, $5) ; }")
//
val () = symbol_close (pf | d0ec_sta)
//
} /* end of [d0ec_sta] */

(* ****** ****** *)

(*
guad0ec_sta
  : e0xp srpthenopt d0ecseq_sta SRPENDIF
                                        { $$ = guad0ec_one($1, $3, $4) ; }
  | e0xp srpthenopt d0ecseq_sta SRPELSE d0ecseq_sta SRPENDIF
                                        { $$ = guad0ec_two($1, $3, $5, $6) ; }
  | e0xp srpthenopt d0ecseq_sta srpelifkind guad0ec_sta
                                        { $$ = guad0ec_cons($1, $3, $4, $5) ; }
; /* end of [guad0ec_sta] */
*)
fun guad0ec_sta_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (guad0ec_sta)
//
val gr = grmrule_append (
  $lst_t {symbol} (tupz! e0xp srpthenopt d0ecseq_sta SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_one($1, $3, $4) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_sta SRPELSE d0ecseq_sta SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_two($1, $3, $5, $6) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_sta srpelifkind guad0ec_sta)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_cons($1, $3, $4, $5) ; }")
//
val () = symbol_close (pf | guad0ec_sta)
//
} // end of [guad0ec_sta_proc]

(* ****** ****** *)

(*
d0ecseq_sta_rev /* tail-recursive */
  : /* empty */                         { $$ = d0ecllst_nil() ; }
  | d0ecseq_sta_rev d0ec_sta semicolonseq
                                        { $$ = d0ecllst_cons($1, $2) ; }
; /* end of [d0ecseq_sta_rev] */
*)
fun d0ecseq_sta_rev_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_sta_rev)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ecseq_sta_rev d0ec_sta semicolonseq))
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0ecseq_sta_rev)
//
} // end of [d0ecseq_sta_proc]

(* ****** ****** *)

(*
d0ecseq_sta
  : d0ecseq_sta_rev                     { $$ = d0ecllst_reverse($1) ; }
;
*)
fun d0ecseq_sta_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_sta)
//
val gr = grmrule_append (d0ecseq_sta_rev)
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_reverse($1) ; }")
//
val () = symbol_close (pf | d0ecseq_sta)
//
} // end of [d0ecseq_sta_proc]

(* ****** ****** *)

(*
d0ec_dyn
  : d0ec                                { $$ = $1 ; }
  | EXTERN dcstkind d0ecargseq d0cstdec andd0cstdecseq
                                        { $$ = d0ec_dcstdecs($2, $3, $4, $5) ; }
  | EXTERN TYPEDEF LITERAL_string EQ s0exp
                                        { $$ = d0ec_extype($3, $5) ; }  
  | EXTERN VAL LITERAL_string EQ d0exp  { $$ = d0ec_extval($3, $5) ; }
  | valkind v0aldec andv0aldecseq       { $$ = d0ec_valdecs($1, $2, $3) ; }
  | VAL PAR v0aldec andv0aldecseq       { $$ = d0ec_valdecs_par($3, $4) ; }
  | VAL REC v0aldec andv0aldecseq       { $$ = d0ec_valdecs_rec($3, $4) ; }
  | funkind d0ecargseq f0undec andf0undecseq       
                                        { $$ = d0ec_fundecs($1, $2, $3, $4) ; }
  | VAR v0ardec andv0ardecseq           { $$ = d0ec_vardecs($2, $3) ; }
  | IMPLEMENT decs0argseqseq i0mpdec    { $$ = d0ec_impdec($1, $2, $3) ; }
  | LOCAL d0ecseq_dyn IN d0ecseq_dyn END
                                        { $$ = d0ec_local($1, $2, $4, $5) ; }
  | LITERAL_extcode                     { $$ = d0ec_extcode_dyn($1) ; }
  | srpifkind guad0ec_dyn               { $$ = d0ec_guadec($1, $2) ; }
  | SRPINCLUDE LITERAL_string           { $$ = d0ec_include(1/*dyn*/, $2) ; }
  | DYNLOAD LITERAL_string              { $$ = d0ec_dynload($2) ; }
; /* end of [d0ec_dyn] */
*)
fun d0ec_dyn_proc (): void = () where {
//
val (pf | ()) = symbol_open (d0ec_dyn)
//
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ec))
val () = grmrule_set_action (gr, "{ $$ = $1 ; }")
val gr = grmrule_append
  ($lst_t {symbol} (tupz! EXTERN dcstkind d0ecargseq d0cstdec andd0cstdecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_dcstdecs($2, $3, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! EXTERN TYPEDEF LITERAL_string EQ s0exp))
val () = grmrule_set_action (gr, "{ $$ = d0ec_extype($3, $5) ; }  ")
val gr = grmrule_append ($lst_t {symbol} (tupz! EXTERN VAL LITERAL_string EQ d0exp))
val () = grmrule_set_action (gr, "{ $$ = d0ec_extval($3, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! valkind v0aldec andv0aldecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_valdecs($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! VAL PAR v0aldec andv0aldecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_valdecs_par($3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! VAL REC v0aldec andv0aldecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_valdecs_rec($3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! funkind d0ecargseq f0undec andf0undecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_fundecs($1, $2, $3, $4) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! VAR v0ardec andv0ardecseq))
val () = grmrule_set_action (gr, "{ $$ = d0ec_vardecs($2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! IMPLEMENT decs0argseqseq i0mpdec))
val () = grmrule_set_action (gr, "{ $$ = d0ec_impdec($1, $2, $3) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LOCAL d0ecseq_dyn IN d0ecseq_dyn END))
val () = grmrule_set_action (gr, "{ $$ = d0ec_local($1, $2, $4, $5) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! LITERAL_extcode))
val () = grmrule_set_action (gr, "{ $$ = d0ec_extcode_dyn($1) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! srpifkind guad0ec_dyn))
val () = grmrule_set_action (gr, "{ $$ = d0ec_guadec($1, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! SRPINCLUDE LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = d0ec_include(1/*dyn*/, $2) ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! DYNLOAD LITERAL_string))
val () = grmrule_set_action (gr, "{ $$ = d0ec_dynload($2) ; }")
//
val () = symbol_close (pf | d0ec_dyn)
//
} // end of [d0ec_dyn_proc]

(* ****** ****** *)

(*
guad0ec_dyn
  : e0xp srpthenopt d0ecseq_dyn SRPENDIF
                                        { $$ = guad0ec_one($1, $3, $4) ; }
  | e0xp srpthenopt d0ecseq_dyn SRPELSE d0ecseq_dyn SRPENDIF
                                        { $$ = guad0ec_two($1, $3, $5, $6) ; }
  | e0xp srpthenopt d0ecseq_dyn srpelifkind guad0ec_dyn
                                        { $$ = guad0ec_cons($1, $3, $4, $5) ; }
; /* end of [guad0ec_dyn] */
*)
fun guad0ec_dyn_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (guad0ec_dyn)
//
val gr = grmrule_append (
  $lst_t {symbol} (tupz! e0xp srpthenopt d0ecseq_dyn SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_one($1, $3, $4) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_dyn SRPELSE d0ecseq_dyn SRPENDIF)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_two($1, $3, $5, $6) ; }")
//
val gr = grmrule_append ($lst_t {symbol}
  (tupz! e0xp srpthenopt d0ecseq_dyn srpelifkind guad0ec_dyn)
) // end of [val]
val () = grmrule_set_action (gr, "{ $$ = guad0ec_cons($1, $3, $4, $5) ; }")
//
val () = symbol_close (pf | guad0ec_dyn)
//
} // end of [guad0ec_dyn_proc]

(* ****** ****** *)

(*
d0ecseq_dyn_rev /* tail-recursive */
  : /* empty */                         { $$ = d0ecllst_nil() ; }
  | d0ecseq_dyn_rev d0ec_dyn semicolonseq
                                        { $$ = d0ecllst_cons($1, $2) ; }
; /* end of [d0ecseq_dyn_rev] */
*)
fun d0ecseq_dyn_rev_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_dyn_rev)
//
val gr = grmrule_append ()
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_nil() ; }")
val gr = grmrule_append ($lst_t {symbol} (tupz! d0ecseq_dyn_rev d0ec_dyn semicolonseq))
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_cons($1, $2) ; }")
//
val () = symbol_close (pf | d0ecseq_dyn_rev)
//
} // end of [d0ecseq_dyn_proc]

(*
d0ecseq_dyn
  : d0ecseq_dyn_rev                     { $$ = d0ecllst_reverse($1) ; }
;
*)
fun d0ecseq_dyn_proc
  (): void = () where {
//
val (pf | ()) = symbol_open (d0ecseq_dyn)
//
val gr = grmrule_append (d0ecseq_dyn_rev)
val () = grmrule_set_action (gr, "{ $$ = d0ecllst_reverse($1) ; }")
//
val () = symbol_close (pf | d0ecseq_dyn)
//
} // end of [d0ecseq_dyn_proc]

(* ****** ****** *)

extern fun atsgrammar_main (): void

(* ****** ****** *)

implement
atsgrammar_main
  () = () where {
//
  val () = theStartEntry_proc ()
//
  val () = abskind_proc ()
  val () = dcstkind_proc ()
  val () = datakind_proc ()
  val () = stadefkind_proc ()
//
  val () = valkind_proc ()
  val () = funkind_proc ()
//
  val () = lamkind_proc ()
  val () = fixkind_proc ()
//
  val () = srpifkind_proc ()
  val () = srpelifkind_proc ()
  val () = srpthenopt_proc ()
//
  val () = i0de_proc ()
  val () = i0de_dlr_proc ()
  val () = i0deseq_proc ()
  val () = i0dext_proc ()
//
  val () = l0ab_proc ()
  val () = stai0de_proc ()
  val () = p0rec_proc ()
//
  val () = e0xp_proc ()
  val () = atme0xp_proc ()  
  val () = e0xpseq_proc ()
  val () = commae0xpseq_proc ()
  val () = e0xpopt_proc ()
//
  val () = e0ffid_proc ()
  val () = e0fftag_proc ()
  val () = e0fftagseq_proc ()
  val () = commae0fftagseq_proc ()
  val () = colonwith_proc ()
//
  val () = d0atsrtcon_proc ()
  val () = d0atsrtconseq_proc ()
  val () = bard0atsrtconseq_proc ()
  val () = d0atsrtdec_proc ()
  val () = andd0atsrtdecseq_proc ()
//
  val () = s0rt_proc ()
  val () = s0rtq_proc ()
  val () = s0rtid_proc ()
  val () = atms0rt_proc ()
  val () = s0rtseq_proc ()
  val () = commas0rtseq_proc ()
  val () = s0rtpol_proc ()
//
  val () = s0taq_proc ()
  val () = d0ynq_proc ()
//
  val () = si0de_proc ()
  val () = sqi0de_proc ()
  val () = commasi0deseq_proc ()
//
  val () = di0de_proc ()
  val () = dqi0de_proc ()
  val () = pi0de_proc ()
  val () = fi0de_proc ()
  val () = arri0de_proc ()
  val () = arrqi0de_proc ()
  val () = tmpi0de_proc ()
  val () = tmpqi0de_proc ()
//
  val () = colons0rtopt_proc ()
//
  val () = s0arg_proc ()
  val () = s0argseq_proc ()  
  val () = commas0argseq_proc ()  
  val () = s0argseqseq_proc ()  
//
  val () = decs0argseq_proc ()
  val () = commadecs0argseq_proc ()
  val () = decs0argseqseq_proc ()
//
  val () = sp0at_proc ()
//
  val () = s0exp_proc ()
  val () = atms0exp_proc ()
  val () = apps0exp_proc ()
  val () = exts0exp_proc ()
  val () = s0expelt_proc ()
  val () = s0arrind_proc ()
//
  val () = s0qua_proc ()
  val () = s0quaseq_proc ()
  val () = barsemis0quaseq_proc ()
//
  val () = s0rtext_proc ()
//
  val () = s0expseq_proc ()
  val () = barsemis0expseq_proc ()
  val () = commas0expseq_proc ()
  val () = s0expseq1_proc ()
  val () = labs0expseq_proc ()
  val () = commalabs0expseq_proc ()
//
  val () = t0mps0exp_proc ()
  val () = t1mps0exp_proc ()
  val () = t1mps0expseq_proc ()
  val () = commat1mps0expseq_proc ()
  val () = gtlt_t1mps0expseqseq_proc ()
//
  val () = impqi0de_proc ()
//
  val () = s0rtdef_proc ()
  val () = ands0rtdefseq_proc ()
  val () = d0atarg_proc ()
  val () = d0atargseq_proc ()
  val () = commad0atargseq_proc ()
  val () = s0tacon_proc ()
  val () = ands0taconseq_proc ()
  val () = s0tacst_proc ()
  val () = ands0tacstseq_proc ()
  val () = s0tavar_proc ()
  val () = ands0tavarseq_proc ()
  val () = s0expdef_proc ()
  val () = ands0expdefseq_proc ()
  val () = s0aspdec_proc ()
//
  val () = conq0uaseq_proc ()
  val () = coni0ndopt_proc ()
  val () = cona0rgopt_proc ()
  val () = d0atcon_proc ()
  val () = d0atconseq_proc ()
  val () = bard0atconseq_proc ()
  val () = d0atdec_proc ()
  val () = andd0atdecseq_proc ()
  val () = s0expdefseqopt_proc ()
//
  val () = e0xndec_proc ()
  val () = ande0xndecseq_proc ()
//
  val () = p0arg_proc ()
  val () = p0argseq_proc ()
  val () = commap0argseq_proc ()
  val () = d0arg_proc ()
  val () = d0argseq_proc ()
//
  val () = extnamopt_proc ()
  val () = d0cstdec_proc ()
  val () = andd0cstdecseq_proc ()
//
  val () = s0vararg_proc ()
  val () = s0exparg_proc ()
  val () = s0elop_proc ()
  val () = witht0ype_proc ()
//
  val () = p0at_proc ()
  val () = atmp0at_proc ()
  val () = argp0at_proc ()
  val () = argp0atseq_proc ()
  val () = p0atseq_proc ()
  val () = commap0atseq_proc ()
  val () = labp0atseq_proc ()
  val () = commalabp0atseq_proc ()
//
  val () = f0arg1_proc ()
  val () = f0arg1seq_proc ()
  val () = f0arg2_proc ()
  val () = f0arg2seq_proc ()
//
  val () = d0exp_proc ()
  val () = atmd0exp_proc ()
  val () = s0expdarg_proc ()
  val () = s0expdargseq_proc ()
  val () = argd0exp_proc ()
  val () = argd0expseq_proc ()
  val () = d0arrind_proc ()
  val () = colons0expopt_proc ()
  val () = funarrow_proc ()
  val () = caseinv_proc ()
  val () = ifhead_proc ()
  val () = sifhead_proc ()
  val () = casehead_proc ()
  val () = scasehead_proc ()
  val () = forhead_proc ()
  val () = whilehead_proc ()
  val () = tryhead_proc ()
//
  val () = d0expcommaseq_proc ()
  val () = commad0expseq_proc ()
  val () = d0expsemiseq0_proc ()
  val () = d0expsemiseq1_proc ()
  val () = labd0expseq_proc ()
  val () = commalabd0expseq_proc ()
//
  val () = m0atch_proc ()
  val () = m0atchseq_proc ()
  val () = andm0atchseq_proc ()
  val () = guap0at_proc ()
  val () = c0lau_proc ()
  val () = c0lauseq_proc ()
  val () = barc0lauseq_proc ()
  val () = sc0lau_proc ()
  val () = sc0lauseq_proc ()
  val () = barsc0lauseq_proc ()
//
  val () = i0nvqua_proc ()
  val () = i0nvmet_proc ()
  val () = i0nvarg_proc ()
  val () = i0nvargseq_proc ()
  val () = commai0nvargseq_proc ()
  val () = i0nvargstate_proc ()
  val () = i0nvresqua_proc ()
  val () = i0nvresstate_proc ()
  val () = loopi0nv_proc ()
  val () = initestpost_proc ()
//
  val () = m0arg_proc ()
  val () = m0argseq_proc ()
  val () = commam0argseq_proc ()
  val () = m0acarg_proc ()
  val () = m0acargseq_proc ()
  val () = m0acdef_proc ()
  val () = andm0acdefseq_proc ()
//
  val () = v0aldec_proc ()
  val () = andv0aldecseq_proc ()
  val () = f0undec_proc ()
  val () = andf0undecseq_proc ()
  val () = v0arwth_proc ()
  val () = v0ardec_proc ()
  val () = andv0ardecseq_proc ()
  val () = i0mpdec_proc ()
//
  val () = d0ec_proc ()
//
  val () = d0ecarg_proc ()
  val () = d0ecargseq_proc ()
  val () = semicolonseq_proc ()
//
  val () = d0ec_sta_proc ()
  val () = guad0ec_sta_proc ()
  val () = d0ecseq_sta_rev_proc () // reversed static declaration sequence
  val () = d0ecseq_sta_proc ()
//
  val () = d0ec_dyn_proc ()
  val () = guad0ec_dyn_proc ()
  val () = d0ecseq_dyn_rev_proc () // reversed dynamic declaration sequence
  val () = d0ecseq_dyn_proc ()
//
} // end of [atsgrammar_main]

(* ****** ****** *)

datatype outfmt =
  | OUTFMTyats of ()
  | OUTFMTyats_html of ()
  | OUTFMTdesc of ()
  | OUTFMTdesc_html of ()
  | OUTFMTnone of ()
// end of [outfmt]

fun fprint_usage
  (out: FILEref, cmd: string): void = let
  val () = fprintf (out, "The command [%s] accepts the following flags:\n", @(cmd))
  val () = fprintf (out, "  --help\n", @())
  val () = fprintf (out, "  --format=yats\n", @())
  val () = fprintf (out, "  --format=yats_html\n", @())
  val () = fprintf (out, "  --format=desc\n", @())
  val () = fprintf (out, "  --format=desc_html\n", @())
in
  // nothing
end // end of [fprint_usage]

(* ****** ****** *)

implement
main (
  argc, argv
) = () where {
//
  val cmd = "atsgrammar"
//
  var fmt: outfmt = OUTFMTyats()
  val () = loop (argc, argv, 1, fmt) where {
    fun loop {n,i:nat | i <= n} .<n-i>. (
      argc: int n, argv: &(@[string][n]), i: int i, fmt: &outfmt
    ) :<cloref1> void =
    if argc > i then let
      var arg = argv.[i]
    in
      case+ arg of
      | "--help" => let
          val () = fprint_usage (stderr_ref, cmd)
        in
          fmt := OUTFMTnone // loop exits
        end // end of [...]
      | "--format=yats" => (fmt := OUTFMTyats) // loop exits
      | "--format=yats_html" => (fmt := OUTFMTyats_html) // loop exits
      | "--format=desc" => (fmt := OUTFMTdesc) // loop exits
      | "--format=desc_html" => (fmt := OUTFMTdesc_html) // loop exits
      | _ => let
          val () = prerrf ("Warning(atsgrammar): unrecognized flag: %s\n", @(arg))
        in
          loop (argc, argv, i+1, fmt)
        end // end of [_]
    end // end of [if]
  } // end of [val]
//
  val () = atsgrammar_main ()
//
  val () = (case+ fmt of
    | OUTFMTyats () => emit_yats (stdout_ref)
    | OUTFMTyats_html () => emit_yats_html (stdout_ref)
    | OUTFMTdesc () => emit_desc (stdout_ref)
    | OUTFMTdesc_html () => emit_desc_html (stdout_ref)
    | OUTFMTnone () => ()
(*
    | _ => let
        val () = prerrf ("Warning(atsgrammar): unrecognized format.\n", @())
      in
        // nothing
      end // end of [_]
*)
  ) : void // end of [val]
//
} // end of [main]

(* ****** ****** *)

(* end of [atsgrammar_main.dats] *)
