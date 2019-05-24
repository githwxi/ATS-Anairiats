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

staload "atsgrammar.sats"

(* ****** ****** *)

assume
symbol (s:int) = '{
  symbol_name= string
, symbol_nonterm= bool
, symbol_fullname= Stropt
, symbol_tyname= tyname
, symbol_grmrulelst= grmrulelst
, symbol_stamp= int
} // end of [symbol]

extern
typedef "atsgrammar_symbol_t" = symbol

(* ****** ****** *)

implement
symbol_make
  (name) = #[0 | '{
  symbol_name= name
, symbol_nonterm= false
, symbol_fullname= stropt_none
, symbol_tyname= theTynameNone
, symbol_grmrulelst= list_nil ()
, symbol_stamp= theSymbolStampCount_getinc ()
} ] // end of [symbol_make]

implement
symbol_make_nt
  (name) = x where {
  val x = symbol_make (name)
  val () = symbol_set_nonterm (x, true)
} // end of [symbol_make_nt]

(* ****** ****** *)

implement
eq_symbol_symbol
  (x1, x2) = (x1.symbol_stamp = x2.symbol_stamp)
// end of [eq_symbol_symbol]

(* ****** ****** *)

implement
symbol_get_name (x) = x.symbol_name

implement
symbol_get_nonterm (x) = x.symbol_nonterm

implement
symbol_get_fullname (x) = x.symbol_fullname

implement
symbol_get_tyname (x) = x.symbol_tyname

implement
symbol_get_grmrulelst (x) = x.symbol_grmrulelst

(* ****** ****** *)

implement
fprint_symbol
  (out, sym) = let
  val () = fprint (out, sym.symbol_name)
  val () = fprint (out, "(")
  val () = fprint (out, sym.symbol_stamp)
  val () = fprint (out, ")")
in
  // nothing
end // end of [fprint_symbol]

implement print_symbol (sym) = fprint_symbol (stdout_ref, sym)
implement prerr_symbol (sym) = fprint_symbol (stderr_ref, sym)

(* ****** ****** *)

%{$
//
ats_void_type
atsgrammar_symbol_set_nonterm
  (ats_ptr_type sym, ats_bool_type nt) {
  ((atsgrammar_symbol_t)sym)->atslab_symbol_nonterm = nt ;
  return ;
} /* end of [atsgrammar_symbol_set_nonterm] */
//
ats_void_type
atsgrammar_symbol_set_fullname
  (ats_ptr_type sym, ats_ptr_type fname) {
  ((atsgrammar_symbol_t)sym)->atslab_symbol_fullname = fname ;
  return ;
} /* end of [atsgrammar_symbol_set_fullname] */
//
ats_void_type
atsgrammar_symbol_set_tyname
  (ats_ptr_type sym, ats_ptr_type tname) {
  ((atsgrammar_symbol_t)sym)->atslab_symbol_tyname = tname ;
  return ;
} /* end of [atsgrammar_symbol_set_tyname] */
//
ats_void_type
atsgrammar_symbol_set_grmrulelst
  (ats_ptr_type sym, ats_ptr_type grlst) {
  ((atsgrammar_symbol_t)sym)->atslab_symbol_grmrulelst = grlst ;
   return ;
} /* end of [atsgrammar_symbol_set_grmrulelst] */
//
%} // end of [%{$]

(* ****** ****** *)

(* end of [atsgrammar_symbol.sats] *)
