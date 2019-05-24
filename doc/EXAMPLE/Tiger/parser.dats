(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

//
// atscc -IATS PARCOMB ...
//

(* ****** ****** *)

%{^
#include "libc/CATS/stdio.cats"
%} // end of [%{^]

(* ****** ****** *)

staload "error.sats"

staload "PARCOMB/posloc.sats"
staload "PARCOMB/tokenize.sats"

staload "fixity.sats"

(* ****** ****** *)

staload "PARCOMB/parcomb.sats" ;
staload _(*anonymous*) = "PARCOMB/parcomb.dats" ;

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "absyn.sats"
staload "symbol.sats"

(* ****** ****** *)

staload "parser.sats"

(* ****** ****** *)

infix (|| + 1) wth
infixl (&& + 2) <<; infixr (&& + 1) >>
postfix ^* ^+ ^?

(* ****** ****** *)

typedef P (a: t@ype) = parser_t (a, token)
typedef LP (a: t@ype) = lazy (parser_t (a, token))

(* ****** ****** *)

val anytoken = any_parser<token> ()
val anyopttoken = anyopt_parser<token> ()

//

fn litchar (c0: char): P token =
  anytoken \sat (lam (tok: token): bool =<cloref>
    case+ tok.token_node of TOKsingleton c => c0 = c | _ => false
  )

val LPAREN = litchar '\('
val RPAREN = litchar ')'
val LBRACKET = litchar '\['
val RBRACKET = litchar ']'
val LBRACE = litchar '\{'
val RBRACE = litchar '}'

val COMMA = litchar ','
val SEMICOLON = litchar ';'

//

fn litident (name0: string): P token =
  anytoken \sat (lam (tok: token): bool =<cloref>
    case+ tok.token_node of TOKide name => name0 = name | _ => false
  )
// end of [litident]

val ARRAY = litident "array"
val BREAK = litident "break"
val CONTINUE = litident "continue"
val DO = litident "do"
val ELSE = litident "else"
val END = litident "end"
val FOR = litident "for"
val FUNCTION = litident "function" 
val IF = litident "if"
val IN = litident "in"
val LET = litident "let"
val NIL = litident "nil"
val OF = litident "of"
val TO = litident "to"
val VAR = litident "var"
val THEN = litident "then"
val TYPE = litident "type"
val WHILE = litident "while"

val COLON = litident ":"
val DOT = litident "."

val UMINUS = litident "~"

val PLUS = litident "+"
val MINUS = litident "-"
val TIMES = litident "*"
val DIVIDE = litident "/"

val EQ = litident "="
val NEQ = litident "<>"
val COLONEQ = litident ":="

val GTEQ = litident ">="
val GT = litident ">"
val LTEQ = litident "<="
val LT = litident "<"

val AMP = litident "&"
val BAR = litident "|"

(* ****** ****** *)

local

val arrpsz = $arrpsz{string}(
  "array"
, "break"
, "do"
, "else"
, "end"
, "for"
, "function"
, "if"
, "in"
, "let"
, "nil"
, "of"
, "then"
, "to"
, "type"
, "var"
, "while"
, "|", "&"
, ".", ":"
, "+", "-", "/", "*"
, "=",":="
, ">=", ">", "<=", "<", "<>"
) // end of [arrpsz]

in // in of [local]

val theKeywordArrSz = arrpsz.3
val theKeywordArray = array_make_arrpsz{string}(arrpsz)

end // end of [local]

(* ****** ****** *)

fn isKeyword
  (name0: string):<> bool = ans where {
  var i: Nat = 0 and ans: bool = false
  val () = $effmask_all (
    while (i < theKeywordArrSz) let
      val name = theKeywordArray[i] in
      if name0 = name then (ans := true; break); i := i+1
    end // end of [while]
  ) // end of [val]
} (* end of [isKeyword] *)

(* ****** ****** *)

val p_ident: P token =
  anytoken \sat (lam (tok: token): bool =<fun> case+ tok.token_node of
    | TOKide name => if isKeyword name then false else true | _ => false
  )
// end of [p_ident]

val p_number: P token =
  anytoken \sat (lam (tok: token): bool =<fun>
    case+ tok.token_node of TOKint _ => true | _ => false
  )
// end of [p_number]

val p_string: P token =
  anytoken \sat (lam (tok: token): bool =<fun>
    case+ tok.token_node of TOKstr _ => true | _ => false
  )
// end of [p_string]

(* ****** ****** *)

local

#define PLUS_precedence 40
#define MINUS_precedence 40

#define TIMES_precedence 60
#define DIVIDE_precedence 60

#define UMINUS_precedence 80

#define EQ_precedence 20
#define NEQ_precedence 20

#define GTEQ_precedence 20
#define GT_precedence 20
#define LTEQ_precedence 20
#define LT_precedence 20

#define AMP_precedence 9
#define BAR_precedence 8

#define L LeftAssoc; #define R RightAssoc; #define N NonAssoc

in // in of [local]

val p_oper: P (fixopr exp) = begin
  UMINUS wth (
    lam (tok: token) =<fun> f_uminus (tok, UMINUS_precedence)
  ) ||
  PLUS wth (
    lam (tok: token) =<fun> f_infix (tok, L, PLUS_precedence, PlusOp)
  ) ||
  MINUS wth (
    lam (tok: token) =<fun> f_infix (tok, L, MINUS_precedence, MinusOp)
  ) ||
  TIMES wth (
    lam (tok: token) =<fun> f_infix (tok, L, TIMES_precedence, TimesOp)
  ) ||
  DIVIDE wth (
    lam (tok: token) =<fun> f_infix (tok, L, DIVIDE_precedence, DivideOp)
  ) ||
  GTEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, GTEQ_precedence, GeOp)
  ) ||
  GT wth (
    lam (tok: token) =<fun> f_infix (tok, N, GT_precedence, GtOp)
  ) ||
  LTEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, LTEQ_precedence, LeOp)
  ) ||
  LT wth (
    lam (tok: token) =<fun> f_infix (tok, N, LT_precedence, LtOp)
  ) ||
  EQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, EQ_precedence, EqOp)
  ) ||
  NEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, NEQ_precedence, NeqOp)
  ) ||
  AMP wth (
    lam (tok: token) =<fun> f_infix (tok, L, AMP_precedence, AndOp)
  ) ||
  BAR wth (
    lam (tok: token) =<fun> f_infix (tok, L, BAR_precedence, OrOp)
  )
end where {
  fn f_uminus (tok: token, prec: int):<> fixopr exp = let
    val tok_loc = tok.token_loc
    val f = lam (e: exp): exp =<cloref> let
      val e_0 = IntExp_make (tok_loc, 0)
      val loc = location_combine (tok_loc, e.exp_loc)
    in
      OpExp_make (loc, e_0, MinusOp, e)
    end // end of [f]
  in
    Prefix (tok.token_loc, prec, f)
  end // end of [f_minus]
  fn f_infix
    (tok: token, assoc: assoc, prec: int, oper: oper)
    :<> fixopr exp = let
    val f = lam (e1: exp, e2: exp): exp =<cloref> let
      val loc = location_combine (e1.exp_loc, e2.exp_loc) in
      OpExp_make (loc, e1, oper, e2)
    end // end of [f]
  in
    Infix (tok.token_loc, prec, assoc, f)
  end // end of [f_infix]
}

end // end of [local]
  
(* ****** ****** *)

fn symbol_make_token
  (tok: token):<> sym = let
  val- TOKide name = tok.token_node
in
  $effmask_all (symbol_make_name name)
end // end of [symbol_make_token]

(* ****** ****** *)

val p_SimpleVar: P v1ar = 
  p_ident wth (lam (tok: token): v1ar =<fun> let
    val loc = tok.token_loc; val sym = symbol_make_token tok in
    SimpleVar_make (loc, sym)
  end)
// end of [p_SimpleVar]

(* ****** ****** *)

val p_BreakExp = BREAK wth f_break where {
  fn f_break (tok: token):<> exp = BreakExp_make (tok.token_loc)
} // end of [p_BreakExp]

val p_ContinueExp = CONTINUE wth f_continue where {
  fn f_continue (tok: token):<> exp = ContinueExp_make (tok.token_loc)
} // end of [p_ContinueExp]

(* ****** ****** *)

val p_fieldtyp: P fieldtyp = begin
  seq2wth_parser_fun (p_ident, COLON >> p_ident, f) 
end where {
  fn f (tok1: token, tok2: token):<> fieldtyp = let
    val loc1 = tok1.token_loc and loc2 = tok2.token_loc
    val loc12 = location_combine (loc1, loc2)
    val- TOKide name1 = tok1.token_node
    val- TOKide name2 = tok2.token_node
    val sym1 = $effmask_all (symbol_make_name name1)
    val sym2 = $effmask_all (symbol_make_name name2)
  in
    fieldtyp_make (loc12, sym1, sym2)
  end // end of [f]
} // end of [val]

val p_fieldtyplst: P fieldtyplst = repeat0_sep_parser (p_fieldtyp, COMMA)

(* ****** ****** *)

typedef v1arc = v1ar -<cloref> v1ar

typedef typdeclst1 = List1 (typdec)
typedef fundeclst1 = List1 (fundec)

(* ****** ****** *)

val
rec lp_exp: LP exp = $delay ( // ordering is significant!
  lzeta lp_AssignExp ||
  lzeta lp_ArrayExp ||
  lzeta lp_RecordExp ||
  lzeta lp_IfExp ||
  lzeta lp_WhileExp ||
  lzeta lp_ForExp ||
  p_BreakExp || p_ContinueExp ||
  lzeta lp_LetExp ||
  lzeta lp_exp1
) // end of [lp_exp]

(* ****** ****** *)

and lp_explst: LP explst = $delay (
  repeat0_sep_parser<exp,token> (!lp_exp, COMMA)
) // end of [lp_explst]

and lp_expseq: LP explst = $delay (
  repeat0_sep_parser<exp,token> (!lp_exp, SEMICOLON)
) // end of [lp_expseq]

(* ****** ****** *)

and lp_var: LP v1ar = $delay (
  seq2wth_parser_fun
    (p_SimpleVar, lzeta lp_varc, f) where {
    val f = lam (v: v1ar, vc: v1arc) =<fun> vc (v)
  }
) // end of [lp_var]

and lp_varc: LP v1arc = $delay (
  seq2wth_parser_fun
    (DOT >> p_ident, lzeta lp_varc, f_field) ||
  seq3wth_parser_fun
    (LBRACKET >> !lp_exp, RBRACKET, lzeta lp_varc, f_subscript) ||
  return (lam (v: v1ar) =<cloref> v)
) where {
  fn f_field
    (tk_id: token, vc: v1arc):<> v1arc = lam (v0) => let
    val loc = location_combine (v0.v1ar_loc, tk_id.token_loc)
    val sym_id = symbol_make_token tk_id
    val v1 = FieldVar_make (loc, v0, sym_id)
  in
    vc (v1)
  end // end of [f_field]
  fn f_subscript
    (ind: exp, tk_rb: token, vc: v1arc):<> v1arc = lam (v0) => let
    val loc = location_combine (v0.v1ar_loc, tk_rb.token_loc)
    val v1 = SubscriptVar_make (loc, v0, ind)
  in
    vc (v1)
  end // end of [f_subscript]
} // end of [lp_varc]

(* ****** ****** *)

and lp_exp0: LP exp = $delay ( // ordering is significant!
  NIL wth f_nil ||
  p_number wth f_number ||
  p_string wth f_string ||
  seq4wth_parser_fun
    (p_ident, LPAREN, !lp_explst, RPAREN, f_callexp) ||
  !lp_var wth f_varexp ||
  seq3wth_parser_fun (LPAREN, !lp_expseq, RPAREN, f_seq)
) where {
  fn f_nil (tok: token):<> exp = NilExp_make (tok.token_loc)
  fn f_number (tok: token):<> exp = let
    val loc = tok.token_loc; val- TOKint int = tok.token_node
  in
    IntExp_make (loc, int)
  end // end of [f_string]
  fn f_string (tok: token):<> exp = let
    val loc = tok.token_loc; val- TOKstr str = tok.token_node
  in
    StringExp_make (loc, str)
  end // end of [f_string]
  fn f_varexp (v: v1ar):<> exp = VarExp_make (v.v1ar_loc, v)
  fn f_callexp (
      tk_id: token
    , tk_beg: token, arg: explst, tk_end: token
    ) :<> exp = let
    val loc = location_combine (tk_id.token_loc, tk_end.token_loc)
    val sym_id = symbol_make_token tk_id
  in
    CallExp_make (loc, sym_id, arg)
  end // end of [f_callexp]
  fn f_seq (tk_beg: token, es: explst, tk_end: token):<> exp = begin
    case+ es of
    | list_cons (e, list_nil ()) => e | _ => let
        val loc = location_combine (tk_beg.token_loc, tk_end.token_loc)
      in
        SeqExp_make (loc, es)
      end // end of [_]
  end // end of [f_seq]
  fn f_seq0 (tk_beg: token, tk_end: token):<> exp =
    f_seq (tk_beg, list_nil (), tk_end)
} // end of [lp_exp0]

(* ****** ****** *)

and lp_operexp0: LP (fixitm exp) = $delay (
  p_oper wth f_oper || !lp_exp0 wth f_exp0
) where {
  fn f_oper (opr: fixopr exp):<> fixitm exp =
    FIXITMopr opr
  fn f_exp0 (exp: exp):<> fixitm exp = FIXITMatm exp
} // end of [lp_operexp0]

(* ****** ****** *)

and lp_exp1: LP (exp) = $delay (
  (repeat1_parser !lp_operexp0) wth f
) where {
  typedef T = fixitm exp
  fn err (loc: loc): exp = begin
    prerr_location loc;
    prerr ": exit(TIGER)";
    prerr ": parsing failure: unresolved fixity";
    prerr_newline ();
    abort {exp} (1)
  end // end [err]

  fn fixitm_loc_get
    (itm: fixitm exp):<> loc = case+ itm of
    | FIXITMatm exp => exp.exp_loc
    | FIXITMopr opr => fixopr_loc_get opr
  // end of [fixitm_loc_get]

  fn f (itms: List1 T):<> exp = let
    val res = $effmask_all (fixity_resolve itms)
  in
    case+ res of
    | ~Some_vt e => e | ~None_vt () => let
        val+ list_cons (itm0, itms) = itms
        val loc0 = fixitm_loc_get (itm0)
        val loc01 = case+ itms of
          | list_cons _ => let
              val itm1 = list_last<T> (itms)
              val loc1 = fixitm_loc_get itm1
            in
              location_combine (loc0, loc1)
            end // end of [list_cons]
          | list_nil () => loc0
        // end of [val]
      in
        $effmask_all (err loc01) // report the error right here!
      end // end of [None_vt]
  end // end of [f]
} // end of [lp_exp1]

(* ****** ****** *)

and lp_fieldexp: LP fieldexp = $delay (
  seq2wth_parser_fun (p_ident, EQ >> !lp_exp, f)
) where {
  fn f (tk_id: token, e: exp):<> fieldexp = let
    val loc = location_combine (tk_id.token_loc, e.exp_loc)
    val sym_id = symbol_make_token (tk_id)
  in
    fieldexp_make (loc, sym_id, e)
  end // end of [f]
} // end of [lp_fieldexp]

and lp_fieldexplst: LP fieldexplst =
  $delay (repeat0_sep_parser (!lp_fieldexp, COMMA))

and lp_RecordExp: LP exp = $delay (seq3wth_parser_fun
  (p_ident, LBRACE >> !lp_fieldexplst, RBRACE, f_RecordExp)
) where {
  fn f_RecordExp
    (tk_id: token, fes: fieldexplst, tk_end: token):<> exp = let
    val id_loc = tk_id.token_loc
    val loc = location_combine (id_loc, tk_end.token_loc)
    val sym_id = symbol_make_token (tk_id)
    val t_rec = NameTyp_make (id_loc, sym_id)
  in
    RecordExp_make (loc, fes, t_rec)
  end // end of [f]
} // end of [lp_RecordExp]

(* ****** ****** *)

and lp_AssignExp: LP exp = $delay (
  seq2wth_parser_fun
    (!lp_var, COLONEQ >> !lp_exp, f) where {
    fn f (v: v1ar, e: exp):<> exp = let
      val loc = location_combine (v.v1ar_loc, e.exp_loc)
    in
      AssignExp_make (loc, v, e)
    end // end of [f]
  }
) // end of [lp_AssignExp]

(* ****** ****** *)

and lp_ArrayExp: LP exp = $delay (seq3wth_parser_fun
  (p_ident, LBRACKET >> !lp_exp << RBRACKET, OF >> !lp_exp, f_ArrayExp)
) where {
  fn f_ArrayExp
    (tk_id: token, e_size: exp, e_init: exp):<> exp = let
    val id_loc = tk_id.token_loc
    val loc = location_combine (id_loc, e_init.exp_loc)
    val sym_id = symbol_make_token (tk_id)
    val t_elt = NameTyp_make (id_loc, sym_id)
  in
    ArrayExp_make (loc, t_elt, e_size, e_init)
  end // end of [f_ArrayExp]
} (* end of [lp_ArrayExp] *)

(* ****** ****** *)

and lp_IfExp: LP exp = $delay (seq4wth_parser_fun
  (IF, !lp_exp, THEN >> !lp_exp, (ELSE >> !lp_exp)^?, f_IfExp)
) where {
  fn f_IfExp
    (tk_if: token, e1: exp, e2: exp, oe3: expopt):<> exp = let
    val loc = case+ oe3 of
    | Some e3 => location_combine (tk_if.token_loc, e3.exp_loc)
    | None () => location_combine (tk_if.token_loc, e2.exp_loc)
  in
    IfExp_make (loc, e1, e2, oe3)
  end // end of [f_IfExp]
} // end of [lp_IfExp]

(* ****** ****** *)

and lp_WhileExp: LP exp = $delay (
  seq3wth_parser_fun
    (WHILE, !lp_exp, DO >> !lp_exp, f_WhileExp)
) where {
  fn f_WhileExp
    (tk_while: token, e_test: exp, e_body: exp):<> exp = let
    val loc = location_combine (tk_while.token_loc, e_body.exp_loc)
  in
    WhileExp_make (loc, e_test, e_body)
  end // end of [f_WhileExp]
} // end of [lp_WhileExp]

(* ****** ****** *)

and lp_ForExp: LP exp = $delay (seq5wth_parser_fun (
    FOR
  , p_ident
  , COLONEQ >> !lp_exp
  , TO >> !lp_exp
  , DO >> !lp_exp, f_ForExp
  )
) where {
  fn f_ForExp (
      tk_for: token
    , tk_id: token, e_lo: exp, e_hi: exp, e_body: exp
    ) :<> exp = let
    val loc = location_combine (tk_for.token_loc, e_body.exp_loc)
    val sym_id = symbol_make_token tk_id
  in
    ForExp_make (loc, sym_id, e_lo, e_hi, e_body)
  end // end of [f_WhileExp]
} // end of [lp_ForExp]

(* ****** ****** *)

and lp_LetExp: LP exp = $delay (
  seq5wth_parser_fun (LET, !lp_declst, IN, !lp_expseq, END, f_LetExp)
) where {
  fn f_LetExp (
      tk_let: token
    , ds: declst, tk_in: token
    , es: explst, tk_end: token
    ) :<> exp = let
    val loc = location_combine (tk_let.token_loc, tk_end.token_loc)
    val e_body = (case+ es of
      | list_cons (e, list_nil ()) => e | _ => let
          val loc = location_combine (tk_in.token_loc, tk_end.token_loc)
        in
          SeqExp_make (loc, es)
        end // end of [_]
    ) : exp
  in
    LetExp_make (loc, ds, e_body)
  end // end of [f_LetExp]
} // end of [lp_LetExp]

(* ****** ****** *)

and lp_dec: LP dec = $delay (
  lzeta lp_vardec ||
  lzeta lp_typdeclst1 wth f_typdeclst ||
  lzeta lp_fundeclst1 wth f_fundeclst
) where {
  fn f_typdeclst (tds0: typdeclst1):<> dec = let
    val+ list_cons (td, tds1) = tds0
    val loc0 = td.typdec_loc
    val loc01 = (case+ tds1 of
      | list_cons _ => let
          val td1 = list_last<typdec> (tds1)
        in
          location_combine (loc0, td1.typdec_loc)
        end // end of [list_cons]
      | list_nil () => loc0
    ) : loc
  in
    TypeDec_make (loc01, tds0)
  end // end of [f_typdeclst]
  fn f_fundeclst (fds0: fundeclst1):<> dec = let
    val+ list_cons (fd, fds1) = fds0
    val loc0 = fd.fundec_loc
    val loc01 = (case+ fds1 of
      | list_cons _ => let
          val fd1 = list_last<fundec> (fds1)
        in
          location_combine (loc0, fd1.fundec_loc)
        end // end of [list_cons]
      | list_nil () => loc0
    ) : loc
  in
    FunctionDec_make (loc01, fds0)
  end // end of [f_typdeclst]
} // end of [lp_dec]

and lp_declst: LP declst = $delay (repeat0_parser !lp_dec)

(* ****** ****** *)

and lp_vardec: LP dec = $delay (seq4wth_parser_fun
  (VAR, p_ident, (COLON >> p_ident)^?, COLONEQ >> !lp_exp, f_VarDec)
) where {
  fn f_VarDec (
      tk_var: token
    , tk_id: token
    , tokopt_id: tokenopt
    , e_init: exp
    ) :<> dec = let
    val loc = location_combine (tk_var.token_loc, e_init.exp_loc)
    val name_id = symbol_make_token tk_id
    val otp = (case+ tokopt_id of
      | Some tk_id => let
          val loc = tk_id.token_loc
          val- TOKide name = tk_id.token_node
          val sym = $effmask_all (symbol_make_name name)
        in
          Some (NameTyp_make (loc, sym))
        end // end of [Some]
      | None () => None ()
    ) : typopt
  in
    VarDec_make (loc, name_id, otp, e_init)
  end // end of [f_VarDec]
} // end of [lp_vardec]

(* ****** ****** *)

and lp_typ: LP typ = $delay (
  p_ident wth f_ident ||
  seq3wth_parser_fun (LBRACE, p_fieldtyplst, RBRACE, f_record) ||
  seq3wth_parser_fun (ARRAY, OF, p_ident, f_array)
) where {
  fn f_ident (tk_id: token):<> typ = let
    val loc = tk_id.token_loc
    val sym_id = symbol_make_token tk_id
  in
    NameTyp_make (loc, sym_id)
  end // end of [f_ident]

  fn f_record
    (tk_beg: token, fts: fieldtyplst, tk_end: token):<> typ = let
    val loc = location_combine (tk_beg.token_loc, tk_end.token_loc)
  in
    RecordTyp_make (loc, fts)
  end // end of [f_record]
  fn f_array
    (tk_array: token, tk_of: token, tk_id: token):<> typ = let
    val loc = tk_id.token_loc
    val sym_id = symbol_make_token tk_id
  in
    ArrayTyp_make (loc, sym_id)
  end // end of [f_array]
} // end of [lp_typ]

and lp_typdec: LP typdec = $delay (
  seq3wth_parser_fun (TYPE, p_ident, EQ >> !lp_typ, f_typdec)
) where {
  fn f_typdec
    (tk_type: token, tk_id: token, t: typ):<> typdec = let
    val loc = location_combine (tk_type.token_loc, t.typ_loc)
    val- TOKide name = tk_id.token_node
    val sym = $effmask_all (symbol_make_name name)
  in
    typdec_make (loc, sym, t)
  end // end of [f_typdec]
} (* end of [lp_typdec] *)

and lp_typdeclst1: LP typdeclst1 = $delay (repeat1_parser !lp_typdec)

(* ****** ****** *)

and lp_fundec: LP fundec = $delay (seq5wth_parser_fun (
    FUNCTION, p_ident
  , LPAREN >> p_fieldtyplst << RPAREN, (COLON >> !lp_typ)^?, EQ >> !lp_exp
  , f_fundec
  )
) where {
  fn f_fundec (
      tk_function: token
    , tk_id: token
    , arglst: fieldtyplst
    , otp: typopt
    , e_body: exp
    ) :<> fundec = let
    val loc = location_combine (tk_function.token_loc, e_body.exp_loc)
    val sym_id = symbol_make_token (tk_id)
  in
    fundec_make (loc, sym_id, arglst, otp, e_body)
  end // end of [f_fundec]
} // end of [lp_fundec]

and lp_fundeclst1: LP fundeclst1 = $delay (repeat1_parser !lp_fundec)

(* ****** ****** *)

extern fun parse_failure
  (tks: stream token, ncur: int, nmax: int): void

implement parse_failure (tks, ncur, nmax) = let
  fun loop
    (tks: stream token, n: int): Option_vt (token) =
    case+ !tks of
    | stream_cons (tk, tks) =>
        if n > 0 then loop (tks, n-1) else Some_vt (tk)
    | stream_nil () => None_vt ()
  // end of [loop]
  val otk = loop (tks, nmax - ncur)
in
  case+ otk of
  | ~Some_vt tk => begin
      prerr_location tk.token_loc;
      prerr ": exit(TIGER)";
      prerr ": parsing failure";
      prerr_newline ()
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr ": exit(TIGER)";
      prerr ": parsing failure at the end of the token stream.";
      prerr_newline ()
    end // end of [None_vt]
end // end of [parse_failure]

(* ****** ****** *)

fn parse_from_charstream (cs: stream char): exp = let
  val tks0 = tokenstream_make_charstream (cs)
  var tks: stream token = tks0
  var ncur: int = 0 and nmax: int = 0
  val r = apply_parser (!lp_exp, tks, ncur, nmax)
  val res = (case+ r of
    | ~Some_vt e => e
    | ~None_vt _ => let
        val () = parse_failure (tks, ncur, nmax) in abort {exp} (1)
      end // end of [Fail]
  ) : exp // end of [val]
  val otk = stream_item_get<token> (tks)
  val () = (case+ otk of
    | ~Some_vt tk => begin
        prerr_location tk.token_loc;
        prerr ": exit(TIGER)";
        prerr ": parsing failure: unconsumed token";
        prerr_newline ();
        abort {void} (1)
      end // end of [Some]
    // there are no unconsumed tokens
    | ~None_vt () => ()
  ) : void // end of [token]
in
  res
end // end of [parse_from_charstream]

(* ****** ****** *)

implement parse_from_stdin () = let
  val () = filename_push (filename_stdin)
  val cs = char_stream_make_file stdin_ref
  val res = parse_from_charstream (cs)
  val () = filename_pop ()
in
  res
end // end of [parse_from_stdin]

implement parse_from_file (filename) = let
  val fileref = open_file_exn (filename, file_mode_r)
  val () = filename_push (filename) where
    { val filename = filename_make_string (filename) }
  // end of [val]
  val cs = char_stream_make_file fileref
  val res: exp = parse_from_charstream (cs)
  val () = filename_pop ()
  // ALERT: this should not be called as [fileref] may
  // val () = close_file (fileref) // have already been closed!!!
in
  res
end // end of [parse_from_file]

(* ****** ****** *)

(* end of [parser.dats] *)
