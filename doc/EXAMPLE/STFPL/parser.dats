(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

//
// A parser for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/SATS/filebas.sats" // for [stdio.cats]?
staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload _(*anon*) = "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/parcomb/SATS/posloc.sats"
staload "contrib/parcomb/SATS/tokenize.sats"
staload "contrib/parcomb/SATS/parcomb.sats" ;
staload _(*anonymous*) = "contrib/parcomb/DATS/parcomb.dats" ;

(* ****** ****** *)

staload "error.sats"
staload "fixity.sats"

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

(* ****** ****** *)

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

(* ****** ****** *)

fn litident (name0: string): P token =
  anytoken \sat (lam (tok: token): bool =<cloref>
    case+ tok.token_node of TOKide name => name0 = name | _ => false
  )
// end of [litident]

//

val COLON = litident ":"
val DOT = litident "."

val UMINUS = litident "~"

val PLUS = litident "+"
val MINUS = litident "-"
val TIMES = litident "*"
val DIVIDE = litident "/"

val GTEQ = litident ">="
val GT = litident ">"
val LTEQ = litident "<="
val LT = litident "<"

val EQ = litident "="
val NEQ = litident "<>"

//

val EQGT = litident "=>"

val MINUSGT = litident "->"

//

val AND   = litident "and"
val APP   = litident "app"
val ELSE  = litident "else"
val END   = litident "end"
val FALSE = litident "false"
val FIX   = litident "fix"
val FN    = litident "fn"
val FUN   = litident "fun"
val IF    = litident "if"
val IN    = litident "in"
val LAM   = litident "lam"
val LET   = litident "let"
val THEN  = litident "then"
val TRUE  = litident "true"
val VAL   = litident "val"
val REC   = litident "rec"

val PRINT = litident "print"
val PRINT_INT = litident "print_int"

(* ****** ****** *)

local

val arrsz = $arrsz {string} (
  "and"
, "else"
, "end"
, "fix"
, "fun"
, "if"
, "in"
, "lam"
, "let"
, "then"
, "rec"
, "val"
, ".", ":"
, "~", "+", "-", "*", "/"
, "=",":="
, ">=", ">", "<=", "<", "<>"
, "|", "&"
) // end of [arrsz]

in // in of [local]

val theKeywordArrSz = arrsz.3
val theKeywordArray = array_make_arrsz {string} arrsz

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

fn symbol_make_token
  (tok: token):<> sym = let
  val- TOKide name = tok.token_node
in
  $effmask_all (symbol_make_name name)
end // end of [symbol_make_token]

(* ****** ****** *)

local

#define PLUS_precedence 40
#define MINUS_precedence 40

#define TIMES_precedence 60
#define DIVIDE_precedence 60

#define UMINUS_precedence 61

#define EQ_precedence 20
#define NEQ_precedence 20

#define GTEQ_precedence 20
#define GT_precedence 20
#define LTEQ_precedence 20
#define LT_precedence 20

#define AMPAMP_precedence 9
#define BARBAR_precedence 8

#define PRINT_precedence 61
#define PRINT_INT_precedence 61

#define L LeftAssoc; #define R RightAssoc; #define N NonAssoc

in // in of [local]

val p_opr: P (fixopr e0xp) = begin
  PLUS wth (
    lam (tok: token) =<fun> f_infix (tok, L, PLUS_precedence)
  ) ||
  MINUS wth (
    lam (tok: token) =<fun> f_infix (tok, L, MINUS_precedence)
  ) ||
  TIMES wth (
    lam (tok: token) =<fun> f_infix (tok, L, TIMES_precedence)
  ) ||
  DIVIDE wth (
    lam (tok: token) =<fun> f_infix (tok, L, DIVIDE_precedence)
  ) ||
  GTEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, GTEQ_precedence)
  ) ||
  GT wth (
    lam (tok: token) =<fun> f_infix (tok, N, GT_precedence)
  ) ||
  LTEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, LTEQ_precedence)
  ) ||
  LT wth (
    lam (tok: token) =<fun> f_infix (tok, N, LT_precedence)
  ) ||
  EQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, EQ_precedence)
  ) ||
  NEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, NEQ_precedence)
  ) ||
  UMINUS wth (
    lam (tok: token) =<fun> f_prefx (tok, UMINUS_precedence)
  ) ||
  PRINT wth (
    lam (tok: token) =<fun> f_prefx (tok, PRINT_precedence)  
  ) ||
  PRINT_INT wth (
    lam (tok: token) =<fun> f_prefx (tok, PRINT_INT_precedence)  
  )
end where {
  fn f_prefx
    (tok: token, prec: int)
    :<> fixopr e0xp = let
    val opr = OPR (symbol_make_token tok)
    val f = lam (e: e0xp): e0xp =<cloref> let
      val loc = location_combine (tok.token_loc, e.e0xp_loc)
    in
      e0xp_make_opr (loc, opr, '[e])
    end // end of [f]
  in
    Prefix (tok.token_loc, prec, f)
  end // end of [f_minus]
  fn f_infix
    (tok: token, assoc: assoc, prec: int)
    :<> fixopr e0xp = let
    val f = lam
      (e1: e0xp, e2: e0xp): e0xp =<cloref> let
      val opr = OPR (symbol_make_token tok)
      val loc = location_combine (e1.e0xp_loc, e2.e0xp_loc) in
      e0xp_make_opr (loc, opr, '[e1, e2])
    end // end of [f]
  in
    Infix (tok.token_loc, prec, assoc, f)
  end // end of [f_infix]
} (* end of [where] *)

end // end of [local]
  
(* ****** ****** *)

(*
** ty0 = sym | (ty, ..., ty); ty = ty0 | ty0 -> ty
*)

typedef t0ypc = t0yp -<cloref> t0yp

val
rec lp_t0yp
  : LP (t0yp) = $delay (
  seq2wth_parser_fun (lzeta lp_t0yp1, lzeta lp_t0ypc, f)
) where {
  val f = lam (t: t0yp, tc: t0ypc) =<fun> tc (t) 
} (* end of [lp_t0yp] *)

and lp_t0yplist: LP t0yplst = $delay (
  repeat0_sep_parser<t0yp,token> (!lp_t0yp, COMMA)
) // end of [lp_t0yplst]

and lp_t0yp1
  : LP (t0yp) = $delay (
  p_ident wth f_ident ||
  seq3wth_parser_fun (LPAREN, lzeta lp_t0yplist, RPAREN, f_tup)
) where {
  val f_ident = lam
    (tok_ide: token) =<> let
    val loc = tok_ide.token_loc; val sym_id = symbol_make_token tok_ide
  in
    t0yp_make_sym (loc, sym_id)
  end // end of [f_ident]
  val f_tup = lam
    (tok1: token, ts: t0yplst, tok2: token) =<> begin
    case+ ts of
    | list_cons (t, list_nil ()) => t | _ => let
        val loc = location_combine (tok1.token_loc, tok2.token_loc) in
        t0yp_make_tup (loc, ts)
      end // end of [f_seq]  
  end // end of [lam]     
} (* end of [lp_t0yp1] *)

and lp_t0ypc
  : LP (t0ypc) = $delay (
  seq2wth_parser_fun
    (MINUSGT, !lp_t0yp, f) ||
  return_parser<t0ypc> (lam t => t) 
) where {
  val f = lam
    (_: token, t_res: t0yp): t0ypc =<fun> (lam t_arg => let
    val loc = location_combine (t_arg.t0yp_loc, t_res.t0yp_loc)
  in
    t0yp_make_fun (loc, t_arg, t_res)
  end) // end of [val]
} (* end of [lp_t0ypc] *)

(* ****** ****** *)

val lp_typann
  : LP (t0ypopt) = $delay (
  seq2wth_parser_fun (COLON, !lp_t0yp, f_some) ||
  return_parser (None ())
) where {
  val f_some = lam (_: token, t: t0yp) =<fun> Some (t)
} // end of [lp_annty]

(* ****** ****** *)

val app_e0xp
  : fixitm e0xp = let
  val f = lam
    (e1: e0xp, e2: e0xp): e0xp =<cloref> let
    val loc = location_combine (e1.e0xp_loc, e2.e0xp_loc)
  in
    e0xp_make_app (loc, e1, e2)
  end // end of [val]
in
  fixitm_make_app (f)  
end (* end of [app_e0xp] *)

(* ****** ****** *)

typedef e0xpc = e0xp -<cloref> e0xp

(* ****** ****** *)

val
rec lp_e0xp
  : LP (e0xp) = $delay (
  lzeta lp_e0xp_if ||
  lzeta lp_e0xp_lam || 
  lzeta lp_e0xp_fix || 
  lzeta lp_e0xp2
) // end of [lp_e0xp]

and lp_e0xplist: LP e0xplst = $delay (
  repeat0_sep_parser<e0xp,token> (!lp_e0xp, COMMA)
) // end of [p_explst]

(* ****** ****** *)

and lp_e0xp_if
  : LP e0xp = $delay (seq4wth_parser_fun
  (IF, !lp_e0xp, THEN >> !lp_e0xp, (ELSE >> !lp_e0xp)^?, f_if)
) where {
  fn f_if
    (tok_if: token, e1: e0xp, e2: e0xp, oe3: e0xpopt):<> e0xp = let
    val loc = case+ oe3 of
      | Some e3 => location_combine (tok_if.token_loc, e3.e0xp_loc)
      | None () => location_combine (tok_if.token_loc, e2.e0xp_loc)
    // end of [val]  
  in
    e0xp_make_if (loc, e1, e2, oe3)
  end // end of [f_if]
} // end of [lp_e0xp_if]

(* ****** ****** *)

and lp_a0rg
  : LP a0rg = $delay (
  seq2wth_parser_fun (p_ident, !lp_typann, f_a0rg) 
) where {
  fn f_a0rg (
    tok_ide: token, oty: t0ypopt
  ) :<> a0rg = let
    val sym = symbol_make_token (tok_ide) in @{
    a0rg_loc= tok_ide.token_loc, a0rg_nam= sym, a0rg_typ= oty
  } end // end of [f_a0rg]
} (* end of [lp_a0rg] *)

and lp_a0rglist
  : LP a0rglst = $delay (
  repeat0_sep_parser<a0rg,token> (!lp_a0rg, COMMA)
) // end of [p_explst]

and lp_e0xp_lam
  : LP e0xp = $delay (
  seq4wth_parser_fun (
    LAM, LPAREN >> !lp_a0rglist << RPAREN, !lp_typann, EQGT >> !lp_e0xp, f_lam
  ) // end of [seq5wth]
) where {
  fn f_lam (
      tok_lam: token
    , args: a0rglst
    , res: t0ypopt
    , body: e0xp
    ) :<> e0xp = let
    val loc = location_combine (tok_lam.token_loc, body.e0xp_loc)
  in
    e0xp_make_lam (loc, args, res, body)
  end // end of [f_lam]  
} // end of [lp_e0xp_lam]

and lp_e0xp_fix
  : LP e0xp = $delay (
  seq5wth_parser_fun (
    FIX,  p_ident, LPAREN >> !lp_a0rglist << RPAREN, !lp_typann, EQGT >> !lp_e0xp, f_fix
  ) // end of [seq5wth]
) where {
  fn f_fix (
      tok_fix: token
    , tok_ide: token  
    , args: a0rglst
    , res: t0ypopt
    , body: e0xp
    ) :<> e0xp = let
    val loc = location_combine (tok_fix.token_loc, body.e0xp_loc)
    val sym = symbol_make_token (tok_ide)
  in
    e0xp_make_fix (loc, sym, args, res, body)
  end // end of [f_lam]  
} // end of [lp_e0xp_lam]

(* ****** ****** *)

and lp_e0xp0
  : LP e0xp = $delay ( // ordering is significant!
  TRUE wth f_true ||
  FALSE wth f_false ||
  p_ident wth f_var ||
  p_number wth f_number ||
  p_string wth f_string ||
  seq3wth_parser_fun
    (LPAREN, !lp_e0xplist, RPAREN, f_tup) ||
  // end of [seq3wth_parser]
  seq5wth_parser_fun
    (LET, lzeta lp_d0eclist, IN, !lp_e0xp, END, f_let)
  // end of [seq5wth_parser]
) where {
  fn f_var (tok: token):<> e0xp = let
    val loc = tok.token_loc; val sym = symbol_make_token tok in
    e0xp_make_var (loc, sym)
  end // end of [f_string]
  fn f_true (tok: token):<> e0xp = e0xp_make_bool (tok.token_loc, true)
  fn f_false (tok: token):<> e0xp = e0xp_make_bool (tok.token_loc, false)
  fn f_number (tok: token):<> e0xp = let
    val loc = tok.token_loc; val- TOKint int = tok.token_node in
    e0xp_make_int (loc, int)
  end // end of [f_string]
  fn f_string (tok: token):<> e0xp = let
    val loc = tok.token_loc; val- TOKstr str = tok.token_node in
    e0xp_make_str (loc, str)
  end // end of [f_string]
  fn f_tup
    (tok_beg: token, es: e0xplst, tok_end: token):<> e0xp = begin
    case+ es of
    | list_cons (e, list_nil ()) => e | _ => let
        val loc = location_combine (tok_beg.token_loc, tok_end.token_loc)
      in
        e0xp_make_tup (loc, es)
      end // end of [_]
  end // end of [f_seq]
  fn f_let (
      tok_let: token
    , ds: d0eclst
    , _(*in*)
    , e: e0xp
    , tok_end: token
    ) :<> e0xp = let
    val loc = location_combine
      (tok_let.token_loc, tok_end.token_loc) in e0xp_make_let (loc, ds, e)
  end // end of [f_let]  
    
} // end of [lp_e0xp0]

(* ****** ****** *)

and lp_opre0xp0
  : LP (fixitm e0xp) = $delay (
  p_opr wth f_opr ||
  seq2wth_parser_fun (DOT, p_number, f_proj) ||
  !lp_e0xp0 wth f_e0xp
) where {
  fn f_opr
    (opr: fixopr e0xp):<> fixitm e0xp = FIXITMopr opr
  #define DOT_precedence 80
  fn f_proj (tok_dot: token, tok_num: token):<> fixitm e0xp = let
    val loc = location_combine (tok_dot.token_loc, tok_num.token_loc)
    val- TOKint n = tok_num.token_node
    val opr = Postfix {e0xp} (
      loc
    , DOT_precedence
    , lam (e) => let
        val loc = location_combine (loc, e.e0xp_loc)
      in
        e0xp_make_proj (loc, e, n)
      end
    ) // end of [Postfix]  
  in
    FIXITMopr (opr)
  end // end of [f_proj]
  fn f_e0xp (exp: e0xp):<> fixitm e0xp = FIXITMatm exp
} // end of [lp_opre0xp0]

(* ****** ****** *)

and lp_e0xp1
  : LP (e0xp) = $delay (
  (repeat1_parser !lp_opre0xp0) wth f
) where {
  typedef T = fixitm e0xp
  fn err (loc: loc): e0xp = begin
    prerr_location loc;
    prerr ": exit(STFPL)";
    prerr ": parsing failure: unresolved fixity";
    prerr_newline ();
    abort {e0xp} (1)
  end // end [err]

  fn fixitm_loc_get
    (itm: fixitm e0xp):<> loc = case+ itm of
    | FIXITMatm exp => exp.e0xp_loc
    | FIXITMopr opr => fixopr_loc_get opr
  // end of [fixitm_loc_get]

  fn f (itms: List1 T):<> e0xp = let
(*
    val () = $effmask_all (loop (itms, 0)) where {
      val out = stderr_ref
      fun loop (itms: List T, i: int):<cloref1> void =
        case+ itms of
        | list_cons (itm, itms) => loop (itms, i+1) where {
            val () = if i > 0 then fprint_string (out, ", ")
            val () = (case+ itm of
              | FIXITMatm exp => fprint_e0xp (out, exp)
              | FIXITMopr opr => fprint_fixopr (out, opr)
            ) : void // end of [val]  
          } // end of [list_cons]
        | list_nil () => ()
    } // end of [val]
    val () = $effmask_all (prerr_newline ())
*)
    val res = $effmask_all (fixity_resolve (app_e0xp, itms))
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
} // end of [lp_e0xp1]

and lp_e0xp1c
  : LP (e0xpc) = $delay (
  COLON >> !lp_t0yp wth f_ann || return_parser<e0xpc> (lam e => e)
) where {
  fn f_ann (t: t0yp):<> e0xpc = lam e => let
    val loc = location_combine (e.e0xp_loc, t.t0yp_loc)
  in
    e0xp_make_ann (loc, e, t)
  end // end of [f]
} // end of [lp_e0xp1c]

and lp_e0xp2: LP (e0xp) = $delay (
  seq2wth_parser_fun (!lp_e0xp1, !lp_e0xp1c, f)
) where {
  val f = lam (e: e0xp, ec: e0xpc) =<fun> ec (e)
} (* end of [lp_e0xp2] *)

(* ****** ****** *)

and lp_v0aldec: LP (v0aldec) = $delay (
  seq3wth_parser_fun (p_ident, !lp_typann, EQ >> !lp_e0xp, f_v0aldec)
) where {
  fn f_v0aldec (
      tok_ide: token, oty: t0ypopt, e: e0xp
    ) :<> v0aldec = let
    val loc = location_combine (tok_ide.token_loc, e.e0xp_loc)
    val sym = symbol_make_token (tok_ide)
  in '{
    v0aldec_loc= loc, v0aldec_nam= sym, v0aldec_ann= oty, v0aldec_def= e
  } end // end of [f_v0aldec]
} // end of [lp_v0aldec]

and lp_v0aldeclist: LP (List1 v0aldec) = $delay (
  repeat1_sep_parser<v0aldec,token> (!lp_v0aldec, AND)
) // end of [lp_v0aldeclist]

(* ****** ****** *)

and lp_d0ec
  : LP (d0ec) = $delay (
  seq3wth_parser_fun (VAL, (REC)^?, !lp_v0aldeclist, f_v0al)
) where {
  fn f_v0al (
      tok_val: token
    , tokopt_rec: Option token
    , vds: List1 v0aldec
    ) :<> d0ec = let
    val isrec = (
      case+ tokopt_rec of Some _ => true | None _ => false
    ) : bool
    val vd = list_last<v0aldec> (vds)
    val loc = location_combine (tok_val.token_loc, vd.v0aldec_loc)
  in  
    d0ec_make_val (loc, isrec, vds)
  end // end of [f_v0al]  
} // end of [lp_d0ec]

and lp_d0eclist: LP (d0eclst) = $delay (repeat0_parser<d0ec> (!lp_d0ec))

(* ****** ****** *)

extern fun parse_failure
  (toks: stream token, ncur: int, nmax: int): void

implement
parse_failure (toks, ncur, nmax) = let
  fun loop
    (toks: stream token, n: int): Option_vt (token) =
    case+ !toks of
    | stream_cons (tok, toks) =>
        if n > 0 then loop (toks, n-1) else Some_vt (tok)
    | stream_nil () => None_vt ()
  // end of [loop]
  val tokopt = loop (toks, nmax - ncur)
in
  case+ tokopt of
  | ~Some_vt tok => begin
      prerr_location tok.token_loc;
      prerr ": exit(STFPL)";
      prerr ": parsing failure";
      prerr_newline ()
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr ": exit(STFPL)";
      prerr ": parsing failure at the end of the token stream.";
      prerr_newline ()
    end // end of [None_vt]
end // end of [parse_failure]

(* ****** ****** *)

fun
parse_from_charstream
  (cs: stream char): e0xp = let
  val toks0 = tokenstream_make_charstream (cs)
  var toks: stream token = toks0
  var ncur: int = 0 and nmax: int = 0
  val r = apply_parser (!lp_e0xp, toks, ncur, nmax)
  val res = (case+ r of
    | ~Some_vt e => e
    | ~None_vt _ => let
        val () = parse_failure (toks, ncur, nmax) in abort {e0xp} (1)
      end // end of [Fail]
  ) : e0xp // end of [val]
  val otok = stream_get_item<token> (toks)
  val () = (case+ otok of
    | ~Some_vt tok => begin
        prerr_location tok.token_loc;
        prerr ": exit(STFPL)";
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

implement
parse_from_stdin () = let
  val () = filename_push (filename_stdin)
  val cs = char_stream_make_file stdin_ref
  val res = parse_from_charstream (cs)
  val () = filename_pop ()
in
  res
end // end of [parse_from_stdin]

implement
parse_from_file (filename) = let
  val fileref = open_file_exn (filename, file_mode_r)
  val () = filename_push (filename) where
    { val filename = filename_make_string (filename) }
  // end of [val]
  val cs = char_stream_make_file fileref
  val res: e0xp = parse_from_charstream (cs)
  val () = filename_pop ()
  // ALERT: this should not be called as [fileref] may
  // val () = close_file (fileref) // have already been closed!!!
in
  res
end // end of [parse_from_file]

(* ****** ****** *)

(* end of [parser.dats] *)
