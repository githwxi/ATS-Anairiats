(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload Loc = "PARCOMB/posloc.sats"

staload Sym = "symbol.sats"

(* ****** ****** *)

typedef loc = $Loc.location_t
typedef sym = $Sym.symbol_t

(* ****** ****** *)

staload "types.sats"

(* ****** ****** *)

datatype oper =
  | PlusOp | MinusOp | TimesOp | DivideOp
  | EqOp | NeqOp | GtOp | GeOp | LtOp | LeOp
  | AndOp | OrOp

fun fprint_oper (out: FILEref, oper: oper): void
fun print_oper (oper: oper): void
fun prerr_oper (oper: oper): void

(* ****** ****** *)

typedef refb = ref (bool)

datatype v1ar_node =
  | SimpleVar of sym(*name*)
  | FieldVar of (v1ar, sym(*field label*))
  | SubscriptVar of (v1ar, exp(*array index*))

and exp_node =
  | VarExp of v1ar
  | NilExp of ()
  | IntExp of int
  | StringExp of string
  | CallExp of (sym(*fun*), explst(*arg*))
  | OpExp of (exp(*left*), oper(*oper*), exp(*right*))
  | RecordExp of (fieldexplst, typ)
  | SeqExp of explst
  | AssignExp of (v1ar, exp)
  | IfExp of (exp(*cond*), exp(*then*), expopt(*else*))
  | WhileExp of (exp(*test*), exp(*body*))
  | ForExp of (
      sym(*ind*), refb(*escape*), exp(*lo*), exp(*hi*), exp(*body*)
    ) // end of [ForExp]
  | BreakExp of ()
  | ContinueExp of () // this is my addition
  | LetExp of (declst, exp(*body*))
  | ArrayExp of (typ, exp(*size*), exp(*init*))

and dec_node =
  | FunctionDec of fundeclst
  | VarDec of (sym(*name*), refb(*escape*), typopt, exp(*init*))
  | TypeDec of typdeclst

and typ_node =
  | NameTyp of sym
  | RecordTyp of fieldtyplst
  | ArrayTyp of sym

where v1ar = '{
  v1ar_loc= loc, v1ar_node= v1ar_node, v1ar_ty= ty
}

and exp = '{
  exp_loc= loc, exp_node= exp_node, exp_ty= ty // to store
// the type of the expression computed during typechecking
} // end of [exp]

and explst = List exp
and expopt = Option exp

and fieldexp = '{
  fieldexp_loc= loc
, fieldexp_lab= sym
, fieldexp_exp= exp
}

and fieldexplst = List fieldexp

and dec = '{
  dec_loc= loc, dec_node= dec_node
}

and declst = List dec

and typ = '{
  typ_loc= loc, typ_node= typ_node, typ_ty= ty // to store
// the corresponding type computed during typechecking
} // end of [typ]

and typopt = Option (typ)

and fieldtyp = '{
  fieldtyp_loc= loc
, fieldtyp_lab= sym
, fieldtyp_escape= refb
, fieldtyp_typ= sym
}

and fieldtyplst = List fieldtyp

and fundec = '{
  fundec_loc= loc
, fundec_name= sym
, fundec_arglst= fieldtyplst
, fundec_result= typopt
, fundec_body= exp
}

and fundeclst = List fundec

and typdec = '{
  typdec_loc= loc
, typdec_name= sym
, typdec_typ= typ
}

and typdeclst = List typdec

(* ****** ****** *)

fun SimpleVar_make (loc: loc, sym: sym):<> v1ar
fun FieldVar_make (loc: loc, x: v1ar, name: sym):<> v1ar
fun SubscriptVar_make (loc: loc, x: v1ar, ind: exp):<> v1ar

fun fprint_v1ar (out: FILEref, v: v1ar): void
fun print_v1ar (v: v1ar): void
fun prerr_v1ar (v: v1ar): void

(* ****** ****** *)

fun fieldexp_make (loc: loc, lab: sym, e: exp):<> fieldexp

fun VarExp_make (loc: loc, x: v1ar):<> exp
fun NilExp_make (loc: loc):<> exp
fun IntExp_make (loc: loc, i: int):<> exp
fun StringExp_make (loc: loc, s: string):<> exp
fun CallExp_make (loc: loc, _fun: sym, _arg: explst):<> exp
fun OpExp_make (loc: loc, lft: exp, oper: oper, rgh: exp):<> exp
fun RecordExp_make (loc: loc, fes: fieldexplst, typ: typ):<> exp
fun SeqExp_make (loc: loc, es: explst):<> exp
fun AssignExp_make (loc: loc, x: v1ar, e: exp):<> exp
fun IfExp_make (loc: loc, _cond: exp, _then: exp, _else: expopt):<> exp
fun WhileExp_make (loc: loc, _test: exp, _body: exp):<> exp
fun ForExp_make (loc: loc, v: sym, _lo: exp, _hi: exp, _body: exp):<> exp
fun BreakExp_make (loc: loc):<> exp
fun ContinueExp_make (loc: loc):<> exp
fun LetExp_make (loc: loc, ds: declst, _body: exp):<> exp
fun ArrayExp_make (loc: loc, typ: typ, _size: exp, _init: exp):<> exp

(* ****** ****** *)

fun fprint_exp (out: FILEref, e: exp): void
fun print_exp (e: exp): void
fun prerr_exp (e: exp): void

fun fprint_explst (out: FILEref, es: explst): void

(* ****** ****** *)

fun fieldtyp_make (loc: loc, lab: sym, typ: sym):<> fieldtyp

fun fundec_make (
    loc: loc, name: sym, arglst: fieldtyplst, otp: typopt, _body: exp
  ) :<> fundec

fun typdec_make (loc: loc, name: sym, typ: typ):<> typdec

(* ****** ****** *)

fun FunctionDec_make (loc: loc, fds: fundeclst):<> dec
fun VarDec_make (loc: loc, name: sym, otp: typopt, e_init: exp):<> dec
fun TypeDec_make (loc: loc, tds: typdeclst):<> dec

(* ****** ****** *)

fun NameTyp_make (loc: loc, name: sym):<> typ
fun RecordTyp_make (loc: loc, fts: fieldtyplst):<> typ
fun ArrayTyp_make (loc: loc, sym: sym):<> typ

(* ****** ****** *)

fun typ_ty_set (typ: typ, ty: ty): void = "tigerats_typ_ty_set"
fun v1ar_ty_set (v1ar: v1ar, ty: ty): void = "tigerats_v1ar_ty_set"
fun exp_ty_set (exp: exp, ty: ty): void = "tigerats_exp_ty_set"

(* ****** ****** *)

(* end of [absyn.sats] *)
