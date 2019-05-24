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

staload "types.sats"
staload "absyn.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

typedef loc = $Loc.location_t
typedef sym = $Sym.symbol_t

(* ****** ****** *)

implement fprint_oper (out, oper) = case+ oper of
  | PlusOp _ => fprint_string (out, "+")  
  | MinusOp _ => fprint_string (out, "-")
  | TimesOp _ => fprint_string (out, "*")
  | DivideOp _ => fprint_string (out, "/")
  | EqOp _ => fprint_string (out, "=")
  | NeqOp _ => fprint_string (out, "<>")
  | GtOp _ => fprint_string (out, ">")
  | GeOp _ => fprint_string (out, ">=")
  | LtOp _ => fprint_string (out, "<")
  | LeOp _ => fprint_string (out, "<=")
  | AndOp _ => fprint_string (out, "&")
  | OrOp _ => fprint_string (out, "|")
// end of [fprint_oper]

implement print_oper (oper) = fprint_oper (stdout_ref, oper)
implement prerr_oper (oper) = fprint_oper (stderr_ref, oper)

(* ****** ****** *)

implement SimpleVar_make (loc, sym) = '{
  v1ar_loc= loc
, v1ar_node= SimpleVar (sym)
, v1ar_ty= TYtop ()
} // end of [SimpleVar_make]

implement FieldVar_make (loc, x, name) = '{
  v1ar_loc= loc
, v1ar_node= FieldVar (x, name)
, v1ar_ty= TYtop ()
} // end of [FieldVar_make]

implement SubscriptVar_make (loc, x, ind) = '{
  v1ar_loc= loc
, v1ar_node= SubscriptVar (x, ind)
, v1ar_ty= TYtop ()
} // end of [SubscriptVar_make]

(* ****** ****** *)

implement fprint_v1ar
  (out, v) = case+ v.v1ar_node of
  | SimpleVar (sym) => begin
      fprint_string (out, "SimpleVar(");
      $Sym.fprint_symbol (out, sym);
      fprint_string (out, ")")
    end // end of [SimpleVar]
  | FieldVar (v, lab) => begin
      fprint_string (out, "FieldVar(");
      fprint_v1ar (out, v);
      fprint_string (out, "; ");
      $Sym.fprint_symbol (out, lab);
      fprint_string (out, ")")
    end // end of [FieldVar]
  | SubscriptVar (v, ind) => begin
      fprint_string (out, "SubscriptVar(");
      fprint_v1ar (out, v);
      fprint_string (out, "; ");
      fprint_exp (out, ind);
      fprint_string (out, ")")
    end // end of [SubscriptVar]
// end of [fprint_v1ar]

implement print_v1ar (x) = fprint_v1ar (stdout_ref, x)
implement prerr_v1ar (x) = fprint_v1ar (stderr_ref, x)

(* ****** ****** *)

implement fieldexp_make (loc, lab, exp) = '{
  fieldexp_loc= loc
, fieldexp_lab= lab
, fieldexp_exp= exp
} // end of [fieldexp_make]

implement NilExp_make (loc) = '{
  exp_loc= loc
, exp_node= NilExp ()
, exp_ty= TYtop ()
}

implement VarExp_make (loc, v) = '{
  exp_loc= loc
, exp_node= VarExp (v)
, exp_ty= TYtop ()
}

implement IntExp_make (loc, int) = '{
  exp_loc= loc
, exp_node= IntExp (int)
, exp_ty= TYtop ()
}

implement StringExp_make (loc, str) = '{
  exp_loc= loc
, exp_node= StringExp (str)
, exp_ty= TYtop ()
}

implement CallExp_make (loc, sym, arg) = '{
  exp_loc= loc
, exp_node= CallExp (sym, arg)
, exp_ty= TYtop ()
}

implement OpExp_make (loc, e_lft, oper, e_rgh) = '{
  exp_loc= loc
, exp_node= OpExp (e_lft, oper, e_rgh)
, exp_ty= TYtop ()
}

implement RecordExp_make (loc, fes, t_rec) = '{
  exp_loc= loc
, exp_node= RecordExp (fes, t_rec)
, exp_ty= TYtop ()
}

implement SeqExp_make (loc, es) = '{
  exp_loc= loc
, exp_node= SeqExp (es)
, exp_ty= TYtop ()
}

implement AssignExp_make (loc, v, e) = '{
  exp_loc= loc
, exp_node= AssignExp (v, e)
, exp_ty= TYtop ()
}

implement ArrayExp_make (loc, t_elt, e_size, e_init) = '{
  exp_loc= loc
, exp_node= ArrayExp (t_elt, e_size, e_init)
, exp_ty= TYtop ()
}

implement IfExp_make (loc, e1, e2, oe3) = '{
  exp_loc= loc
, exp_node= IfExp (e1, e2, oe3)
, exp_ty= TYtop ()
}

implement WhileExp_make (loc, e_test, e_body) = '{
  exp_loc= loc
, exp_node= WhileExp (e_test, e_body)
, exp_ty= TYtop ()
}

implement ForExp_make
  (loc, sym, e_lo, e_hi, e_body) = let
  val escape = ref_make_elt<bool> (false)
in '{
  exp_loc= loc
, exp_node= ForExp (sym, escape, e_lo, e_hi, e_body)
, exp_ty= TYtop ()
} end // end of [ForExp_make]

implement BreakExp_make (loc) = '{
  exp_loc= loc
, exp_node= BreakExp ()
, exp_ty= TYtop ()
}

implement ContinueExp_make (loc) = '{
  exp_loc= loc
, exp_node= ContinueExp ()
, exp_ty= TYtop ()
}

implement LetExp_make (loc, ds, e_body) = '{
  exp_loc= loc
, exp_node= LetExp (ds, e_body)
, exp_ty= TYtop ()
}

(* ****** ****** *)

implement fprint_exp (out, e) = let
  macdef prexp (e) = fprint_exp (out, ,(e))
  macdef prexplst (es) = fprint_explst (out, ,(es))
  macdef prvar (v) = fprint_v1ar (out, ,(v))
  macdef prstr (str) = fprint_string (out, ,(str))
  macdef prsym (sym) = $Sym.fprint_symbol (out, ,(sym))
in
  case+ e.exp_node of
  | VarExp v => begin
      prstr "VarExp("; prvar v; prstr ")"
    end
  | NilExp () => prstr "NilExp()"
  | IntExp int => begin
      prstr "IntExp("; fprint_int (out, int); prstr ")"
    end
  | StringExp str => begin
      prstr "StringExp("; fprint_string (out, str); prstr ")"
    end
  | CallExp (f, arg) => begin
      prstr "CallExp("; prsym f; prstr "; "; prexplst arg; prstr ")"
    end
  | OpExp (e1, oper, e2) => begin
      prstr "OpExp(";
      fprint_oper (out, oper);
      prstr "; ";
      prexp e1; prstr ", "; prexp e2;
      prstr ")"
    end
  | RecordExp _ => begin
      prstr "RecordExp("; prstr "..."; prstr ")"
    end // end of [RecordExp]
  | SeqExp es => begin
      prstr "SeqExp("; prexplst es; prstr ")"
    end
  | AssignExp (v, e) => begin
      prstr "AssignExp("; prvar v; prstr ", "; prexp e; prstr ")"
    end
  | IfExp (e1, e2, oe3) => begin
      prstr "IfExp(";
      prexp e1;
      prstr "; "; prexp e2;
      begin case+ oe3 of
        | Some e3 => (prstr "; "; prexp e3) | None () => ()
      end;
      prstr ")"
    end // end of [IfExp]
  | WhileExp (e_test, e_body) => begin
      prstr "WhileExp(";
      prexp e_test;
      prstr "; "; prexp e_body;
      prstr ")"
    end // end of [WhileExp]
  | ForExp (v, _(*escape*), e_lo, e_hi, e_body) => begin
      prstr "ForExp(";
      prsym v;
      prstr "; "; prexp e_lo;
      prstr "; "; prexp e_hi;
      prstr "; "; prexp e_body;
      prstr ")"
    end // end of [ForExp]
  | BreakExp () => prstr "BreakExp()"
  | ContinueExp () => prstr "ContinueExp()"
  | LetExp (ds, e_body) => begin
      prstr "LetExp(";
      prstr "...";
      prstr "; "; prexp e_body;
      prstr ")"
    end // end of [LetExp]
  | ArrayExp (t_elt, e_size, e_init) => begin
      prstr "ArrayExp(";
      prstr "...";
      prstr "; "; prexp e_size;
      prstr "; "; prexp e_init;
      prstr ")"
    end // end of [ArrayExp]
(*
  | _ => begin
      prstr "fprint_exp: not yet supported"; exit (1)
    end // end of [_]
*)
end // end of [fprint_exp]

implement fprint_explst
  (out, es) = loop (out, es, 0) where {
  fun loop (out: FILEref, es: explst, i: int): void =
    case+ es of
    | list_cons (e, es) => let
        val () = if i > 0 then fprint_string (out, ", ")
      in
        fprint_exp (out, e); loop (out, es, i+1)
      end // end of [list_cons]
    | list_nil () => ()
} // end of [fprint_explst]

implement print_exp (e) = fprint_exp (stdout_ref, e)
implement prerr_exp (e) = fprint_exp (stderr_ref, e)

(* ****** ****** *)

implement fieldtyp_make (loc, lab, typ) = '{
  fieldtyp_loc= loc
, fieldtyp_lab= lab
, fieldtyp_escape= ref_make_elt<bool> (false)
, fieldtyp_typ= typ
} // end of [fieldtyp_make]

implement fundec_make
  (loc, name, arglst, otp, e_body) = '{
  fundec_loc= loc
, fundec_name= name
, fundec_arglst= arglst
, fundec_result= otp
, fundec_body= e_body
} // end of [fundec_make]

implement typdec_make (loc, name, typ) = '{
  typdec_loc= loc
, typdec_name= name
, typdec_typ= typ
} // end of [typdec_make]

(* ****** ****** *)

implement FunctionDec_make (loc, fds) = '{
  dec_loc= loc, dec_node= FunctionDec (fds)
}

implement VarDec_make (loc, name, otp, e_init) = let
  val escape = ref_make_elt<bool> (false)
in '{
  dec_loc= loc, dec_node= VarDec (name, escape, otp, e_init)
} end // end of [VarDec_make]

implement TypeDec_make (loc, tds) = '{
  dec_loc= loc, dec_node= TypeDec (tds)
}

(* ****** ****** *)

implement NameTyp_make (loc, name) = '{
  typ_loc= loc, typ_node= NameTyp (name), typ_ty= TYtop ()
}

implement RecordTyp_make (loc, fts) = '{
  typ_loc= loc, typ_node= RecordTyp (fts), typ_ty= TYtop ()
}

implement ArrayTyp_make (loc, sym) = '{
  typ_loc= loc, typ_node= ArrayTyp (sym), typ_ty= TYtop ()
}

(* ****** ****** *)

extern typedef "typ_t" = typ
extern typedef "v1ar_t" = v1ar
extern typedef "exp_t" = exp

%{$

ats_void_type
tigerats_typ_ty_set
  (ats_ptr_type typ, ats_ptr_type ty) {
  ((typ_t)typ)->atslab_typ_ty = ty; return ;
} // tigerats_typ_ty_set

ats_void_type
tigerats_v1ar_ty_set
  (ats_ptr_type v1ar, ats_ptr_type ty) {
  ((v1ar_t)v1ar)->atslab_v1ar_ty = ty; return ;
} // tigerats_v1ar_ty_set

ats_void_type
tigerats_exp_ty_set
  (ats_ptr_type exp, ats_ptr_type ty) {
  ((exp_t)exp)->atslab_exp_ty = ty; return ;
} // tigerats_exp_ty_set

%}

(* ****** ****** *)

(* end of [absyn.dats] *)
