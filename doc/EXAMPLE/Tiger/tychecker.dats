(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "error.sats"
staload "stamp.sats"

staload "PARCOMB/posloc.sats"
typedef loc = location_t

staload "symbol.sats"
typedef sym = symbol_t

(* ****** ****** *)

staload "types.sats"
staload "absyn.sats"

staload "tychecker.sats"

(* ****** ****** *)

staload _(*anonymous*) = "symbol.dats"

(* ****** ****** *)

val ty_INT = TYbase (symbol_INT)
val ty_STRING = TYbase (symbol_STRING)

val ty_NIL = TYnil () and ty_UNIT = TYunit ()

(* ****** ****** *)

fun tyleq_solve
  (loc: loc, ty1: ty, ty2: ty): void = case+ (ty1, ty2) of
  | (TYname (sym1, r_ty1), _) => let
      val ty1 = ty_lnkrmv r_ty1 in tyleq_solve (loc, ty1, ty2)
    end // end of [TYname, _]
  | (_, TYname (sym2, r_ty2)) => let
      val ty2 = ty_lnkrmv r_ty2 in tyleq_solve (loc, ty1, ty2)
    end // end of [_, TYname]
  | (TYbase sym1, TYbase sym2) when sym1 = sym2 => ()
  | (TYnil _, TYnil _) => () | (TYnil _, TYrec _) => ()
  | (TYrec (stamp1, _), TYrec (stamp2, _)) when stamp1 = stamp2 => ()
  | (TYarr (stamp1, _), TYarr (stamp2, _)) when stamp1 = stamp2 => ()
  | (TYunit _, TYunit _) => ()
  | (_, _) => begin
      prerr_location loc;
      prerr ": exit(TIGER): type mismatch";
      prerr ": the needed type is [";
      prerr_ty ty2;
      prerr "] but the actual type is [";
      prerr_ty ty1;
      prerr "]";
      prerr_newline ();
      abort {void} (1)
    end // end of [_, _]
// end of [tyleq_solve]

(* ****** ****** *)

implement vfty_var_make (level, rb, ty) = '{
  vfty_level=level, vfty_node= VFTYvar (rb, ty)
}

implement vfty_fun_make (level, tys, ty) = '{
  vfty_level=level, vfty_node= VFTYfun (tys, ty)
}

(* ****** ****** *)

local

val the_funlevel = ref_make_elt<int> (0)

in // in of [local]

fun the_funlevel_get (): int = !the_funlevel

fun the_funlevel_inc (): void = let
  val n = !the_funlevel in !the_funlevel := n + 1
end // end of [the_funlevel_inc]

fun the_funlevel_dec (): void = let
  val n = !the_funlevel in !the_funlevel := n - 1
end // end of [the_funlevel_dec]

end // end of [local]

(* ****** ****** *)

local

val the_looplevel = ref_make_elt<int> (0)

in // in of [local]

fun the_looplevel_get (): int = !the_looplevel

fun the_looplevel_inc (): void = let
  val n = !the_looplevel in !the_looplevel := n + 1
end // end of [the_looplevel_inc]

fun the_looplevel_dec (): void = let
  val n = !the_looplevel in !the_looplevel := n - 1
end // end of [the_looplevel_dec]

end // end of [local]


(* ****** ****** *)

staload M = "LIB/funmap_avltree.dats"

typedef tymap = $M.map_t (sym, ty)
typedef vftymap = $M.map_t (sym, vfty)

(* ****** ****** *)

local

val _cmp =
  lam (x1: sym, x2: sym): Sgn =<cloref> compare (x1, x2)
// end of [val]

in

fn tymap_empty () = $M.funmap_empty<> ()
fn vftymap_empty () = $M.funmap_empty<> ()

fn tymap_search
  (loc0: loc, tmap: tymap, sym: sym): ty = let
  val ans =
    $M.funmap_search<sym,ty> (tmap, sym, _cmp) in
    case+ ans of
    | ~Some_vt ty => ty | ~None_vt () => begin
      prerr_location loc0;
      prerr ": exit(TIGER)";
      prerr ": unrecognized type symbol ["; prerr_symbol sym;
      prerr "]"; prerr_newline ();
      abort {ty} (1)
    end // end of [None_vt]
end // end of [tymap_search]

fn vftymap_search
  (loc0: loc, vmap: vftymap, sym: sym): vfty = let
  val ans =
    $M.funmap_search<sym,vfty> (vmap, sym, _cmp) in
  case+ ans of
  | ~Some_vt (vfty) => vfty | ~None_vt () => begin
      prerr_location loc0;
      prerr ": exit(TIGER)";
      prerr ": unrecognized var/fun symbol ["; prerr_symbol sym;
      prerr "]"; prerr_newline ();
      abort {vfty} (1)
    end // end of [None_vt]
end // end of [env_search]

fn tymap_insert
  (tmap: tymap, sym: sym, ty: ty): tymap =
  $M.funmap_insert<sym,ty> (tmap, sym, ty, _cmp)
// end of [tymap_insert]

fn vftymap_insert
  (vmap: vftymap, sym: sym, vfty: vfty): vftymap =
  $M.funmap_insert<sym,vfty> (vmap, sym, vfty, _cmp)
// end of [vftymap_insert]

end // end of [local]

(* ****** ****** *)

fun ty_make_typ
  (tmap: tymap, typ: typ): ty = let
  val ty0 = case+ typ.typ_node of
    | NameTyp sym => let
        val loc0 = typ.typ_loc in tymap_search (loc0, tmap, sym)
      end // end of [NameTyp]
    | RecordTyp fts => let
        val stamp = stamp_make ()
        val lts = aux (tmap, fts) where {
          fun aux (tmap: tymap, fts: fieldtyplst): labtylst =
            case+ fts of
            | list_cons (ft, fts) => let
                val loc = ft.fieldtyp_loc
                val lab = ft.fieldtyp_lab
                val sym = ft.fieldtyp_typ
                val ty = tymap_search (loc, tmap, sym)
              in
                LABTYLSTcons (lab, ty, aux (tmap, fts))
              end // end of [list_cons]
            | list_nil () => LABTYLSTnil ()
          // end of [aux]
        } // end of [val]
      in
        TYrec (stamp, lts)
      end // end of [RecordTyp]
    | ArrayTyp sym => let
        val loc0 = typ.typ_loc
        val stamp = stamp_make ()
        val ty = tymap_search (loc0, tmap, sym)
      in
        TYarr (stamp, ty)
      end // end of [ArrayTyp]
  // end of [val]
in
  typ_ty_set (typ, ty0); ty0
end // end of [ty_make_typ]

(* ****** ****** *)

extern fun transVar (tmap: tymap, vmap: vftymap, x: v1ar): ty
extern fun transExpUp (tmap: tymap, vmap: vftymap, e: exp): ty
extern fun transExpDn (tmap: tymap, vmap: vftymap, e: exp, t: ty): void

extern fun transDec
  (tmap: &tymap, vmap: &vftymap, d: dec): void
extern fun transDeclst
  (tmap: &tymap, vmap: &vftymap, ds: declst): void

(* ****** ****** *)

implement transVar (tmap, vmap, x0) = let
  val ty0 = case+ x0.v1ar_node of
  | SimpleVar sym => let
      val vfty = vftymap_search (x0.v1ar_loc, vmap, sym)
    in
      case+ vfty.vfty_node of
      | VFTYvar (rb, ty) => ty where {
          val level = the_funlevel_get ()
          val isEscaped = level > vfty.vfty_level
(*
          val () = if isEscaped then begin
            prerr "transVar: the variable [";
            prerr_symbol sym; prerr "] escapes";
            prerr_newline ()
          end // end of [val]
*)
          val () = if isEscaped then !rb := true // escaped
        } // end of [VFTYvar]
      | VFTYfun _ => begin
          prerr ": exit(TIGER)";
          prerr ": the variable [";
          prerr_symbol sym;
          prerr "] is not a recognized variable";
          prerr_newline ();
          abort {ty} (1)
        end // end of [SimpleVar]
    end // end of [SimpleVar]
  | FieldVar (x, lab) => let
      val ty_rec = transVar (tmap, vmap, x)
      val ty_rec = ty_normalize (ty_rec)
      val fts = (case+ ty_rec of
        | TYrec (_(*stamp*), fts) => fts | _ => begin
            prerr x.v1ar_loc;
            prerr ": exit(TIGER)";
            prerr ": the type of the variable is expected to be a record type";
            prerr ", but it is not.";
            prerr_newline ();
            abort {labtylst} (1)
          end // end of [_]
      ) : labtylst // end of [fts]
      val ty = loop (lab, fts) where {
        fun loop (lab0: sym, fts: labtylst):<cloref1> ty =
          case+ fts of
          | LABTYLSTcons (lab, ty, fts) =>
              if lab = lab0 then ty else loop (lab0, fts)
            // end of [LABLSTcons]
          | LABTYLSTnil () => begin
              prerr x.v1ar_loc;
              prerr ": exit(TIGER)";
              prerr ": the label ["; prerr_symbol lab0;
              prerr "] is not found in the recorded type assigned to the variable.";
              prerr_newline ();
              abort {ty} (1)
            end // end of [LABTYLSTnil]
      } // end of [val]
    in
      ty
    end // end of [FieldVar]
  | SubscriptVar (x, e_ind) => let
      val ty_arr = transVar (tmap, vmap, x)
      val ty_arr = ty_normalize ty_arr
      val ty_elt = case+ ty_arr of
        | TYarr (_(*stamp*), ty_elt) => ty_elt
        | _ => begin
            prerr x.v1ar_loc;
            prerr ": exit(TIGER)";
            prerr ": the variable should be assigned an array type";
            prerr ", but it is not";
            prerr_newline ();
            abort {ty} (1)
          end // end of [_]
      // end of [val]
      val () = transExpDn (tmap, vmap, e_ind, ty_INT)
    in
      ty_elt
    end // end of [SubscriptVar]
  val ty0 = ty_normalize ty0
in
  v1ar_ty_set (x0, ty0); ty0
end // end of [transVar]

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

fn transExpUp_callexp (
    tmap: tymap, vmap: vftymap
  , e0: exp, f: sym, es: explst
  ) : ty = let
  val vfty = vftymap_search (e0.exp_loc, vmap, f)
in
  case+ vfty.vfty_node of
  | VFTYfun (tys, ty) => ty where {
      fun loop (
          tmap: tymap
        , vmap: vftymap
        , e0: exp
        , es: explst
        , tys: tylst
        ) : void = begin case+ (es, tys) of
        | (e :: es, ty :: tys) => let
            val () =
              transExpDn (tmap, vmap, e, ty) in
            loop (tmap, vmap, e0, es, tys)
          end // end of [::, ::]
        | (nil (), nil ()) => ()
        | (cons _, nil _) => begin
            prerr_location e0.exp_loc;
            prerr ": exit(TIGER)";
            prerr ": arith mismatch: less arguments are needed";
            prerr_newline ();
            abort {void} (1)
          end // end of [cons, nil]
        | (nil _, cons _) => begin
            prerr_location e0.exp_loc;
            prerr ": exit(TIGER)";
            prerr ": arith mismatch: more arguments are needed";
            prerr_newline ();
            abort {void} (1)
          end // end of [nil, cons]
      end // end of [loop]
      val () = loop (tmap, vmap, e0, es, tys)
    } // end of [VFTYfun]
  | VFTYvar _ => begin
      prerr_location e0.exp_loc;
      prerr ": exit(TIGER)";
      prerr ": ["; prerr_symbol f;
      prerr "] should be assigned a function type but it is not.";
      prerr_newline ();
      abort {ty} (1)
    end // end of [VFTYvar]
end // end of [transExpUp_callexp]

fn transExpUp_opexp_eqop (
    tmap: tymap, vmap: vftymap, e0: exp, e1: exp, e2: exp
  ) : void = () where {
  val ty1 = transExpUp (tmap, vmap, e1)
  val ty2 = transExpUp (tmap, vmap, e2)
  val ty12 = join_ty_ty (ty1, ty2); val () = case+ ty12 of
    | TYtop () => begin
        prerr_location e0.exp_loc;
        prerr ": exit(TIGER)";
        prerr ": type mismatch: the arguments need to be assigned the same type";
        prerr ", but they are not";
        prerr_newline ();
        abort {void} (1)
      end // end of [TYtop]
    | _ => ()
  // end of [val]
} // end of [transExpUp_opexp_eqop]

fn transExpUp_opexp (
    tmap: tymap, vmap: vftymap
  , e0: exp, e1: exp, oper: oper, e2: exp
  ) : ty = let
  // macros for fun!
  macdef transExpUp_opexp_arith () = let
    val () = transExpDn (tmap, vmap, e1, ty_INT)
    val () = transExpDn (tmap, vmap, e2, ty_INT) in
    ty_INT
  end // [transExpUp_opexp_arith]
  macdef transExpUp_opexp_logic () = let
    val () = transExpDn (tmap, vmap, e1, ty_INT)
    val () = transExpDn (tmap, vmap, e2, ty_INT) in
    ty_INT
  end // [transExpUp_opexp_logic]
in
  case+ oper of
  | PlusOp _ => transExpUp_opexp_arith ()
  | MinusOp _ => transExpUp_opexp_arith ()
  | TimesOp _ => transExpUp_opexp_arith ()
  | DivideOp _ => transExpUp_opexp_arith () 
  | GtOp _ => transExpUp_opexp_logic ()
  | GeOp _ => transExpUp_opexp_logic ()
  | LtOp _ => transExpUp_opexp_logic ()
  | LeOp _ => transExpUp_opexp_logic ()
  | EqOp _ => let
      val () = transExpUp_opexp_eqop (tmap, vmap, e0, e1, e2)
    in
      ty_INT
    end // end of [EqOp]
  | NeqOp _ => let
      val () = transExpUp_opexp_eqop (tmap, vmap, e0, e1, e2)
    in
      ty_INT
    end // end of [NeqOp]
  | AndOp _ => let
      val () = transExpDn (tmap, vmap, e1, ty_INT)
      val () = transExpDn (tmap, vmap, e2, ty_INT)
    in
      ty_INT
    end // end of [AndOp]
  | OrOp _ => let
      val () = transExpDn (tmap, vmap, e1, ty_INT)
      val () = transExpDn (tmap, vmap, e2, ty_INT)
    in
      ty_INT
    end // end of [OrOp]
end // end of [transExpUp_opexp]

fn transExpUp_recordexp (
    tmap: tymap, vmap: vftymap
  , e0: exp, fes: fieldexplst, ty_rec: ty
  ) : void = () where {
  val ty_rec = ty_normalize (ty_rec)
  val lts = (case+ ty_rec of
    | TYrec (_(*stamp*), fts) => fts | _ => begin
        prerr e0.exp_loc;
        prerr ": exit(TIGER)";
        prerr ": the type for the record is not a record type.";
        prerr_newline ();
        abort {labtylst} (1)
      end // end of [_]
  ) : labtylst // end of [val]
  val () = loop (fes, lts) where {
    fun loop
      (fes: fieldexplst, lts: labtylst):<cloref1> void = begin
      case+ fes of
      | list_cons (fe, fes) => let
          val fe_lab = fe.fieldexp_lab in case+ lts of
          | LABTYLSTcons (lab, ty, lts) when fe_lab = lab => let
              val () = transExpDn (tmap, vmap, fe.fieldexp_exp, ty) in
              loop (fes, lts)
            end // end of [LABTYLSTcons _ when ...]
          | _ => begin
              prerr e0.exp_loc;
              prerr ": exit(TIGER)";
              prerr ": the lable ["; prerr_symbol fe_lab;
              prerr "] is skipped.";
              prerr_newline ();
              abort {void} (1)
            end (* end of [_] *)
        end // end of [list_cons]
      | list_nil () => begin case+ lts of
        | LABTYLSTcons (lab, _, _) => begin
            prerr e0.exp_loc;
            prerr ": exit(TIGER)";
            prerr ": the lable ["; prerr_symbol lab;
            prerr "] is extra.";
            prerr_newline ();
            abort {void} (1)
          end // end of [list_nil]
        | LABTYLSTnil () => ()
        end // end of [list_nil]
    end // end of [loop]
  } // end of [val]
} (* end of [transExpUp_recordexp] *)

implement transExpUp (tmap, vmap, e0) = let
  val ty0 = case+ e0.exp_node of
  | VarExp x => transVar (tmap, vmap, x)
  | NilExp _ => ty_NIL
  | IntExp _ => ty_INT
  | StringExp _ => ty_STRING
  | CallExp (f, es) => let
      val loc0 = e0.exp_loc in
      transExpUp_callexp (tmap, vmap, e0, f, es)
    end // end of [CallExp]
  | OpExp (e1, oper, e2) =>
      transExpUp_opexp (tmap, vmap, e0, e1, oper, e2)
    // end of [OpExp]
  | RecordExp (fes, typ) => let
      val ty_rec = ty_make_typ (tmap, typ); val () =
        transExpUp_recordexp (tmap, vmap, e0, fes, ty_rec) in
      ty_rec
    end // end of [RecordExp]
  | ArrayExp (typ, e_size, e_init) => let
      val ty_arr = ty_make_typ (tmap, typ)
      val ty_arr = ty_normalize ty_arr
      val ty_elt = (case+ ty_arr of
        | TYarr (_(*stamp*), ty_elt) => ty_elt
        | _ => begin
            prerr e0.exp_loc;
            prerr ": exit(TIGER)";
            prerr ": the type assigned to the array expression is not an array type";
            prerr_newline ();
            abort {ty} (1)
          end // end of [_]
      ) : ty // end of [val]
      val () = transExpDn (tmap, vmap, e_size, ty_INT)
      val () = transExpDn (tmap, vmap, e_init, ty_elt)
    in
      ty_arr
    end // end of [Array]
  | AssignExp (x, e) => let
      val ty = transVar (tmap, vmap, x)
      val () = transExpDn (tmap, vmap, e, ty)
    in
      ty_UNIT
    end // end of [AssignExp]
  | SeqExp es => begin case+ es of
    | list_cons _ => loop (tmap, vmap, es) where {
        fun loop {n:pos} .<n>. (
            tmap: tymap, vmap: vftymap, es: list (exp, n)
          ) : ty = let
          val+ list_cons (e, es) = es
        in
          case+ es of
          | list_cons _ => let
              val _(*ty*) =
                transExpUp (tmap, vmap, e) in loop (tmap, vmap, es)
            end // end of [list_cons]
          | list_nil () => transExpUp (tmap, vmap, e)
        end // end of [list_cons]
      } // end of [list_cons]
    | list_nil () => ty_UNIT
    end // end of [SeqExp]
  | IfExp (e1, e2, oe3) => ty where {
      val () = transExpDn (tmap, vmap, e1, ty_INT)
      val ty = (case+ oe3 of
        | Some e3 => ty where {
            val ty2 = transExpUp (tmap, vmap, e2)
(*
            val () = (prerr "ty2 = "; prerr_ty ty2; prerr_newline ())
*)
            val ty3 = transExpUp (tmap, vmap, e3)
(*
            val () = (prerr "ty3 = "; prerr_ty ty3; prerr_newline ())
*)
            val ty = join_ty_ty (ty2, ty3)
(*
            val () = (prerr "ty = "; prerr_ty ty; prerr_newline ())
*)
            val () = case+ ty of
              | TYtop () => begin
                  prerr_location e0.exp_loc;
                  prerr ": exit(TIGER): type mismatch";
                  prerr ": the type for the then-branch is [";
                  prerr_ty ty2;
                  prerr "] but the type for the else-branch is [";
                  prerr_ty ty3;
                  prerr "]";
                  prerr_newline ();
                  abort {void} (1)
                end // end of [TYtop]
              | _ => ()
            // end of [val]
          } // end of [Some]
        | None () => let
            val () = transExpDn (tmap, vmap, e2, ty_UNIT) in ty_UNIT
          end // end of [None]
      ) : ty // end of [val]
    } // end of [IfExp]
  | WhileExp (e_test, e_body) => let
      val () = transExpDn (tmap, vmap, e_test, ty_INT)
      val () = the_looplevel_inc ()
      val () = transExpDn (tmap, vmap, e_body, ty_UNIT)
      val () = the_looplevel_dec ()
    in
      ty_UNIT
    end // end of [WhileExp]
  | ForExp (ind, rb, e_lo, e_hi, e_body) => let
      val () = transExpDn (tmap, vmap, e_lo, ty_INT)
      val () = transExpDn (tmap, vmap, e_hi, ty_INT)
      val vmap = let
        val level = the_funlevel_get ()
        val vfty_ind = vfty_var_make (level, rb, ty_INT)
      in
        vftymap_insert (vmap, ind, vfty_ind)
      end // end of [val]
      val () = the_looplevel_inc ()
      val () = transExpDn (tmap, vmap, e_body, ty_UNIT)
      val () = the_looplevel_dec ()
    in
      ty_UNIT
    end // end of [ForExp]
  | BreakExp () => let
      val level = the_looplevel_get ()
    in
      case+ 0 of
      | _ when level > 0 => ty_UNIT // is this good enough?
        // should a bottom type be introduced for handling this?
      | _ => begin
          prerr_location e0.exp_loc;
          prerr ": exit(TIGER): [break] can only occur inside a loop";
          prerr_newline ();
          abort {ty} (1)
        end // end of [_]
    end // end of [BreakExp]
  | ContinueExp () => let
      val level = the_looplevel_get ()
    in
      case+ 0 of
      | _ when level > 0 => ty_UNIT // is this good enough?
        // should a bottom type be introduced for handling this?
      | _ => begin
          prerr_location e0.exp_loc;
          prerr ": exit(TIGER): [continue] can only occur inside a loop";
          prerr_newline ();
          abort {ty} (1)
        end // end of [_]
    end // end of [BreakExp]
  | LetExp (ds, e_body) => let
      var tmap = tmap and vmap = vmap
      val () = transDeclst (tmap, vmap, ds) in
      transExpUp (tmap, vmap, e_body)
    end // end of [LetExp]
(*
  | _ => begin
      prerr "INTERNAL ERROR: transExp: e = "; prerr_exp e0;
      prerr_newline ();
      abort {ty} (1)
    end // end of [_]
*)
in
  exp_ty_set (e0, ty0); ty0
end // end of [transExpUp]

implement transExpDn
  (tmap, vmap, e0, ty0) = () where {
  val ty = transExpUp (tmap, vmap, e0)
  val () = tyleq_solve (e0.exp_loc, ty, ty0)
  val () = exp_ty_set (e0, ty0)
} // end of [transExpDn]

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

fun transTypdeclst
  (tmap: &tymap, tds: typdeclst): void = () where {
  val n = list_length (tds)
  val rtyfds = aux (tmap, tds) where {
    fun aux (tmap: &tymap, tds: typdeclst)
      : List_vt @(tyref, typdec) = begin case+ tds of
      | list_cons (td, tds) => let
          val r_ty = ref_make_elt<ty> (TYtop ())
          val sym = td.typdec_name
          val () = tmap := tymap_insert (tmap, sym, TYname (sym, r_ty))
        in
          list_vt_cons (@(r_ty, td), aux (tmap, tds))
        end // end of [list_cons]
      | list_nil () => list_vt_nil ()
    end // end of [aux]
  } // end of [val]
  val () = loop (tmap, rtyfds) where {
    fun loop (
        tmap: tymap
      , xs: !List_vt @(tyref, typdec)
      ) : void =
      case+ xs of
      | list_vt_cons (x, !p_xs1) => let
          val r_ty = x.0 and td = x.1
          val () = !r_ty := ty_make_typ (tmap, td.typdec_typ)
          val () = loop (tmap, !p_xs1)
        in
          fold@ xs
        end // end of [list_vt_cons]
      | list_vt_nil () => fold@ xs
    // end of [loop]
  } // end of [val]
  var err: int = 0
  // checking for circular type definition
  val () = loop (rtyfds, n - 1, err) where {
    fun loop (
        xs: List_vt @(tyref, typdec), max: int, err: &int
      ) : void = case+ xs of
      | ~list_vt_cons (x, xs) => let
          val r_ty = x.0; val ty = ty_normalize_max (!r_ty, max)
          val () = case+ ty of
            | TYname (sym, _) => let
                val () = err := err + 1
              in
                prerr "The type ["; prerr_symbol sym;
                prerr "] is involved in a circular type definition.";
                prerr_newline ()
              end // end of [TYname]
            | _ => ()
          // end of [val]
        in
          loop (xs, max, err)
        end // end of [list_vt_cons]
      | ~list_vt_nil () => ()
    // end of [loop]
  } // end of [loop]
  val () = if err > 0 then abort {void} (1)
} // end of [transTypdeclst]

(* ****** ****** *)

typedef labrbtylst = List @(sym, refb, ty)

fn transFundec (
    tmap: tymap, vmap: &vftymap, fd: fundec
  ) : @(labrbtylst, ty) = let
  val labrbtys = aux (tmap, vmap, fd.fundec_arglst) where {
    fun aux (
        tmap: tymap
      , vmap: &vftymap
      , fts: fieldtyplst
      ) : labrbtylst = begin case+ fts of
      | list_cons (ft, fts) => let
          val loc = ft.fieldtyp_loc
          val lab = ft.fieldtyp_lab
          val typ = ft.fieldtyp_typ
          val ty = tymap_search (loc, tmap, typ)
          val rb = ft.fieldtyp_escape
          val x = @(lab, rb, ty)
        in
          list_cons (x, aux (tmap, vmap, fts))
        end // end of [list_cons]
      | list_nil () => list_nil ()
    end // end [aux]
  }
  val tys_arg = aux (labrbtys) where {
    fun aux (xs: labrbtylst): tylst = case+ xs of
      | list_cons (x, xs) => list_cons (x.2, aux xs)
      | list_nil () => list_nil ()
    // end of [aux]
  } // end of [val]
  val ty_res = (case+ fd.fundec_result of
    | Some typ => ty_make_typ (tmap, typ)
    | None () => ty_UNIT
  ) : ty // end of [val]
  val level = the_funlevel_get ()
  val vfty_fun = vfty_fun_make (level, tys_arg, ty_res)
  val () = vmap := vftymap_insert (vmap, fd.fundec_name, vfty_fun)
  // end of [val]
in
  @(labrbtys, ty_res)
end // end of [transFundec]

fn transFundeclst (
    tmap: tymap
  , vmap: &vftymap
  , fds: fundeclst
  ) : void = let
  val lrtsets = aux (tmap, vmap, fds) where {
    fun aux {n:nat} (
        tmap: tymap
      , vmap: &vftymap
      , fds: list (fundec, n)
      ) : list_vt (@(labrbtylst, exp, ty), n) = begin
      case+ fds of
      | list_cons (fd, fds) => let
          val lrtst = transFundec (tmap, vmap, fd)
          val lrtset = @(lrtst.0, fd.fundec_body, lrtst.1)
        in
          list_vt_cons (lrtset, aux (tmap, vmap, fds))
        end // end of [list_cons]
      | list_nil () => list_vt_nil ()
    end // end of [aux]
  } // end of [val]
  val () = loop (tmap, vmap, lrtsets) where {
    fun loop (
        tmap: tymap, vmap: vftymap
      , lrtsets: List_vt @(labrbtylst, exp, ty)
      ) : void = begin case+ lrtsets of
      | ~list_vt_cons (lrtset, lrtsets) => let
          val vmap_new = loop1 (vmap, lrtset.0) where {
            fun loop1
              (vmap: vftymap, lrts: labrbtylst): vftymap = begin
              case+ lrts of
              | list_cons (lrt, lrts) => let
                  val level = the_funlevel_get ()
                  val vfty = vfty_var_make (level, lrt.1, lrt.2)
                  val vmap = vftymap_insert (vmap, lrt.0, vfty)
                in
                  loop1 (vmap, lrts)
                end (* end of [LABTYLSTcons] *)
              | list_nil () => vmap
            end // end of [loop]
          } // end of [val]
          val () = transExpDn (tmap, vmap_new, lrtset.1, lrtset.2)
        in
          loop (tmap, vmap, lrtsets)
        end // end of [list_cons]
      | ~list_vt_nil () => ()
    end // end of [loop]
  } // end of [val]
in
  // empty
end // end of [transFundeclst]

implement transDec (tmap, vmap, d) = begin
  case+ d.dec_node of
  | FunctionDec fds => () where {
      val () = the_funlevel_inc ()
      val () = transFundeclst (tmap, vmap, fds)
      val () = the_funlevel_dec ()
    } // end of [FunctionDec]
  | VarDec (sym, rb, oty, e_init) => let
      val ty = (case+ oty of
        | Some typ => let
            val ty = ty_make_typ (tmap, typ) in
            transExpDn (tmap, vmap, e_init, ty); ty
          end // end of [Some]
        | None () => transExpUp (tmap, vmap, e_init)
      ) : ty
      val level = the_funlevel_get ()
      val vfty = vfty_var_make (level, rb, ty)
    in
      vmap := vftymap_insert (vmap, sym, vfty)
    end // end of [VarDec]      
  | TypeDec tds => transTypdeclst (tmap, tds)
end // end of [transDec]

implement transDeclst (tmap, vmap, ds) = case+ ds of
  | list_cons (d, ds) => begin
      transDec (tmap, vmap, d); transDeclst (tmap, vmap, ds)
    end // end of [list_cons]
  | list_nil () => ()
// end of [transDeclst]

(* ****** ****** *)

val vfty_PRINT =
  vfty_fun_make (0, $lst (ty_STRING), ty_UNIT)

val vfty_PRINT_INT =
  vfty_fun_make (0, $lst (ty_INT), ty_UNIT)

val vfty_FLUSH =
  vfty_fun_make (0, $lst (), ty_UNIT)

val vfty_GETCHAR =
  vfty_fun_make (0, $lst (), ty_STRING)

val vfty_ORD =
  vfty_fun_make (0, $lst (ty_STRING), ty_INT)

val vfty_CHR =
  vfty_fun_make (0, $lst (ty_INT), ty_STRING)

val vfty_SIZE =
  vfty_fun_make (0, $lst (ty_STRING), ty_INT)

val vfty_SUBSTRING = vfty_fun_make
  (0, $lst (ty_STRING, ty_INT, ty_INT), ty_STRING)

val vfty_CONCAT = vfty_fun_make
  (0, $lst (ty_STRING, ty_STRING), ty_STRING)

val vfty_NOT =
  vfty_fun_make (0, $lst (ty_INT), ty_INT)

val vfty_EXIT =
  vfty_fun_make (0, $lst (ty_INT), ty_UNIT)

implement transProg (e) = let
  val tmap = tmap where {
    val tmap = tymap_empty ()
    val tmap = tymap_insert (tmap, symbol_INT, ty_INT)
    val tmap = tymap_insert (tmap, symbol_STRING, ty_STRING)
    val tmap = tymap_insert (tmap, symbol_UNIT, ty_UNIT)
  } // end of [val]
  val vmap = vmap where {
    val vmap = vftymap_empty ()
    val vmap = vftymap_insert (vmap, symbol_CHR, vfty_CHR)
    val vmap = vftymap_insert (vmap, symbol_FLUSH, vfty_FLUSH)
    val vmap = vftymap_insert (vmap, symbol_GETCHAR, vfty_GETCHAR)
    val vmap = vftymap_insert (vmap, symbol_ORD, vfty_ORD)
    val vmap = vftymap_insert (vmap, symbol_PRINT, vfty_PRINT)
    val vmap = vftymap_insert (vmap, symbol_PRINT_INT, vfty_PRINT_INT)
    val vmap = vftymap_insert (vmap, symbol_SIZE, vfty_SIZE)
    val vmap = vftymap_insert (vmap, symbol_SUBSTRING, vfty_SUBSTRING)
    val vmap = vftymap_insert (vmap, symbol_CONCAT, vfty_CONCAT)
    val vmap = vftymap_insert (vmap, symbol_NOT, vfty_NOT)
    val vmap = vftymap_insert (vmap, symbol_EXIT, vfty_EXIT)
  } // end of [val]
in
  transExpUp (tmap, vmap, e)
end // end of [transProg]

(* ****** ****** *)

(* end of [tychecker.dats] *)
