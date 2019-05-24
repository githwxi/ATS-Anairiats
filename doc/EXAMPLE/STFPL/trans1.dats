(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//
(* ****** ****** *)
//
// A typechecker for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//
(* ****** ****** *)

staload
POSLOC = "contrib/parcomb/SATS/posloc.sats"
(*
typedef loc_t = $POSLOC.location_t
*)
macdef prerr_loc = $POSLOC.prerr_location

(* ****** ****** *)

staload "error.sats"
staload "symbol.sats"
staload _(*anon*) = "symbol.dats"
staload "absyn.sats"

(* ****** ****** *)

staload "trans1.sats"

(* ****** ****** *)

staload M = "libats/SATS/funmap_avltree.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats" 
staload _(*anon*) = "prelude/DATS/list_vt.dats" 
staload _(*anon*) = "libats/DATS/funmap_avltree.dats" 

(* ****** ****** *)

#define l2l list_of_list_vt

(* ****** ****** *)

val t1yp_bool = T1YPbase symbol_BOOL
val t1yp_int = T1YPbase symbol_INT
val t1yp_string = T1YPbase symbol_STRING
val t1yp_unit = T1YPtup (list_nil)

(* ****** ****** *)

implement fprint_t1yp (out, t) = let
  macdef prstr (s) = fprint_string (out, ,(s))
in
  case+ t of
  | T1YPbase sym => fprint_symbol (out, sym)
  | T1YPfun (t1, t2) => let
      val isatm = (case+ t1 of
        | T1YPbase _ => true | T1YPtup _ => true | _ => false
      ) : bool
    in  
      if ~isatm then prstr "(";
      fprint_t1yp (out, t1);
      if ~isatm then prstr ")";
      prstr " -> ";
      fprint_t1yp (out, t2)
    end // end of [T1YPfun]
  | T1YPtup ts => begin
      prstr "("; fprint_t1yplst (out, ts); prstr ")"
    end // end of [T1YPtup] 
end // end of [fprint_t1yp]

implement fprint_t1yplst
  (out, ts) = loop (ts, 0) where {
  fun loop (ts: t1yplst, i: int):<cloref1> void =
    case+ ts of
    | list_cons (t, ts) => loop (ts, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_t1yp (out, t)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]
} // end of [fprint_t1yplst]

(* ****** ****** *)

implement trans1_typ (t) = aux (t) where {
  fun aux (t: t0yp): t1yp = case+ t.t0yp_node of
    | T0YPbase sym => begin case+ 0 of
        | _ when sym = symbol_UNIT => t1yp_unit | _ => T1YPbase sym
      end // end of [T0YPbase]  
    | T0YPfun (t1, t2) => T1YPfun (aux t1, aux t2)
    | T0YPtup (ts) => T1YPtup (l2l (list_map_fun (ts, aux)))
  // end of [aux]
} // end of [trans1_typ]   

(* ****** ****** *)

val cmp_sym_sym = lam
  (s1: sym, s2: sym) =<cloref> compare (s1, s2)
// end of [cmp_sym_sym]

(* ****** ****** *)

abstype theConstTypMap_t
extern fun theConstTypFind (opr: opr): t1yp

local

assume theConstTypMap_t = $M.map (sym, t1yp)

#define cmp cmp_sym_sym

#define :: list_cons; #define nil list_nil
macdef list_sing (x) = list_cons (,(x), list_nil ())

val theConstTypMap = res where {
  val ini = $M.funmap_make_nil ()
  val t1yp_int1 = T1YPtup (t1yp_int :: nil)
  val t1yp_int2 = T1YPtup (t1yp_int :: t1yp_int :: nil)
  val t1yp_str1 = T1YPtup (t1yp_string :: nil)
  val t1yp_aop = T1YPfun (t1yp_int2, t1yp_int)
  val t1yp_bop = T1YPfun (t1yp_int2, t1yp_bool)
  val cts =
    (symbol_PLUS, t1yp_aop) ::
    (symbol_MINUS, t1yp_aop) ::
    (symbol_TIMES, t1yp_aop) ::
    (symbol_SLASH, t1yp_aop) ::
    (symbol_UMINUS, T1YPfun (t1yp_int1, t1yp_int)) ::
    (symbol_GT, t1yp_bop) ::
    (symbol_GTE, t1yp_bop) ::
    (symbol_LT, t1yp_bop) ::
    (symbol_LTE, t1yp_bop) ::
    (symbol_EQ, t1yp_bop) ::
    (symbol_NEQ, t1yp_bop) ::
    (symbol_PRINT_INT, T1YPfun (t1yp_int1, t1yp_unit)) ::
    (symbol_PRINT, T1YPfun (t1yp_str1, t1yp_unit)) ::
    nil ()
  typedef T = @(sym, t1yp)
  var res: theConstTypMap_t = ini
  fun loop (cts: List T, res: &theConstTypMap_t): void =
    case+ cts of
    | ct :: cts => let
        val _already = $M.funmap_insert (res, ct.0, ct.1, cmp) in loop (cts, res)
      end // end of [::]
    | nil () => ()
  // end of [loop]  
  val () = loop (cts, res)
} // end of [val]

in // in of [local]

implement theConstTypFind (opr) = let
  val+ OPR sym = opr
  var res: t1yp?
  val ans = $M.funmap_search<sym,t1yp> (theConstTypMap, sym, cmp, res)
in
  if ans then let
    prval () = opt_unsome (res) in res
  end else let
    prval () = opt_unnone (res)
    val () = begin
      prerr "exit(STFPL)";
      prerr ": unrecognized constant ["; prerr sym; prerr "]";
      prerr_newline ()
    end (* end of [val] *)
  in
    abort {t1yp} (1)
  end // end of [None_vt]    
end // end of [theConstMapFind]

end // end of [local]

(* ****** ****** *)

fun lte_t1yp_t1yp (
  t1: t1yp, t2: t1yp
) : bool = case+ (t1, t2) of
    | (T1YPbase sym1, T1YPbase sym2) => sym1 = sym2
    | (T1YPfun (t11, t12), T1YPfun (t21, t22)) =>
        lte_t1yp_t1yp (t21, t11) andalso lte_t1yp_t1yp (t12, t22)
      // end of [T1YPfun, T1YPfun]
    | (T1YPtup ts1, T1YPtup ts2) => lte_t1yplst_t1yplst (ts1, ts2)
    | (_, _) => false
// end of [lte_t1yp_t1yp]

and lte_t1yplst_t1yplst (
  ts1: t1yplst, ts2: t1yplst
) : bool =
  case+ (ts1, ts2) of
  | (list_cons (t1, ts1), list_cons (t2, ts2)) =>
      lte_t1yp_t1yp (t1, t2) andalso lte_t1yplst_t1yplst (ts1, ts2)
    // end of [list_cons, list_cons]
  | (list_nil (), list_nil ()) => true
  | (_, _) => false
// end of [lte_t1yplst_t1yplst]

implement print_t1yp (t) = fprint_t1yp (stdout_ref, t)
implement prerr_t1yp (t) = fprint_t1yp (stderr_ref, t)

(* ****** ****** *)

implement
v1ar_make (
  loc, sym, typ
) = '{
  v1ar_loc= loc
, v1ar_nam= sym
, v1ar_typ= typ
, v1ar_def= None ()
} // end of ...

(* ****** ****** *)

implement e1xp_make_ann (loc, e, t) = '{
  e1xp_loc= loc, e1xp_node = E1XPann (e, t), e1xp_typ= t
}

implement e1xp_make_app (loc, e1, e2, t) = '{
  e1xp_loc= loc, e1xp_node = E1XPapp (e1, e2), e1xp_typ= t
}

implement e1xp_make_bool (loc, b) = '{
  e1xp_loc= loc, e1xp_node = E1XPbool b, e1xp_typ= t1yp_bool
}

implement e1xp_make_fix (loc, f, xs, body, t_fun) = '{
  e1xp_loc= loc, e1xp_node = E1XPfix (f, xs, body), e1xp_typ= t_fun
}

implement e1xp_make_if (loc, e1, e2, oe3, t) = '{
  e1xp_loc= loc, e1xp_node = E1XPif (e1, e2, oe3), e1xp_typ= t
}

implement e1xp_make_int (loc, i) = '{
  e1xp_loc= loc, e1xp_node = E1XPint i, e1xp_typ= t1yp_int
}

implement e1xp_make_lam (loc, xs, body, t_fun) = '{
  e1xp_loc= loc, e1xp_node = E1XPlam (xs, body), e1xp_typ= t_fun
}

implement e1xp_make_let (loc, decs, body, t_let) = '{
  e1xp_loc= loc, e1xp_node= E1XPlet (decs, body), e1xp_typ= t_let
}

implement e1xp_make_opr (loc, opr, es, t_res) = '{
  e1xp_loc= loc, e1xp_node= E1XPopr (opr, es), e1xp_typ= t_res
}

implement e1xp_make_proj (loc, e, i, t_proj) = '{
  e1xp_loc= loc, e1xp_node= E1XPproj (e, i), e1xp_typ= t_proj
}

implement e1xp_make_str (loc, s) = '{
  e1xp_loc= loc, e1xp_node = E1XPstr s, e1xp_typ= t1yp_string
}

implement e1xp_make_tup (loc, es, t_tup) = '{
  e1xp_loc= loc, e1xp_node = E1XPtup es, e1xp_typ= t_tup
}

implement e1xp_make_var (loc, x) = '{
  e1xp_loc= loc, e1xp_node = E1XPvar x, e1xp_typ= x.v1ar_typ
}

implement v1aldec_make (loc, x, def) = '{
  v1aldec_loc= loc, v1aldec_var= x, v1aldec_def= def
}

implement d1ec_make_val (loc, isrec, vds) = '{
  d1ec_loc= loc, d1ec_node= D1ECval (isrec, vds)
}

(* ****** ****** *)

fn typerr_mismatch
  (loc: loc, t1: t1yp, t2: t1yp): void = begin
  prerr_loc (loc);
  prerr ": exit(STFPL): type mismatch: ";
  prerr_t1yp t1; prerr " <> "; prerr_t1yp t2;
  prerr_newline ();
  abort {void} (1)
end // end of [typerr_mismatch]

typedef ctx = symenv_t (v1ar)

fun ctx_extend_arglst (
  G: &ctx, args: a0rglst
) : v1arlst = xs where {
  var xs: List_vt v1ar = list_vt_nil ()
  fun loop (
      G: &ctx, args: a0rglst, xs: &List_vt v1ar
    ) : void = case+ args of
    | list_cons (arg, args) => let
        val loc = arg.a0rg_loc and sym = arg.a0rg_nam
        val t = (case+ arg.a0rg_typ of
          | Some t => trans1_typ t | None _ => abort{t1yp} (1) where {
              val () = prerr_loc (loc)
              val () = prerr ": exit(STFPL)"
              val () = prerr ": the function arugment needs to be assigned a type."
              val () = prerr_newline ()
            } // end of [None]
        ) : t1yp // end of [val]     
        val x = v1ar_make (loc, sym, t)
        val () = xs := list_vt_cons (x, xs)
        val () = G := symenv_insert (G, sym, x)
      in
        loop (G, args, xs)
      end // end of [list_cons]  
    | list_nil () => ()
  // end of [loop]
  val () = loop (G, args, xs)
  val xs = list_vt_reverse (xs)
  val xs = l2l (xs)
} // end of [ctx_extend_arglst]

(* ****** ****** *)

implement
trans1_exp (e) =
  auxExp (G0, e) where {
  val G0: ctx = symenv_make_nil ()
  fun auxExp (G: ctx, e0: e0xp): e1xp = let
(*
    val () = begin
      prerr "auxExp: e0 = "; prerr_e0xp e0; prerr_newline ()
    end // end of [val]  
*)
    val loc0 = e0.e0xp_loc
  in
    case+ e0.e0xp_node of
    | E0XPann (e, t) => let
        val t = trans1_typ t; val e = auxExpCK (G, e, t)
      in
        e1xp_make_ann (loc0, e, t)
      end // end pf [E0XPann]  
    | E0XPapp (e1, e2) => let
        val e1 = auxExp (G, e1); val t_fun = e1.e1xp_typ
      in
        case+ t_fun of
        | T1YPfun (t_arg, t_res) => let
            val e2 = auxExpCK (G, e2, t_arg) in
            e1xp_make_app (loc0, e1, e2, t_res)
          end // end of [T1YPfun]
        | _ => abort {e1xp} (1) where {
            val () = prerr_loc (loc0)
            val () = prerr ": exit(STFPL)"
            val () = prerr ": the expression should be assigned a function type: ";
            val () = prerr_t1yp (t_fun)
            val () = prerr_newline ()
          } // end of [_]
      end // end of [E0XPapp]
    | E0XPbool b => e1xp_make_bool (loc0, b)
    | E0XPfix (sym, args, oty, body) => let
        var G = G
        val xs = ctx_extend_arglst (G, args)
        val ts_arg =
          list_map_fun<v1ar><t1yp> (xs, lam x =<fun> x.v1ar_typ)
        // end of [val]
        val ts_arg = l2l (ts_arg)
        val t_arg = (case+ ts_arg of
          | list_cons (t, list_nil ()) => t | _ => T1YPtup (ts_arg)
        ) : t1yp
        val t_res = (case+ oty of
          | Some t => trans1_typ (t) | None _ => abort {t1yp} (1) where {
              val () = prerr_loc (loc0)
              val () = prerr ": exit(STFPL)"
              val () = prerr ": the return type of a recursive function needs to be given."
              val () = prerr_newline ()
            } // end of [val]
        ) : t1yp // end of [val]
        val t_fun = T1YPfun (t_arg, t_res)
        val f = v1ar_make (loc0, sym, t_fun)
        val () = G := symenv_insert (G, sym, f)
        val body = auxExpCK (G, body, t_res)
        val e_fix = e1xp_make_fix (loc0, f, xs, body, t_fun)
        val () = v1ar_def_set (f, Some e_fix)
      in
        e_fix
      end // end of [E0XPfix]  
    | E0XPopr (opr, es) => let
        val t_opr = theConstTypFind (opr)
        val (ts_arg, t_res) = (case+ t_opr of
          | T1YPfun (t_arg, t_res) => begin case+ t_arg of
            | T1YPtup (ts_arg) => (ts_arg, t_res) | _ => (list_cons (t_arg, list_nil), t_res)
            end // end of [T1YPfun]
          | _ => begin
              prerr "INTERNAL ERROR: trans1_exp: E0XPopr"; abort {..} (1)
            end // end of [_]  
        ) : @(t1yplst, t1yp)
        stavar n1: int and n2: int
        val () = loop
          (es: list (e0xp, n1), ts_arg: list (t1yp, n2)) where {
          fun loop {n1,n2:nat} .<n1>.
            (es: list (e0xp, n1), ts: list (t1yp, n2)):<cloref1> [n1==n2] void =
            case+ (es, ts) of
            | (list_cons (_, es), list_cons (_, ts)) => loop (es, ts)
            | (list_nil (), list_nil ()) => ()
            | (list_cons _, list_nil ()) => abort (1) where {
                val () = prerr_loc (loc0)
                val () = prerr ": exit(STFPL)"
                val () = prerr ": arity mismatch: less arguments are expected."
                val () = prerr_newline ()
              } // end of [list_cons, list_nil]
            | (list_nil (), list_cons _) => abort (1) where {
                val () = prerr_loc (loc0)
                val () = prerr ": exit(STFPL)"
                val () = prerr ": arity mismatch: more arguments are expected."
                val () = prerr_newline ()
              } // end of [list_nil, list_cons]
          // end of [loop]
        } // end of [loop]
        val es = auxExpCK_list (G, es, ts_arg)
      in
        e1xp_make_opr (loc0, opr, es, t_res)
      end // edn of [E0XPopr]
    | E0XPif (e1, e2, oe3) => let
        val e1 = auxExpCK (G, e1, t1yp_bool)
        val (e2, oe3) = (case+ oe3 of
          | Some e3 => let
              val e2 = auxExp (G, e2)
              val e3 = auxExpCK (G, e3, e2.e1xp_typ)
            in
              (e2, Some e3)
            end // end of [Some]
          | None _ => let
              val e2 = auxExpCK (G, e2, t1yp_unit)
            in
              (e2, None ())
            end // end of [None]
        ) : @(e1xp, e1xpopt) // end of [val] 
        val t2 = e2.e1xp_typ
      in
        e1xp_make_if (loc0, e1, e2, oe3, t2)   
      end // end of [E0XPif]   
    | E0XPint i => e1xp_make_int (loc0, i)
    | E0XPlam (args, oty, body) => let
        var G = G
        val xs = ctx_extend_arglst (G, args)
        val ts_arg =
          list_map_fun<v1ar><t1yp> (xs, lam x =<fun> x.v1ar_typ)
        // end of [val]
        val ts_arg = l2l (ts_arg)
        val t_arg = (case+ ts_arg of
          | list_cons (t, list_nil ()) => t | _ => T1YPtup (ts_arg)
        ) : t1yp
        val body = (case+ oty of
          | Some t => let
              val t = trans1_typ t in auxExpCK (G, body, t)
            end // end of [Some]   
          | None _ => auxExp (G, body)
        ) : e1xp
        val t_res = body.e1xp_typ
      in
        e1xp_make_lam (loc0, xs, body, T1YPfun (t_arg, t_res))
      end // end of [E0XPlam]
    | E0XPlet (decs, body) => let
        var G = G
        val decs = auxDeclst (G, decs)
        val body = auxExp (G, body)
      in
        e1xp_make_let (loc0, decs, body, body.e1xp_typ)
      end // end of [val]  
    | E0XPproj (e, i) => let
        val [i:int] i = int1_of_int (i)
        val () = (if i >= 0 then () else begin
          prerr_loc (loc0);
          prerr ": exit(STFPL)"; prerr ": negative index is illegal";
          prerr_newline ();
          abort (1)
        end) : [i >= 0] void
        val e = auxExp (G, e)
        val t_tup = e.e1xp_typ
        val t_proj = (case+ t_tup of
          | T1YPtup ts => loop (ts, i) where {
              fun loop (ts: t1yplst, i: Nat):<cloref1> t1yp =
                case+ ts of
                | list_cons (t, ts) => if i > 0 then loop (ts, i-1) else t
                | list_nil () => begin
                    prerr_loc (loc0);
                    prerr ": exit(STFPL)";
                    prerr ": index is too large for the tuple expression.";
                    prerr_newline ();
                    abort (1)
                  end // end of [list_nil]
              // end of [loop]    
            } // end of [T1YPtup]
          | _ => begin
              prerr_loc (loc0);
              prerr ": exit(STFPL)";
              prerr ": a tuple type for the expression is expected: ";
              prerr_t1yp t_tup;
              prerr_newline ();
              abort (1)
            end // end of [_]  
        ) : t1yp
      in
        e1xp_make_proj (loc0, e, i, t_proj)
      end // end of [E0XPproj]  
    | E0XPstr (s) => e1xp_make_str (loc0, s)
    | E0XPtup (es) => let
        prval pf = unit_v ()
        val es = list_map_vclo (pf | es, !p_clo) where {
          var !p_clo = @lam
            (pf: !unit_v | e: e0xp): e1xp =<clo> $effmask_all (auxExp (G, e))
          // end of [var
        } // end of [val]
        prval unit_v () = pf
        val es = l2l (es)
        val ts = list_map_fun<e1xp><t1yp> (es, lam e =<fun> e.e1xp_typ)
        val ts = l2l (ts)
      in
        e1xp_make_tup (loc0, es, T1YPtup ts)
      end // end of [E0XPtup]
    | E0XPvar sym => let
        val ans = symenv_lookup (G, sym)
      in
        case+ ans of
        | ~Some_vt (x) => e1xp_make_var (loc0, x)
        | ~None_vt () => let
            val () = prerr_loc (loc0)
            val () = prerr ": exit(STFPL)"
            val () = (prerr ": unbound variable ["; prerr sym; prerr "]")
            val () = prerr_newline ()
          in
            abort {e1xp} (1)
          end // end of [None_vt]
      end (* end of [E0XPvar] *)
(*
    | _ => exit (1)
*)
  end // end of [auxExp]
//
  and auxExpCK
    (G: ctx, e: e0xp, t: t1yp): e1xp = e where {
    val loc = e.e0xp_loc
    val e = auxExp (G, e)
    val t1 = e.e1xp_typ and t2 = t
    val ans = lte_t1yp_t1yp (t1, t2)
    val () = if ~ans then typerr_mismatch (loc, t1, t2)
  } // end of [auxExpCK]
//
  and auxExpCK_list {n:nat}
    (G: ctx, es: list (e0xp, n), ts: list (t1yp, n)): e1xplst =
    case+ (es, ts) of
    | (list_cons (e, es), list_cons (t, ts)) => let
        val e = auxExpCK (G, e, t); val es = auxExpCK_list (G, es, ts)
      in
        list_cons (e, es)
      end // end of [list_cons, list_cons]
    | (list_nil (), list_nil ()) => list_nil ()
  (* end of [auxExpCK_list] *)
//
  and auxDec (G: &ctx, dec: d0ec): d1ec =
    case+ dec.d0ec_node of
    | D0ECval (isrec, vds) => let
        val vds = auxValdeclst (G, isrec, vds)
        val dec = d1ec_make_val (dec.d0ec_loc, isrec, vds)
      in
        dec
      end // end of [D0ECval]
  (* end of [auxDec] *)
//
  and auxValdeclst
    (G: &ctx, isrec: bool, vds: v0aldeclst): v1aldeclst =
    case+ 0 of
    | _ when isrec => let
        val xs = aux (vds) where {
          fun aux {n:nat} .<n>. (
            vds: list (v0aldec, n)
          ) : list (v1ar, n) = case+ vds of
            | list_cons (vd, vds) => let
                val loc = vd.v0aldec_loc and sym = vd.v0aldec_nam
                val t_val = (case+ vd.v0aldec_ann of
                  | Some t => trans1_typ t
                  | None () => abort (1) where {
                      val () = prerr_loc (loc)
                      val () = prerr ": exit(STFPL)"
                      val () = prerr ": a recursive declaration needs to be annotated with a type."
                      val () = prerr_newline ()
                    } // end of [None]
                ) : t1yp // end of [val]
                val x = v1ar_make (loc, sym, t_val)
              in
                list_cons (x, aux (vds))
              end // end of [list_cons]  
            | list_nil () => list_nil ()
          // end of [aux]   
        } // end of [val]
        val () = loop (G, xs) where {
          fun loop (
            G: &ctx, xs: v1arlst
          ) : void = case+ xs of
            | list_cons (x, xs) => let
                val () = G := symenv_insert (G, x.v1ar_nam, x) in loop (G, xs)
              end // end of [list_cons]
            | list_nil () => ()
          // end of [loop]  
        } // end of [val]
        val vds = aux (G, xs, vds) where {
          fun aux {n:nat} .<n>.
            (G: ctx, xs: list (v1ar, n), vds: list (v0aldec, n))
            : list (v1aldec, n) =
            case+ xs of
            | list_cons (x, xs) => let
                val+ list_cons (vd, vds) = vds
                val def = auxExp (G, vd.v0aldec_def)
                val vd = v1aldec_make (vd.v0aldec_loc, x, def)
                val () = v1ar_def_set (x, Some def)
              in
                list_cons (vd, aux (G, xs, vds))
              end // end of [list_cons]
            | list_nil () => list_nil ()
        } // end of [val]
      in
        vds
      end // end of [_ when isrec]
    | _ (*nonrec*) => vds where {
        val defs = aux (G, vds) where {
          fun aux {n:nat} .<n>.
            (G: ctx, vds: list (v0aldec, n)): list (e1xp, n) =
            case+ vds of
            | list_cons (vd, vds) => let
                val def = (case+ vd.v0aldec_ann of
                  | Some t => let
                      val t = trans1_typ (t) in auxExpCK (G, vd.v0aldec_def, t)
                    end // end of [Some]
                  | None () => auxExp (G, vd.v0aldec_def)
                ) : e1xp // end of [val]
              in
                list_cons (def, aux (G, vds))
              end // end of [list_cons]
            | list_nil () => list_nil ()
          // end of [aux]   
        } // end of [val]
        val vds = aux (G, vds, defs) where {
          fun aux {n:nat} .<n>. (
              G: &ctx
            , vds: list (v0aldec, n)
            , defs: list (e1xp, n)
            ) : list (v1aldec, n) = case+ vds of
            | list_cons (vd, vds) => let
                val+ list_cons (def, defs) = defs
                val loc = vd.v0aldec_loc and sym = vd.v0aldec_nam
                val x = v1ar_make (loc, sym, def.e1xp_typ)
                val vd = v1aldec_make (loc, x, def)
                val () = G := symenv_insert (G, sym, x)
                val vds = aux (G, vds, defs)
              in
                list_cons (vd, vds)
              end // end of [list_cons]  
            | list_nil () => list_nil ()
          // end of [aux]     
        } // end of [val]
     } (* end of [_ when nonrec] *)
  (* end of [auxDec] *)
//
  and auxDeclst (G: &ctx, decs: d0eclst): d1eclst =
    case+ decs of
    | list_cons (dec, decs) => let
        val dec = auxDec (G, dec)
        val decs =  auxDeclst (G, decs)
      in
        list_cons (dec, decs)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [auxDeclst]  
} (* end of [trans1_exp] *)

(* ****** ****** *)

extern typedef "v1ar_t" = v1ar

%{$

ats_bool_type
eq_v1ar_v1ar (v1ar_t x1, v1ar_t x2) {
  return (x1 == x2 ? ats_true_bool : ats_false_bool) ;
} /* end of [eq_v1ar_v1ar] */

ats_void_type
v1ar_def_set (
  ats_ptr_type x
, ats_ptr_type oe
) {
  ((v1ar_t)x)->atslab_v1ar_def = oe ;  return ;
} /* end of [v1ar_def_set] */

%} // end of [%{$]

(* ****** ****** *)

(* end of [trans1.dats] *)
