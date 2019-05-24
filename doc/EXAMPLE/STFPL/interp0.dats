(*
** CAS CS525, Spring 2011
** Instructor: Hongwei Xi
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "absyn.sats"
staload "error.sats"
staload "symbol.sats"
staload _(*anon*) = "symbol.dats"

(* ****** ****** *)

staload "interp0.sats"

exception ArityMismatch of ()
exception OperatorError of ()
exception SubscriptError of ()
exception TypeError of ()
exception UnboundVariable of ()

(* ****** ****** *)

(*
** please implement as follows the function interfaces declared
** in [interp0.sats]
*)

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

implement
fprint_v0al (out, v) =
  case+ v of
  | V0ALbool (b) =>
      fprint! (out, "V0ALbool(", b, ")")
  | V0ALint (i) =>
      fprint! (out, "V0ALint(", i, ")")
  | V0ALstr (s) =>
      fprint! (out, "V0ALstr(", s, ")")
  | V0ALtup vs => () where {
      val () = fprint (out, "V0ALtup(")
      val () = fprint_v0allst (out, vs)
      val () = fprint (out, ")")
    } // end of [V0ALtup]
  | V0ALclo _ => fprint! (out, "V0ALclo(...)")
  | V0ALfix _ => fprint! (out, "V0ALfix(...)")
  | V0ALref _ => fprint! (out, "V0ALref(...)")
// end of [fprint_v0al]

implement
fprint_v0allst (out, vs) =
  list_iforeach_cloref<v0al> (vs,
    lam (i, v) =<cloref1> let
      val () = if i > 0 then fprint_string (out, ", ")
    in
      fprint_v0al (out, v)
    end // end of [lam]
  ) // end of [list0_iforeach_cloref]
(* end of [fprint_v0allst] *)

implement print_v0al (x) = fprint_v0al (stdout_ref, x)
implement prerr_v0al (x) = fprint_v0al (stderr_ref, x)

(* ****** ****** *)

(*
implement
interp0_exp (e) = let
  val () = println! ("interp0_exp: yet to be implemented!")
  val () = assertloc (false)
in
  exit (1)
end // end of [interp0_exp]
*)

(* ****** ****** *)

typedef env = symenv_t (v0al)

extern
fun eval (env: env, e: e0xp): v0al

(* ****** ****** *)

val v0al_void = V0ALtup (nil)

fun evalopt (
  env: env, oe: e0xpopt
) : v0al =
  case+ oe of
  | Some (e) => eval (env, e) | None () => v0al_void
// end of [evalopt]

fun evallst (
  env: env, es: e0xplst
) : List v0al = let
  val es = list_map_cloref<e0xp><v0al> (es, lam e =<cloref1> eval (env, e))
in
  list_of_list_vt (es)
end // end of [evallst]

(* ****** ****** *)

fun eval_var (
  env: env, x: sym
) : v0al = let
  val ans = symenv_lookup (env, x)
in
  case+ ans of
  | ~Some_vt v => v
  | ~None_vt () => let
      val () = (
        prerr "eval_var: unbound variable: "; prerr x; prerr_newline ()
      ) // end of [val]
    in
      $raise UnboundVariable ()
    end // end of [option0_none]
end // end of [eval_var]

(* ****** ****** *)

fun eval_if (
  env: env, e_test: e0xp, e_then: e0xp, e_else: e0xpopt
) : v0al = let
  val v_test = eval (env, e_test)
in
  case+ v_test of
  | V0ALbool b =>
      if b then eval (env, e_then) else evalopt (env, e_else)
  | _ => $raise TypeError ()
end // end of [eval_if]

(* ****** ****** *)

fun eval_opr (
  env: env, opr: opr, es: e0xplst
) : v0al = let
  val OPR nam = opr
  val vs = evallst (env, es)
in
  if nam = symbol_UMINUS then
    case vs of
    | V0ALint i :: nil () => V0ALint (~i)
    | _ => $raise TypeError ()
  else if nam = symbol_PLUS then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALint (i1 + i2)
    | _ => $raise TypeError ()
  else if nam = symbol_MINUS then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALint (i1 - i2)
    | _ => $raise TypeError ()
  else if nam = symbol_TIMES then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALint (i1 * i2)
    | _ => $raise TypeError ()
  else if nam = symbol_SLASH then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALint (i1 / i2)
    | _ => $raise TypeError ()
  else if nam = symbol_GT then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALbool (i1 > i2)
    | _ => $raise TypeError ()
  else if nam = symbol_GTE then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALbool (i1 >= i2)
    | _ => $raise TypeError ()
  else if nam = symbol_LT then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALbool (i1 < i2)
    | _ => $raise TypeError ()
  else if nam = symbol_LTE then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALbool (i1 <= i2)
    | _ => $raise TypeError ()
  else if nam = symbol_EQ then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALbool (i1 = i2)
    | _ => $raise TypeError ()
  else if nam = symbol_NEQ then
    case vs of
    | V0ALint i1 :: V0ALint i2 :: nil () => V0ALbool (i1 <> i2)
    | _ => $raise TypeError ()
  else if nam = symbol_PRINT then
    case vs of
    | V0ALstr s :: nil () => (print_string s; v0al_void)
    | _ => $raise TypeError ()
  else if nam = symbol_PRINT_INT then
    case vs of
    | V0ALint i :: nil () => (print_int i ; v0al_void)
    | _ => $raise TypeError ()
  else let
    val () = (
      prerr "Unrecognized Operator: "; prerr nam; prerr_newline ()
    ) // end of [val]
  in
    $raise OperatorError ()
  end // end of [if]
end (* end of [eval_opr] *)

(* ****** ****** *)

fun argenv_extend (
  env: env, args: a0rglst, v0: v0al
) : symenv_t v0al =
  case+ args of
  | (arg :: nil ()) =>
      symenv_insert (env, arg.a0rg_nam, v0)
  | _ => (case+ v0 of
    | V0ALtup vs => argenvlst_extend (env, args, vs)
    | _ => $raise TypeError ()
    ) // end of [_]
// end of [argenv_extend]

and argenvlst_extend (
  env: env, args: a0rglst, vs: List (v0al)
) : env =
  case+ (args, vs) of
  | (arg :: args, v :: vs) => let
      val env = symenv_insert (env, arg.a0rg_nam, v)
    in
      argenvlst_extend (env, args, vs)
    end // end of ...
  | (nil (), nil ()) => env
  | (_, _) => $raise ArityMismatch ()
// end of [argenvlst_extend]

(* ****** ****** *)

fun eval_app (
  env: env, e1: e0xp, e2: e0xp
) : v0al = let
  val v1 = eval (env, e1)
  val v2 = eval (env, e2)
in
  case+ v1 of
  | V0ALclo (env, e_lam) => let
      val- E0XPlam (args, _, e_body) = e_lam.e0xp_node
      val env = argenv_extend (env, args, v2)
    in
      eval (env, e_body)
    end // end of [V0ALclo]
  | V0ALfix (env, e_fix) => let
      val- E0XPfix (f, args, _, e_body) = e_fix.e0xp_node
      val env = argenv_extend (env, args, v2)
      val env = symenv_insert (env, f, v1)
    in
      eval (env, e_body)
    end // end of [V0ALclo]
  | V0ALref r => let
(*
      val () = println! ("eval_app: !r = ", !r)
*)
      val- V0ALclo (env, e_lam) = !r
      val- E0XPlam (args, _, e_body) = e_lam.e0xp_node
      val env = argenv_extend (env, args, v2)
    in
      eval (env, e_body)
    end // end of [V0ALref]
  | _ => $raise TypeError ()
end // end of [eval_app]

(* ****** ****** *)

fun eval_proj (
  env: env, e: e0xp, n: int
) : v0al = let
  val v = eval (env, e)
  val n = int1_of_int (n)
  val () = assert (n >= 0)
in
  case+ v of
  | V0ALtup vs => (try
      list_nth_exn (vs, n)
    with
      | ~ListSubscriptException () => $raise SubscriptError ()
    ) // end of [V0ALtup]
  | _ => $raise TypeError ()
end // end of [eval_proj]

(* ****** ****** *)

fun eval_v0aldeclst_true (
  env: env, vds: v0aldeclst
) : env = let
  typedef v0alref = ref (v0al)
  fun loop (
    env: env
  , vds: v0aldeclst
  , res: env
  , rs: List (v0alref)
  ) : (env, List (v0alref)) =
    case+ vds of
    | cons (vd, vds) => let
        val x = vd.v0aldec_nam
        val r = ref<v0al> (V0ALint (0)) // dummy for now
        val v = V0ALref (r)
        val res = symenv_insert (res, x, v)
      in
        loop (env, vds, res, r :: rs)
      end // end of [list0_cons]
    | nil () => (res, rs)
  // end of [loop]
  val (env, rs) = loop (env, vds, env, nil)
  val rs = list_reverse (rs)
  val rs = list_of_list_vt (rs)
  fun loop2 (
    env: env
  , vds: v0aldeclst
  , rs: List (v0alref)
  ) : void =
    case+ (vds, rs) of
    | (cons (vd, vds), cons (r, rs)) => (
        !r := eval (env, vd.v0aldec_def); loop2 (env, vds, rs)
      ) // end of ...
    | (_, _) => ()
  // end of [loop2]
  val () = loop2 (env, vds, rs)
in
  env
end // end of [eval_v0aldeclst_true]

fun eval_v0aldeclst_false (
  env: env, vds: v0aldeclst
) : env = let
  fun loop (
    env: env, vds: v0aldeclst, res: env
  ) : env =
    case+ vds of
    | cons (vd, vds) => let
        val x = vd.v0aldec_nam
        val v = eval (env, vd.v0aldec_def)
        val res = symenv_insert (res, x, v)
      in
        loop (env, vds, res)
      end // end of [list0_cons]
    | nil () => res
in
  loop (env, vds, env)
end // end of [eval_v0aldeclst_false]

(*
and d0ec_node =
  | D0ECval of (bool(*isrec*), v0aldeclst)
// end of [d0ec_node]
*)
fun eval_dec
  (env: env, d: d0ec): env =
  case+ d.d0ec_node of
  | D0ECval (isrec, vds) =>
      if isrec then
        eval_v0aldeclst_true (env, vds)
      else
        eval_v0aldeclst_false (env, vds)
      // end of [if]
// end of [eval_dec]

(* ****** ****** *)

fun eval_declst
  (env: env, ds: d0eclst): env =
  case+ ds of
  | cons (d, ds) => let
      val env = eval_dec (env, d) in eval_declst (env, ds)
    end // end of [list0_cons]
  | nil () => env
// end of [eval_declst]

(* ****** ****** *)

implement
eval (env, e) =
  case+ e.e0xp_node of
  | E0XPann (e, _) => eval (env, e)
  | E0XPbool (b) => V0ALbool (b)
  | E0XPint (i) => V0ALint (i)
  | E0XPstr (s) => V0ALstr (s)
  | E0XPvar (x) => eval_var (env, x)
  | E0XPif (e_test, e_then, e_else) =>
      eval_if (env, e_test, e_then, e_else)
  | E0XPopr (opr, es) => eval_opr (env, opr, es)
  | E0XPtup es => let
      val vs = evallst (env, es) in V0ALtup (vs)
    end // end of [E0XPtup]
  | E0XPproj (e, n) => eval_proj (env, e, n)
  | E0XPlam _ => V0ALclo (env, e)
  | E0XPlet (ds, e) => let
      val env = eval_declst (env, ds)
    in
      eval (env, e)
    end // end of [E0XPlet]
  | E0XPfix _ => V0ALfix (env, e)
  | E0XPapp (e1, e2) => eval_app (env, e1, e2)
// end of [eval]

(* ****** ****** *)

implement
interp0_exp (e) = let
  val env = symenv_make_nil () in eval (env, e)
end // end of [interp0]

(* ****** ****** *)

(* end of [interp0.dats] *)
