\begin{verbatim}
staload "prelude/DATS/list.dats"
staload "prelude/DATS/list0.dats"
staload "prelude/DATS/list_vt.dats"

datatype exp =
  | EXPcst of double | EXPvar of string
  | EXPadd of (exp, exp) | EXPsub of (exp, exp)
  | EXPmul of (exp, exp) | EXPdiv of (exp, exp)
  | EXPpow of (exp, int)

val expcst_0 = EXPcst 0.0 and expcst_1 = EXPcst 1.0

exception UnboundVariable of string
typedef bind = @(string, double); typedef env = list0 bind

fn expvar_eval (env: env, x: string) = let
  fun aux (xds: env, x: string): double = begin case+ xds of
    | list0_cons (xd, xds) => if xd.0 = x then xd.1 else aux (xds, x)
    | list0_nil () => $raise UnboundVariable (x)
  end // end of [aux_var]
in
  aux (env, x)
end // end of [expvar_eval]

fn exp_eval (env: env, e0: exp): double = let
  fun aux (e0: exp):<cloref1> double = begin case+ e0 of
    | EXPcst c => c
    | EXPvar x => expvar_eval (env, x)
    | EXPadd (e1, e2) => aux e1 + aux e2
    | EXPsub (e1, e2) => aux e1 - aux e2
    | EXPmul (e1, e2) => aux e1 * aux e2
    | EXPdiv (e1, e2) => aux e1 / aux e2
    | EXPpow (e, i) => pow (aux e, double_of_int i)
  end // end of [aux]
in
  aux (e0)
end // end of [exp_eval]

fn exp_derivate (e0: exp, x0: string): exp = let
  fun aux (e0: exp):<cloref1> exp = case+ e0 of
    | EXPcst _ => expcst_0
    | EXPvar x => if (x = x0) then expcst_1 else expcst_0
    | EXPadd (e1, e2) => EXPadd (aux e1, aux e2)
    | EXPsub (e1, e2) => EXPsub (aux e1, aux e2)
    | EXPmul (e1, e2) => begin
        EXPadd (EXPmul (aux e1, e2), EXPmul (e1, aux e2))
      end
    | EXPdiv (e1, e2) => begin EXPdiv
        (EXPsub (EXPmul (aux e1, e2), EXPmul (e1, aux e2)), EXPpow (e2, 2))
      end
    | EXPpow (e, n) => begin
        EXPmul (EXPcst (double_of_int n), EXPmul (EXPpow (e, n-1), aux e))
      end
in
  aux (e0)
end // end of [exp_derivate]

implement main () = let
  val x = EXPvar "x" and y = EXPvar "y"
  val e = EXPadd (EXPmul (EXPpow (x, 2), EXPpow (y, 2)), expcst_1)
  val e'_x = exp_derivate (e, "x")
  val e'_y = exp_derivate (e, "y")
  val env = list0 @[bind][ @("x", 1.0), @("y", 2.0) ]
  val ans = exp_eval (env, e)
  val ans'_x = exp_eval (env, e'_x)
  val ans'_y = exp_eval (env, e'_y)
in
  printf ("ans = %f", @(ans)); print_newline ();
  printf ("ans'_x = %f", @(ans'_x)); print_newline ();
  printf ("ans'_y = %f", @(ans'_y)); print_newline ();
end
\end{verbatim}
