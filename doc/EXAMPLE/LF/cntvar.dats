//
//
// An example constructed to answer a question
// raised by Adam Poswosky
//
// Time: July 25 & 26
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
//

datasort typ = typ_0 | typ_arr of (typ, typ)

dataparasort exp = exp_lam of (exp -> exp) | exp_app of (exp, exp)

stadef typ_id = typ_arr (typ_0, typ_0)
stadef fexp_id = lam (x: exp) => x
stadef exp_id = exp_lam (fexp_id)

stadef typ_xy = typ_arr (typ_id, typ_id)
stadef fexp_xy = lam (x: exp) => exp_lam (lam (y: exp) => exp_app (x, y))
stadef exp_xy = exp_lam (fexp_xy)

datasort ctx = ctx_nil | ctx_cons of (exp, typ, ctx)

#define nil ctx_nil
#define cons ctx_cons
#define :: ctx_cons

//

datatype IND (ctx, exp, typ) = // deBruijn indexes
  | {ets:ctx;e:exp;t:typ} INDone (cons (e, t, ets), e, t)
  | {ets:ctx;e,e1:exp;t,t1:typ} INDsucc (cons (e1, t1, ets), e, t) of IND (ets, e, t)

fun cntind {ets:ctx;e:exp;t:typ} (ind: IND (ets, e, t)): int =
  case+ ind of INDone () => 0 | INDsucc ind => cntind (ind) + 1

datatype EXP (ctx, exp, typ) =
  | {ets:ctx;e:exp;t:typ} Var (ets, e, t) of IND (ets, e, t)
  | {ets:ctx;f:exp->exp;t1,t2:typ}
      Lam (ets, exp_lam f, typ_arr (t1, t2)) of {e:exp} EXP (cons (e, t1, ets), f e, t2)
  | {ets:ctx; e1,e2:exp; t1,t2:typ}
      App (ets, exp_app (e1, e2), t2) of (EXP (ets, e1, typ_arr (t1, t2)), EXP (ets, e2, t2))

extern praxi exp_new (): [c:exp] void // an oracle

fun cntvar_one {ets:ctx;e:exp;t:typ} (E: EXP (ets, e, t), i: int): int =
  case+ E of
  | Var ind => if cntind (ind) = i then 1 else 0
  | App (E1, E2) => cntvar_one (E1, i) + cntvar_one (E2, i)
  | Lam (F) => let
      prval [c:exp] () = exp_new ()
    in
      cntvar_one (F {c}, i + 1)
    end

fun cntvar_all {ets:ctx;e:exp;t:typ} (E: EXP (ets, e, t)): int =
  case+ E of
  | Var ind => 1
  | App (E1, E2) => cntvar_all (E1) + cntvar_all (E2)
  | Lam (F) => let
      prval [c:exp] () = exp_new ()
    in
      cntvar_all (F {c})
    end

(* ****** ****** *)

val EXP_id: EXP (nil, exp_id, typ_id) =
  Lam {nil,fexp_id,typ_0,typ_0} (Var (INDone))

val EXP_xy: EXP (nil, exp_xy, typ_xy) =
  Lam {nil,fexp_xy,typ_id,typ_id}
    (Lam (App (Var (INDsucc INDone), Var (INDone))))

implement main () = begin
  print "cntvar_all (EXP_id) = "; print (cntvar_all (EXP_id)); print_newline ();
  print "cntvar_one (EXP_id, ~1) = "; print (cntvar_one (EXP_id, ~1)); print_newline ();
  print "cntvar_all (EXP_xy) = "; print (cntvar_all (EXP_xy)); print_newline ();
  print "cntvar_one (EXP_xy, ~1) = "; print (cntvar_one (EXP_xy, ~1)); print_newline ();
  print "cntvar_one (EXP_xy, ~2) = "; print (cntvar_one (EXP_xy, ~2)); print_newline ();
end // end of [main]

(* ****** ****** *)

(* end of [cntvar] *)
