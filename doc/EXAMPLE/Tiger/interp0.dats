(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "error.sats"

staload "symbol.sats"
typedef sym = symbol_t
typedef symlst = List sym

(* ****** ****** *)

staload "absyn.sats"

(* ****** ****** *)

staload "interp0.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/array0.dats"
staload _(*anonymous*) = "prelude/DATS/list.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

implement fprint_value (out, v) = let
  macdef prstr (str) = fprint_string (out, ,(str))
in
  case+ v of
  | VALint i => begin
      prstr "VALint("; fprint_int (out, i); prstr ")"
    end // end of [VALint]
  | VALstring s => begin
      prstr "VALstring("; fprint_string (out, s); prstr ")"
    end // end of [VALint]
  | VALrec _ => begin
      prstr "VALrec("; fprint_string (out, "..."); prstr ")"
    end // end of [VALrec]
  | VALarr _ => begin
      prstr "VALarr("; fprint_string (out, "..."); prstr ")"
    end // end of [VALarr]
  | VALunit () => begin
      prstr "VALunit("; prstr ")"
    end // end of [VALunit]
end // end of [fprint_value]

implement print_value (v) = fprint_value (stdout_ref, v)
implement prerr_value (v) = fprint_value (stderr_ref, v)

(* ****** ****** *)

staload M = "LIB/funmap_avltree.dats"

datatype vfval =
  | VFVALvar of ref (value)
  | VFVALfun of (ref env, symlst, exp) // static binding
  | VFVALpre of (valuelst -<fun1> value)

where env = $M.map_t (sym, vfval)

(*
// A note:
// dynamic binding is implemented if the [env] argument of
// [VFVALfun] is dropped
//
*)

typedef valref = ref (value)

local

val _cmp =
  lam (x1: sym, x2: sym): Sgn =<cloref> compare (x1, x2)
// end of [val]

in // in of [local]

fn env_empty (): env = $M.funmap_empty<> ()

fn env_search
  (env: env, sym: sym): vfval = let
  val ans =
    $M.funmap_search<sym,vfval> (env, sym, _cmp) in
  case+ ans of
  | ~Some_vt (vfval) => vfval | ~None_vt () => begin
      prerr "INTERNAL ERROR";
      prerr ": env_search: unbound symbol: sym = ";
      prerr_symbol sym;
      prerr_newline ();
      abort {vfval} (1)
    end // end of [None_vt]
end // end of [env_search]

fn env_insert
  (env: env, sym: sym, vfval: vfval): env = begin
  $M.funmap_insert<sym,vfval> (env, sym, vfval, _cmp)
end // end of [env_insert]

end // end of [local]

(* ****** ****** *)

extern fun interp0Var (env: env, x: v1ar): value
extern fun interp0Exp (env: env, e: exp): value
extern fun interp0Dec (env: env, d: dec): env

(* ****** ****** *)

implement interp0Var
  (env, x) = case+ x.v1ar_node of
  | SimpleVar sym => let
      val ans = env_search (env, sym) in
      case+ ans of
      | VFVALvar v_ref => !v_ref | _ => begin
          prerr "INTERNAL ERROR";
          prerr ": interp0Var: unbound variable: sym = ";
          prerr_symbol sym;
          prerr_newline ();
          abort {value} (1)
        end // end of [None_vt]
    end // end of [SimpleVar]
  | FieldVar (x1, lab) => let
      val v_rec = interp0Var (env, x1)
      val- VALrec lvs = v_rec
      fun loop (lab: sym, lvs: labvaluelst): value =
        case+ lvs of
        | LABVALUELSTcons (l, v_ref, lvs) =>
            if lab = l then !v_ref else loop (lab, lvs)
        | LABVALUELSTnil () => begin
            prerr "INTERNAL ERROR";
            prerr ": interp0Var: FieldVar: unfound label: lab = ";
            prerr_symbol lab;
            prerr_newline ();
            abort {value} (1)
          end // end of [LABVALUELSTnil]
      // end of [loop]
    in
      loop (lab, lvs)
    end // end of [FieldVar]
  | SubscriptVar (x1, e_ind) => let
      val v_arr = interp0Var (env, x1)
      val- VALarr arr = v_arr
      val v_ind = interp0Exp (env, e_ind)
      val- VALint i_ind = v_ind
(*
      val asz = array0_size arr
      val asz = int_of_size asz
      val () = assert (i_ind < asz)
*)
    in
      arr[i_ind]
    end // end of [SubscriptVar]
// end of [interp0Var]

(* ****** ****** *)

fun interp0Exp_CallExp
  (env0: env, f: sym, es: explst): value = let
  val vfval = env_search (env0, f) in case+ vfval of
    | VFVALfun (r_env, xs, e_body) => let
        val env = loop (!r_env, xs, es) where {
          fun loop (
              env: env, xs: symlst, es: explst
            ) :<cloref1> env =
            case+ (xs, es) of
            | (list_cons (x, xs), list_cons (e, es)) => let
                val v = interp0Exp (env0, e)
                val v_ref = ref_make_elt<value> (v)
                val env = env_insert (env, x, VFVALvar v_ref)
              in
                loop (env, xs, es)
              end // end of [list_cons, list_cons]
            | (_, _) => env
          // end of [loop]
        } // end of [val]
      in
        interp0Exp (env, e_body)
      end // end of [VFVALfun]
    | VFVALpre f_pre => let
        var !p_interp0 = @lam
          (pf: !unit_v | e: exp): value =<clo1> interp0Exp (env0, e)
        // end of [var]
        prval pf = unit_v
        val vs = list_map_vclo<exp><value> (pf | es, !p_interp0)
        prval unit_v () = pf
        val vs = list_of_list_vt (vs)
      in
        f_pre (vs)
      end // end of [VFVALpre]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": interp0Exp_CallExp: unbound function: sym = ";
        prerr_symbol f;
        prerr_newline ();
        abort {value} (1)
      end // end of [_]
end // end of [interp0Exp_CallExp]

(* ****** ****** *)

macdef TRUE = 1 and FALSE = 0
macdef isTRUE (b) = (,(b) <> 0)

fn interp0Exp_OpExp_eqop (v1: value, v2: value): int = res where {
  val res = (case+ (v1, v2) of
    | (VALint i1, VALint i2) => if i1 = i2 then TRUE else FALSE
    | (VALstring s1, VALstring s2) => if s1 = s2 then TRUE else FALSE
    | (VALunit _, VALunit _) => TRUE
    | (VALrec _, VALunit _) => FALSE
    | (VALunit _, VALrec _) => FALSE
    | (_, _) => begin
        prerr "INTERNAL ERROR";
        prerr ": interp0Exp_OpExp_eqop: argument mismatch";
        prerr_newline ();
        abort {int} (1)
      end // end of [_, _]
  ) : int
} // end of [interp0Exp_OpExp_eqop]

fn interp0Exp_OpExp
  (env: env, e1: exp, oper: oper, e2: exp): value = let
  val v1 = interp0Exp (env, e1); val v2 = interp0Exp (env, e2)
in
  case+ oper of
  | PlusOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (i1 + i2)
    end // end of [PlusOp]
  | MinusOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (i1 - i2)
    end // end of [MinusOp]
  | TimesOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (i1 * i2)
    end // end of [TimesOp]
  | DivideOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (i1 / i2)
    end // end of [DivideOp]
  | EqOp _ => let
      val eq = interp0Exp_OpExp_eqop (v1, v2) in VALint (eq)
    end // end of [NeqOp]
  | NeqOp _ => let
      val eq = interp0Exp_OpExp_eqop (v1, v2)
      val neq = if isTRUE (eq) then FALSE else TRUE
    in
      VALint (neq)
    end // end of [NeqOp]
  | GtOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (if i1 > i2 then TRUE else FALSE)
    end // end of [GtOp]
  | GeOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (if i1 >= i2 then TRUE else FALSE)
    end // end of [GeOp]
  | LtOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (if i1 < i2 then TRUE else FALSE)
    end // end of [LtOp]
  | LeOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (if i1 <= i2 then TRUE else FALSE)
    end // end of [LeOp]
  | AndOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (if isTRUE (i1) then i2 else FALSE)
    end // end of [AndOp]
  | OrOp _ => let
      val- VALint i1 = v1; val- VALint i2 = v2
    in
      VALint (if isTRUE (i1) then TRUE else i2)
    end // end of [OrOp]
end // end of [interp0Exp_OpExp]

(* ****** ****** *)

fun interp0Exp_RecordExp
  (env: env, fes: fieldexplst): labvaluelst = let
  fun loop (
      env: env
    , fes: fieldexplst
    , res: &labvaluelst? >> labvaluelst
    ) : void =
    case+ fes of
    | list_cons (fe, fes) => let
        val l = fe.fieldexp_lab
        val v = interp0Exp (env, fe.fieldexp_exp)
        val v_ref = ref_make_elt<value> (v)
        val () = res := LABVALUELSTcons (l, v_ref, ?)
        val+ LABVALUELSTcons (_, _, !p_res_nxt) = res
        val () = loop (env, fes, !p_res_nxt)
      in
        fold@ res
      end // end of [list_cons]
    | list_nil () => (res := LABVALUELSTnil ())
  // end of [loop]
  var res: labvaluelst // uninitialized
  val () = loop (env, fes, res)
in
  res
end // end of [interp0Exp_RecordExp]

(* ****** ****** *)

fn interp0Exp_SeqExp
  (env: env, es: explst): value = case+ es of
  | list_cons _ => loop es where {
      fun loop {n:int | n > 0} .<n>.
        (es: list (exp, n)):<cloref1> value = let
        val+ list_cons (e, es) = es
        val v = interp0Exp (env, e) in case+ es of
          | list_cons _ => loop (es) | list_nil _ => v
      end // end of [loop]
    } // end of [list_cons]
  | list_nil () => VALunit ()
// end of [SeqExp]

fn interp0Exp_AssignExp
  (env: env, x: v1ar, e: exp): void = case+ x.v1ar_node of
  | SimpleVar sym => let
      val ans = env_search (env, sym) in
      case+ ans of
      | VFVALvar v_ref => let
          val v = interp0Exp (env, e) in !v_ref := v
        end // end of [VFVALvar]
      | _ => begin
          prerr "INTERNAL ERROR";
          prerr ": interp0Exp_AssignExp: unbound variable: sym = ";
          prerr_symbol sym;
          prerr_newline ();
          abort {void} (1)
        end // end of [None_vt]
    end // end of [SimpleVar]
  | FieldVar (x1, lab) => let
      val v_rec = interp0Var (env, x1)
      val- VALrec lvs = v_rec
      fun loop
        (env: env, lab: sym, lvs: labvaluelst, e: exp): void =
        case+ lvs of
        | LABVALUELSTcons (l, v_ref, lvs) =>
            if lab = l then let
              val v = interp0Exp (env, e) in !v_ref := v
            end else begin
              loop (env, lab, lvs, e)
            end // end of [if]
        | LABVALUELSTnil () => begin
            prerr "INTERNAL ERROR";
            prerr ": interp0Var: FieldVar: unfound label: lab = ";
            prerr_symbol lab;
            prerr_newline ();
            abort {void} (1)
          end // end of [LABVALUELSTnil]
      // end of [loop]
    in
      loop (env, lab, lvs, e)
    end // end of [FieldVar]
  | SubscriptVar (x1, e_ind) => let
      val v_arr = interp0Var (env, x1)
      val- VALarr arr = v_arr
      val v_ind = interp0Exp (env, e_ind)
      val- VALint i_ind = v_ind
      val v = interp0Exp (env, e)
    in
      arr[i_ind] := v
    end // end of [val]
// end of [interp0Exp_AssignExp]


local

exception LoopBreak of ()
exception LoopContinue of ()

in // in of [local]

fn interp0Exp_WhileExp
  (env: env, e_test: exp, e_body: exp): void = let
  fun loop
    (env: env, e_test: exp, e_body: exp): void = let
    val v_test =
      interp0Exp (env, e_test)
    val- VALint i_test = v_test
  in
    if isTRUE (i_test) then let
      val _(*unit*) = interp0Exp (env, e_body)
    in
      loop (env, e_test, e_body)
    end // end of [if]
  end // end of [loop]
in
  try loop (env, e_test, e_body) with
    | ~LoopBreak () => ()
    | ~LoopContinue () => loop (env, e_test, e_body)
  // end of [try]
end (* end of [WhileExp] *)

fn interp0Exp_ForExp
  (env: env, x: sym, e_lo: exp, e_hi: exp, e_body: exp)
  : void = let
  val v_lo = interp0Exp (env, e_lo)
  val- VALint i_lo = v_lo
  val v_hi = interp0Exp (env, e_hi)
  val- VALint i_hi = v_hi
  val v_ref = ref_make_elt<value> (v_lo)
  val env = env_insert (env, x, VFVALvar v_ref)
  fun loop
    (env: env, e_body: exp, i: int):<cloref1> void =
    if i < i_hi then let
      val _(*unit*) = interp0Exp (env, e_body)
      val () = !v_ref := VALint (i+1) in loop (env, e_body, i+1)
    end else begin
      if i <= i_hi then let
        val _(*unit*) = interp0Exp (env, e_body) in // no increment
      end // end of [if]
    end (* end of [if] *)
  // end of [loop]
in
  try loop (env, e_body, i_lo) with
    | ~LoopBreak () => ()
    | ~LoopContinue () => let
        val v = !v_ref; val- VALint i = v in
        if i < i_hi then let
          val () = !v_ref := VALint (i+1) in loop (env, e_body, i+1)
        end // end of [if]
      end (* end of [LoopContinue] *)
  // end of [try]
end // end of [interp0Exp_forexp]

fn interp0Exp_BreakExp (): value = $raise LoopBreak ()
fn interp0Exp_ContinueExp (): value = $raise LoopContinue ()

end // end of [local]

(* ****** ****** *)

implement interp0Exp
  (env, e) = case+ e.exp_node of
  | VarExp x => interp0Var (env, x)
  | NilExp () => VALunit ()
  | IntExp i => VALint i
  | StringExp s => VALstring s
  | CallExp (f, es) => 
      interp0Exp_CallExp (env, f, es)
    // end of [CallExp]
  | OpExp (e1, oper, e2) =>
      interp0Exp_OpExp (env, e1, oper, e2)
    // end of [OpExp]
  | RecordExp (fes, _(*type*)) => let
      val lvs = interp0Exp_RecordExp (env, fes) in VALrec lvs
    end // end of [RecordExp]
  | SeqExp es => interp0Exp_SeqExp (env, es)
  | AssignExp (x, e) => let
      val () = interp0Exp_AssignExp (env, x, e) in
      VALunit ()
    end // end of [AssignExp]
  | IfExp (e1, e2, oe3) => let
      val v1 = interp0Exp (env, e1)
      val- VALint i1 = v1
    in
      if isTRUE (i1) then begin
        interp0Exp (env, e2)
      end else begin case+ oe3 of
        | Some e3 => interp0Exp (env, e3)
        | None () => VALunit ()
      end // end of [if]
    end // end of [IfExp]
  | WhileExp (e_test, e_body) => let
      val () = interp0Exp_WhileExp (env, e_test, e_body) in
        VALunit ()
    end // end of [WhileExp]
  | ForExp (x, _, e_lo, e_hi, e_body) => let
      val () = interp0Exp_ForExp (env, x, e_lo, e_hi, e_body) in
      VALunit ()
    end // end of [ForExp]
  | BreakExp () => interp0Exp_BreakExp ()
  | ContinueExp () => interp0Exp_ContinueExp ()
  | LetExp (ds, e_body) => interp0Exp (env, e_body) where {
      fun loop (env: env, ds: declst): env = case+ ds of
        | list_cons (d, ds) => let
            val env = interp0Dec (env, d) in loop (env, ds)
          end // end of [list_cons]
        | list_nil () => env
      // end of [loop]
      val env = loop (env, ds)
    } // end of [LetExp]
  | ArrayExp (_(*typ*), e_size, e_init) => let
      val v_size = interp0Exp (env, e_size)
      val- VALint i_size = v_size
      val i_size = int1_of_int i_size
      val i_size = begin
        if i_size >= 0 then size_of_int1 (i_size) else begin
          print "interp0Exp: array size is negative: size = ";
          print i_size;
          abort {size_t} (1)
        end // end of [if]
      end : size_t // end of [val]
      val v_init = interp0Exp (env, e_init)
      val arr = array0_make_elt<value> (i_size, v_init)
    in
      VALarr (arr)
    end // end of [ArrayExp]
// end of [interp0Exp]

(* ****** ****** *)

fn interp0Fundec
  (r_env: ref env, fd: fundec): void = let
(*
  val () = begin
    prerr "interp0Fundec: fd.fundec_name = ";
    prerr fd.fundec_name;
    prerr_newline ()
  end // end of [val]
*)
  val arg = list_map_fun<fieldtyp><sym>
    (fd.fundec_arglst, lam (x) =<fun> x.fieldtyp_lab)
  val arg = list_of_list_vt (arg) 
  val vfval = VFVALfun (r_env, arg, fd.fundec_body)
in
  !r_env := env_insert (!r_env, fd.fundec_name, vfval)
end // end of [interp0Fundec]

implement interp0Dec (env, d) = let
(*
  val () = begin
    prerr "interp0Dec: enter"; prerr_newline ()
  end // end of [val]
*)
in
  case+ d.dec_node of
  | VarDec (sym, _, _, e_init) => let
      val v_init = interp0Exp (env, e_init)
      val v_ref = ref_make_elt<value> (v_init)
(*
      val () = begin
        prerr "interp0Dec: VarDec: sym = "; prerr_symbol sym;
        prerr_newline ()
      end // end of [val]
*)
      val vfval = VFVALvar v_ref
    in
      env_insert (env, sym, vfval)
    end // end of [VarDec]
  | FunctionDec fds => loop (r_env, fds) where {
      val r_env = ref_make_elt<env> (env)
      fun loop (r_env: ref env, fds: fundeclst): env = begin
        case+ fds of
        | list_cons (fd, fds) => let
            val () = interp0Fundec (r_env, fd) in loop (r_env, fds)
          end // end of [list_cons]
        | list_nil () => !r_env
      end (* end of [loop] *)
    } // end of [FunctionDec]
  | TypeDec _ => env // type declarations are ignored
end (* end of [interp0Dec] *)


(* ****** ****** *)

val vfval_chr = lam (vs: valuelst): value => let
  val- list_cons (v, _) = vs
  val- VALint i = v
  val c = char_of_int (i)
  val sbp = string_make_char (1, c)
  val s = string1_of_strbuf (sbp)
in
  VALstring (s)
end // end of [vfval_chr]

val vfval_concat = lam (vs: valuelst): value => let
  val- list_cons (v1, vs) = vs
  val- VALstring str1 = v1
  val- list_cons (v2, vs) = vs
  val- VALstring str2 = v2
in
  VALstring (str1 + str2)
end // end of [vfval_concat]

val vfval_flush =
  lam (vs: valuelst): value => let
  val () = fflush_exn (stdout_ref) in VALunit ()
end // end of [vfval_flush]

val vfval_getchar = lam (vs: valuelst): value => let
  val i = getchar ()
  val c = char_of_int i
  val sbp = string_make_char (1, c)
  val s = string1_of_strbuf (sbp)
in
  VALstring (s)
end // end of [vfval_getchar]

val vfval_ord = lam (vs: valuelst): value => let
  val- list_cons (v, _) = vs
  val- VALstring s = v
  val s = string1_of_string s
  val () = assert (string_isnot_atend (s, 0))
  val c = s[0]
  val i = int_of_char c
in
  VALint (i)
end // end of [vfval_ord]

val vfval_print = lam (vs: valuelst): value => let
  val- list_cons (v, _) = vs
  val () = case+ v of
    | VALint int => fprint_int (stdout_ref, int)
    | VALstring str => fprint_string (stdout_ref, str)
    | _ => () // not supported
  // end of [val]
in
  VALunit ()
end // end of [vfval_print]

val vfval_print_int = lam (vs: valuelst): value => let
  val- list_cons (v, _) = vs
  val- VALint int = v
  val () = fprint_int (stdout_ref, int)
in
  VALunit ()
end // end of [vfval_print_int]

val vfval_print_str = lam (vs: valuelst): value => let
  val- list_cons (v, _) = vs
  val- VALstring str = v
  val () = fprint_string (stdout_ref, str)
in
  VALunit ()
end // end of [vfval_print]

val vfval_size = lam (vs: valuelst): value => let
  val- list_cons (v, _) = vs; val- VALstring str = v
  val n = string_length (str)
  val n = int_of_size n
in
  VALint (n)
end // end of [vfval_size]

val vfval_substring = lam (vs: valuelst): value => let
  val- list_cons (v1, vs) = vs; val- VALstring str = v1
  val- list_cons (v2, vs) = vs; val- VALint st = v2
  val- list_cons (v3, vs) = vs; val- VALint ln = v3
  val str = string1_of_string str
  val nstr = string1_length (str)
  val st = int1_of_int st and ln = int1_of_int ln
  val () = assert_errmsg_bool1 (st >= 0, "substring: illegal start")
  val () = assert_errmsg_bool1 (ln >= 0, "substring: illegal length")
  val () = assert_errmsg_bool1 (st+ln <= nstr, "substring: illegal length")
  val st = size1_of_int1 st and ln = size1_of_int1 ln
  val substr =
    string1_of_strbuf (sbp) where {
    val sbp = string_make_substring (str, st, ln)
  } // end of [val]
in
  VALstring (substr)
end // end of [vfval_substring]

implement interp0Prog (e) = let
  val env = env_empty ()
  val env = env_insert (env, symbol_CHR, VFVALpre vfval_chr)
  val env = env_insert (env, symbol_CONCAT, VFVALpre vfval_concat)
  val env = env_insert (env, symbol_FLUSH, VFVALpre vfval_flush)
  val env = env_insert (env, symbol_GETCHAR, VFVALpre vfval_getchar)
  val env = env_insert (env, symbol_ORD, VFVALpre vfval_ord)
  val env = env_insert (env, symbol_PRINT, VFVALpre vfval_print)
  val env = env_insert (env, symbol_PRINT_INT, VFVALpre vfval_print_int)
  val env = env_insert (env, symbol_SIZE, VFVALpre vfval_size)
  val env = env_insert (env, symbol_SUBSTRING, VFVALpre vfval_substring)
in
  interp0Exp (env, e)
end // end of [interp0Prog]

(* ****** ****** *)

(* end of [interp0.dats] *)
