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
// An interpreter for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//
(* ****** ****** *)

staload "prelude/DATS/list.dats"
staload "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "error.sats"
staload "symbol.sats"
staload _(*anon*) = "symbol.dats"
staload "absyn.sats"
staload "trans1.sats"

(* ****** ****** *)

staload "interp1.sats"

(* ****** ****** *)

implement fprint_v1al (out, v) = let
  macdef prstr (s) = fprint_string (out, ,(s))
in 
  case+ v of
  | V1ALbool b => begin
      prstr "V1ALbool("; fprint_bool (out, b); prstr ")"
    end // end [V1ALbool]  
  | V1ALint i => begin
     prstr "V1ALint("; fprint_int (out, i); prstr ")"
    end // end of [V1ALint]
  | V1ALclo _ => begin
      prstr "V1ALclo("; fprint_string (out, "..."); prstr ")"
    end // end of [V1ALclo]
  | V1ALstr s => begin
      prstr "V1ALstr("; fprint_string (out, s); prstr ")"
    end // end of [V1ALstr]
  | V1ALtup (vs) => begin
      prstr "V1ALtup("; fprint_v1allst (out, vs); prstr ")"
    end // end of [V1ALtup]
  | V1ALref (r) => fprint_v1al (out, !r)
end // end of [fprint_v1al]

implement fprint_v1allst
  (out, vs) = loop (vs, 0) where {
  fun loop (vs: List v1al, i: int):<cloref1> void =
    case+ vs of
    | list_cons (v, vs) => loop (vs, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_v1al (out, v)
      } // end of [list_cons]
    | list_nil () => () 
  // end of [loop]  
} // end of [fprint_v1allst]

implement print_v1al (v) = fprint_v1al (stdout_ref, v)
implement prerr_v1al (v) = fprint_v1al (stderr_ref, v)

(* ****** ****** *)

typedef v1alref = ref (v1al)
typedef v1alreflst = List (v1alref)

val v1al_dummy = V1ALint (0)

implement interp1_exp (e0) = let
//
  #define :: list_cons; #define nil list_nil
//
  fun auxExp (
    env: env, e0: e1xp
  ) : v1al = begin
    case+ e0.e1xp_node of
    | E1XPann (e, t) => auxExp (env, e)
    | E1XPapp (e1, e2) => let
        val v1 = auxExp (env, e1)
        val v1 = (
          case+ v1 of V1ALref r => !r | _ => v1
        ) : v1al
        val v2 = auxExp (env, e2)
        val- V1ALclo (env1, xs, body) = v1
        val env = (case+ xs of
          | x :: nil () =>
             symenv_insert (env1, x.v1ar_nam, v2)
            // unary function call  
          | _ => loop (env1, xs, vs) where {
              fun loop (
                  env1: env, xs: v1arlst, vs: List v1al
                ) : env = case+ vs of
                | list_cons (v, vs) => let
                    val- list_cons (x, xs) = xs 
                    val env1 = symenv_insert (env1, x.v1ar_nam, v)
                  in
                    loop (env1, xs, vs)
                  end // end of [list_cons]  
                | list_nil () => env1
              // end of [loop]   
              val- V1ALtup vs = v2
            } // end of [_]
        ) : env // end of [val]
      in
        auxExp (env, body)
      end (* end of [E1XPapp] *)
    | E1XPbool (b) => V1ALbool (b)
    | E1XPfix (f, xs, body) => !r where {
        val r = ref<v1al> (v1al_dummy)
        val v = V1ALref (r)
        val env = symenv_insert (env, f.v1ar_nam, v)
        val () = !r := V1ALclo (env, xs, body)
      } // end of [E1XPfix]
    | E1XPif (e1, e2, oe3) => let
        val- V1ALbool b = auxExp (env, e1)
      in
        if b then auxExp (env, e2) else begin case+ oe3 of
          | Some e3 => auxExp (env, e3) | None () => V1ALtup (nil)
        end // end of [if]
      end // end of [E1XPif]
    | E1XPint (i) => V1ALint (i)
    | E1XPlam (xs, body) => V1ALclo (env, xs, body)
    | E1XPlet (decs, body) => let
        val env = auxDeclst (env, decs) in auxExp (env, body)
      end // end of [E1XPlet]
    | E1XPopr (opr, es) => auxOpr (env, opr, es)
    | E1XPproj (e, i) => loop (vs, i) where {
        val- V1ALtup vs = auxExp (env, e)
        fun loop (vs: List v1al, i: int): v1al = let
          val- list_cons (v, vs) = vs
        in
          if i > 0 then loop (vs, i-1) else v
        end // end of [loop]
      } // end of [E1XPproj]  
    | E1XPstr (s) => V1ALstr (s)
    | E1XPtup (es) => let
        val vs = auxExp_list (env, es) in V1ALtup (vs)
      end // end of [E1XPtup]
    | E1XPvar (x) => auxVar (env, x)
(*
    | _ => begin
        prerr "auxExp: not implemented"; prerr_newline (); abort (1)
      end // end of [_]
*)
  end // end of [auxExp]    
//
  and auxExp_list (
    env: env, es: e1xplst
  ) : List v1al = case+ es of
    | list_cons (e, es) => list_cons (auxExp (env, e), auxExp_list (env, es))
    | list_nil () => list_nil ()
  (* end of [auxExp_list] *)
//
  and auxOpr
    (env: env, opr: opr, es: e1xplst): v1al = let
    val+ OPR sym = opr
    val vs = auxExp_list (env, es)
  in
    case+ 0 of
    | _ when sym = symbol_PLUS => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 + i2)
      end // end of [_ when ...]
    | _ when sym = symbol_MINUS => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 - i2)
      end // end of [_ when ...]
    | _ when sym = symbol_TIMES => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 * i2)
      end // end of [_ when ...]
    | _ when sym = symbol_SLASH => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 / i2)
      end // end of [_ when ...]
    | _ when sym = symbol_UMINUS => let
        val- V1ALint i :: _ = vs in V1ALint (~i)
      end // end of [_ when ...]
    | _ when sym = symbol_GT => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 > i2)
      end // end of [_ when ...]
    | _ when sym = symbol_GTE => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 >= i2)
      end // end of [_ when ...]
    | _ when sym = symbol_LT => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 < i2)
      end // end of [_ when ...]
    | _ when sym = symbol_LTE => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 <= i2)
      end // end of [_ when ...]
    | _ when sym = symbol_EQ => let      
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 = i2)
      end // end of [_ when ...]
    | _ when sym = symbol_NEQ => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 <> i2)
      end // end of [_ when ...]
    | _ when sym = symbol_PRINT => let
        val- V1ALstr s :: _ = vs; val () = print_string s
      in
        V1ALtup (nil)
      end // end of [_ when ...]
    | _ when sym = symbol_PRINT_INT => let
        val- V1ALint i  :: _ = vs; val () = print_int i
      in
        V1ALtup (nil)
      end // end of [_ when ...]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": exit(STFPL): interp: auxExp: opr = "; prerr sym; prerr_newline ();
        abort {v1al} (1)
      end // end of [_]
  end // end of [auxOpr]
//
  and auxVar (
    env: env, x: v1ar
  ) : v1al = let
(*
    val () = (print "x = "; print (x.v1ar_nam); print_newline ())
*)
    val- ~Some_vt (v) = symenv_lookup (env, x.v1ar_nam)
  in
    v
  end // end of [auxVar]
//
  and auxDec (
    env: env, dec: d1ec
  ) : env =
    case+ dec.d1ec_node of
    | D1ECval (isrec, vds) => auxValdeclst (env, isrec, vds)
  (* end of [auxDec] *)
//
  and auxValdeclst (
    env: env, isrec: bool, vds: v1aldeclst
  ) : env =
    case+ 0 of
    | _ when isrec => env where {
        fun loop1 (
          env: env, vds: v1aldeclst, res: env, rs: v1alreflst
        ) : (env, v1alreflst)  =
          case+ vds of
          | list_cons (vd, vds) => let
              val x = vd.v1aldec_var
              val r = ref<v1al> (v1al_dummy)
              val v = V1ALref (r)
              val res = symenv_insert (res, x.v1ar_nam, v)
              val rs = list_cons (r, rs)
            in
              loop1 (env, vds, res, rs)
            end // end of [list_cons]
          | list_nil () => (res, rs)
        // end of [loop]  
        val (env, rs) = loop1 (env, vds, env, list_nil)
        val rs = list_reverse (rs)
        val rs = list_of_list_vt (rs)
        fun loop2 (
          env: env, vds: v1aldeclst, rs: v1alreflst
        ) : void =
          case+ (vds, rs) of
          | (list_cons (vd, vds), list_cons (r, rs)) => (
              !r := auxExp (env, vd.v1aldec_def); loop2 (env, vds, rs)
            ) // end of [list_cons, list_cons]
          | (_, _) => ()
        // end of [loop2]
        val () = loop2 (env, vds, rs)
      } // end of [_ (*rec*) ]
    | _ (*nonrec*) => res where {
        fun loop (
          env: env, vds: v1aldeclst, res: env
        ) : env =
          case+ vds of
          | list_cons (vd, vds) => let
              val x = vd.v1aldec_var
              val def = auxExp (env, vd.v1aldec_def)
              val res = symenv_insert (res, x.v1ar_nam, def)
            in
              loop (env, vds, res)
            end // end of [list_cons]
          | list_nil () => res
        // end of [loop]
        val res = loop (env, vds, env)
      } // end of [_ (*nonrec*) ]
  (* end of [auxValdeclst] *)
//
  and auxDeclst (
    env: env, decs: d1eclst
  ) : env = begin
    case+ decs of
    | list_cons (dec, decs) => let
        val env = auxDec (env, dec) in auxDeclst (env, decs)
      end // end of [list_cons]
    | list_nil () => env
  end // end of [auxDeclst]     
//
  val env0: env = symenv_make_nil ()
in
  auxExp (env0, e0)
end // end of [interp1_exp]

(* ****** ****** *)

(* end of [interp1.dats] *)
