(*
**
** An Example of Stack Algebra
** See Section 8.5.2 in Dines Bjorner's SE book
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

staload "stack_alg.sats"
staload "stack_list.sats"

(* ****** ****** *)

datatype
stlst (a:t@ype, ilist) =
  | stlst_nil (a, nil) of ()
  | {x:int} {xs:ilist}
    stlst_cons (a, cons (x, xs)) of (E (a, x), stlst (a, xs))
assume Stack (a:t@ype, xs:ilist) = stlst (a, xs)

(* ****** ****** *)

implement{a}
make_nil () = (EMPTY () | stlst_nil)

implement{a}
is_empty (es) = case+ es of
  | stlst_nil () => (IS_EMPTY_nil | true)
  | stlst_cons _ => (IS_EMPTY_cons | false)
// end of [is_empty]

implement{a}
top (pf | es) = (TOP () | e) where {
  prval IS_EMPTY_cons () = pf // proving that [es] is not empty
  val+ stlst_cons (e, _) = es
} // end of [top]

implement{a}
pop (pf | es) = (POP () | es) where {
  prval IS_EMPTY_cons () = pf // proving that [es] is not empty
  val+ stlst_cons (_, es) = es
} // end of [pop]

implement{a}
push (e, es) = (PUSH () | stlst_cons (e, es))

(* ****** ****** *)

(* end of [stack_list.dats] *)
