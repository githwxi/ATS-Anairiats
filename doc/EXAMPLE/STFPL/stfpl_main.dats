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

staload "absyn.sats"
staload "parser.sats"
staload "interp0.sats"
staload "trans1.sats"
staload "interp1.sats"

(* ****** ****** *)

dynload "contrib/parcomb/dynloadall.dats"

(* ****** ****** *)

dynload "error.dats"
dynload "symbol.dats"
dynload "absyn.dats"
dynload "fixity.dats"
dynload "parser.dats"
dynload "interp0.dats"
dynload "trans1.dats"
dynload "interp1.dats"

(* ****** ****** *)

(*
//
// Usage: ./stfpl < [input file]
//
// For instance, you can try
//
//   ./stfpl < EXAMPLE/ackermann.stfpl
//   ./stfpl < EXAMPLE/fact.stfpl
//   ./stfpl < EXAMPLE/fact_fix.stfpl
//   ./stfpl < EXAMPLE/fib.stfpl
//   ./stfpl < EXAMPLE/queens.stfpl
//
*)

fn stfpl_usage (cmd: string): void = () where {
  val () = printf ("%s < [source code in stfpl]\n", @(cmd))
} // end of [val]

(* ****** ****** *)

implement main () = () where {
  val () = begin
    print "Please input a program written in STFPL:"; print_newline ()
  end // end of [val]
  val prog = parse_from_stdin ()
  val () = print "prog =\n"
  val () = fprint_e0xp (stdout_ref, prog) 
  val () = print_newline ()
//
(*
  val v0al = interp0_exp (prog)
  val () = (print "v0al = "; print_v0al v0al; print_newline ())
*)
//
  val e1xp = trans1_exp (prog)
  val t1yp = e1xp.e1xp_typ
  val () = (print "t1yp = "; print_t1yp t1yp; print_newline ())
  val v1al = interp1_exp (e1xp)
  val () = (print "v1al = "; print_v1al v1al; print_newline ())
//
} // end of [main]

(* ****** ****** *)

//
// Some examples of STFPL programs are given as follows
//

(* ****** ****** *)

(*

/*
** computing ackermann numbers
*/

let

val
rec ack: (int, int) -> int = lam (m: int, n: int) =>
  if m > 0 then
    if n > 0 then ack (m-1, ack (m, n-1)) else ack (m-1, 1)
  else n+1

val _ = print "ack (3, 3) = "
val _ = print_int (ack (3, 3))
val _ = print "\n"

in

()

end // end of [let]

/* ****** ****** */

/* end of [ackermann.stfpl] */

*)

(* ****** ****** *)

(*

/*
** implementing MacCarthy's 91-function
*/

let
  val
  rec f91: int -> int =
    lam (n: int) => if n >= 101 then n - 10 else f91 (f91 (n + 11))
  // end of [val rec]
  val _ = print "f91 (57) = "
  val _ = print_int (f91 57)
  val _ = print "\n"
in
  ()
end // end of [let]

/* ****** ****** */

/* end of [f91.stfpl] */

*)

(* ****** ****** *)

(*

/*
** computing the factorial numbers
*/

let
  val
  rec fact: int -> int =
    lam (n: int) => if n >= 1 then n * fact (n-1) else 1
  // end of [val rec]
  val _ = print "fact (10) = "
  val _ = print_int (fact 10)
  val _ = print "\n"
in
  fact (10)
end // end of [let]

/* ****** ****** */

/* end of [fact.stfpl] */

*)

(* ****** ****** *)

(*

/*
** computing the factorial numbers
*/

let
  val fact = fix f (n:int): int => if n >= 1 then n * f (n-1) else 1
  // end of [val rec]
  val fact10 = fact (10)
  val _ = print "fact (10) = "
  val _ = print_int (fact10)
  val _ = print "\n"
in
  ()
end // end of [let]

/* ****** ****** */

/* end of [fact_fix.stfpl] */

*)

(* ****** ****** *)

(*

/*
** computing the fibonacci numbers
*/

let 
  val rec fib: int -> int = lam (n: int) =>
    if n >= 2 then fib (n-1) + fib (n-2) else n
  // end of [val rec]
  val fib20 = fib (20)
  val _ = print "fib (20) = "
  val _ = print_int (fib20)
  val _ = print "\n"
in
  ()
end // end of [let]

/* ****** ****** */

/* end of [fib.stfpl] */

*)

(* ****** ****** *)

(*

/*
**
** The eight-queens problem
** 
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: June 21, 2009
**
** The original version was written when the author was at U of Cincinnati
** around 2000.
**
*/

let
  val abs =
    lam (x:int): int => if x >= 0 then x else ~x
  // end of [abs]

  val dots_pr = fix f (n:int): unit =>
    if n > 0 then let val _ = print (".") in f (n-1) end
  // end of [dots_pr]

  val row_pr = lam (n:int): unit => let
    val _ = dots_pr (n-1)
    val _ = print ("Q")
    val _ = dots_pr (8-n)
  in  
    print ("\n")
  end // end of [val]

  val board_pr = lam
    (bd: (int, (int, (int, (int, (int, (int, (int, int)))))))): unit => let
    val _ = row_pr (bd.0)
    val bd = bd.1
    val _ = row_pr (bd.0)
    val bd = bd.1
    val _ = row_pr (bd.0)
    val bd = bd.1
    val _ = row_pr (bd.0)
    val bd = bd.1
    val _ = row_pr (bd.0)
    val bd = bd.1
    val _ = row_pr (bd.0)
    val bd = bd.1
    val _ = row_pr (bd.0)
    val _ = row_pr (bd.1)
  in
    ()
  end // end of [board_pr]

  val test2 = lam (x: (int, int)): bool =>
    let val x1 = x.0 and x2 = x.1 in
      if x1 = x2 then false else abs (x1-x2) <> 1
    end
  // end of [val test2]

  val test_2 = lam (xyn: (int, ((int, int), int))): bool => let
    val x = xyn.0
    val yn = xyn.1
    val y = yn.0
    val n = yn.1
    val y1 = y.0
    val y2 = y.1
  in
    if x = y1 then false else (
      if abs(x-y1) = n+1 then false else
        (if x = y2 then false else abs (x-y2) <> n+2)
    )
  end // end of [test_2]

  val test3 = lam (x: (int, (int, int))): bool => let
    val x1 = x.0
    val x2 = x.1
  in
    if test_2 (x1, (x2, 0)) then test2 (x2) else false
  end // end of [test3]

  val test_3 = lam (xyn: (int, ((int, (int, int)), int))): bool => let
    val x = xyn.0
    val yn = xyn.1
    val y = yn.0
    val n = yn.1
    val y1 = y.0
    val y2 = y.1
  in
    if x = y1 then false else (
      if abs(x-y1) = n+1 then false else test_2 (x, (y2, n+1))
    )
  end

  val test4 = lam (x: (int, (int, (int, int)))): bool => let
    val x1 = x.0
    val x2 = x.1
  in
    if test_3 (x1, (x2, 0)) then test3 (x2) else false
  end // end of [test4]

  val test_4 = lam (xyn: (int, ((int, (int, (int, int))), int))): bool => let
    val x = xyn.0
    val yn = xyn.1
    val y = yn.0
    val n = yn.1
    val y1 = y.0
    val y2 = y.1
  in
    if x = y1 then false else (
      if abs(x-y1) = n+1 then false else test_3 (x, (y2, n+1))
    )
  end // end of [test_4]

  val test5 = lam (x: (int, (int, (int, (int, int))))): bool => let
    val x1 = x.0
    val x2 = x.1
  in
    if test_4 (x1, (x2, 0)) then test4 (x2) else false
  end // end of [test5]

  val test_5 = lam
    (xyn: (int, ((int, (int, (int, (int, int)))), int))): bool => let
    val x = xyn.0
    val yn = xyn.1
    val y = yn.0
    val n = yn.1
    val y1 = y.0
    val y2 = y.1
  in
    if x = y1 then false else (
      if abs(x-y1) = n+1 then false else test_4 (x, (y2, n+1))
    )
  end // end of [test_5]

  val test6 = lam (x: (int, (int, (int, (int, (int, int)))))): bool => let
    val x1 = x.0
    val x2 = x.1
  in
    if test_5 (x1, (x2, 0)) then test5 (x2) else false
  end // end of [test6]

  val test_6 = lam
    (xyn: (int, ((int, (int, (int, (int, (int, int))))), int))): bool => let
    val x = xyn.0
    val yn = xyn.1
    val y = yn.0
    val n = yn.1
    val y1 = y.0
    val y2 = y.1
  in
    if x = y1 then false else (
      if abs(x-y1) = n+1 then false else test_5 (x, (y2, n+1))
    )
  end // end of [test_6]

  val test7 = lam
    (x: (int, (int, (int, (int, (int, (int, int))))))): bool => let
    val x1 = x.0
    val x2 = x.1
  in
    if test_6 (x1, (x2, 0)) then test6 (x2) else false
  end // end of [test7]

  val test_7 = lam
    (xyn: (int, ((int, (int, (int, (int, (int, (int, int)))))), int))): bool => let
    val x = xyn.0
    val yn = xyn.1
    val y = yn.0
    val n = yn.1
    val y1 = y.0
    val y2 = y.1
  in
    if x = y1 then false else (
      if abs(x-y1) = n+1 then false else test_6 (x, (y2, n+1))
    )
  end // end of [test_7]

  val test8 = lam
    (x: (int, (int, (int, (int, (int, (int, (int, int)))))))): bool => let
    val x1 = x.0
    val x2 = x.1
  in
    if test_7 (x1, (x2, 0)) then test7 (x2) else false
  end // end of [test8]

  val
  rec inc1: int -> unit =
    lam (x: int) => if x < 8 then inc2 (0, x+1) else ()
  // end of [inc1]

  and inc2: (int, int) -> unit = lam
    (xy: (int, int)) => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test2 (x+1, y) then inc3 (0, (x+1, y)) else inc2 (x+1, y)
    else inc1 (y)
  end // end of [inc2]

  and inc3: (int, (int, int)) -> unit = lam
    (xy: (int, (int, int))) => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test3 (x+1, y) then inc4 (0, (x+1, y)) else inc3 (x+1, y)
    else inc2 (y)
  end // end of [inc3]

  and inc4: (int, (int, (int, int))) -> unit = lam
    (xy: (int, (int, (int, int)))) => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test4 (x+1, y) then inc5 (0, (x+1, y)) else inc4 (x+1, y)
    else inc3 (y)
  end // end of [inc4]

  and inc5: (int, (int, (int, (int, int)))) -> unit = lam
    (xy: (int, (int, (int, (int, int))))) => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test5 (x+1, y) then inc6 (0, (x+1, y)) else inc5 (x+1, y)
    else inc4 (y)
  end // end of [inc5]

  and inc6: (int, (int, (int, (int, (int, int))))) -> unit = lam
    (xy: (int, (int, (int, (int, (int, int)))))) => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test6 (x+1, y) then inc7 (0, (x+1, y)) else inc6 (x+1, y)
    else inc5 (y)
  end // end of [inc6]

  and inc7: (int, (int, (int, (int, (int, (int, int)))))) -> unit = lam
    (xy: (int, (int, (int, (int, (int, (int, int))))))) => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test7 (x+1, y) then inc8 (0, (x+1, y)) else inc7 (x+1, y)
    else inc6 (y)
  end // end of [inc7]

  and inc8: (int, (int, (int, (int, (int, (int, (int, int))))))) -> unit = lam
    (xy: (int, (int, (int, (int, (int, (int, (int, int))))))))  => let
    val x = xy.0
    val y = xy.1
  in
    if (x < 8) then
      if test8 (x+1, y) then let
	val _ = board_pr (x+1, y) val _ = print ("\n")
      in
        inc8 (x+1, y)
      end else inc8 (x+1, y)
    else inc7 (y)
  end // end of [inc8]
in
  inc1 (0)
end // end of [queens]

*)

(* ****** ****** *)

(* end of [stfpl_main] *)
