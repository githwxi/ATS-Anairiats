(*
** RMS: rate-monotonic scheduler
*)

(* ****** ****** *)

(*
** It is primarily based on an implementation by Matthew Danish
*)

(* ****** ****** *)

staload "rms.sats"

(* ****** ****** *)

extern
fun budget_is_negligible (b: span): bool

(* ****** ****** *)

extern fun pvttimer_set (n: tick): void
extern fun arm_read_cycle_counter (): int

(* ****** ****** *)

extern fun get_prev_span (): span
extern fun get_prev_timer_val (): span

extern fun get_process_current (): process

(* ****** ****** *)

extern fun do_process_switch (p: process): void

(* ****** ****** *)

extern fun the_processlst_get (): processlst

(* ****** ****** *)

local

fun process_adjust_budget
  (p: process, s0: span): void = let
  val b = process_get_budget (p)
  val b = (
    if b >= s0 then b - s0 else ZERO()
  ) : span // end of [val]
  val b = (
    if budget_is_negligible (b) then ZERO() else b
  ) : span // end of [val]
  val () = process_set_budget (p, b)
in
  // nothing
end // end of [process_adjust_budget]

fun process_adjust_replenish
  (p: process, t0: tick): void = let
  val r = process_get_replenish (p)
in
  if r <= t0 then let
    val () = process_reset_replenish (p)
  in
    process_adjust_replenish (p, t0)
  end else () // end of [if]
end // end of [process_adjust_replenish]

fun processlst_adjust_replenish
  {n:nat} (
  ps: processlst (n), t0: tick
) : void = let
in
  if processlst_is_cons (ps) then let
    var p: process
    val ps = processlst_uncons (ps, p)
    val () = process_adjust_replenish (p, t0)
  in
    processlst_adjust_replenish (ps, t0)
  end else let
    prval () = processlst_free_nil (ps)
  in
    // nothing
  end // end of [if]
end // end of [processlst_adjust_replenish]

extern
fun processlst_select_period
  {n:nat} (ps: processlst (n)): process
// end of [processlst_select_period]

fun processlst_find_pvttimer_val
  {n:nat} (
  ps: processlst (n), p_next: process, t_now: tick
) : tick = let
//
fun loop {n:nat} (
  ps: processlst (n), T0: span, res: tick
) : tick = let
in
  if processlst_is_cons (ps) then let
    var p: process
    val ps = processlst_uncons (ps, p)
    val T = process_get_period (p)
  in
    if T < T0 then let
      val R = process_get_replenish (p)
      val res = (if R < res then R else res): tick
    in
      loop (ps, T0, res)
    end else
      loop (ps, T0, res)
    // end of [if]
  end else let
    prval () = processlst_free_nil (ps)
  in
    res
  end // end of [if]
end // end of [loop]
//
val T0 = process_get_period (p_next)
val res = t_now + process_get_budget (p_next)
//
in
  loop (ps, T0, res)
end // end of [processlst_find_pvttimer_val]

in // in of [local]

implement
schedule () = let
//
  val prev_span = get_prev_span ()
  val p_current = get_process_current ()
  val () = process_adjust_budget (p_current, prev_span)
//
  val t_now = timer_32k_value ()
//
  val ps = the_processlst_get ()
  val () = processlst_adjust_replenish (ps, t_now)
//
  val ps = the_processlst_get ()
  val p_next = processlst_select_period (ps)
  val ps = the_processlst_get ()
  val t_val = processlst_find_pvttimer_val (ps, p_next, t_now)
  val () = pvttimer_set (t_val)
//
  val () = do_process_switch (p_next)
//
in
end // end of [schedule]

end // end of [local]

(* ****** ****** *)

(* end of [rms_sched.dats] *)
