(*
** RMS: rate-monotonic scheduler
*)

(* ****** ****** *)
//
#define ATS_STALOADFLAG 0 // no run-time staloading
//
(* ****** ****** *)

abst@ype span = uint

(* ****** ****** *)

fun{} ZERO (): span

(* ****** ****** *)

fun sub_span_span (s1: span, s2: span): span
overload - with sub_span_span

fun lt_span_span (s1: span, s2: span): bool
overload < with lt_span_span
fun lte_span_span (s1: span, s2: span): bool
overload <= with lte_span_span

fun gt_span_span (s1: span, s2: span): bool
overload > with gt_span_span
fun gte_span_span (s1: span, s2: span): bool
overload >= with gte_span_span

(* ****** ****** *)

abst@ype tick = uint

fun add_tick_span (t1: tick, s2: span): tick
overload + with add_tick_span

fun sub_tick_tick (t1: tick, t2: tick): span
overload - with sub_tick_tick

fun lt_tick_tick (t1: tick, t2: tick): bool
overload < with lt_tick_tick
fun lte_tick_tick (t1: tick, t2: tick): bool
overload <= with lte_tick_tick

(* ****** ****** *)

abst@ype pid = int // process id

(* ****** ****** *)

abstype process = ptr // boxed record

fun process_get_pid (p: process): pid // fixed

fun process_get_period (p: process): span // fixed
fun process_get_capacity (p: process): span // fixed

fun process_get_budget (p: process): span
fun process_set_budget (p: process, s: span): void

fun process_get_replenish (p: process): tick
fun process_set_replenish (p: process, t: tick): void
fun process_reset_replenish (p: process): void

(* ****** ****** *)

absviewtype
processopt_vtype (bool)
stadef processopt = processopt_vtype
viewtypedef processopt = [b:bool] processopt b

(* ****** ****** *)

absviewtype
processlst_vtype (n:int)
stadef processlst = processlst_vtype
viewtypedef processlst = [n:nat] processlst (n)

prfun
processlst_free_nil (xs: processlst (0)): void

fun
processlst_is_cons
  {n:int} (xs: !processlst (n)): bool (n > 0)
// end of [processlst_is_cons]

fun
processlst_uncons
  {n:int | n > 0}
  (xs: processlst n, x: &process? >> process): processlst (n-1)
// end of [processlst_uncons]

(* ****** ****** *)
//
// various specific functions
//
(* ****** ****** *)

fun timer_32k_value (): tick
fun timer_32k_delay (s: span): void

(* ****** ****** *)

fun schedule (): void

(* ****** ****** *)

(* end of [rms.sats] *)
