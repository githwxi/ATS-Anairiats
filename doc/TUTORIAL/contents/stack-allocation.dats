//
// code used for illustration in stack-allocation.html
//

(* ****** ****** *)

fn name_of_month_1 {i:int | 1 <= i; i <= 12} (i: int i): string = let
  var !p_arr with pf_arr = @[string](
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"
  )
in
  p_arr->[i-1]
end // end of [name_of_month_1]

fn name_of_month_2 {i:int | 1 <= i; i < 12} (i: int i): string = let
  var !p_arr with pf_arr = @[string][12]("")
  val () = p_arr->[0] := "Jan"
  val () = p_arr->[1] := "Feb"
  val () = p_arr->[2] := "Mar"
  val () = p_arr->[3] := "Apr"
  val () = p_arr->[4] := "May"
  val () = p_arr->[5] := "Jun"
  val () = p_arr->[6] := "Jul"
  val () = p_arr->[7] := "Aug"
  val () = p_arr->[8] := "Sep"
  val () = p_arr->[9] := "Oct"
  val () = p_arr->[10] := "Nov"
  val () = p_arr->[11] := "Dec"
in
  p_arr->[i-1]
end // end of [name_of_month_2]

(* ****** ****** *)

fn print_month_names () = let
  var !p_arr with pf_arr = @[string](
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"
  )
  var !p_clo with pf_clo = @lam // this closure is allocated in the stack frame
    (pf: !unit_v | i: sizeLt 12, x: &string): void =<clo> $effmask_all (if i > 0 then print ", "; print x)
  // end of [var]
  prval pf = unit_v ()
  val () = array_ptr_iforeach_clo_tsz {string} {unit_v} (pf | !p_arr, !p_clo, 12, sizeof<string>)
  prval unit_v () = pf
  val () = print_newline ()
in
  // empty
end // end of [print_month_names]

(* ****** ****** *)

// print out a line segment in the reverse order
fn print_lineseg_rev {m,n:nat} {st,len:nat | st + len <= n}
  (buf: &strbuf (m, n), st: size_t st, len: size_t len):<!ref> void = let
  var i: intBtw (0, len+1) // uninitialized
  // too lazy to prove the termination of the following loop
  val () = $effmask_ntm (for (i := 0; i < len; i := i+1) print buf[st + len - i - 1])
in
  // empty
end // end of [print_lineseg_rev]

(* ****** ****** *)

#define BUFSZ 1024

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

extern fun print_file_rev (): void

implement print_file_rev () = let
  var !p_buf with pf_buf = @[byte][BUFSZ]() // allocation in the stack frame
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  val (pf_stdin | p_stdin) = stdin_get ()
  val () = while (true) let
    val () = fgets_exn (file_mode_lte_r_r, pf_buf | p_buf, BUFSZ, !p_stdin)
    val n = strbuf_length (!p_buf) // n needs to be positive
    val () = if (n = 0) then let
      prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
    in
      break // loop exits
    end // end of [val]
    val () = assert (n > 0) // the check is redundant at run-time
    val c_last = strbuf_get_char_at (!p_buf, n-1)
  in
    if c_last = '\n' then let
      val () = (print_lineseg_rev (!p_buf, 0, n-1); print '\n')
    in
      pf_buf := bytes_v_of_strbuf_v (pf_buf)
    end else let
      val () = print_lineseg_rev (!p_buf, 0, n)
    in
      pf_buf := bytes_v_of_strbuf_v (pf_buf)
    end // end of [if]
  end // end of [val]
  val () = stdin_view_set (pf_stdin | (*none*))
in
  // empty
end // end of [main]

(* ****** ****** *)

implement main () = let
  val () = print_file_rev ()
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [stack-allocation.dats] *)
