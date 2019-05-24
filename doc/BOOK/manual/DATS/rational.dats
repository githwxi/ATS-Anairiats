%% extern fun gcd (p: int, q: int): int
\begin{figure}[thp]
\begin{verbatim}
staload "rational.sats"

assume rat = '{numer= int, denom= int} // a boxed record

implement rat_make_int (p) = '{numer= p, denom= 1}

fn rat_make_int_int_main (p: int, q: int): rat = let
  val g = gcd (p, q) in '{numer= p / g, denom= q / g}
end // end of [rat_make_int_int_main]

implement rat_make_int_int (p, q) = case+ 0 of
  | _ when q > 0 => rat_make_int_int_main (p, q)
  | _ when q < 0 => rat_make_int_int_main (~p, ~q)
  | _ (*q=0*) => $raise DenominatorIsZeroException ()

implement add_rat_rat (r1, r2) =
  rat_make_int_int_main (p1 * q2 + p2 * q1, q1 * q2) where {
  val '{numer=p1, denom=q1} = r1 and '{numer=p2, denom=q2} = r2
} // end of [add_rat_rat]

implement sub_rat_rat (r1, r2) =
  rat_make_int_int_main (p1 * q2 - p2 * q1, q1 * q2) where {
  val '{numer=p1, denom=q1} = r1 and '{numer=p2, denom=q2} = r2
} // end of [sub_rat_rat]

implement mul_rat_rat (r1, r2) = 
  rat_make_int_int_main (p1 * p2, q1 * q2) where {
  val '{numer=p1, denom=q1} = r1 and '{numer=p2, denom=q2} = r2
} // end of [mul_rat_rat]

implement div_rat_rat (r1, r2) =
  rat_make_int_int (p1 * q2, p2 * q1) where {
  val '{numer=p1, denom=q1} = r1 and '{numer=p2, denom=q2} = r2
} // end of [div_rat_rat]

implement fprint_rat (out, r) =
  let val p = r.numer and q = r.denom in
    if q = 1 then fprint_int (out, p) else begin
      fprint_int (out, p); fprint_char (out, '/'); fprint_int (out, q)
    end // end of [if]
  end // end of [fprint_rat]
\end{verbatim}
\caption{The content of rational.dats}
\label{figure:rational.dats}
\end{figure}



