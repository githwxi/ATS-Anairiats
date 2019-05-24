%%staload "libc/SATS/time.sats"
\begin{verbatim}
implement main () = let
  // obtain the number of seconds since the Epoch
  var ntick: time_t = time_get ()
  // allocate memory in the stack frame
  var !p_buf with pf_buf = @[byte][CTIME_BUFLEN]()
  // turn the number into a string representation
  val _(*p_buf*) = ctime_r (pf_buf | ntick, p_buf)
  val () = print (!p_buf) // print out the string representation
in
  pf_buf := bytes_v_of_strbuf_v (pf_buf) // change the view of pf_buf
  // to @[byte][CTIME_BUFEN] @ p_buf as is expected by the typechecker
end // end of [main]
\end{verbatim}
