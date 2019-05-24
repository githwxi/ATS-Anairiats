\begin{verbatim}
staload "prelude/SATS/file.sats" // it is loaded so that
// the functions [open_file] and [close_file] become available

#define MAXDIGIT 9 // [MAXDIGIT] is to be replaced with [9]

fun loop_one (fil: FILEref, row: int, col: int): void =
  if col <= row then let
    val () = if col > 1 then fprint_string (fil, " | ")
    val () = fprintf (fil, "%i*%i=%2.2i", @(col, row, col * row))
  in
    loop_one (fil, row, col + 1)
  end else begin
    fprint_newline (fil)
  end // end of [if]

fun loop_all (fil: FILEref, row: int): void =
  if row <= MAXDIGIT then begin
    loop_one (fil, row, 1); loop_all (fil, row + 1)
  end // end of [if]

implement main () = let
  val () = print_string ("Please input a name for the ouput file: ")
  val name = input_line (stdin_ref)
  val is_stdout = string0_is_empty name
  val fil = if is_stdout then stdout_ref else open_file (name, file_mode_w)
  val () = loop_all (fil, 1)
  val () = if is_stdout then exit (0) else close_file (fil)
in
  printf ("The multiplication table is now stored in the file [%s].", @(name));
  print_newline ()
end // end of [main]
\end{verbatim}
