\begin{verbatim}
// this is wrong
fun sway_bool_char (xy: @(bool, char)): @(bool, char) =
  sway_type_type {char,bool} (xy)

// this is right
fun sway_string_string (xy: @(string, string)): @(string, string)
  = sway_type_type {string,string} (xy)
\end{verbatim}
