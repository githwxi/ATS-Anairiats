\begin{verbatim}
extern fun list0_is_nil
  {a:type} (xs: list0 a): bool = "list0_is_nil"
// end of [extern]

implement list0_is_nil (xs) =
  case+ xs of list0_cons _ => true | list0_nil _ => false

exception ListIsEmpty
extern fun list0_tail {a:type} (xs: list0 a): list0 a = "list0_tail"
implement list0_tail (xs) = begin
  case+ xs of list0_cons (_, xs) => xs | list0_nil () => $raise ListIsEmpty
end // end of [list0_tail]

extern fun list0_length {a:type} (xs: list0 a): int = "list0_length"

%{

extern ats_ptr_type list0_tail (ats_ptr_type xs) ;

ats_int_type list0_length (ats_ptr_type xs) {
  int len = 0 ;
  while (1) {
    if (list0_is_nil (xs)) break ; xs = list0_tail (xs) ; len += 1 ;
  }
  return len ;
} /* end of list0_length */

%}
\end{verbatim}
