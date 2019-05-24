%%{^
%
%typedef double T ;
%
%%}
%
\begin{verbatim}
abst@ype T = $extype "T"
extern typedef "list0_cons_pstruct" = list0_cons_pstruct (T, list0 T)
extern fun list0_append (xs: list0 T, ys: list0 T): list0 T = "list0_append"

%{

// how [list0_cons_make] should be implemented is to be
extern list0_cons_pstruct list0_cons_make () ; // discussed later

ats_ptr_type
list0_append (ats_ptr_type xs, ats_ptr_type ys) {
  list0_cons_pstruct res0, res, res_nxt ;
  if (list0_is_nil (xs)) return ys ;
  res0 = res = list0_cons_make () ;
  while (1) { /* invariant: [res] is not null */
    res->atslab_0 = ((list0_cons_pstruct)xs)->atslab_0 ;
    xs = ((list0_cons_pstruct)xs)->atslab_1 ;
    if (!xs) break ;
    res_nxt = list0_cons_make () ;
    res->atslab_1 = res_nxt ; res = res_nxt ;
  } /* end of [while] */
  res->atslab_1 = ys ; return res0 ;
} /* end of list0_append */

%}
\end{verbatim}
