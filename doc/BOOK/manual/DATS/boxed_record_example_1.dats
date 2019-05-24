\begin{verbatim}
val boxed_1_2 = '{one= 1, two= 2}
val '{one= x, two= y} = boxed_1_2 // record pattern matching
val '{one= x, ...} = boxed_1_2 // record pattern matching with omission
val '{two= y, ...} = boxed_1_2 // record pattern matching with omission
val x = boxed_1_2.one and y = boxed_1_2.two // field selection
\end{verbatim}
